import asyncio
import itertools
import json
import os
import random
import shutil
import time
from collections import Counter, defaultdict
from typing import Optional

import discord
from discord import app_commands
from discord.ext import commands, tasks

# ---------------------------------------------------------------- settings
MODES = {"1v1": 2, "2v2": 4, "3v3": 6}  # mode -> players needed
VOTES_NEEDED = 3                         # approvals needed to change a result
VOTE_SECONDS = 15 * 60                   # how long an undo vote stays open
MIN_GAMES_TOGETHER = 2                   # games needed before a teammate is ranked
ENROLL_ROLE = "pendi6man"                # default role name used by /setup
PING_TEXT = "players are in sixmans looking for more"  # fixed message sent by /ping

# Elo (one rating per player, shared across 1v1 / 2v2 / 3v3)
START_ELO = 1000          # everyone starts here (the middle of the scale)
ELO_FLOOR = 100           # ratings never drop below this
K_FACTOR = 32             # base points per game (higher = faster swings, good for small groups)
STREAK_BONUS = 0.15       # extra +15% per game in a row after the first...
STREAK_CAP = 1.75         # ...up to this multiplier (win streaks gain more, loss streaks lose more)
BALANCE_TOLERANCE = 30    # balanced teams: splits this close to the fairest one are picked from at random
TEAM_TOP_WEIGHT = 0.25    # team rating = mean of its players, pulled this far toward its best player
PLAYER_WEIGHT = 0.4       # how much a player's own rating (vs. the team's) shapes their expected result
UPSET_BONUS = 0.25        # up to +25% swing when the lower-rated team beats the higher-rated one
UPSET_FULL_GAP = 400      # rating gap at which the full upset bonus applies
# How big Elo swings are per mode (3v3 is the full-strength baseline). Scales gains, losses,
# streak and upset effects, and the MVP bonus. Smaller games are noisier, so they move ratings less.
MODE_INTENSITY = {"1v1": 0.6, "2v2": 0.8, "3v3": 1.0}
MVP_BONUS = 5             # extra Elo for the winning team's MVP (picked by the losing team)
MVP_VOTE_SECONDS = 120      # seconds the losing team has to vote (2v2 and 3v3 only)
PANEL_REFRESH_SECONDS = 30  # how often the bot checks that the queue panel is the newest message

# Profile picture rotation: put image files in this folder (on the computer running the bot)
AVATAR_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "avatars")
AVATAR_EXTENSIONS = (".png", ".jpg", ".jpeg", ".gif", ".webp")
AVATAR_CHANGE_HOURS = 24    # how often the picture changes
AVATAR_MAX_BYTES = 8 * 1024 * 1024  # bigger files are skipped

QUEUE_TIMEOUT_MINUTES = 30  # a player waiting this long with no game starting is removed from the queue

LOBBY_WAIT_SECONDS = 300    # how long a 2v2/3v3 waits for everyone to join the lobby voice channel

# Posted in the queue channel each time the bot starts, then deleted again.
ONLINE_MESSAGE = "Pendis Rocket League Queue Bot is now online"
ONLINE_MESSAGE_SECONDS = 120  # how long it stays before the bot deletes it

# The bot's status text (shown under its name in the member list) rotates through tips and fun facts.
STATUS_MINUTES = 5          # how often the status changes
STATUS_FACT_EVERY = 3       # every 3rd change is a fun fact about a player (the others are tips)
CONGRATS_SECONDS = 120      # after a result is reported, the status congratulates the winners this long
STATUS_STYLE = "watching"   # "watching", "playing", "listening", or "custom" (free text; see note in the docs)
FACTS_FALLBACK_TO_ALL = True  # if nobody is in a queue, pick the fun fact from any enrolled player
# Tips only mention commands everyone can use, never admin ones.
STATUS_TIPS = [
    "/help to see a list of commands",
    "/enroll6mans to join the 6mans and unlock queuing",
    "/queue or tap the queue panel buttons to find a game",
    "/stats to see your record, Elo and streaks",
    "/stats @player to check someone else's stats",
    "/leaderboard to see who's on top in each mode",
    "/headtohead @player to compare your record against theirs",
    "/records for your best win streaks and Elo peaks",
    "/matchfinder to look up any past match by its number",
    "/ping to let everyone know more players are needed",
    "/status to see who's waiting in each queue",
    "/leave to step out of the queue",
    "/undo if a result was reported wrong",
    "Balanced teams split players by Elo",
    "2v2 and 3v3 are best of 3. 1v1 is best of 1",
    "In 2v2 and 3v3 the losing team can vote an MVP",
    "Join the lobby voice channel before a 2v2 or 3v3 starts",
    "Win streaks earn extra Elo, loss streaks cost extra",
    "Queues time out after 30 minutes with no game",
    "Report your match result so you can queue again",
]
VOICE_VOTE_SECONDS = 120    # how long players have to vote on using team voice channels

# Draft picks are read from @mentions. Discord still sends the mention list
# without the privileged "Message Content" intent. If picks aren't being
# detected, turn that intent on in the Developer Portal (Bot tab) and set
# this to True.
USE_MESSAGE_CONTENT = False

APPROVE, REJECT = "\u2705", "\u274c"     # check / x

# ------------------------------------------------------------------ storage
DATA_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rl_data.json")


def load_data() -> dict:
    try:
        with open(DATA_FILE, "r") as f:
            d = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        d = {}
    d.setdefault("next_id", 1)
    d.setdefault("matches", [])
    d.setdefault("profiles", {})  # user id (str) -> {"name": ..., "enrolled": unix time}
    d.setdefault("config", {})    # guild id (str) -> {"home_channel_id": ..., "queue_role_id": ...}
    return d


def save_data() -> None:
    tmp = DATA_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, DATA_FILE)


data = load_data()
queues: dict[str, list[int]] = {mode: [] for mode in MODES}
# user id -> when and where they joined, for players currently waiting (used for the queue timeout)
queue_joined: dict[int, dict] = {}
pending_votes: dict[int, dict] = {}  # vote message id -> info (resets on restart)


def get_match(match_id: int) -> Optional[dict]:
    return next((m for m in data["matches"] if m["id"] == match_id), None)


def match_by_message(message_id: int) -> Optional[dict]:
    return next((m for m in data["matches"] if m.get("message_id") == message_id), None)


def match_by_prompt(message_id: int) -> Optional[dict]:
    return next((m for m in data["matches"] if m.get("prompt_message_id") == message_id), None)


def team_of(m: dict, uid: int) -> Optional[str]:
    if uid in m["blue"]:
        return "blue"
    if uid in m["orange"]:
        return "orange"
    return None


def finished_matches(uid: int) -> list[dict]:
    return [m for m in data["matches"] if m["winner"] and team_of(m, uid)]


def did_win(m: dict, uid: int) -> bool:
    return m["winner"] == team_of(m, uid)


def record_matches(uid: int) -> list[dict]:
    """Matches that count toward a player's win/loss record (those after their last W/L reset in that mode)."""
    profile = data["profiles"].get(str(uid), {})
    return [
        m for m in finished_matches(uid)
        if m.get("reported_at", m["created"]) > reset_time(profile, m["mode"], "wl")
    ]


def series_scores(m: dict) -> Optional[tuple[int, int]]:
    """(blue games, orange games) for a best-of-3 series, or None if no series score was reported."""
    s = m.get("series")
    if not s or not m.get("winner"):
        return None
    won, lost = s
    return (won, lost) if m["winner"] == "blue" else (lost, won)


def score_for(m: dict, uid: int) -> str:
    """The series score from this player's side, like ' 2-1' (empty if there isn't one)."""
    scores = series_scores(m)
    team = team_of(m, uid)
    if not scores or not team:
        return ""
    mine, theirs = (scores[0], scores[1]) if team == "blue" else (scores[1], scores[0])
    return f" {mine}-{theirs}"


def stamp_resets(existing, modes: list[str]) -> dict:
    """Per-mode reset times: set `modes` to now, keep the rest (older saves stored one number for all modes)."""
    now = time.time()
    stamps = dict(existing) if isinstance(existing, dict) else {md: (existing or 0) for md in MODES}
    for md in modes:
        stamps[md] = now
    return stamps


def active_match_for(uid: int) -> Optional[dict]:
    """A match this player is in whose result hasn't been reported yet (None if they're free to queue)."""
    for m in data["matches"]:
        if not m["winner"] and uid in (m.get("players") or m["blue"] + m["orange"]):
            return m
    return None


def format_text(mode: str) -> str:
    """How a match in this mode is played."""
    if mode == "1v1":
        return "Best of 1 (one game decides it)"
    return "Best of 3 (first team to win 2 games wins the series)"


def mention_list(ids: list[int]) -> str:
    return "\n".join(f"<@{u}>" for u in ids) or "-"


def get_config(guild_id: Optional[int]) -> Optional[dict]:
    """Home channel and queue role chosen with /setup (None until it's been run)."""
    return data["config"].get(str(guild_id))


# -------------------------------------------------------------------- queue
def remove_from_all(user_id: int) -> None:
    queue_joined.pop(user_id, None)
    for q in queues.values():
        if user_id in q:
            q.remove(user_id)


def status_embed() -> discord.Embed:
    embed = discord.Embed(title="Rocket League Queues", color=0x1E90FF)
    for mode, size in MODES.items():
        players = queues[mode]
        names = ", ".join(f"<@{uid}>" for uid in players) or "Empty"
        embed.add_field(name=f"{mode} ({len(players)}/{size})", value=names, inline=False)
    return embed


panel_lock = asyncio.Lock()


def queue_channel_id(cfg: dict) -> int:
    """Where queuing happens: the /set-queue-channel channel, or the /setup home channel."""
    return cfg.get("queue_channel_id") or cfg["home_channel_id"]


async def post_panel(cfg: dict, channel) -> None:
    """Delete the old standing panel (if any) and post a fresh one at the bottom of `channel`."""
    old_channel, old_message = cfg.get("panel_channel_id"), cfg.get("panel_message_id")
    if old_channel and old_message:
        try:
            await bot.get_partial_messageable(old_channel).get_partial_message(old_message).delete()
        except discord.HTTPException:
            pass
    cfg["panel_message_id"] = None
    msg = await channel.send(embed=status_embed(), view=QueueView())
    cfg["panel_channel_id"], cfg["panel_message_id"] = channel.id, msg.id
    save_data()


async def keep_panel_on_top(cfg: dict) -> None:
    """Make sure the panel exists in the queue channel and is that channel's newest message."""
    channel = bot.get_channel(queue_channel_id(cfg))
    if channel is None:
        return
    message_id = cfg.get("panel_message_id")
    if message_id and cfg.get("panel_channel_id") == channel.id:
        try:
            newest = [m async for m in channel.history(limit=1)]
        except discord.HTTPException:
            return
        if newest and newest[0].id == message_id:
            return  # already the most recent message
    await post_panel(cfg, channel)


async def refresh_panels() -> None:
    # the lock keeps edits in order, and the embed is built inside it
    # so the last edit always shows the latest queue state
    async with panel_lock:
        embed = status_embed()
        for cfg in data["config"].values():
            channel_id, message_id = cfg.get("panel_channel_id"), cfg.get("panel_message_id")
            if not (channel_id and message_id):
                continue
            msg = bot.get_partial_messageable(channel_id).get_partial_message(message_id)
            try:
                await msg.edit(embed=embed)
            except discord.NotFound:
                cfg["panel_message_id"] = None  # panel was deleted; the next check re-posts it
                save_data()
            except discord.HTTPException:
                pass


def queues_changed() -> None:
    asyncio.create_task(refresh_panels())


@tasks.loop(seconds=PANEL_REFRESH_SECONDS)
async def bump_panels() -> None:
    async with panel_lock:
        for cfg in list(data["config"].values()):
            try:
                await keep_panel_on_top(cfg)
            except discord.HTTPException:
                pass


@bump_panels.before_loop
async def before_bump_panels() -> None:
    await bot.wait_until_ready()


# ------------------------------------------------------- channel management
async def resolve_members(guild: discord.Guild, ids: list[int]) -> list[discord.Member]:
    out = []
    for uid in ids:
        try:
            out.append(guild.get_member(uid) or await guild.fetch_member(uid))
        except discord.HTTPException:
            pass
    return out


async def create_text_channel(guild, category, match_id, players, fallback):
    """Private text channel for the match. Returns (channel, created_by_us)."""
    name = f"match-{match_id}"
    reason = f"Rocket League match {match_id}"
    overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        guild.me: discord.PermissionOverwrite(
            view_channel=True, send_messages=True, embed_links=True, read_message_history=True
        ),
    }
    for member in await resolve_members(guild, players):
        overwrites[member] = discord.PermissionOverwrite(
            view_channel=True, send_messages=True, read_message_history=True
        )
    try:
        return await guild.create_text_channel(
            name, category=category, overwrites=overwrites, reason=reason
        ), True
    except discord.Forbidden:
        # can't set private permissions: fall back to an open channel
        try:
            return await guild.create_text_channel(name, category=category, reason=reason), True
        except discord.HTTPException:
            return fallback, False
    except discord.HTTPException:
        return fallback, False


async def create_voice_channels(guild, category, match_id, blue, orange):
    """Private voice channel per team. Returns (channel_ids, success)."""
    ids: list[int] = []
    for team, members in (("Blue", blue), ("Orange", orange)):
        name = f"Match {match_id} - {team}"
        reason = f"Rocket League match {match_id}"
        overwrites = {
            guild.default_role: discord.PermissionOverwrite(connect=False),
            guild.me: discord.PermissionOverwrite(view_channel=True, connect=True),
        }
        for member in await resolve_members(guild, members):
            overwrites[member] = discord.PermissionOverwrite(connect=True, view_channel=True)
        try:
            ch = await guild.create_voice_channel(
                name, category=category, overwrites=overwrites, reason=reason
            )
        except discord.Forbidden:
            try:
                ch = await guild.create_voice_channel(name, category=category, reason=reason)
            except discord.HTTPException:
                return ids, False
        except discord.HTTPException:
            return ids, False
        ids.append(ch.id)
    return ids, True


async def delete_match_channels(guild: Optional[discord.Guild], m: dict) -> None:
    """Delete the match's voice channels and (if we made it) its text channel."""
    if guild is None:
        return
    targets = list(m.get("vc", []))
    if m.get("text_owned") and m.get("text_channel_id"):
        targets.append(m["text_channel_id"])
    for cid in targets:
        ch = guild.get_channel(cid)
        if ch:
            try:
                await ch.delete(reason=f"Match {m['id']} finished")
            except discord.HTTPException:
                pass
    m["vc"] = []
    m["text_channel_id"] = None
    save_data()


# ------------------------------------------------------------- match flow
async def join_queue(interaction: discord.Interaction, mode: str) -> None:
    user_id = interaction.user.id
    q = queues[mode]

    cfg = get_config(interaction.guild_id)
    if not cfg:
        await interaction.response.send_message(
            "An admin needs to run **/setup** before queues can be used.", ephemeral=True
        )
        return
    if interaction.channel_id != queue_channel_id(cfg):
        await interaction.response.send_message(
            f"Queues live in <#{queue_channel_id(cfg)}>. Head over there to join.", ephemeral=True
        )
        return
    has_role = cfg["queue_role_id"] in {r.id for r in interaction.user.roles}
    if str(user_id) not in data["profiles"] or not has_role:
        await interaction.response.send_message(
            "You need to enroll before you can play. Run **/enroll6mans**, then join a queue.",
            ephemeral=True,
        )
        return

    active = active_match_for(user_id)
    if active:
        where = f" in <#{active['text_channel_id']}>" if active.get("text_channel_id") else ""
        await interaction.response.send_message(
            f"You're still in match #{active['id']}{where}. Once its result is reported you can queue again.",
            ephemeral=True,
        )
        return

    if user_id in q:
        await interaction.response.send_message(f"You're already in the {mode} queue.", ephemeral=True)
        return

    remove_from_all(user_id)  # one queue at a time
    q.append(user_id)
    queue_joined[user_id] = {
        "time": time.time(),
        "guild_id": interaction.guild_id,
        "channel_id": interaction.channel_id,
    }

    if len(q) < MODES[mode]:
        queues_changed()
        await interaction.response.send_message(
            f"Joined **{mode}** ({len(q)}/{MODES[mode]}). "
            f"You'll be removed after {QUEUE_TIMEOUT_MINUTES} minutes if no game starts.",
            ephemeral=True
        )
        return

    # queue is full: create the match
    await interaction.response.defer()  # channel creation can take a moment
    players = q[:]
    q.clear()
    for uid in players:
        queue_joined.pop(uid, None)
    queues_changed()
    guild = interaction.guild
    category = getattr(interaction.channel, "category", None)

    match_id = data["next_id"]
    data["next_id"] += 1
    text_ch, owned = await create_text_channel(guild, category, match_id, players, interaction.channel)

    m = {
        "id": match_id,
        "mode": mode,
        "players": players,
        "blue": [],
        "orange": [],
        "winner": None,
        "created": int(time.time()),
        "state": "pick",  # pick -> draft -> active -> done
        "origin_channel_id": interaction.channel.id,
        "text_channel_id": text_ch.id,
        "text_owned": owned,
        "vc": [],
        "message_id": None,
        "prompt_message_id": None,
        "guild_id": interaction.guild_id,
        "voice": True if mode == "1v1" else None,  # None = the team voice channel vote is still open
    }
    data["matches"].append(m)
    save_data()

    pings = " ".join(f"<@{u}>" for u in players)
    announce = discord.Embed(
        title=f"Match #{match_id} - {mode} ready!",
        description=f"Head to {text_ch.mention} to sort out teams.\n**Format:** {format_text(mode)}",
        color=0x2ECC71,
    )
    await interaction.followup.send(content=pings, embed=announce)

    if mode == "1v1":
        shuffled = players[:]
        random.shuffle(shuffled)
        m["team_mode"] = "Random"
        await finalize_match(guild, m, [shuffled[0]], [shuffled[1]])
        return

    # 2v2 / 3v3: wait for everyone in the lobby voice channel (if one is set), then ask about teams
    if lobby_channel(guild) is not None:
        await start_lobby_wait(guild, m, pings)
    else:
        await start_team_selection(guild, m, pings)


# ------------------------------------------------------ lobby and voice vote
def lobby_channel(guild: discord.Guild):
    cfg = get_config(guild.id)
    return guild.get_channel(cfg.get("lobby_vc_id") or 0) if cfg else None


def lobby_progress(guild: discord.Guild, m: dict) -> tuple[int, list[int]]:
    """(how many of the match's players are in the lobby voice channel, who is still missing)."""
    lobby = lobby_channel(guild)
    here = set(lobby.voice_states) if lobby else set()
    missing = [u for u in m["players"] if u not in here]
    return len(m["players"]) - len(missing), missing


def lobby_embed(guild: discord.Guild, m: dict) -> discord.Embed:
    lobby = lobby_channel(guild)
    present, missing = lobby_progress(guild, m)
    embed = discord.Embed(title=f"Match #{m['id']} - waiting for players", color=0xF1C40F)
    embed.description = (
        f"Everyone needs to join {lobby.mention if lobby else 'the lobby voice channel'} first. "
        f"Once all {len(m['players'])} players are in, I'll ask how to make teams.\n"
        f"I'll continue on my own <t:{int(m['lobby_deadline'])}:R>."
    )
    embed.add_field(
        name=f"In the lobby ({present}/{len(m['players'])})",
        value=("Still needed:\n" + mention_list(missing)) if missing else "Everyone is here!",
        inline=False,
    )
    return embed


async def start_lobby_wait(guild: discord.Guild, m: dict, pings: str) -> None:
    channel = guild.get_channel(m["text_channel_id"])
    if channel is None:
        return
    m["state"] = "lobby"
    m["lobby_deadline"] = time.time() + LOBBY_WAIT_SECONDS
    msg = await channel.send(content=pings, embed=lobby_embed(guild, m), view=LobbyView())
    m["lobby_message_id"] = msg.id
    m["lobby_count"] = lobby_progress(guild, m)[0]
    save_data()
    asyncio.create_task(lobby_expiry(m["id"], LOBBY_WAIT_SECONDS))
    await check_lobby(guild, m)  # some of them may already be in there


async def check_lobby(guild: discord.Guild, m: dict, force: bool = False) -> None:
    """Move on once everyone is in the lobby (or when forced by the skip button or the timeout)."""
    if m.get("state") != "lobby":
        return
    present, missing = lobby_progress(guild, m)
    message = bot.get_partial_messageable(m["text_channel_id"]).get_partial_message(m["lobby_message_id"])
    if force or not missing:
        m["state"] = "pick"  # claimed right away so this only runs once
        save_data()
        embed = lobby_embed(guild, m)
        embed.description = (
            "Everyone is in the lobby. Moving on to team selection."
            if not missing
            else "Moving on without waiting for everyone."
        )
        try:
            await message.edit(embed=embed, view=None)
        except discord.HTTPException:
            pass
        await start_team_selection(guild, m)
        return
    if present != m.get("lobby_count"):
        m["lobby_count"] = present
        save_data()
        try:
            await message.edit(embed=lobby_embed(guild, m))
        except discord.HTTPException:
            pass


async def lobby_expiry(match_id: int, delay: float) -> None:
    await bot.wait_until_ready()
    await asyncio.sleep(delay)
    m = get_match(match_id)
    guild = bot.get_guild(m.get("guild_id") or 0) if m else None
    if m and guild and m.get("state") == "lobby":
        await check_lobby(guild, m, force=True)


class LobbyView(discord.ui.View):
    """Lets the players stop waiting for the lobby. Looked up by message id, so it survives restarts."""

    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="Continue without waiting", style=discord.ButtonStyle.secondary, custom_id="rl:lobby:skip")
    async def skip(self, interaction: discord.Interaction, button: discord.ui.Button):
        m = next((x for x in data["matches"] if x.get("lobby_message_id") == interaction.message.id), None)
        if not m or m.get("state") != "lobby":
            await interaction.response.send_message("This match already moved on.", ephemeral=True)
            return
        if interaction.user.id not in m["players"]:
            await interaction.response.send_message("Only players in this match can do that.", ephemeral=True)
            return
        await interaction.response.defer()
        await check_lobby(interaction.guild, m, force=True)


async def start_team_selection(guild: discord.Guild, m: dict, pings: Optional[str] = None) -> None:
    """Post the team choice and the team voice channel vote in the match text channel."""
    channel = guild.get_channel(m["text_channel_id"])
    if channel is None:
        return
    m["state"] = "pick"
    pings = pings or " ".join(f"<@{u}>" for u in m["players"])
    prompt = discord.Embed(
        title=f"Match #{m['id']} - choose teams",
        description=f"**Format: {format_text(m['mode'])}**\nAny player in this match can pick how teams are made.",
        color=0x3498DB,
    )
    msg = await channel.send(content=pings, embed=prompt, view=TeamModeView())
    m["prompt_message_id"] = msg.id

    m["voice"] = None
    m["voice_votes"] = {}
    m["voice_deadline"] = time.time() + VOICE_VOTE_SECONDS
    vote = await channel.send(embed=voice_prompt_embed(m), view=VoiceChoiceView())
    m["voice_prompt_message_id"] = vote.id
    save_data()
    asyncio.create_task(voice_expiry(m["id"], VOICE_VOTE_SECONDS))


def voice_pending(m: dict) -> bool:
    return "voice" in m and m["voice"] is None


def voice_tally(m: dict) -> tuple[int, int]:
    votes = m.get("voice_votes", {})
    yes = sum(1 for v in votes.values() if v)
    return yes, len(votes) - yes


def voice_result(m: dict) -> Optional[bool]:
    """The outcome once a majority is reached (or everyone has voted), else None. A tie means Yes."""
    yes, no = voice_tally(m)
    needed = len(m["players"]) // 2 + 1
    if yes >= needed:
        return True
    if no >= needed:
        return False
    if yes + no == len(m["players"]):
        return yes >= no
    return None


def voice_prompt_embed(m: dict) -> discord.Embed:
    embed = discord.Embed(title="Will team voice channels be used?", color=0x9B59B6)
    if m.get("voice") is None:
        yes, no = voice_tally(m)
        embed.description = (
            "Vote **Yes** or **No**. The majority decides (a tie, or no votes, means Yes).\n"
            f"Closes <t:{int(m['voice_deadline'])}:R>.\n\n"
            f"Yes: **{yes}**   No: **{no}**   ({len(m['players'])} players)"
        )
    elif m["voice"]:
        embed.description = "Team voice channels: **Yes**. They'll be created once teams are set."
    else:
        embed.description = "Team voice channels: **No**. The match will start without them."
    return embed


def disabled_copy(view: discord.ui.View) -> discord.ui.View:
    done = type(view)()
    for child in done.children:
        child.disabled = True
    return done


class VoiceChoiceView(discord.ui.View):
    """Yes / No vote on team voice channels. Looked up by message id, so it survives restarts."""

    def __init__(self):
        super().__init__(timeout=None)

    async def cast(self, interaction: discord.Interaction, choice: bool):
        m = next((x for x in data["matches"] if x.get("voice_prompt_message_id") == interaction.message.id), None)
        if not m:
            await interaction.response.send_message("I can't find this match.", ephemeral=True)
            return
        if interaction.user.id not in m["players"]:
            await interaction.response.send_message("Only players in this match can vote.", ephemeral=True)
            return
        if not voice_pending(m):
            await interaction.response.send_message("This vote is already closed.", ephemeral=True)
            return
        m["voice_votes"][str(interaction.user.id)] = choice
        result = voice_result(m)
        if result is not None:
            m["voice"] = result
        save_data()
        await interaction.response.edit_message(
            embed=voice_prompt_embed(m), view=self if result is None else disabled_copy(self)
        )
        if result is not None:
            await maybe_finalize(interaction.guild, m)

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.success, custom_id="rl:voice:yes")
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.cast(interaction, True)

    @discord.ui.button(label="No", style=discord.ButtonStyle.danger, custom_id="rl:voice:no")
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.cast(interaction, False)


async def voice_expiry(match_id: int, delay: float) -> None:
    """If the vote isn't settled in time, go with the votes so far (a tie or no votes means Yes)."""
    await bot.wait_until_ready()
    await asyncio.sleep(delay)
    m = get_match(match_id)
    if not m or not voice_pending(m):
        return
    yes, no = voice_tally(m)
    m["voice"] = yes >= no
    save_data()
    try:
        message = bot.get_partial_messageable(m["text_channel_id"]).get_partial_message(m["voice_prompt_message_id"])
        await message.edit(embed=voice_prompt_embed(m), view=disabled_copy(VoiceChoiceView()))
    except (discord.HTTPException, TypeError):
        pass
    guild = bot.get_guild(m.get("guild_id") or 0)
    if guild:
        await maybe_finalize(guild, m)


async def teams_ready(guild: discord.Guild, m: dict, blue: list[int], orange: list[int]) -> None:
    """Teams are decided. The match starts once the team voice channel vote is settled too."""
    m["pending_teams"] = [blue, orange]
    m["state"] = "teams_set"  # stops further draft picks
    save_data()
    if voice_pending(m):
        channel = guild.get_channel(m["text_channel_id"])
        if channel:
            await channel.send("Teams are set. Waiting for the team voice channel vote to finish...")
    await maybe_finalize(guild, m)


async def maybe_finalize(guild: discord.Guild, m: dict) -> None:
    pending = m.get("pending_teams")
    if pending and not voice_pending(m) and m.get("state") != "active":
        await finalize_match(guild, m, pending[0], pending[1])


async def move_players_to_teams(guild: discord.Guild, m: dict, text_channel) -> None:
    """Drag the players who are in the lobby into their team's voice channel."""
    lobby = lobby_channel(guild)
    if lobby is None or len(m["vc"]) != 2:
        return
    in_lobby = set(lobby.voice_states)
    moved = 0
    not_in_lobby, failed = [], []
    for team, vc_id in (("blue", m["vc"][0]), ("orange", m["vc"][1])):
        target = guild.get_channel(vc_id)
        for uid in m[team]:
            if uid not in in_lobby:
                not_in_lobby.append(uid)
                continue
            try:
                member = guild.get_member(uid) or await guild.fetch_member(uid)
                await member.move_to(target, reason=f"Match {m['id']} teams")
                moved += 1
            except (discord.HTTPException, AttributeError):
                failed.append(uid)

    lines = []
    if moved:
        lines.append(f"Moved {moved} player(s) from the lobby to their team voice channels.")
    on_your_own = not_in_lobby + failed
    if on_your_own:
        lines.append("Join your team's voice channel yourselves: " + " ".join(f"<@{u}>" for u in on_your_own))
    if failed:
        lines.append("(I couldn't move everyone who was in the lobby. I may be missing the Move Members permission.)")
    if lines:
        await text_channel.send("\n".join(lines))


async def finalize_match(guild: discord.Guild, m: dict, blue: list[int], orange: list[int]) -> None:
    """Teams and the voice choice are settled: make team voice channels (if wanted), move players in
    from the lobby, and post the match card with the result buttons."""
    channel = guild.get_channel(m["text_channel_id"])
    if channel is None:
        return
    m["state"] = "active"  # claimed right away so nothing can start this match twice
    m["blue"], m["orange"] = blue, orange
    m.pop("draft", None)
    m.pop("pending_teams", None)

    use_voice = m.get("voice", True)
    vc_ids, vc_ok = [], True
    if use_voice:
        vc_ids, vc_ok = await create_voice_channels(guild, channel.category, m["id"], blue, orange)
    m["vc"] = vc_ids

    embed = discord.Embed(title=f"Match #{m['id']} - {m['mode']}", color=0x2ECC71)
    embed.add_field(name="Blue", value=mention_list(blue))
    embed.add_field(name="Orange", value=mention_list(orange))
    embed.add_field(name="Format", value=format_text(m["mode"]), inline=False)
    embed.add_field(
        name="Teams",
        value=f"{m.get('team_mode', 'Random')}  |  Avg Elo: Blue {team_avg(blue, m['mode'])} - Orange {team_avg(orange, m['mode'])}",
        inline=False,
    )
    if not use_voice:
        embed.add_field(name="Voice", value="Team voice channels are not being used for this match.", inline=False)
    elif vc_ids and vc_ok:
        embed.add_field(
            name="Voice",
            value=" ".join(f"<#{c}>" for c in vc_ids) + "\nDeleted when the result is reported.",
            inline=False,
        )
    else:
        embed.add_field(
            name="Voice",
            value="Couldn't create voice channels (the bot needs Manage Channels).",
            inline=False,
        )
    if m["mode"] == "1v1":
        embed.set_footer(text="When the game ends, click the winning team below.")
    else:
        embed.set_footer(text="Best of 3: when the series ends, click the winner and the series score below.")
    msg = await channel.send(embed=embed, view=match_view(m["mode"]))
    m["message_id"] = msg.id
    save_data()

    if use_voice and m["mode"] != "1v1":
        await move_players_to_teams(guild, m, channel)


# ------------------------------------------------------------------- draft
def draft_embed(m: dict) -> discord.Embed:
    d = m["draft"]
    embed = discord.Embed(title=f"Match #{m['id']} - draft", color=0xE67E22)
    embed.add_field(name="Blue (Captain 1)", value=mention_list(d["teams"][0]))
    embed.add_field(name="Orange (Captain 2)", value=mention_list(d["teams"][1]))
    embed.add_field(name="Available", value=mention_list(d["remaining"]), inline=False)
    return embed


async def start_draft(channel: discord.abc.Messageable, m: dict) -> None:
    players = m["players"][:]
    captains = random.sample(players, 2)
    remaining = [p for p in players if p not in captains]
    # snake order by team index: 0,1,1,0,0,1,1,0 ...
    order = [((i + 1) // 2) % 2 for i in range(len(remaining))]
    m["draft"] = {
        "captains": captains,
        "teams": [[captains[0]], [captains[1]]],
        "remaining": remaining,
        "order": order,
        "pick": 0,
    }
    m["state"] = "draft"
    m["team_mode"] = "Draft"
    save_data()
    await channel.send(
        content=(
            f"Captains: <@{captains[0]}> (Blue) and <@{captains[1]}> (Orange).\n"
            f"<@{captains[0]}>, you pick first. **@mention** a player to pick them. "
            f"Picks go in snake order (1, 2, 2, 1, 1, 2...)."
        ),
        embed=draft_embed(m),
    )


async def handle_pick(message: discord.Message, m: dict) -> None:
    d = m["draft"]
    team = d["order"][d["pick"]]
    captain = d["captains"][team]

    mentioned = [u for u in message.mentions if not u.bot]
    if message.author.id != captain:
        if mentioned and message.author.id in m["players"]:
            await message.reply(f"It's <@{captain}>'s turn to pick.", delete_after=8)
        return
    if not mentioned:
        return

    target = next((u for u in mentioned if u.id in d["remaining"]), None)
    if target is None:
        await message.reply("That player isn't available to pick.", delete_after=8)
        return

    d["remaining"].remove(target.id)
    d["teams"][team].append(target.id)
    d["pick"] += 1

    # one player left: they go to the team that owns the final slot
    if len(d["remaining"]) == 1:
        last = d["remaining"].pop()
        d["teams"][d["order"][d["pick"]]].append(last)
    save_data()

    if not d["remaining"]:
        blue, orange = d["teams"]
        await message.channel.send("Draft complete! Setting up the match...")
        await teams_ready(message.guild, m, blue, orange)
        return

    next_team = d["order"][d["pick"]]
    next_cap = d["captains"][next_team]
    await message.channel.send(
        content=f"<@{captain}> picked {target.mention}. <@{next_cap}>, you're up!",
        embed=draft_embed(m),
    )


# ------------------------------------------------------------------- views
class QueueView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="1v1", style=discord.ButtonStyle.primary, custom_id="rl:1v1")
    async def one(self, interaction: discord.Interaction, button: discord.ui.Button):
        await join_queue(interaction, "1v1")

    @discord.ui.button(label="2v2", style=discord.ButtonStyle.primary, custom_id="rl:2v2")
    async def two(self, interaction: discord.Interaction, button: discord.ui.Button):
        await join_queue(interaction, "2v2")

    @discord.ui.button(label="3v3", style=discord.ButtonStyle.primary, custom_id="rl:3v3")
    async def three(self, interaction: discord.Interaction, button: discord.ui.Button):
        await join_queue(interaction, "3v3")

    @discord.ui.button(label="Leave", style=discord.ButtonStyle.danger, custom_id="rl:leave")
    async def leave(self, interaction: discord.Interaction, button: discord.ui.Button):
        remove_from_all(interaction.user.id)
        queues_changed()
        await interaction.response.send_message("You left the queue.", ephemeral=True)


class TeamModeView(discord.ui.View):
    """Random teams or draft. Persistent, looked up by prompt message id."""

    def __init__(self):
        super().__init__(timeout=None)

    async def choose(self, interaction: discord.Interaction, choice: str):
        m = match_by_prompt(interaction.message.id)
        if not m:
            await interaction.response.send_message("I can't find this match.", ephemeral=True)
            return
        if interaction.user.id not in m["players"]:
            await interaction.response.send_message("Only players in this match can choose.", ephemeral=True)
            return
        if m["state"] != "pick":
            await interaction.response.send_message("Teams were already chosen.", ephemeral=True)
            return

        m["state"] = "choosing"  # blocks double clicks
        embed = interaction.message.embeds[0]
        embed.description = f"{interaction.user.mention} chose **{choice} teams**."
        done = TeamModeView()
        for child in done.children:
            child.disabled = True
        await interaction.response.edit_message(embed=embed, view=done)

        if choice == "random":
            players = m["players"][:]
            random.shuffle(players)
            half = len(players) // 2
            m["team_mode"] = "Random"
            await teams_ready(interaction.guild, m, players[:half], players[half:])
        elif choice == "balanced":
            blue, orange = balanced_split(m["players"], m["mode"])
            m["team_mode"] = "Balanced"
            await teams_ready(interaction.guild, m, blue, orange)
        else:
            await start_draft(interaction.channel, m)

    @discord.ui.button(label="Random teams", style=discord.ButtonStyle.primary, custom_id="rl:teams:random")
    async def random_teams(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.choose(interaction, "random")

    @discord.ui.button(label="Draft teams", style=discord.ButtonStyle.success, custom_id="rl:teams:draft")
    async def draft_teams(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.choose(interaction, "draft")

    @discord.ui.button(label="Balanced teams", style=discord.ButtonStyle.secondary, custom_id="rl:teams:balanced")
    async def balanced_teams(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.choose(interaction, "balanced")


async def report_result(interaction: discord.Interaction, team: str, series: Optional[tuple[int, int]] = None):
    """Record who won (and, for 2v2/3v3, the best-of-3 series score), then post the summary."""
    m = match_by_message(interaction.message.id)
    if not m:
        await interaction.response.send_message("I can't find this match.", ephemeral=True)
        return
    if interaction.user.id not in m["blue"] + m["orange"]:
        await interaction.response.send_message("Only players in this match can report the result.", ephemeral=True)
        return
    if m["winner"]:
        await interaction.response.send_message("This result was already reported.", ephemeral=True)
        return

    m["winner"] = team
    m["state"] = "done"
    m["reported_at"] = time.time()
    if series:
        m["series"] = list(series)  # games won by the winner, then by the loser, e.g. [2, 1]
    recompute_elo()  # updates ratings and saves

    embed = interaction.message.embeds[0]
    score = f" Series {series[0]}-{series[1]}." if series else ""
    embed.add_field(
        name="Result",
        value=f"**{team.title()} won!**{score} (reported by {interaction.user.mention})",
        inline=False,
    )
    done = match_view(m["mode"])
    for child in done.children:
        child.disabled = True
    await interaction.response.edit_message(embed=embed, view=done)

    # post the result where the queue started; 2v2 and 3v3 also open the MVP vote (1v1 is best of 1, no vote)
    vote = m["mode"] != "1v1"
    if vote:
        m["mvp_open"] = True
        m["mvp_votes"] = {}
        m["mvp_deadline"] = time.time() + MVP_VOTE_SECONDS
    origin = bot.get_channel(m.get("origin_channel_id", 0))
    posted = False
    if origin:
        try:
            if vote:
                losers = m["orange"] if team == "blue" else m["blue"]
                pings = " ".join(f"<@{u}>" for u in losers)
                msg = await origin.send(
                    content=f"{pings} - optional: vote for the other team's MVP below.",
                    embed=summary_embed(m),
                    view=MvpView(),
                )
            else:
                msg = await origin.send(embed=summary_embed(m))
            m["summary_message_id"] = msg.id
            posted = True
        except discord.HTTPException:
            pass
    if vote and not posted:
        m["mvp_open"] = False
    save_data()
    if m.get("mvp_open"):
        asyncio.create_task(mvp_expiry(m["id"], MVP_VOTE_SECONDS))
    asyncio.create_task(show_congrats(m))  # celebrate in the bot's status for a couple of minutes
    await delete_match_channels(interaction.guild, m)


class MatchView(discord.ui.View):
    """Result buttons for 1v1 (best of 1), looked up by match message id."""

    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="Blue won", style=discord.ButtonStyle.primary, custom_id="rl:win:blue")
    async def blue_won(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "blue")

    @discord.ui.button(label="Orange won", style=discord.ButtonStyle.secondary, custom_id="rl:win:orange")
    async def orange_won(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "orange")


class SeriesMatchView(discord.ui.View):
    """Result buttons for 2v2 and 3v3 (best of 3): the winner and the series score in one click."""

    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="Blue won 2-0", style=discord.ButtonStyle.primary, custom_id="rl:series:blue:2-0")
    async def blue_20(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "blue", (2, 0))

    @discord.ui.button(label="Blue won 2-1", style=discord.ButtonStyle.primary, custom_id="rl:series:blue:2-1")
    async def blue_21(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "blue", (2, 1))

    @discord.ui.button(label="Orange won 2-0", style=discord.ButtonStyle.secondary, custom_id="rl:series:orange:2-0")
    async def orange_20(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "orange", (2, 0))

    @discord.ui.button(label="Orange won 2-1", style=discord.ButtonStyle.secondary, custom_id="rl:series:orange:2-1")
    async def orange_21(self, interaction: discord.Interaction, button: discord.ui.Button):
        await report_result(interaction, "orange", (2, 1))


def match_view(mode: str) -> discord.ui.View:
    return MatchView() if mode == "1v1" else SeriesMatchView()


# --------------------------------------------------------------------- mvp
def summary_embed(m: dict) -> discord.Embed:
    team = m["winner"]
    embed = discord.Embed(title=f"Match #{m['id']} finished - {team.title()} wins!", color=0x2ECC71)
    embed.add_field(name="Blue", value=result_lines(m, "blue"))
    embed.add_field(name="Orange", value=result_lines(m, "orange"))
    scores = series_scores(m)
    if scores:
        embed.add_field(
            name="Series (best of 3)",
            value=f"Blue **{scores[0]}** - **{scores[1]}** Orange",
            inline=False,
        )
    ratings = m.get("team_ratings")
    if ratings:
        loser = "orange" if team == "blue" else "blue"
        upset = " - **upset!**" if ratings[team] < ratings[loser] else ""
        embed.add_field(
            name="Team ratings",
            value=f"Blue {ratings['blue']} - Orange {ratings['orange']}{upset}",
            inline=False,
        )
    if m.get("mvp_open"):
        losers = m["orange" if team == "blue" else "blue"]
        voted = len(m.get("mvp_votes", {}))
        embed.add_field(
            name="MVP vote",
            value=(
                "The losing team can vote for the other team's MVP (private and optional). "
                f"Closes <t:{int(m['mvp_deadline'])}:R> - {voted}/{len(losers)} voted. Elo is final once voting closes."
            ),
            inline=False,
        )
    elif m.get("mvp"):
        embed.add_field(name="MVP", value=f"<@{m['mvp']}> (+{mvp_bonus(m['mode'])} Elo bonus)", inline=False)
    elif "mvp_open" in m and m["mode"] != "1v1":
        embed.add_field(name="MVP", value="No MVP this match.", inline=False)
    footer = f"Wrong result? Use /undo match_id:{m['id']}"
    if m.get("edits"):
        footer = f"Edited by an admin. {footer}"
    embed.set_footer(text=footer)
    return embed


async def update_summary(m: dict) -> None:
    channel_id, message_id = m.get("origin_channel_id"), m.get("summary_message_id")
    if not channel_id or not message_id:
        return
    msg = bot.get_partial_messageable(channel_id).get_partial_message(message_id)
    try:
        if m.get("mvp_open"):
            await msg.edit(embed=summary_embed(m), view=MvpView())
        else:
            await msg.edit(content=None, embed=summary_embed(m), view=None)
    except discord.HTTPException:
        pass


async def finalize_mvp(m: dict) -> None:
    """Close the vote. The player with the most votes is MVP; a tie or no votes means no MVP."""
    if not m.get("mvp_open"):
        return
    m["mvp_open"] = False
    tally = Counter(m.get("mvp_votes", {}).values())
    mvp = None
    if tally:
        top = max(tally.values())
        leaders = [uid for uid, count in tally.items() if count == top]
        if len(leaders) == 1:
            mvp = leaders[0]
    if mvp:
        m["mvp"] = mvp
        recompute_elo()  # applies the bonus and saves
    else:
        save_data()
    await update_summary(m)


async def mvp_expiry(match_id: int, delay: float) -> None:
    await asyncio.sleep(delay)
    m = get_match(match_id)
    if m and m.get("mvp_open"):
        await finalize_mvp(m)


class MvpPickView(discord.ui.View):
    """Private (ephemeral) picker shown only to the voter."""

    def __init__(self, match_id: int, options: list[discord.SelectOption]):
        super().__init__(timeout=300)
        self.match_id = match_id
        self.select = discord.ui.Select(placeholder="Choose an MVP...", options=options)
        self.select.callback = self.on_pick
        self.add_item(self.select)

    async def on_pick(self, interaction: discord.Interaction):
        m = get_match(self.match_id)
        if not m or not m.get("mvp_open"):
            await interaction.response.edit_message(content="Voting has closed.", view=None)
            return
        choice = int(self.select.values[0])
        m["mvp_votes"][str(interaction.user.id)] = choice
        save_data()
        name = data["profiles"].get(str(choice), {}).get("name", f"player {choice}")
        await interaction.response.edit_message(
            content=f"Vote saved: **{name}**. Only you can see this. Click the vote button again to change it.",
            view=None,
        )
        losers = m["orange" if m["winner"] == "blue" else "blue"]
        if len(m["mvp_votes"]) >= len(losers):
            await finalize_mvp(m)  # everyone voted, no need to wait
        else:
            await update_summary(m)


class MvpView(discord.ui.View):
    """Persistent vote button under the result summary."""

    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="Vote MVP (losing team)", style=discord.ButtonStyle.secondary, custom_id="rl:mvp")
    async def vote(self, interaction: discord.Interaction, button: discord.ui.Button):
        m = next((x for x in data["matches"] if x.get("summary_message_id") == interaction.message.id), None)
        if not m or not m.get("mvp_open"):
            await interaction.response.send_message("Voting has closed.", ephemeral=True)
            return
        losers = m["orange" if m["winner"] == "blue" else "blue"]
        if interaction.user.id not in losers:
            await interaction.response.send_message("Only the losing team can vote for an MVP.", ephemeral=True)
            return
        options = [
            discord.SelectOption(
                label=data["profiles"].get(str(u), {}).get("name", f"Player {u}")[:100],
                value=str(u),
            )
            for u in m[m["winner"]]
        ]
        await interaction.response.send_message(
            "Pick the other team's MVP. This is optional, and only you can see it.",
            view=MvpPickView(m["id"], options),
            ephemeral=True,
        )


# ---------------------------------------------------------------- admin edit
def player_name(uid: int) -> str:
    for pool in (data["profiles"], data.get("unenrolled", {})):
        name = pool.get(str(uid), {}).get("name")
        if name:
            return name
    return f"Player {uid}"


STATE_LABELS = {
    "lobby": "Waiting for players to join the lobby",
    "pick": "Choosing teams",
    "draft": "Drafting teams",
    "teams_set": "Teams chosen, finishing setup",
    "active": "Being played",
}


def match_info_embed(m: dict) -> discord.Embed:
    """Everything the bot knows about one match, for /matchfinder."""
    finished = bool(m["winner"])
    embed = discord.Embed(title=f"Match #{m['id']} - {m['mode']}", color=0x2ECC71 if finished else 0xE67E22)
    if finished:
        status = f"Finished (reported <t:{int(m.get('reported_at', m['created']))}:f>)"
    else:
        status = STATE_LABELS.get(m.get("state"), "In progress")
    embed.add_field(name="Status", value=status, inline=False)
    embed.add_field(name="Format", value=format_text(m["mode"]), inline=False)

    if finished:
        result = f"**{m['winner'].title()}** won"
        scores = series_scores(m)
        if scores:
            result += f"  |  Series: Blue {scores[0]} - {scores[1]} Orange"
        embed.add_field(name="Result", value=result, inline=False)
        embed.add_field(name="Blue", value=result_lines(m, "blue"))  # includes each player's rating and change
        embed.add_field(name="Orange", value=result_lines(m, "orange"))
    elif m["blue"] or m["orange"]:
        embed.add_field(name="Blue", value=mention_list(m["blue"]))
        embed.add_field(name="Orange", value=mention_list(m["orange"]))
    else:
        embed.add_field(name="Players", value=mention_list(m.get("players", [])), inline=False)

    ratings = m.get("team_ratings")
    if finished and ratings:
        loser = "orange" if m["winner"] == "blue" else "blue"
        upset = " - upset!" if ratings[m["winner"]] < ratings[loser] else ""
        embed.add_field(
            name="Team ratings (before the match)",
            value=f"Blue {ratings['blue']} - Orange {ratings['orange']}{upset}",
            inline=False,
        )

    if m["mode"] != "1v1":
        if m.get("mvp"):
            mvp = f"<@{m['mvp']}> (+{mvp_bonus(m['mode'])} Elo)"
        elif m.get("mvp_open"):
            mvp = "Vote in progress"
        else:
            mvp = "None" if finished else None
        if mvp:
            embed.add_field(name="MVP", value=mvp)

    setup = []
    if m.get("team_mode"):
        setup.append(f"Teams: {m['team_mode']}")
    if m["mode"] != "1v1" and m.get("voice") is not None:
        setup.append("Team voice channels: " + ("Yes" if m["voice"] else "No"))
    if setup:
        embed.add_field(name="Setup", value="  |  ".join(setup))
    embed.add_field(name="Created", value=f"<t:{int(m['created'])}:f>")
    if m.get("edits"):
        embed.set_footer(text=f"Edited by an admin {len(m['edits'])} time{'s' if len(m['edits']) != 1 else ''}.")
    return embed


def deleted_record_embed(entry: dict) -> discord.Embed:
    m = entry["match"]
    embed = discord.Embed(
        title=f"Match #{m['id']} was deleted", description=f"**Reason:** {entry['reason']}", color=0xE74C3C
    )
    embed.add_field(name="Mode", value=m["mode"])
    embed.add_field(name="Deleted", value=f"<t:{int(entry['at'])}:f> by <@{entry['by']}>")
    players = m.get("players") or (m["blue"] + m["orange"])
    embed.add_field(name="Players", value=" ".join(f"<@{u}>" for u in players) or "-", inline=False)
    return embed


def edit_embed(m: dict) -> discord.Embed:
    embed = discord.Embed(title=f"Edit match #{m['id']} - {m['mode']}", color=0x95A5A6)
    embed.add_field(name="Blue", value=mention_list(m["blue"]))
    embed.add_field(name="Orange", value=mention_list(m["orange"]))
    embed.add_field(name="Winner", value=m["winner"].title(), inline=False)
    if m["mode"] != "1v1":
        scores = series_scores(m)
        embed.add_field(
            name="Series (best of 3)",
            value=f"Blue {scores[0]} - {scores[1]} Orange" if scores else "not reported",
        )
        embed.add_field(name="MVP", value=f"<@{m['mvp']}>" if m.get("mvp") else "none")
    embed.add_field(name="Reported", value=f"<t:{int(m.get('reported_at', m['created']))}:R>")
    embed.add_field(name="Edits so far", value=str(len(m.get("edits", []))))
    return embed


async def apply_edit(m: dict, admin_id: int, kind: str, value: str) -> str:
    """Apply one admin edit ("winner", "series" or "mvp"), recalculate Elo and refresh the public summary."""
    if kind == "winner":
        if m["winner"] == value:
            return "The winner was already set to that."
        old = m["winner"]
        m["winner"] = value
        if m["mode"] != "1v1":
            m["mvp_open"] = False  # closes any vote still running
            m.pop("mvp", None)  # the old winning team's MVP no longer applies
            m.pop("mvp_votes", None)
        what = f"winner {old} -> {value}"
        message = f"Winner changed to **{value.title()}**. Elo was recalculated."
        if m["mode"] != "1v1":
            message += " The MVP was cleared, so set a new one if needed."
    elif kind == "series":
        won, lost = (int(x) for x in value.split("-"))
        m["series"] = [won, lost]
        what = f"series {won}-{lost}"
        message = f"Series score set to **{m['winner'].title()} {won}-{lost}**."
    else:  # mvp
        m["mvp_open"] = False  # closes any vote still running
        if value == "0":
            m.pop("mvp", None)
            what, message = "mvp cleared", "MVP cleared. Elo was recalculated."
        else:
            m["mvp"] = int(value)
            what, message = f"mvp {value}", f"MVP set to **{player_name(int(value))}**. Elo was recalculated."

    m.setdefault("edits", []).append({"by": admin_id, "at": time.time(), "what": what})
    for vote_id, vote in list(pending_votes.items()):  # an open /undo vote for this match no longer applies
        if vote["match_id"] == m["id"]:
            pending_votes.pop(vote_id, None)
    recompute_elo()  # ratings, streaks and records are rebuilt (also saves)
    await update_summary(m)
    return message


PICK_PROMPTS = {
    "winner": "Who actually won? (Changing the winner clears the MVP.)",
    "series": "What was the final series score?",
    "mvp": "Who was the MVP? (Choose No MVP to clear it.)",
}


class EditView(discord.ui.View):
    """Main /edit panel: choose what to change. Only the admin who ran /edit can use it."""

    def __init__(self, owner_id: int, m: dict):
        super().__init__(timeout=300)
        self.owner_id = owner_id
        self.match_id = m["id"]
        if m["mode"] == "1v1":  # best of 1: no series score and no MVP
            self.remove_item(self.series_btn)
            self.remove_item(self.mvp_btn)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.owner_id:
            await interaction.response.send_message("This isn't your edit panel. Run /edit yourself.", ephemeral=True)
            return False
        return True

    async def open_picker(self, interaction: discord.Interaction, kind: str):
        m = get_match(self.match_id)
        if not m or not m["winner"]:
            await interaction.response.edit_message(content="That match is no longer available.", embed=None, view=None)
            return
        await interaction.response.edit_message(
            content=PICK_PROMPTS[kind], embed=edit_embed(m), view=EditPickView(self.owner_id, m, kind)
        )

    @discord.ui.button(label="Change winner", style=discord.ButtonStyle.primary)
    async def winner_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.open_picker(interaction, "winner")

    @discord.ui.button(label="Set series score", style=discord.ButtonStyle.secondary)
    async def series_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.open_picker(interaction, "series")

    @discord.ui.button(label="Set MVP", style=discord.ButtonStyle.secondary)
    async def mvp_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.open_picker(interaction, "mvp")

    @discord.ui.button(label="Done", style=discord.ButtonStyle.success)
    async def done_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(content="Edit panel closed.", view=None)


class EditPickView(discord.ui.View):
    """Second step of /edit: pick the new value for one thing."""

    def __init__(self, owner_id: int, m: dict, kind: str):
        super().__init__(timeout=300)
        self.owner_id = owner_id
        self.match_id = m["id"]
        self.kind = kind
        if kind == "winner":
            options = [
                discord.SelectOption(label="Blue won", value="blue", default=m["winner"] == "blue"),
                discord.SelectOption(label="Orange won", value="orange", default=m["winner"] == "orange"),
            ]
        elif kind == "series":
            current = "-".join(str(x) for x in m.get("series", []))
            options = [
                discord.SelectOption(label=f"{m['winner'].title()} won {score}", value=score, default=score == current)
                for score in ("2-0", "2-1")
            ]
        else:
            options = [discord.SelectOption(label="No MVP", value="0", default=not m.get("mvp"))]
            options += [
                discord.SelectOption(label=player_name(u)[:100], value=str(u), default=m.get("mvp") == u)
                for u in m[m["winner"]]
            ]
        self.select = discord.ui.Select(placeholder="Choose...", options=options, row=0)
        self.select.callback = self.on_pick
        self.add_item(self.select)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.owner_id:
            await interaction.response.send_message("This isn't your edit panel. Run /edit yourself.", ephemeral=True)
            return False
        return True

    async def on_pick(self, interaction: discord.Interaction):
        m = get_match(self.match_id)
        if not m or not m["winner"]:
            await interaction.response.edit_message(content="That match is no longer available.", embed=None, view=None)
            return
        await interaction.response.defer()  # recalculating and refreshing the summary can take a moment
        result = await apply_edit(m, interaction.user.id, self.kind, self.select.values[0])
        await interaction.edit_original_response(content=result, embed=edit_embed(m), view=EditView(self.owner_id, m))

    @discord.ui.button(label="Back", style=discord.ButtonStyle.secondary, row=1)
    async def back(self, interaction: discord.Interaction, button: discord.ui.Button):
        m = get_match(self.match_id)
        if not m or not m["winner"]:
            await interaction.response.edit_message(content="That match is no longer available.", embed=None, view=None)
            return
        await interaction.response.edit_message(
            content="Pick what to change.", embed=edit_embed(m), view=EditView(self.owner_id, m)
        )


# ------------------------------------------------------------ delete a match
def deleted_embed(m: dict, reason: str, admin) -> discord.Embed:
    embed = discord.Embed(title=f"Match #{m['id']} was deleted", description=f"**Reason:** {reason}", color=0xE74C3C)
    embed.add_field(name="Mode", value=m["mode"])
    embed.add_field(name="Deleted by", value=admin.mention)
    players = m.get("players") or (m["blue"] + m["orange"])
    embed.add_field(name="Players", value=" ".join(f"<@{u}>" for u in players) or "-", inline=False)
    embed.set_footer(text="Ratings, records and stats were recalculated as if this match never happened.")
    return embed


async def delete_match(interaction: discord.Interaction, m: dict, reason: str) -> None:
    """Remove a match (finished or still being played) and keep a record of why."""
    # a game still in progress also has a text channel and team voice channels to clean up
    await delete_match_channels(interaction.guild, m)
    data["matches"].remove(m)
    data.setdefault("deleted_matches", []).append(
        {"match": m, "reason": reason, "by": interaction.user.id, "at": time.time()}
    )
    for vote_id, vote in list(pending_votes.items()):  # an open /undo vote for it no longer applies
        if vote["match_id"] == m["id"]:
            pending_votes.pop(vote_id, None)
    recompute_elo()  # Elo, streaks, win/loss, MVPs and records all revert (also saves)

    # tell the channel: turn the result summary into a "deleted" notice, or post one if there isn't a summary
    embed = deleted_embed(m, reason, interaction.user)
    posted = False
    channel_id, message_id = m.get("origin_channel_id"), m.get("summary_message_id")
    if channel_id and message_id:
        try:
            await bot.get_partial_messageable(channel_id).get_partial_message(message_id).edit(
                content=None, embed=embed, view=None
            )
            posted = True
        except discord.HTTPException:
            pass
    if not posted:
        origin = bot.get_channel(channel_id or 0)
        if origin is not None:
            try:
                await origin.send(embed=embed)
            except discord.HTTPException:
                pass


class DeleteMatchModal(discord.ui.Modal):
    """Asks the admin to type why the match is being deleted."""

    reason = discord.ui.TextInput(
        label="Reason for deleting this match",
        style=discord.TextStyle.paragraph,
        placeholder="e.g. players disconnected, wrong teams, test game",
        min_length=3,
        max_length=300,
        required=True,
    )

    def __init__(self, match_id: int):
        super().__init__(title=f"Delete match #{match_id}")
        self.match_id = match_id

    async def on_submit(self, interaction: discord.Interaction):
        if not interaction.user.guild_permissions.manage_guild:
            await interaction.response.send_message("You need the Manage Server permission to delete matches.", ephemeral=True)
            return
        m = get_match(self.match_id)
        if not m:
            await interaction.response.send_message("That match no longer exists.", ephemeral=True)
            return
        await interaction.response.defer(ephemeral=True)  # cleaning up channels and recalculating can take a moment
        await delete_match(interaction, m, str(self.reason.value).strip())
        await interaction.followup.send(
            f"Match #{self.match_id} was deleted and the reason was recorded. Ratings and stats were recalculated.",
            ephemeral=True,
        )


class ConfirmView(discord.ui.View):
    def __init__(self, owner_id: int, on_confirm, confirm_label: str):
        super().__init__(timeout=60)
        self.owner_id = owner_id
        self.on_confirm = on_confirm
        self.yes.label = confirm_label

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.owner_id:
            await interaction.response.send_message("This isn't your prompt.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.danger)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.on_confirm(interaction)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(content="Cancelled.", view=None)


# --------------------------------------------------------------- undo votes
async def start_vote(interaction: discord.Interaction, match_id: int):
    m = get_match(match_id)
    if not m or not m["winner"]:
        await interaction.response.edit_message(content="That match can't be changed right now.", view=None)
        return
    if any(v["match_id"] == match_id for v in pending_votes.values()):
        await interaction.response.edit_message(content="A vote for this match is already open.", view=None)
        return

    new_winner = "orange" if m["winner"] == "blue" else "blue"
    await interaction.response.edit_message(content="Vote posted in the channel.", view=None)

    embed = discord.Embed(
        title=f"Vote: change Match #{m['id']} result",
        description=(
            f"{interaction.user.mention} says the result was reported wrong.\n"
            f"**{m['winner'].title()} win** -> **{new_winner.title()} win**\n\n"
            f"{APPROVE} **{VOTES_NEEDED}** approvals to change it\n"
            f"{REJECT} **{VOTES_NEEDED}** rejections to keep it\n"
            f"Voting closes in {VOTE_SECONDS // 60} minutes."
        ),
        color=0xE67E22,
    )
    msg = await interaction.channel.send(embed=embed)
    await msg.add_reaction(APPROVE)
    await msg.add_reaction(REJECT)

    pending_votes[msg.id] = {"match_id": m["id"], "new_winner": new_winner}
    asyncio.create_task(expire_vote(msg))


async def expire_vote(msg: discord.Message):
    await asyncio.sleep(VOTE_SECONDS)
    if pending_votes.pop(msg.id, None) is None:
        return  # already decided
    embed = msg.embeds[0]
    embed.color = 0x95A5A6
    embed.set_footer(text="Vote expired. Result unchanged.")
    try:
        await msg.edit(embed=embed)
    except discord.HTTPException:
        pass


# ------------------------------------------------------------------- stats
# --------------------------------------------------------------------- elo
def empty_ratings() -> dict:
    return {mode: START_ELO for mode in MODES}


def pstat(profile: dict, key: str, mode: str, default):
    """Read one mode's value from a per-mode profile field (elo, streak, elo_w, elo_l)."""
    value = profile.get(key)
    return value.get(mode, default) if isinstance(value, dict) else default


def get_elo(uid: int, mode: str) -> int:
    return pstat(data["profiles"].get(str(uid), {}), "elo", mode, START_ELO)


def team_avg(team: list[int], mode: str) -> int:
    return round(sum(get_elo(u, mode) for u in team) / len(team)) if team else START_ELO


def streak_text(streak: int) -> str:
    if streak >= 2:
        return f"{streak}-win streak"
    if streak <= -2:
        return f"{-streak}-loss streak"
    return "no streak"


def reset_time(profile: dict, mode: str, kind: str = "elo") -> float:
    """When this player's `kind` ("elo" or "wl") was last reset in `mode` (their own or the group's, whichever is later)."""

    def at(value) -> float:
        if isinstance(value, dict):
            return value.get(mode, 0)
        return value or 0  # older saves stored a single time for all modes

    return max(at(data.get(f"{kind}_reset_all", 0)), at(profile.get(f"{kind}_reset", 0)))


def mvp_bonus(mode: str) -> int:
    """MVP bonus for a mode (scaled by that mode's intensity, never below 1)."""
    return max(1, round(MVP_BONUS * MODE_INTENSITY.get(mode, 1.0)))


def recompute_elo() -> None:
    """Rebuild every rating from the match history, separately for each mode.

    Replaying history keeps streaks correct after an /undo and lets resets
    work by ignoring games played before a player's (or the group's) reset.
    """
    ratings = {mode: {} for mode in MODES}
    streaks = {mode: {} for mode in MODES}
    wins = {mode: defaultdict(int) for mode in MODES}
    losses = {mode: defaultdict(int) for mode in MODES}

    reported = [m for m in data["matches"] if m["winner"] and m["mode"] in MODES]
    reported.sort(key=lambda m: (m.get("reported_at", m["created"]), m["id"]))

    for m in reported:
        mode = m["mode"]
        rating, streak_of = ratings[mode], streaks[mode]
        intensity = MODE_INTENSITY.get(mode, 1.0)
        when = m.get("reported_at", m["created"])

        def team_rating(team: str) -> float:
            """Mean rating of the team, nudged toward its best player (stars carry games)."""
            vals = [rating.get(u, START_ELO) for u in m[team]]
            return (1 - TEAM_TOP_WEIGHT) * sum(vals) / len(vals) + TEAM_TOP_WEIGHT * max(vals)

        T = {t: team_rating(t) for t in ("blue", "orange")}
        m["team_ratings"] = {t: round(T[t]) for t in T}

        changes = {}
        for team in ("blue", "orange"):
            won = m["winner"] == team
            for uid in m[team]:
                profile = data["profiles"].get(str(uid), {})
                if when <= reset_time(profile, mode):
                    continue  # this game was before the player's last reset in this mode
                prev = streak_of.get(uid, 0)
                streak = (max(prev, 0) + 1) if won else (min(prev, 0) - 1)
                mult = min(1 + STREAK_BONUS * (abs(streak) - 1), STREAK_CAP)
                opp = "orange" if team == "blue" else "blue"
                gap = T[team] - T[opp]  # positive = this is the higher-rated team
                e_team = 1 / (1 + 10 ** ((T[opp] - T[team]) / 400))
                e_self = 1 / (1 + 10 ** ((T[opp] - rating.get(uid, START_ELO)) / 400))
                expected = (1 - PLAYER_WEIGHT) * e_team + PLAYER_WEIGHT * e_self
                base = K_FACTOR * ((1 - expected) if won else expected)
                upset = (won and gap < 0) or (not won and gap > 0)  # the lower-rated team won
                upset_mult = 1 + UPSET_BONUS * min(abs(gap) / UPSET_FULL_GAP, 1) if upset else 1
                delta = max(1, round(base * mult * upset_mult * intensity)) * (1 if won else -1)
                is_mvp = won and uid == m.get("mvp")
                if is_mvp:
                    delta += mvp_bonus(mode)
                old = rating.get(uid, START_ELO)
                new = max(ELO_FLOOR, old + delta)
                rating[uid], streak_of[uid] = new, streak
                (wins if won else losses)[mode][uid] += 1
                changes[str(uid)] = {"delta": new - old, "after": new, "mvp": is_mvp}
        m["elo"] = changes

    for uid_str, profile in data["profiles"].items():
        uid = int(uid_str)
        profile["elo"] = {mode: ratings[mode].get(uid, START_ELO) for mode in MODES}
        profile["streak"] = {mode: streaks[mode].get(uid, 0) for mode in MODES}
        profile["elo_w"] = {mode: wins[mode][uid] for mode in MODES}
        profile["elo_l"] = {mode: losses[mode][uid] for mode in MODES}
    save_data()


def result_lines(m: dict, team: str) -> str:
    lines = []
    for uid in m[team]:
        c = m.get("elo", {}).get(str(uid))
        star = " \u2b50 MVP" if c and c.get("mvp") else ""
        lines.append(f"<@{uid}> {c['after']} ({c['delta']:+d}){star}" if c else f"<@{uid}>")
    return "\n".join(lines) or "-"


def balanced_split(players: list[int], mode: str) -> tuple[list[int], list[int]]:
    """Split players into two teams with the closest total Elo (using this mode's ratings).

    Splits within BALANCE_TOLERANCE of the fairest one are treated as equal and
    one is picked at random, so the same teams don't come up every time.
    """
    size = len(players) // 2
    total = sum(get_elo(u, mode) for u in players)
    options = []
    for combo in itertools.combinations(players, size):
        options.append((abs(2 * sum(get_elo(u, mode) for u in combo) - total), combo))
    best = min(diff for diff, _ in options)
    pool = [combo for diff, combo in options if diff <= best + BALANCE_TOLERANCE]
    blue = list(random.choice(pool))
    orange = [u for u in players if u not in blue]
    return blue, orange


PAGE_SIZE = 10


def elo_rows(mode: str) -> list[tuple]:
    """Players who have a rated game in this mode, highest Elo first."""
    rows = []
    for u, p in data["profiles"].items():
        w, l = pstat(p, "elo_w", mode, 0), pstat(p, "elo_l", mode, 0)
        if w + l:
            rows.append((int(u), pstat(p, "elo", mode, START_ELO), pstat(p, "streak", mode, 0), w, l))
    rows.sort(key=lambda r: (r[1], r[3] - r[4], r[3]), reverse=True)
    return rows


def page_count(mode: str) -> int:
    return max(1, (len(elo_rows(mode)) + PAGE_SIZE - 1) // PAGE_SIZE)


def leaderboard_embed(page: int, mode: str) -> discord.Embed:
    rows = elo_rows(mode)
    page = max(0, min(page, page_count(mode) - 1))
    medals = {1: "\U0001F947", 2: "\U0001F948", 3: "\U0001F949"}
    lines = []
    start = page * PAGE_SIZE
    for rank, (uid, elo, streak, w, l) in enumerate(rows[start:start + PAGE_SIZE], start=start + 1):
        badge = medals.get(rank, f"`{rank}.`")
        lines.append(f"{badge} <@{uid}> - **{elo}** ({w}W-{l}L, {streak_text(streak)})")
    embed = discord.Embed(
        title=f"{mode} Elo Leaderboard",
        description="\n".join(lines) or f"No rated {mode} games yet.",
        color=0xF1C40F,
    )
    embed.set_footer(text=f"Page {page + 1}/{page_count(mode)}  |  Everyone starts at {START_ELO}")
    return embed


class LeaderboardView(discord.ui.View):
    def __init__(self, owner_id: int, mode: str):
        super().__init__(timeout=180)
        self.owner_id = owner_id
        self.mode = mode
        self.page = 0
        self.sync_buttons()

    def sync_buttons(self) -> None:
        self.prev_page.disabled = self.page <= 0
        self.next_page.disabled = self.page >= page_count(self.mode) - 1
        for button, mode in ((self.mode_1v1, "1v1"), (self.mode_2v2, "2v2"), (self.mode_3v3, "3v3")):
            button.style = discord.ButtonStyle.primary if mode == self.mode else discord.ButtonStyle.secondary

    async def show(self, interaction: discord.Interaction) -> None:
        self.sync_buttons()
        await interaction.response.edit_message(embed=leaderboard_embed(self.page, self.mode), view=self)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.owner_id:
            await interaction.response.send_message("Run /leaderboard to flip through it yourself.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Previous", style=discord.ButtonStyle.secondary)
    async def prev_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page -= 1
        await self.show(interaction)

    @discord.ui.button(label="Next", style=discord.ButtonStyle.secondary)
    async def next_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page += 1
        await self.show(interaction)

    @discord.ui.button(label="1v1", style=discord.ButtonStyle.secondary)
    async def mode_1v1(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.mode, self.page = "1v1", 0
        await self.show(interaction)

    @discord.ui.button(label="2v2", style=discord.ButtonStyle.secondary)
    async def mode_2v2(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.mode, self.page = "2v2", 0
        await self.show(interaction)

    @discord.ui.button(label="3v3", style=discord.ButtonStyle.secondary)
    async def mode_3v3(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.mode, self.page = "3v3", 0
        await self.show(interaction)


# ------------------------------------------------------------- admin tools
def create_profile(member) -> bool:
    """Enroll a member. Returns False if they were already enrolled.

    Someone who was unenrolled earlier gets their old profile back (their match
    history was never deleted, so their ratings come straight back too).
    """
    uid = str(member.id)
    if uid in data["profiles"]:
        return False
    profile = data.setdefault("unenrolled", {}).pop(uid, None) or {
        "enrolled": int(time.time()),
        "elo": empty_ratings(),
        "streak": {},
    }
    profile["name"] = member.display_name
    data["profiles"][uid] = profile
    recompute_elo()  # also saves
    return True


def remove_profile(uid: int) -> bool:
    """Unenroll a player: out of the queues and off the leaderboard, history kept."""
    profile = data["profiles"].pop(str(uid), None)
    if profile is None:
        return False
    data.setdefault("unenrolled", {})[str(uid)] = profile
    remove_from_all(uid)
    save_data()
    return True


def full_reset() -> str:
    """Wipe every stat back to default and empty the queues. Returns the backup file's name."""
    backup = f"rl_data_backup_{time.strftime('%Y%m%d-%H%M%S')}.json"
    if os.path.exists(DATA_FILE):
        shutil.copy2(DATA_FILE, os.path.join(os.path.dirname(DATA_FILE), backup))

    # finished matches go; games still being played stay so their channels and buttons keep working
    data["matches"] = [m for m in data["matches"] if not m["winner"]]
    data.pop("elo_reset_all", None)
    data.pop("wl_reset_all", None)
    for profile in list(data["profiles"].values()) + list(data.get("unenrolled", {}).values()):
        profile.pop("elo_reset", None)
        profile.pop("wl_reset", None)
    for q in queues.values():
        q.clear()
    queue_joined.clear()
    pending_votes.clear()
    recompute_elo()  # every rating, streak and win/loss count goes back to default (also saves)
    return backup


# ----------------------------------------------------------------- records
def chronological(uid: int) -> list[dict]:
    games = finished_matches(uid)
    games.sort(key=lambda m: (m.get("reported_at", m["created"]), m["id"]))
    return games


def streak_records(results: list[bool]) -> tuple[int, int, int]:
    """(best win streak, worst loss streak, current streak: + wins / - losses)."""
    best = worst = current = 0
    for won in results:
        current = (max(current, 0) + 1) if won else (min(current, 0) - 1)
        best, worst = max(best, current), min(worst, current)
    return best, -worst, current


def records_embed(user: discord.abc.User) -> discord.Embed:
    uid = user.id
    games = chronological(uid)
    profile = data["profiles"].get(str(uid), {})
    embed = discord.Embed(title=f"{user.display_name} - Records", color=0xE91E63)
    if not games:
        embed.description = "No finished games yet."
        return embed

    best, worst, current = streak_records([did_win(m, uid) for m in games])
    per_mode = {
        mode: streak_records([did_win(m, uid) for m in games if m["mode"] == mode]) for mode in MODES
    }
    embed.add_field(
        name="Best win streak",
        value=f"**{best}** overall\n" + "\n".join(f"{mode}: {per_mode[mode][0]}" for mode in MODES),
    )
    embed.add_field(
        name="Worst loss streak",
        value=f"**{worst}** overall\n" + "\n".join(f"{mode}: {per_mode[mode][1]}" for mode in MODES),
    )
    if current > 0:
        now = f"{current} win{'s' if current != 1 else ''} in a row"
    elif current < 0:
        now = f"{-current} loss{'es' if current != -1 else ''} in a row"
    else:
        now = "none"
    embed.add_field(name="Current streak", value=now)

    elo_lines = []
    for mode in MODES:
        afters = [
            m["elo"][str(uid)]["after"] for m in games if m["mode"] == mode and str(uid) in m.get("elo", {})
        ]
        if afters:
            elo_lines.append(
                f"{mode}: peak **{max(max(afters), START_ELO)}** | low **{min(min(afters), START_ELO)}** "
                f"| now {pstat(profile, 'elo', mode, START_ELO)}"
            )
        else:
            elo_lines.append(f"{mode}: no rated games")
    embed.add_field(name="Elo peak and low (since last Elo reset)", value="\n".join(elo_lines), inline=False)

    swings = [(m["elo"][str(uid)]["delta"], m) for m in games if str(uid) in m.get("elo", {})]
    if swings:
        gain, gain_match = max(swings, key=lambda s: s[0])
        loss, loss_match = min(swings, key=lambda s: s[0])
        embed.add_field(
            name="Biggest swings",
            value=(
                f"Best game: **{gain:+d}** ({gain_match['mode']}, match #{gain_match['id']})\n"
                f"Worst game: **{loss:+d}** ({loss_match['mode']}, match #{loss_match['id']})"
            ),
            inline=False,
        )

    upsets = []
    for m in games:
        ratings = m.get("team_ratings")
        if ratings and did_win(m, uid):
            team = team_of(m, uid)
            opp = "orange" if team == "blue" else "blue"
            if ratings[opp] > ratings[team]:
                upsets.append((ratings[opp] - ratings[team], m))
    if upsets:
        gap, upset_match = max(upsets, key=lambda u: u[0])
        embed.add_field(
            name="Biggest upset win",
            value=f"Beat a team rated **{gap}** higher ({upset_match['mode']}, match #{upset_match['id']})",
            inline=False,
        )

    wins = sum(1 for m in games if did_win(m, uid))
    mvps = sum(1 for m in games if m.get("mvp") == uid)
    embed.add_field(
        name="All-time",
        value=f"{record_line(wins, len(games) - wins)}\nVoted MVP: {mvps} time{'s' if mvps != 1 else ''}",
        inline=False,
    )
    embed.set_footer(text="Streaks and totals cover every finished game. /fullreset clears them.")
    return embed


def record_line(w: int, l: int) -> str:
    total = w + l
    pct = f"{w / total * 100:.0f}%" if total else "n/a"
    ratio = f"{w / l:.2f}" if l else ("n/a" if w == 0 else "undefeated")
    return f"**{w}W - {l}L**  |  {pct} win rate  |  W/L ratio {ratio}"


def overview_embed(user: discord.abc.User) -> discord.Embed:
    played = record_matches(user.id)
    wins = sum(1 for m in played if did_win(m, user.id))
    losses = len(played) - wins
    mvps = [m for m in data["matches"] if m.get("mvp") == user.id and m["winner"]]
    profile = data["profiles"].get(str(user.id))

    embed = discord.Embed(title=f"{user.display_name} - Overview", color=0x1E90FF)
    embed.add_field(name="Win/Loss", value=record_line(wins, losses), inline=False)
    embed.add_field(name="Total games played", value=str(len(played)), inline=False)
    embed.add_field(name="Voted MVP", value=f"{len(mvps)} time{'s' if len(mvps) != 1 else ''}", inline=False)
    for mode in MODES:
        mm = [m for m in played if m["mode"] == mode]
        w = sum(1 for m in mm if did_win(m, user.id))
        lines = [f"{w}W - {len(mm) - w}L" if mm else "No games"]
        if profile:
            lines.append(f"Elo **{pstat(profile, 'elo', mode, START_ELO)}**")
            lines.append(streak_text(pstat(profile, "streak", mode, 0)))
        if mode != "1v1":  # no MVP vote in 1v1
            lines.append(f"MVPs: {sum(1 for m in mvps if m['mode'] == mode)}")
        embed.add_field(name=mode, value="\n".join(lines), inline=True)
    if profile:
        embed.add_field(name="Enrolled since", value=f"<t:{profile['enrolled']}:D>", inline=False)
    return embed


def mate_lines(records: dict) -> tuple[str, str]:
    ranked = [(u, w, l) for u, (w, l) in records.items() if w + l >= MIN_GAMES_TOGETHER]
    ranked.sort(key=lambda r: (r[1] / (r[1] + r[2]), r[1] + r[2]), reverse=True)
    best = ranked[:3]
    worst = [r for r in reversed(ranked) if r not in best][:3]

    def fmt(rows):
        if not rows:
            return f"Not enough games together yet (need {MIN_GAMES_TOGETHER}+)"
        return "\n".join(f"<@{u}> - {w}W {l}L ({w / (w + l) * 100:.0f}%)" for u, w, l in rows)

    return fmt(best), fmt(worst)


def teammates_embed(user: discord.abc.User) -> discord.Embed:
    embed = discord.Embed(title=f"{user.display_name} - Teammates", color=0x9B59B6)
    for mode in ("3v3", "2v2"):
        records: dict = defaultdict(lambda: [0, 0])
        for m in record_matches(user.id):
            if m["mode"] != mode:
                continue
            team = team_of(m, user.id)
            won = did_win(m, user.id)
            for mate in m[team]:
                if mate != user.id:
                    records[mate][0 if won else 1] += 1
        best, worst = mate_lines(records)
        embed.add_field(name=f"Best in {mode}", value=best, inline=True)
        embed.add_field(name=f"Worst in {mode}", value=worst, inline=True)
        embed.add_field(name="\u200b", value="\u200b", inline=True)
    return embed


def recent_embed(user: discord.abc.User) -> discord.Embed:
    mine = [m for m in data["matches"] if team_of(m, user.id)]
    mine.sort(key=lambda m: m["id"], reverse=True)
    lines = []
    for m in mine[:5]:
        if not m["winner"]:
            result = "\u23f3 **In progress**"
        elif did_win(m, user.id):
            result = f"{APPROVE} **WIN**"
        else:
            result = f"{REJECT} **LOSE**"
        lines.append(f"{result}{score_for(m, user.id)}  -  {m['mode']}  -  Match #{m['id']}  -  <t:{m['created']}:R>")
    return discord.Embed(
        title=f"{user.display_name} - Last 5 matches",
        description="\n".join(lines) or "No matches yet.",
        color=0x2ECC71,
    )


class StatsView(discord.ui.View):
    def __init__(self, user: discord.abc.User, owner_id: int):
        super().__init__(timeout=300)
        self.user = user          # whose stats are shown
        self.owner_id = owner_id  # who ran the command (the only one who can flip pages)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.owner_id:
            await interaction.response.send_message("Run /stats yourself to flip through it.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Overview", style=discord.ButtonStyle.primary)
    async def overview(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=overview_embed(self.user), view=self)

    @discord.ui.button(label="Teammates", style=discord.ButtonStyle.primary)
    async def teammates(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=teammates_embed(self.user), view=self)

    @discord.ui.button(label="Last 5 matches", style=discord.ButtonStyle.primary)
    async def recent(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=recent_embed(self.user), view=self)


# ------------------------------------------------------------ queue timeout
async def notify_timeout(uid: int, mode: str, info: dict) -> None:
    """Tell a player their queue timed out. A DM is the only way to make this private this long after
    they joined (Discord's hidden-reply messages stop working after 15 minutes)."""
    guild = bot.get_guild(info.get("guild_id") or 0)
    where = f" in **{guild.name}**" if guild else ""
    channel_id = info.get("channel_id")
    how = f" Head back to <#{channel_id}> and join a queue again." if channel_id else " Join a queue again."
    text = (
        f"Your **{mode}** queue{where} timed out after {QUEUE_TIMEOUT_MINUTES} minutes because no game started. "
        f"You've been removed from the queue, so you'll need to requeue if you still want to play.{how}"
    )
    try:
        user = bot.get_user(uid) or await bot.fetch_user(uid)
        await user.send(text)
        return
    except discord.HTTPException:
        pass  # their DMs are closed

    # fallback: a short-lived note in the channel they queued from (others can see this one briefly)
    channel = bot.get_channel(channel_id) if channel_id else None
    if channel is not None:
        try:
            await channel.send(
                f"<@{uid}> {text}",
                delete_after=60,
                allowed_mentions=discord.AllowedMentions(users=[discord.Object(id=uid)]),
            )
        except discord.HTTPException:
            pass


@tasks.loop(minutes=1)
async def expire_queues() -> None:
    now = time.time()
    expired = []
    for mode, q in queues.items():
        for uid in list(q):
            info = queue_joined.get(uid)
            if info and now - info["time"] >= QUEUE_TIMEOUT_MINUTES * 60:
                q.remove(uid)
                queue_joined.pop(uid, None)
                expired.append((uid, mode, info))
    if not expired:
        return
    queues_changed()  # panels show the shorter queues
    for uid, mode, info in expired:
        await notify_timeout(uid, mode, info)


@expire_queues.before_loop
async def before_expire_queues() -> None:
    await bot.wait_until_ready()


# ------------------------------------------------------------------- avatar
def avatar_files() -> list[str]:
    """Usable image file names in the avatar folder (empty if the folder doesn't exist)."""
    try:
        names = os.listdir(AVATAR_FOLDER)
    except FileNotFoundError:
        return []
    return sorted(
        n for n in names
        if n.lower().endswith(AVATAR_EXTENSIONS)
        and os.path.getsize(os.path.join(AVATAR_FOLDER, n)) <= AVATAR_MAX_BYTES
    )


async def change_avatar() -> Optional[str]:
    """Switch the bot's profile picture to the next image in the folder.

    Images are used in a shuffled cycle, so every picture shows up before any repeats.
    Returns the file name used, or None if the folder has no usable images.
    """
    available = avatar_files()
    if not available:
        return None
    queue = [n for n in data.get("avatar_queue", []) if n in available]
    if not queue:
        queue = available[:]
        random.shuffle(queue)
        if len(queue) > 1 and queue[0] == data.get("avatar_last"):
            queue.append(queue.pop(0))  # don't show the same picture twice in a row
    name = queue.pop(0)
    with open(os.path.join(AVATAR_FOLDER, name), "rb") as f:
        image = f.read()
    await bot.user.edit(avatar=image)
    data["avatar_queue"], data["avatar_last"], data["avatar_changed"] = queue, name, time.time()
    save_data()
    return name


@tasks.loop(hours=1)
async def rotate_avatar() -> None:
    # checked hourly and compared with the saved time of the last change, so restarts don't cause extra changes
    if time.time() - data.get("avatar_changed", 0) < AVATAR_CHANGE_HOURS * 3600:
        return
    try:
        await change_avatar()
    except discord.HTTPException as error:
        print(f"Couldn't change the avatar (will try again in an hour): {error}")


@rotate_avatar.before_loop
async def before_rotate_avatar() -> None:
    await bot.wait_until_ready()


# ------------------------------------------------------------------ status
status_state = {"tick": 0, "tips": [], "last": None, "hold_until": 0, "token": None}


def congrats_text(m: dict) -> str:
    """Status text congratulating the winners of a match (kept under Discord's 128 character limit)."""
    team = m["winner"]
    names = [player_name(u) for u in m[team]]
    who = names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]
    scores = series_scores(m)  # (blue games, orange games) for best-of-3 series
    score = ""
    if scores:
        won, lost = (scores[0], scores[1]) if team == "blue" else (scores[1], scores[0])
        score = f" ({won}-{lost})"
    text = f"Congrats {who} on winning {m['mode']} match #{m['id']}{score}!"
    if len(text) > 128:  # a lot of long names: name the team instead
        text = f"Congrats team {team} on winning {m['mode']} match #{m['id']}{score}!"
    return text


async def show_congrats(m: dict) -> None:
    """Put a congratulations message in the status for CONGRATS_SECONDS, then go back to tips and facts."""
    text = congrats_text(m)
    token = time.time()  # identifies this celebration, so a newer result isn't cut short by an older timer
    status_state["token"] = token
    status_state["hold_until"] = token + CONGRATS_SECONDS
    status_state["last"] = text
    try:
        await bot.change_presence(activity=make_activity(text))
    except discord.HTTPException as error:
        print(f"Couldn't update the status: {error}")
    await asyncio.sleep(CONGRATS_SECONDS)
    if status_state["token"] == token:
        status_state["hold_until"] = 0
        if rotate_status.is_running():
            rotate_status.restart()  # shows the next tip right away and restarts the 5 minute timer
        else:
            rotate_status.start()


def fun_facts(uid: int) -> list[str]:
    """Things worth announcing about one player, based on their games so far."""
    profile = data["profiles"].get(str(uid))
    if not profile:
        return []
    name = player_name(uid)
    facts = []

    for mode in MODES:  # current streaks
        streak = pstat(profile, "streak", mode, 0)
        if streak >= 3:
            facts.append(f"{name} has a {streak} game win streak in {mode}!")
        elif streak <= -3:
            facts.append(f"{name} has lost {-streak} {mode} games in a row. A comeback is due!")

    for mode in MODES:  # top of a leaderboard (needs at least two ranked players)
        rows = elo_rows(mode)
        if len(rows) >= 2 and rows[0][0] == uid:
            facts.append(f"{name} is #1 on the {mode} leaderboard with {rows[0][1]} Elo!")

    games = chronological(uid)
    if games:
        results = [did_win(m, uid) for m in games]
        best_streak, _, _ = streak_records(results)
        if best_streak >= 3:
            facts.append(f"{name}'s best win streak ever is {best_streak} games!")
        mvps = sum(1 for m in games if m.get("mvp") == uid)
        if mvps:
            facts.append(f"{name} has been voted MVP {mvps} time{'s' if mvps != 1 else ''}!")
        if len(games) >= 5:
            facts.append(f"{name} has played {len(games)} games so far!")
        recent = results[-10:]
        if len(recent) >= 5 and sum(recent) / len(recent) >= 0.7:
            facts.append(f"{name} has won {sum(recent)} of their last {len(recent)} games!")
    return facts


def pick_fun_fact() -> Optional[str]:
    """A fun fact about someone waiting in a queue (or, failing that, any enrolled player)."""
    pools = [list({u for q in queues.values() for u in q})]
    if FACTS_FALLBACK_TO_ALL:
        pools.append([int(u) for u in data["profiles"]])
    for pool in pools:
        candidates = [f for uid in pool for f in fun_facts(uid) if f != status_state["last"]]
        if candidates:
            return random.choice(candidates)
    return None


def next_tip() -> str:
    """Tips come in a shuffled cycle, so each one shows before any repeats."""
    if not status_state["tips"]:
        tips = STATUS_TIPS[:]
        random.shuffle(tips)
        if len(tips) > 1 and tips[0] == status_state["last"]:
            tips.append(tips.pop(0))
        status_state["tips"] = tips
    return status_state["tips"].pop(0)


def make_activity(text: str):
    text = text[:128]  # Discord's limit for status text
    if STATUS_STYLE == "custom":
        return discord.CustomActivity(name=text)
    kinds = {
        "watching": discord.ActivityType.watching,
        "playing": discord.ActivityType.playing,
        "listening": discord.ActivityType.listening,
    }
    return discord.Activity(type=kinds.get(STATUS_STYLE, discord.ActivityType.watching), name=text)


@tasks.loop(minutes=STATUS_MINUTES)
async def rotate_status() -> None:
    if time.time() < status_state["hold_until"]:
        return  # a congratulations message is showing
    status_state["tick"] += 1
    text = pick_fun_fact() if status_state["tick"] % STATUS_FACT_EVERY == 0 else None
    if text is None:
        text = next_tip()
    status_state["last"] = text
    try:
        await bot.change_presence(activity=make_activity(text))
    except discord.HTTPException as error:
        print(f"Couldn't update the status: {error}")


@rotate_status.before_loop
async def before_rotate_status() -> None:
    await bot.wait_until_ready()


# --------------------------------------------------------------------- bot
class RLBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = USE_MESSAGE_CONTENT
        super().__init__(command_prefix="!", intents=intents)

    async def setup_hook(self):
        recompute_elo()
        self.add_view(QueueView())
        self.add_view(TeamModeView())
        self.add_view(MatchView())
        self.add_view(SeriesMatchView())
        self.add_view(LobbyView())
        self.add_view(VoiceChoiceView())
        for m in data["matches"]:  # pick up lobby waits and team voice votes that were still running
            if m.get("state") == "lobby":
                asyncio.create_task(lobby_expiry(m["id"], max(0, m.get("lobby_deadline", 0) - time.time())))
            if voice_pending(m) and m.get("voice_deadline"):
                asyncio.create_task(voice_expiry(m["id"], max(0, m["voice_deadline"] - time.time())))
        self.add_view(MvpView())
        for m in data["matches"]:
            if m.get("mvp_open"):
                remaining = max(0, m.get("mvp_deadline", 0) - time.time())
                asyncio.create_task(mvp_expiry(m["id"], remaining))
        bump_panels.start()
        rotate_avatar.start()
        expire_queues.start()
        rotate_status.start()
        await self.tree.sync()


bot = RLBot()


@bot.tree.command(name="enroll6mans", description="Enroll to play 6mans and create your profile")
@app_commands.guild_only()
async def enroll6mans(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    cfg = get_config(interaction.guild_id)
    role = interaction.guild.get_role(cfg["queue_role_id"]) if cfg else None
    if role is None:
        await interaction.followup.send(
            "An admin needs to run **/setup** before anyone can enroll.", ephemeral=True
        )
        return
    is_new = create_profile(interaction.user)

    # give the enrollment role, creating it the first time
    role_note = ""
    try:
        if role not in interaction.user.roles:
            await interaction.user.add_roles(role, reason="Enrolled in 6mans")
    except discord.HTTPException:
        role_note = (
            f"\n(I couldn't give you the **{role.name}** role. "
            "Ask an admin to check the bot's Manage Roles permission and role position.)"
        )

    if is_new:
        text = f"You're enrolled! Your profile is ready and you can now join queues. Check it any time with **/stats**.{role_note}"
    else:
        text = f"You're already enrolled, so you're good to queue.{role_note}"
    await interaction.followup.send(text, ephemeral=True)


@bot.tree.command(name="setup", description="Set the home channel and the role that allows queuing")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(
    channel="Home channel for queues and match announcements",
    role=f"Role that allows queuing (leave empty to use or create '{ENROLL_ROLE}')",
)
async def setup(
    interaction: discord.Interaction,
    channel: discord.TextChannel,
    role: Optional[discord.Role] = None,
):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to run /setup.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    notes = []

    if role is None:
        role = discord.utils.get(guild.roles, name=ENROLL_ROLE)
        if role is None:
            try:
                role = await guild.create_role(name=ENROLL_ROLE, mentionable=True, reason="6mans setup")
            except discord.HTTPException:
                await interaction.followup.send(
                    "I couldn't create the role. Give me **Manage Roles**, or run /setup again and pick an existing role.",
                    ephemeral=True,
                )
                return

    if role.is_default() or role.managed:
        await interaction.followup.send("Please pick a regular role (not @everyone or a bot role).", ephemeral=True)
        return
    if role >= guild.me.top_role:
        await interaction.followup.send(
            f"I can't hand out {role.mention} because it's above my role. "
            "Move my role above it in Server Settings -> Roles, then run /setup again.",
            ephemeral=True,
        )
        return

    # /ping works best when the role can be mentioned
    if not role.mentionable:
        try:
            await role.edit(mentionable=True, reason="6mans /ping")
        except discord.HTTPException:
            notes.append("I couldn't make the role mentionable, so /ping will tag players one by one instead.")

    cfg = data["config"].setdefault(str(guild.id), {})
    cfg["home_channel_id"] = channel.id
    cfg["queue_role_id"] = role.id
    save_data()

    # everyone who already enrolled gets the role
    given = 0
    for uid in data["profiles"]:
        try:
            member = guild.get_member(int(uid)) or await guild.fetch_member(int(uid))
            if role not in member.roles:
                await member.add_roles(role, reason="6mans setup")
                given += 1
        except discord.HTTPException:
            pass

    try:
        async with panel_lock:
            await keep_panel_on_top(cfg)
    except discord.HTTPException:
        notes.append(f"I couldn't post the queue panel in <#{queue_channel_id(cfg)}>. Check my permissions there.")

    text = (
        f"Setup complete.\nHome channel: {channel.mention}\nQueue channel: <#{queue_channel_id(cfg)}>\nQueue role: {role.mention}\n"
        f"Players must run **/enroll6mans** to get the role and queue."
    )
    if given:
        text += f"\nGave the role to {given} already-enrolled player(s)."
    if notes:
        text += "\n" + "\n".join(notes)
    await interaction.followup.send(text, ephemeral=True)


@bot.tree.command(name="ping", description="Ping everyone with the queue role")
@app_commands.guild_only()
async def ping(interaction: discord.Interaction):
    cfg = get_config(interaction.guild_id)
    role = interaction.guild.get_role(cfg["queue_role_id"]) if cfg else None
    if role is None:
        await interaction.response.send_message("An admin needs to run **/setup** first.", ephemeral=True)
        return
    if role not in interaction.user.roles:
        await interaction.response.send_message(
            "Only enrolled players can use /ping. Run **/enroll6mans** first.", ephemeral=True
        )
        return

    if role.mentionable or interaction.guild.me.guild_permissions.mention_everyone:
        await interaction.response.send_message(
            f"{role.mention} {PING_TEXT}",
            allowed_mentions=discord.AllowedMentions(roles=[role], users=False, everyone=False),
        )
        return

    # role can't be mentioned: tag enrolled players individually
    ids = [int(u) for u in data["profiles"]]
    chunks = [ids[i:i + 60] for i in range(0, len(ids), 60)] or [[]]
    for n, chunk in enumerate(chunks):
        tags = " ".join(f"<@{u}>" for u in chunk)
        content = f"{tags}\n{PING_TEXT}" if n == 0 else tags
        allowed = discord.AllowedMentions(
            users=[discord.Object(id=u) for u in chunk],
            roles=False,
            everyone=False,
        )
        if n == 0:
            await interaction.response.send_message(content, allowed_mentions=allowed)
        else:
            await interaction.followup.send(content, allowed_mentions=allowed)


@bot.tree.command(name="help", description="Show every command and what it does")
async def help_cmd(interaction: discord.Interaction):
    embed = discord.Embed(title="6mans bot - commands", color=0x1E90FF)
    embed.add_field(
        name="Players",
        value=(
            "`/enroll6mans` - Enroll to play. Creates your profile and gives you the queue role (needed before queuing).\n"
            "`/queue` - Join the 1v1, 2v2 or 3v3 queue. The buttons on the queue panel do the same. You're removed after 30 minutes if no game starts. You can't requeue until your last match is reported.\n"
            "`/leave` - Leave your current queue.\n"
            "`/status` - See who is waiting in each queue.\n"
            "`/ping` - Tell everyone with the queue role that players are looking for more.\n"
            "`/stats` - Record, Elo and streak per mode, MVP count, best and worst teammates, and last 5 matches. Shown to everyone. Add a player to see theirs.\n"
            "`/leaderboard` - Elo leaderboard by mode, highest to lowest, with pages.\n"
            "`/headtohead` - Compare your wins and losses against another player.\n"
            "`/matchfinder` - Look up any past match by its number.\n"
            "`/records` - Best win streak, worst loss streak, Elo highs and lows, and other records.\n"
            "`/undo` - Dispute a wrongly reported result and start a vote to change it.\n"
            "`/help` - Show this list."
        ),
        inline=False,
    )
    embed.add_field(
        name="Admins (Manage Server)",
        value=(
            "`/setup` - Set the home channel and the queue role, and post the queue panel.\n"
            "`/set-queue-channel` - Choose the channel where games are queued and where the always-on queue panel lives.\n"
            "`/resetelo` - Reset Elo for one player or everyone, optionally for just one mode.\n"
            "`/resetwl` - Reset the win/loss record for one player or everyone, optionally for just one mode.\n"
            "`/admin-enroll` - Enroll or unenroll any player.\n"
            "`/delete-match` - Delete a match by its number. You'll be asked to type a reason, which is recorded.\n"
            "`/edit` - Fix a past match by its number: change the winner, series score or MVP. Elo is recalculated.\n"
            "`/set-lobby-vc` - Set the voice channel players join before a 2v2 or 3v3 starts.\n"
            "`/change-avatar` - Switch the bot's profile picture to the next image in its folder right now.\n"
            "`/fullreset` - Wipe every stat (Elo, win/loss, MVPs, records, queues) back to default. Saves a backup first."
        ),
        inline=False,
    )
    embed.add_field(
        name="How a match works",
        value=(
            "When a queue fills, the bot makes a private match channel. In 2v2 and 3v3 everyone joins the lobby voice channel first "
            "(if one is set), then you pick Random, Draft or Balanced teams and vote on team voice channels. "
            "Lobby players are moved into their team's channel. "
            "Then play and report the winner. 2v2 and 3v3 are best-of-3 series, so you report the series score too (2-0 or 2-1). "
            "In those two modes the losing team can privately vote for an MVP for 2 minutes, and the MVP gets a small Elo bonus."
        ),
        inline=False,
    )
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="set-queue-channel", description="Choose the channel where games are queued")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(channel="Channel for the always-on queue panel")
async def set_queue_channel(interaction: discord.Interaction, channel: discord.TextChannel):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to use this.", ephemeral=True)
        return
    cfg = get_config(interaction.guild_id)
    if not cfg:
        await interaction.response.send_message("Run **/setup** first.", ephemeral=True)
        return

    await interaction.response.defer(ephemeral=True)
    cfg["queue_channel_id"] = channel.id
    save_data()
    try:
        async with panel_lock:
            await post_panel(cfg, channel)  # fresh panel here, old one removed
    except discord.HTTPException:
        await interaction.followup.send(
            f"Saved {channel.mention} as the queue channel, but I couldn't post the panel there. "
            "Check that I can view, send messages and embed links in that channel.",
            ephemeral=True,
        )
        return
    await interaction.followup.send(
        f"Queue channel set to {channel.mention}. The queue panel is posted there, and every "
        f"{PANEL_REFRESH_SECONDS} seconds I move it back to the bottom if other messages have pushed it up.",
        ephemeral=True,
    )


@bot.tree.command(name="queue", description="Join a queue")
@app_commands.choices(mode=[app_commands.Choice(name=m, value=m) for m in MODES])
async def queue(interaction: discord.Interaction, mode: app_commands.Choice[str]):
    await join_queue(interaction, mode.value)


@bot.tree.command(name="leave", description="Leave your current queue")
async def leave(interaction: discord.Interaction):
    remove_from_all(interaction.user.id)
    queues_changed()
    await interaction.response.send_message("You left the queue.", ephemeral=True)


@bot.tree.command(name="status", description="See who's in each queue")
async def status(interaction: discord.Interaction):
    await interaction.response.send_message(embed=status_embed())


@bot.tree.command(name="stats", description="Show your stats, or another player's")
@app_commands.describe(player="Whose stats to show (leave empty for your own)")
async def stats_cmd(interaction: discord.Interaction, player: Optional[discord.Member] = None):
    target = player or interaction.user
    if target.bot:
        await interaction.response.send_message("Bots don't play 6mans.", ephemeral=True)
        return
    if str(target.id) not in data["profiles"]:
        who = "You haven't" if target.id == interaction.user.id else f"{target.display_name} hasn't"
        await interaction.response.send_message(f"{who} enrolled yet. Enroll with **/enroll6mans**.", ephemeral=True)
        return
    await interaction.response.send_message(
        embed=overview_embed(target),
        view=StatsView(target, interaction.user.id),
    )


@bot.tree.command(name="leaderboard", description="Elo leaderboard for a mode, highest to lowest")
@app_commands.describe(mode="Which mode's leaderboard to show (default 3v3)")
@app_commands.choices(mode=[app_commands.Choice(name=m, value=m) for m in MODES])
async def leaderboard(interaction: discord.Interaction, mode: Optional[app_commands.Choice[str]] = None):
    chosen = mode.value if mode else "3v3"
    await interaction.response.send_message(
        embed=leaderboard_embed(0, chosen), view=LeaderboardView(interaction.user.id, chosen)
    )


@bot.tree.command(name="resetelo", description="Reset Elo for a player or everyone, in one mode or all modes")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(
    player="Player to reset (leave empty to reset the whole group)",
    mode="Mode to reset (leave empty for all modes)",
)
@app_commands.choices(mode=[app_commands.Choice(name=m, value=m) for m in MODES])
async def resetelo(
    interaction: discord.Interaction,
    player: Optional[discord.Member] = None,
    mode: Optional[app_commands.Choice[str]] = None,
):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to reset Elo.", ephemeral=True)
        return

    modes = [mode.value] if mode else list(MODES)
    label = mode.value if mode else "all modes"

    def stamp(existing) -> dict:
        now = time.time()
        stamps = dict(existing) if isinstance(existing, dict) else {md: (existing or 0) for md in MODES}
        for md in modes:
            stamps[md] = now
        return stamps

    if player is not None:
        profile = data["profiles"].get(str(player.id))
        if profile is None:
            await interaction.response.send_message(f"{player.display_name} hasn't enrolled yet.", ephemeral=True)
            return
        profile["elo_reset"] = stamp(profile.get("elo_reset", 0))
        recompute_elo()
        await interaction.response.send_message(
            f"{player.mention}'s Elo was reset to **{START_ELO}** ({label}).",
            allowed_mentions=discord.AllowedMentions.none(),
        )
        return

    async def confirm(i: discord.Interaction):
        data["elo_reset_all"] = stamp(data.get("elo_reset_all", 0))
        recompute_elo()
        await i.response.edit_message(content=f"Everyone's Elo has been reset to {START_ELO} ({label}).", view=None)
        try:
            await i.channel.send(
                f"{i.user.mention} reset Elo for the whole group ({label}). Everyone starts again at **{START_ELO}**.",
                allowed_mentions=discord.AllowedMentions.none(),
            )
        except discord.HTTPException:
            pass

    await interaction.response.send_message(
        f"This resets **everyone's** Elo to {START_ELO} and clears streaks for **{label}**. "
        "Match history and win/loss stats are kept. Continue?",
        view=ConfirmView(interaction.user.id, confirm, "Yes, reset everyone"),
        ephemeral=True,
    )


@bot.tree.command(name="resetwl", description="Reset win/loss record for a player or everyone, in one mode or all modes")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(
    player="Player to reset (leave empty to reset the whole group)",
    mode="Mode to reset (leave empty for all modes)",
)
@app_commands.choices(mode=[app_commands.Choice(name=m, value=m) for m in MODES])
async def resetwl(
    interaction: discord.Interaction,
    player: Optional[discord.Member] = None,
    mode: Optional[app_commands.Choice[str]] = None,
):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to reset records.", ephemeral=True)
        return

    modes = [mode.value] if mode else list(MODES)
    label = mode.value if mode else "all modes"

    if player is not None:
        profile = data["profiles"].get(str(player.id))
        if profile is None:
            await interaction.response.send_message(f"{player.display_name} hasn't enrolled yet.", ephemeral=True)
            return
        profile["wl_reset"] = stamp_resets(profile.get("wl_reset", 0), modes)
        save_data()
        await interaction.response.send_message(
            f"{player.mention}'s win/loss record was reset ({label}). Their Elo is unchanged.",
            allowed_mentions=discord.AllowedMentions.none(),
        )
        return

    async def confirm(i: discord.Interaction):
        data["wl_reset_all"] = stamp_resets(data.get("wl_reset_all", 0), modes)
        save_data()
        await i.response.edit_message(content=f"Everyone's win/loss record has been reset ({label}).", view=None)
        try:
            await i.channel.send(
                f"{i.user.mention} reset win/loss records for the whole group ({label}). Elo is unchanged.",
                allowed_mentions=discord.AllowedMentions.none(),
            )
        except discord.HTTPException:
            pass

    await interaction.response.send_message(
        f"This resets **everyone's** win/loss record, games played and teammate stats for **{label}**. "
        "Elo and match history are kept. Continue?",
        view=ConfirmView(interaction.user.id, confirm, "Yes, reset everyone"),
        ephemeral=True,
    )


@bot.tree.command(name="matchfinder", description="Look up a past match by its number")
@app_commands.rename(match_id="number")
@app_commands.describe(match_id="The match number to look up")
async def matchfinder(interaction: discord.Interaction, match_id: int):
    m = get_match(match_id)
    if m:
        await interaction.response.send_message(embed=match_info_embed(m))
        return
    for entry in data.get("deleted_matches", []):  # deleted matches are archived with their reason
        if entry["match"]["id"] == match_id:
            await interaction.response.send_message(embed=deleted_record_embed(entry))
            return
    await interaction.response.send_message("Match does not exist.", ephemeral=True)


@bot.tree.command(name="headtohead", description="Compare your wins and losses against another player")
@app_commands.describe(player="The player to compare yourself against")
async def headtohead(interaction: discord.Interaction, player: discord.Member):
    me = interaction.user
    if player.bot or player.id == me.id:
        await interaction.response.send_message("Pick another player to compare against.", ephemeral=True)
        return
    for who in (me, player):
        if str(who.id) not in data["profiles"]:
            name = "You haven't" if who.id == me.id else f"{who.display_name} hasn't"
            await interaction.response.send_message(f"{name} enrolled yet.", ephemeral=True)
            return

    mine = {m["id"] for m in record_matches(me.id)}
    shared = [m for m in record_matches(player.id) if m["id"] in mine]
    shared.sort(key=lambda m: m["id"], reverse=True)
    versus = [m for m in shared if team_of(m, me.id) != team_of(m, player.id)]
    together = [m for m in shared if team_of(m, me.id) == team_of(m, player.id)]

    my_wins = sum(1 for m in versus if did_win(m, me.id))
    their_wins = len(versus) - my_wins
    embed = discord.Embed(title=f"{me.display_name} vs {player.display_name}", color=0xE67E22)
    if versus:
        embed.add_field(
            name="Against each other",
            value=(
                f"**{me.display_name} {my_wins} - {their_wins} {player.display_name}**\n"
                f"{my_wins / len(versus) * 100:.0f}% - {their_wins / len(versus) * 100:.0f}%"
            ),
            inline=False,
        )
        for mode in MODES:
            mm = [m for m in versus if m["mode"] == mode]
            w = sum(1 for m in mm if did_win(m, me.id))
            embed.add_field(name=mode, value=f"{w} - {len(mm) - w}" if mm else "No games")
        lines = []
        for m in versus[:5]:
            result = f"{APPROVE} **WIN**" if did_win(m, me.id) else f"{REJECT} **LOSE**"
            lines.append(f"{result}{score_for(m, me.id)}  -  {m['mode']}  -  Match #{m['id']}  -  <t:{m['created']}:R>")
        embed.add_field(name=f"Last meetings (from {me.display_name}'s view)", value="\n".join(lines), inline=False)
    else:
        embed.description = "You haven't played against each other yet."
    if together:
        tw = sum(1 for m in together if did_win(m, me.id))
        embed.add_field(name="As teammates", value=f"{tw}W - {len(together) - tw}L together", inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="records", description="Best win streak, worst loss streak and other records")
@app_commands.describe(player="Whose records to show (leave empty for your own)")
async def records_cmd(interaction: discord.Interaction, player: Optional[discord.Member] = None):
    target = player or interaction.user
    if target.bot:
        await interaction.response.send_message("Bots don't play 6mans.", ephemeral=True)
        return
    if str(target.id) not in data["profiles"]:
        who = "You haven't" if target.id == interaction.user.id else f"{target.display_name} hasn't"
        await interaction.response.send_message(f"{who} enrolled yet. Enroll with **/enroll6mans**.", ephemeral=True)
        return
    await interaction.response.send_message(embed=records_embed(target))


@bot.tree.command(name="admin-enroll", description="Enroll or unenroll a player (admin)")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(player="The player to enroll or unenroll", action="What to do")
@app_commands.choices(
    action=[app_commands.Choice(name="Enroll", value="enroll"), app_commands.Choice(name="Unenroll", value="unenroll")]
)
async def admin_enroll(interaction: discord.Interaction, player: discord.Member, action: app_commands.Choice[str]):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to use this.", ephemeral=True)
        return
    if player.bot:
        await interaction.response.send_message("Bots can't be enrolled.", ephemeral=True)
        return
    cfg = get_config(interaction.guild_id)
    role = interaction.guild.get_role(cfg["queue_role_id"]) if cfg else None
    if role is None:
        await interaction.response.send_message("Run **/setup** first.", ephemeral=True)
        return

    await interaction.response.defer(ephemeral=True)
    note = ""
    if action.value == "enroll":
        created = create_profile(player)
        try:
            if role not in player.roles:
                await player.add_roles(role, reason=f"Enrolled by {interaction.user}")
        except discord.HTTPException:
            note = f"\nI couldn't give them the **{role.name}** role. Check my Manage Roles permission and role position."
        text = f"{player.mention} is now enrolled." if created else f"{player.mention} was already enrolled."
    else:
        removed = remove_profile(player.id)
        queues_changed()
        try:
            if role in player.roles:
                await player.remove_roles(role, reason=f"Unenrolled by {interaction.user}")
        except discord.HTTPException:
            note = f"\nI couldn't remove the **{role.name}** role. Check my Manage Roles permission and role position."
        text = (
            f"{player.mention} was unenrolled. Their match history is kept, so enrolling them again brings their ratings back."
            if removed
            else f"{player.mention} wasn't enrolled."
        )
    await interaction.followup.send(text + note, ephemeral=True, allowed_mentions=discord.AllowedMentions.none())


@bot.tree.command(name="fullreset", description="Reset EVERY stat to default: Elo, win/loss, MVPs, records and queues")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
async def fullreset(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to use this.", ephemeral=True)
        return
    uid = interaction.user.id

    async def step_two(i: discord.Interaction):
        async def final(i2: discord.Interaction):
            backup = full_reset()
            queues_changed()
            await i2.response.edit_message(
                content=f"Done. Every stat is back to default and the queues are empty. The old data was saved as `{backup}` next to the bot.",
                view=None,
            )
            try:
                await i2.channel.send(
                    f"{i2.user.mention} reset all 6mans stats. Everyone starts fresh at **{START_ELO}**.",
                    allowed_mentions=discord.AllowedMentions.none(),
                )
            except discord.HTTPException:
                pass

        await i.response.edit_message(
            content=(
                "**Final confirmation.** This cannot be undone from Discord. Everyone's Elo, win/loss, MVPs, "
                "records, streaks and match history are wiped, and anyone waiting in a queue is removed. "
                "Players stay enrolled. A backup file is saved first. Wipe everything?"
            ),
            view=ConfirmView(uid, final, "Yes, wipe everything"),
        )

    await interaction.response.send_message(
        "This resets **every stat** for **all modes** back to default: Elo, win/loss ratios, MVPs, records and the live queues. Continue?",
        view=ConfirmView(uid, step_two, "Yes, continue"),
        ephemeral=True,
    )


@bot.tree.command(name="set-lobby-vc", description="Set the voice channel players join before a 2v2 or 3v3 starts (admin)")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(channel="The lobby voice channel (leave empty to turn the lobby off)")
async def set_lobby_vc(interaction: discord.Interaction, channel: Optional[discord.VoiceChannel] = None):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to use this.", ephemeral=True)
        return
    cfg = get_config(interaction.guild_id)
    if not cfg:
        await interaction.response.send_message("Run **/setup** first.", ephemeral=True)
        return
    if channel is None:
        cfg.pop("lobby_vc_id", None)
        save_data()
        await interaction.response.send_message(
            "Lobby turned off. 2v2 and 3v3 matches go straight to team selection.", ephemeral=True
        )
        return
    cfg["lobby_vc_id"] = channel.id
    save_data()
    note = ""
    if not interaction.guild.me.guild_permissions.move_members:
        note = "\nI don't have the **Move Members** permission yet, so I won't be able to move players. Please give it to my role."
    await interaction.response.send_message(
        f"Lobby set to {channel.mention}. For 2v2 and 3v3, once the queued players are all in there, "
        f"I'll ask for team selection, then move them to their team voice channels.{note}",
        ephemeral=True,
    )


@bot.tree.command(name="change-avatar", description="Switch the bot's profile picture to the next image now (admin)")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
async def change_avatar_cmd(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to use this.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    try:
        name = await change_avatar()
    except discord.HTTPException as error:
        await interaction.followup.send(
            f"Discord wouldn't let me change it right now (it limits how often a bot can do this): {error}",
            ephemeral=True,
        )
        return
    if name is None:
        await interaction.followup.send(
            f"I couldn't find any images. Put .png or .jpg files in this folder on the computer running the bot: `{AVATAR_FOLDER}`",
            ephemeral=True,
        )
        return
    await interaction.followup.send(f"Profile picture changed to `{name}`. Discord can take a moment to show it.", ephemeral=True)


@bot.tree.command(name="delete-match", description="Delete a match and record why (admin)")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(match_id="The match number to delete")
async def delete_match_cmd(interaction: discord.Interaction, match_id: int):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to delete matches.", ephemeral=True)
        return
    if not get_match(match_id):
        await interaction.response.send_message(f"I couldn't find a match #{match_id}.", ephemeral=True)
        return
    await interaction.response.send_modal(DeleteMatchModal(match_id))


@bot.tree.command(name="edit", description="Edit a past match: winner, series score or MVP (admin)")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(match_id="The match number to edit")
async def edit_cmd(interaction: discord.Interaction, match_id: int):
    if not interaction.user.guild_permissions.manage_guild:
        await interaction.response.send_message("You need the Manage Server permission to edit matches.", ephemeral=True)
        return
    m = get_match(match_id)
    if not m:
        await interaction.response.send_message(f"I couldn't find a match #{match_id}.", ephemeral=True)
        return
    if not m["winner"]:
        await interaction.response.send_message(
            f"Match #{match_id} hasn't been reported yet. Players report the result from its match channel.",
            ephemeral=True,
        )
        return
    await interaction.response.send_message(
        content="Pick what to change. Changes apply right away and Elo is recalculated.",
        embed=edit_embed(m),
        view=EditView(interaction.user.id, m),
        ephemeral=True,
    )


@bot.tree.command(name="undo", description="Start a vote to change a wrongly reported result")
@app_commands.describe(match_id="Match number (leave empty for your most recent reported match)")
async def undo(interaction: discord.Interaction, match_id: Optional[int] = None):
    uid = interaction.user.id
    if match_id is None:
        mine = sorted(finished_matches(uid), key=lambda m: m["id"], reverse=True)
        m = mine[0] if mine else None
    else:
        m = get_match(match_id)

    if not m:
        await interaction.response.send_message("I couldn't find a reported match for you.", ephemeral=True)
        return
    if not m["winner"]:
        await interaction.response.send_message("That match hasn't been reported yet.", ephemeral=True)
        return
    if uid not in m["blue"] + m["orange"]:
        await interaction.response.send_message("Only players in that match can start an undo.", ephemeral=True)
        return

    new_winner = "orange" if m["winner"] == "blue" else "blue"
    mid = m["id"]

    async def step_two(i: discord.Interaction):
        async def final(i2: discord.Interaction):
            await start_vote(i2, mid)

        await i.response.edit_message(
            content=(
                f"**Final confirmation.** This posts a public vote. It needs {VOTES_NEEDED} {APPROVE} "
                f"approvals to change Match #{mid} to a **{new_winner.title()} win**. Post it?"
            ),
            view=ConfirmView(uid, final, "Yes, post the vote"),
        )

    await interaction.response.send_message(
        f"Match #{mid} ({m['mode']}) is recorded as a **{m['winner'].title()} win**. "
        f"Do you want to dispute it and propose a **{new_winner.title()} win** instead?",
        view=ConfirmView(uid, step_two, "Yes, continue"),
        ephemeral=True,
    )


@bot.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    """When someone joins or leaves the lobby, see whether a waiting match now has everyone."""
    if before.channel == after.channel:
        return
    cfg = get_config(member.guild.id)
    lobby_id = cfg.get("lobby_vc_id") if cfg else None
    if not lobby_id or lobby_id not in (getattr(before.channel, "id", None), getattr(after.channel, "id", None)):
        return
    for m in list(data["matches"]):
        if m.get("state") == "lobby" and m.get("guild_id") == member.guild.id and member.id in m["players"]:
            await check_lobby(member.guild, m)


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot or message.guild is None:
        return
    m = next(
        (x for x in data["matches"] if x.get("state") == "draft" and x.get("text_channel_id") == message.channel.id),
        None,
    )
    if m:
        await handle_pick(message, m)


@bot.event
async def on_raw_reaction_add(payload: discord.RawReactionActionEvent):
    if payload.user_id == bot.user.id:
        return
    vote = pending_votes.get(payload.message_id)
    emoji = str(payload.emoji)
    if not vote or emoji not in (APPROVE, REJECT):
        return

    channel = bot.get_channel(payload.channel_id) or await bot.fetch_channel(payload.channel_id)
    message = await channel.fetch_message(payload.message_id)
    counts = {APPROVE: 0, REJECT: 0}
    for r in message.reactions:
        if str(r.emoji) in counts:
            counts[str(r.emoji)] = r.count - (1 if r.me else 0)

    if counts[APPROVE] >= VOTES_NEEDED:
        pending_votes.pop(payload.message_id, None)
        m = get_match(vote["match_id"])
        if not m:
            return
        old = m["winner"]
        m["winner"] = vote["new_winner"]
        m["mvp_open"] = False  # the old winning team's MVP no longer applies
        m.pop("mvp", None)
        m.pop("mvp_votes", None)
        recompute_elo()  # ratings and streaks are rebuilt from history (also saves)
        await update_summary(m)
        embed = message.embeds[0]
        embed.color = 0x2ECC71
        embed.set_footer(text=f"Approved. Match #{m['id']} changed from {old.title()} to {m['winner'].title()} win. Elo recalculated.")
        await message.edit(embed=embed)
    elif counts[REJECT] >= VOTES_NEEDED:
        pending_votes.pop(payload.message_id, None)
        embed = message.embeds[0]
        embed.color = 0xE74C3C
        embed.set_footer(text="Rejected. Result unchanged.")
        await message.edit(embed=embed)


started = {"announced": False}


async def announce_online() -> None:
    """Post the 'now online' message in each server's queue channel (once per start, not on every reconnect)."""
    if started["announced"]:
        return
    started["announced"] = True
    for cfg in list(data["config"].values()):
        channel = bot.get_channel(queue_channel_id(cfg))
        if channel is None:
            continue
        try:
            await channel.send(ONLINE_MESSAGE, delete_after=ONLINE_MESSAGE_SECONDS)
        except discord.HTTPException:
            pass  # no permission in that channel; not worth stopping for


@bot.event
async def on_ready():
    print(f"Logged in as {bot.user}")
    await refresh_panels()  # queues start empty, so clear any stale numbers on old panels
    await announce_online()


bot.run(os.environ["DISCORD_TOKEN"])
