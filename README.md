# Park That Thought

**A tiny floating cloud for Windows that catches stray thoughts while you work, so you can stay focused.**

Free and open source. [![Buy me a coffee](https://img.shields.io/badge/Buy%20me%20a%20coffee-FFDD00?logo=buymeacoffee&logoColor=black)](https://buymeacoffee.com/gmiqbal)

[Thought catcher](#park-a-thought-in-two-seconds) + [Drop shelf](#a-drop-shelf-for-files-snips-and-links) + [Meeting bar](#your-calendar-floating-on-the-taskbar) + [Focus timer](#focus-rounds) + [Check-ins](#check-ins) + [Water and eye breaks](#water-and-eye-breaks) + [Reminders](#reminders) + [Focus sounds](#background-noise-and-music) + [AI pattern insights](#copy-your-patterns-for-ai)

You're in the middle of something and a thought pops up: "look this up", "reply to Sam", "did I pay that bill?". Instead of switching apps (and losing 20 minutes), you park it in two seconds and keep going. At your next break, every thought gets one of three exits: done, later, or let go.

**Capture now, decide at the break.**

**Watch the 2 minute intro:**

https://github.com/user-attachments/assets/a64c7b7c-dccb-46dc-8da6-4e4af4c51c2d

<img src="docs/list.png" width="848" alt="The list in dark and light mode, with a focus round running">

**Contents:** [Why I made it](#why-i-made-it) · [Who it's for](#who-its-for) · [Install](#install-about-2-minutes) · [Tour](#a-quick-tour) · [Drop shelf](#a-drop-shelf-for-files-snips-and-links) · [Calendar](#your-calendar-floating-on-the-taskbar) · [Focus](#focus-rounds) · [Keys](#keys-and-clicks) · [Privacy](#privacy) · [Updating](#updating) · [Uninstall](#uninstall) · [Questions](#questions) · [Run from source](#run-from-source) · [Support](#support)

## Why I made it

I made it in grad school. I was juggling courses, a research project, chores and my hobbies, and while I worked on one thing, thoughts about the others kept showing up. Acting on one might take five minutes, but it cost me the focus I had on the task in front of me, and getting that back took much longer. So I wanted a place to drop the thought in two seconds and trust it would be there at the break. That's this app. The focus timer, the floating meeting bar and the camera check came later, built on the same idea.

## Who it's for

- **People with ADHD or time blindness** who lose focus to their own thoughts, and lose track of time once they follow one.
- **Anyone who works in focus sessions** (Pomodoro or similar): students, researchers, programmers, writers.
- **People who want privacy on screen.** The cloud only shows a number, the quick note box never shows your other notes, and the app is hidden from screen shares and screenshots. Safe in a meeting, on a call or next to your boss.

It is not a full task manager. There's no account, no cloud sync and no phone app. It's one small Windows app that keeps everything on your PC.

## Install (about 2 minutes)

1. Download **[ParkThatThought-Setup.exe](https://github.com/gmiqbal/ParkThatThought/releases/latest/download/ParkThatThought-Setup.exe)** (about 40 MB).
2. Open it.
3. **Windows will most likely show a blue box: "Windows protected your PC".** This is expected. Click **More info**, then **Run anyway**.
4. A cloud appears on the right edge of your screen. That's it.

No admin rights and no Python needed. It adds Park That Thought to the Start menu, your desktop and startup, so it's there every time you log in. If the cloud ever goes missing, double-click the desktop icon.

> **Why the blue box, and is it safe?**
> Windows shows it for any app that isn't "signed". Signing needs a paid certificate, renewed every year, that small free projects usually skip. It says nothing about what the app does.
> - The whole app is open source: one file, [parking_lot.py](parking_lot.py), that anyone can read.
> - It never asks for admin rights. It installs only into your own user folder.
> - Your notes never leave your PC. There's no account and no server.
> - The installer is built from this code and attached to each [release](https://github.com/gmiqbal/ParkThatThought/releases). Windows Defender scans it clean.

## A quick tour

### Park a thought in two seconds

Press `Ctrl+Alt+P` (or scribble the mouse up and down over the cloud), type, press `Enter`. Your cursor goes straight back to where you were typing. The box never shows your other notes.

<img src="docs/quick-note.png" width="530" alt="The quick note box">

Tag it if you like: **urgent**, **distraction** (from outside), **itch** (feels urgent, can wait), **lift**, **drain** or **idea**. You can make your own flags too.

### The list

Click the cloud, press `Ctrl+Alt+L`, or scribble left and right over it. Each thought gets **Done**, **Later** or **Let go**, and `Ctrl+Z` undoes anything. Nothing is ever hard deleted.

### A drop shelf for files, snips and links

Drag a file, a screenshot, a link or some text onto the cloud. A dashed ring shows it's ready, and it lands in your list as a note. Took a screenshot with `Win+Shift+S`? Press `Ctrl+V` in the quick note box and it's parked. Drop more files onto a note to keep them together.

<img src="docs/drop-cloud.png" width="150" alt="A file dragged onto the cloud, with the dashed drop ring">

Files are copied in, so they stay even if the original moves or gets deleted (folders are linked, not copied). When you need one, it's right there: hover it and click its copy button, then paste it into WhatsApp, Slack or an email. Or drag it straight out into a chat, an email or a folder. Double-click opens it, right-click shows it in its folder.

Need the note itself in a message? Hover it and click the copy icon at the start of its buttons, or select it and press `Ctrl+C`. **Copy all** at the bottom copies the whole list.

<img src="docs/drop-shelf.png" width="480" alt="Notes holding a boarding pass, a snip and a lease file, with the copy buttons showing">

### Your calendar, floating on the taskbar

Connect your Google account (the welcome tour asks, or Settings > Calendar > **Connect with Google**) and a small bar shows the current or next meeting with a countdown. It sits on the taskbar, or drag it anywhere to float. Click it for a three-day view with your events in their own colors. All-day events sit in a strip under the dates. **+** adds an event with a description, a calendar and a color; **Instant meet** starts a Google Meet call right away. Hover an event for a quick look; click it to edit, copy it or copy its link to share. Calls show **Join** on their block, and on the bar when they are now or next. The camera button on the bar (or right-click the cloud > **Camera check...**) opens a private **Camera check**: pick your camera, mic and speaker, check them before a call, record 5 seconds to hear yourself, and save a **Daily photo** with the date and time. **Guide** frames each day the same, and **Timelapse** plays them back and makes a video. The bar's **+** adds an event without opening the calendar.

<img src="docs/calendar-bar.png" width="690" alt="The floating meeting bar and the three-day calendar above it">

A few minutes before a meeting, a small note fades in by the cloud with the time and the meeting name, then fades out on its own after a few seconds. No buttons, no sound, never steals focus. You pick the times (30, 10 and 5 minutes before, by default). Join is on the meeting bar.

<img src="docs/meeting-heads-up.png" width="460" alt="Meeting heads-up note: in 10 min, Team planning">

Your notes are never sent to Google.

### Focus rounds

Press **Focus** in the list. The cloud shows the countdown on its outline and asks what you're working on: type it, pick the meeting coming up or a recent answer, or skip. Link focus and break, and the break starts by itself. While it runs: **Pause**, **Stop**, and **Drifted** to take out minutes you drifted off (it confirms with "Noted").

<img src="docs/focus-round.png" width="451" alt="What's this round for? with one-click answers">

At the end, a card shows what you did. With app tracking on, it lists the apps you used, and you mark the ones that distracted you this round. **Take out** removes those minutes and shows your net focus. Then pick a break or another round.

<img src="docs/session-card.png" width="476" alt="Focus complete card with app buttons, Take out 2 min, Start break and Focus again">

### Check-ins

After a long stretch at the computer without a focus round (every 45 minutes by default), the cloud asks a short question: start a focus round, take a break, log a round you forgot to time, say another task came up, tell it you're on track, or ask later. With Calendar connected it can mention what's coming up. Number keys answer it.

<img src="docs/check-in.png" width="462" alt="Check-in: Office hours starts in 1h 24m. Want a focus round before then?">

It stays quiet during calls (mic or camera in use), full screen and presentations. Pause it for an hour, the rest of the day, or until you turn it back on.

### Water and eye breaks

While you use the laptop, a tiny character peeks out from behind the cloud: a look into the distance every 20 minutes, a sip of water every 40. Never in the first 3 minutes of a focus round. Settings can limit it to focus rounds only. It ducks back after a few seconds and clicks pass through it. Optional: a soft sound first, and a 20 second look-away countdown.

<img src="docs/peek.png" width="185" alt="A water peek: Sip of water?">

### Reminders

Add `20m`, `in 1 hour` or `at 3:30 pm` to any note, or press the bell. When it's due, a card grows out of the cloud with snooze buttons, **Open note** and **Done**. Reminders can repeat: every day, weekdays, every week, chosen days or every month. Several due at once share one card: a row per note, plus **Snooze all** and **Stop all**.

<img src="docs/reminder.png" width="569" alt="Reminder card: Buy coffee beans, with snooze, Open note and Done">

### Background noise and music

The **♫** button plays brown, pink or white noise made by the app (no sound files), at three volumes, or only during focus. Under **Music**, open the music folder, drop in your own songs (mp3, m4a, wav, flac, ogg and more), and pick one to play on repeat.

<img src="docs/sound.png" width="718" alt="Noise menu with the Music submenu open">

### Copy your patterns for AI

Every thought you park is logged on your PC: when it came, what the timer was doing, and what you did with it. The **✨** button copies the last 7 days, 30 days or everything as a ready-made prompt for any AI chat: the app first counts your rhythm (best hours and weekdays, streaks, late nights, rounds in a row, the minute thoughts start pulling, what you keep snoozing), and the prompt asks for patterns you probably haven't noticed, each in a small table, ending with a few small changes to try next week. Paste the answer back in to keep it.

<img src="docs/ai.png" width="642" alt="The AI menu: copy last 7 days, 30 days, everything, and saved analyses">

**Browse history** searches every thought you ever parked, by date, type and outcome.

<img src="docs/history.png" width="640" alt="The history window">

### Make it yours

System, Light or Dark theme (System follows Windows). The cloud starts white with the time left on its outline; pick its color, shape (thought cloud, circle, squircle and more) and size. Settings also covers hotkeys, gestures, flags, opacity, check-ins, sounds and privacy.

<img src="docs/settings-appearance.png" width="800" alt="Settings, Appearance page">

## Keys and clicks

| To | Do this |
|---|---|
| Park a thought | `Ctrl+Alt+P`, type, `Enter`. Or scribble the mouse up and down over the cloud. |
| See your list | Click the cloud, `Ctrl+Alt+L`, or scribble left and right over the cloud. |
| Deal with a thought | **Done**, **Later** or **Let go**. Undo with `Ctrl+Z`. |
| Start a focus round | **Focus** in the list. |
| Park a file, image or link | Drag it onto the cloud, or `Ctrl+V` a screenshot in the quick note. |
| Use a parked file | Drag it out of the note, or hover it and click copy. |
| Copy a note into a message | Hover it and click the copy icon, or select it and press `Ctrl+C`. |
| Get help | **?** in the list: how it works and the welcome tour. |
| Settings, timer, nap, quit | Right-click the cloud. |

Everything works from the keyboard.

## Privacy

- **Your notes stay on your PC**, in `%LOCALAPPDATA%\ParkThatThought\parking_lot_data`. No account, no server, no tracking.
- **Hidden from screen share and screenshots** by default (Zoom, Teams, Meet, OBS, Snipping Tool). You can turn this off.
- **App tracking during focus rounds** (on by default, turn it off in Settings > Focus & breaks) notes which app is in front so the end-of-round card can ask which ones distracted you. It never leaves your PC.
- **The internet is used only for:** downloading, updates (**Restart / update**, and the automatic check unless you turn it off), and, if you turn them on, Google Calendar and phone alerts through ntfy.sh (timer messages only, never your notes).
- **Copy for AI** only copies text to your clipboard. You decide where to paste it.

## Updating

It updates itself. Every few hours it checks GitHub, and when a new version is out it installs it while you're away from the keyboard and no focus round is running. Next time you look, the cloud says what changed. Turn it off in Settings > About > **Update automatically**.

To update right now: right-click the cloud > **Restart / update** (also on the meeting bar's right-click menu). If there's a newer version, it downloads it, installs it quietly and starts again, in about a minute. No blue box, nothing to click.

Downloading the installer again from this page and running it works too. Either way **your notes, settings and files stay**: they live in `%LOCALAPPDATA%\ParkThatThought\parking_lot_data`, which installing never touches. No setup again.

## Uninstall

Windows Settings > Apps > Installed apps > **Park That Thought** > Uninstall.

Your notes stay in `%LOCALAPPDATA%\ParkThatThought\parking_lot_data`, in case you come back. To remove them too, press `Win+R`, type `%LOCALAPPDATA%\ParkThatThought`, press Enter, and delete that folder (copy `parking_lot_data` somewhere first if you want to keep it).

## Questions

**Is it free?** Yes. MIT license. If it helps you, you can [buy me a coffee](https://buymeacoffee.com/gmiqbal).

**Mac or Linux?** Not supported yet. The core runs from source there, but screen-share hiding, focus handling and the quiet rules for check-ins are Windows only.

**Nothing appears after installing.** Open Park That Thought from the Start menu. If still nothing, look in `%LOCALAPPDATA%\ParkThatThought\parking_lot_data\error.log` and [open an issue](https://github.com/gmiqbal/ParkThatThought/issues) with what it says.

**My antivirus flagged it.** Some antivirus apps guess about new, unsigned programs. It's a false alarm; you can check the code yourself. Please [open an issue](https://github.com/gmiqbal/ParkThatThought/issues) with the antivirus name so I can report it to them.

**A hotkey doesn't work.** Another app may use it. Right-click the cloud > Settings > Controls, and pick another.

**Why the name?** "Park that thought" means "hold that thought, we'll come back to it". That's the whole app.

## Run from source

For developers, or Mac and Linux:

```
git clone https://github.com/gmiqbal/ParkThatThought
cd ParkThatThought
pip install -r requirements.txt
python parking_lot.py
```

In a git checkout, **Restart / update** only restarts. Use `git pull` to update. Notes are saved in `parking_lot_data/` next to the script.

The whole app is one file, `parking_lot.py`, with two libraries: PySide6 (Qt) and pynput (global hotkeys and mouse gestures).

## Support

I build Park That Thought in my spare time and keep it free. If it saves you some focus:

- [Buy me a coffee](https://buymeacoffee.com/gmiqbal).
- Star the repo so more people find it.
- [Report a bug or ask for a feature](https://github.com/gmiqbal/ParkThatThought/issues).

## License

MIT. Made by G M Iqbal Mahmud.

The Windows app includes Qt for Python and pynput (LGPL v3) and FFmpeg (LGPL 2.1 or later). Their notices and licenses are in the install folder: Settings > About > Open source parts > View.
