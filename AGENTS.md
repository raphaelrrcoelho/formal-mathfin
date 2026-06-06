# AGENTS.md

This file provides guidance to Codex when working with code in this
repository. **`CLAUDE.md` is the single authoritative reference** — read it
first; everything there (commands, architecture, daemon workflow, ledger,
benchmark shape) applies verbatim to Codex sessions. This file deliberately
duplicates nothing: a full mirror lived here until 2026-06-06 and had rotted
into actively-dangerous advice (it opened with a local `docker compose build`,
banned below).

Safety-critical doctrine (summarized from CLAUDE.md "Memory doctrine" — the
two rules whose violation can freeze the host):

1. **One Lean-loaded process locally, ever.** Daemon up ⇒ no `verify` runs,
   no `leanchecker`, no lake builds. Take the slot only with the daemon down.
2. **Never build Docker images locally.** CI `publish-image.yml` builds on
   push to main; locally only `docker compose pull verify`. Local
   `docker compose build` escapes the compose memory caps and redoes the
   full Mathlib layer.

Automation (grind / hammer / loogle) is a scout, not an author — see
CLAUDE.md "Automation toolkit — and its values gate" before committing any
machine-found proof.

## Codex-specific notes

- Codex's user is the same as Claude's user — see `MEMORY.md`-class
  feedback persisted across sessions for both agents.
- The `.codex/` directory holds Codex-local state and is gitignored.
