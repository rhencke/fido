# Collaboration substrate (post-volley era)
The repository is the single shared substrate. Claude (chat) pulls it; ChatGPT receives subtree ZIPs Rob
builds with tools/build_deterministic_bundle.py; Claude Code commits. Every artifact is dated, versioned,
hashed; reviews reference paths + SHA-256, open with the hash handshake (D-14), and mark findings NEW /
REOPENS(D-nn) against the Settled Decisions (FCB GOVERNANCE, D-01..D-21). Reviewer returns are content
documents; packaging is a build act via the shipped tools. Models record APPLIED at most; Rob's countersign
ends everything.
