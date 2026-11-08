# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
975079 (2026-11-08 17:25:57 UTC).

| file | SHA-256 |
|---|---|
| `small-height-lacunary-irrationality-exponent-v1.pdf` | `9ead9fd52ddb275de352e706991ff7240ed034b3beef763e1c4f8aed6dcb27cc` |
| `small-height-lacunary-irrationality-exponent-v1.tar.gz` | `5079d452273e5f6295d33d287d0f63ce529df89a4621bced5479fa2865f48329` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
