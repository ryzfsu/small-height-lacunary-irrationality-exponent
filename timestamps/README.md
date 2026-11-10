# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
975079 (2026-11-08 16:45:57 UTC).

| file | SHA-256 |
|---|---|
| `small-height-lacunary-irrationality-exponent-v1.pdf` | `9ead9fd52ddb275de352e706991ff7240ed034b3beef763e1c4f8aed6dcb27cc` |
| `small-height-lacunary-irrationality-exponent-v1.tar.gz` | `5079d452273e5f6295d33d287d0f63ce529df89a4621bced5479fa2865f48329` |

Proofs for the assets of release `v2` (pending confirmation in the Bitcoin blockchain):

| file | SHA-256 |
|---|---|
| `small-height-lacunary-irrationality-exponent-v2.pdf` | `9ead9fd52ddb275de352e706991ff7240ed034b3beef763e1c4f8aed6dcb27cc` |
| `small-height-lacunary-irrationality-exponent-v2.tar.gz` | `aea231a73632aed22cbf02962b720645c7516f17ff30311505c5177e74ad88e4` |
| `small-height-lacunary-irrationality-exponent-v2-lean.tar.gz` | `e4c5da96ca789d2c969757953825b5e6b19d8948879f18cbcb542bf7c81ab96f` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
