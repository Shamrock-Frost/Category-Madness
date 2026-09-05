#!/usr/bin/env bash
# Fresh builds, safe with local edits. Cites: D-CH-25, D-RT-28, D-TL-17, AT-FD-2.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_seal.py
