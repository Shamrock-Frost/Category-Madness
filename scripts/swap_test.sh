#!/usr/bin/env bash
# D-TL-17, D-RT-28, AT-FD-2: build identical clients in an isolated stub checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_seal.py
