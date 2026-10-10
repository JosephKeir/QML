#!/bin/bash
# Cloud sessions only (Claude Code on the web): give the fresh clone the Lean packages, with
# Mathlib's prebuilt cache, from the warm copy the environment's setup script made in
# /opt/qml-warm.  Locally this exits at once.
[ "$CLAUDE_CODE_REMOTE" = "true" ] || exit 0
export ELAN_HOME="${ELAN_HOME:-/opt/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$CLAUDE_PROJECT_DIR" || exit 0
if [ ! -d .lake/packages/mathlib ] && [ -d /opt/qml-warm/.lake/packages ]; then
  mkdir -p .lake && cp -a /opt/qml-warm/.lake/packages .lake/
fi
# Unpacks Mathlib's oleans if anything is missing; quick when they are already there.
lake exe cache get > /tmp/lake-cache-get.log 2>&1 || echo "lake exe cache get failed; see /tmp/lake-cache-get.log"
exit 0
