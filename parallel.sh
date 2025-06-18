#!/bin/sh

LIB_FILES="$(find src/ -name '*.idr' | grep -v Runner)"
for r in $(echo "$LIB_FILES" | grep -v Derive); do idris2 --find-ipkg --check "$r"; done
for r in $(echo "$LIB_FILES" | grep Derive); do idris2 --find-ipkg --check "$r" & done
wait

