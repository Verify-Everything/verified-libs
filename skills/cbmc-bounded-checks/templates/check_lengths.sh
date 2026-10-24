#!/usr/bin/env bash
# Run a harness for every length 0..MAX, 4 at a time. Prints one line per length.
#   bash check_lengths.sh <upstream.c> <harness.c> <max>
set -u
SRC=$1; H=$2; MAX=$3; HERE=$(cd "$(dirname "$0")" && pwd)
seq 0 "$MAX" | xargs -P 4 -I{} sh -c \
  'bash "'"$HERE"'/run_cbmc.sh" "'"$SRC"'" "'"$H"'" {} >/dev/null 2>&1; rc=$?; case $rc in 0) echo "ok   len={}";; 10) echo "FAIL len={}";; *) echo "ERR  len={} (exit $rc)";; esac' | sort -t= -k2 -n
