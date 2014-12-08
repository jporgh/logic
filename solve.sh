#!/bin/sh
set -e

TIMEOUT=30

solve() {
	input="$1"
	tmp="$(basename "$1" .p).tmp"
	output="$(basename "$1" .p).out"
	[ -f "$output" ] && return 0
	echo "$input"
	if fgrep -qx '%model' "$input"
	then
		tptp_to_ladr < "$input" | mace4 -t$TIMEOUT >"$tmp"
	else
  		tptp_to_ladr < "$input" | prover9 -t$TIMEOUT >"$tmp"
	fi
	mv "$tmp" "$output"
}

for a in *.p
do
	solve "$a"
done