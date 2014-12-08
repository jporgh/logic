#!/bin/sh
set -e

TIMEOUT=30

solve() {
	input="$1"
	tmp="$(basename "$1" .p).tmp"
	output="results/$(basename "$1" .p).out"
	[ ! -f "$output" -o "$input" -nt "$output" ] || return 0
	echo "$input"
	rm -f "$output"
	if fgrep -qx '%model' "$input"
	then
		tptp_to_ladr < "$input" | mace4 -t$TIMEOUT >"$tmp"
	else
  		tptp_to_ladr < "$input" | prover9 -t$TIMEOUT >"$tmp"
	fi
	mv "$tmp" "$output"
}

mkdir -p results
for a in *.p
do
	solve "$a"
done