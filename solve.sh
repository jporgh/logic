#!/bin/sh
set -e

solve() {
	input="$1"
	echo "$input"
	if fgrep -qx '%model' "$input"
	then
		tptp_to_ladr < "$input" | mace4 -t30 >/dev/null
	else
  		tptp_to_ladr < "$input" | prover9 -t30 >/dev/null
	fi
}

for a in *.p
do
	solve "$a"
done