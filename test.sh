#!/bin/bash
for i in {1..10}
do
	python3 generator.py $1 $2 $3 input3.txt > /dev/null && time python3 210050040_210050044_210050155_tile_looptile_loop.py input3.txt > output.txt && python3 verifier.py input3.txt output.txt | grep "CORRECT" && cat output.txt | grep -E "unsat|CORRECT"
done
