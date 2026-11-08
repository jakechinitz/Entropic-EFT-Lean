#!/bin/bash
cd /tmp/claude-0/c25
q1=("MW 0 0 4000 12 0 1" "MW 1 15000 4000 12 0 1" "MW 3 15000 4000 12 0 1" "MW 10 15000 4000 12 0 1")
q2=("dwarf 0 0 4000 12 0 1" "dwarf 3 1000 4000 12 0 1" "dwarf 10 1000 4000 12 0 1" "massive_spiral 3 25700 4000 12 0 1")
( for j in "${q1[@]}"; do timeout 3000 python3 descent3.py $j > "log3_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
( for j in "${q2[@]}"; do timeout 3000 python3 descent3.py $j > "log3_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
wait
echo ALLDONE
