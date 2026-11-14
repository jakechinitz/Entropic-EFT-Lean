#!/bin/bash
cd /tmp/claude-0/c25
q1=("MW 1 15000 4000 12 175 2" "MW 1 15000 4000 12 175 3" "massive_spiral_heavy 3 25700 4000 12 175 1" "group_small 3 25700 4000 12 175 1")
q2=("MW 1 15000 8000 12 175 1" "dwarf 3 1000 4000 12 175 2" "dwarf 3 1000 4000 12 175 3")
( for j in "${q1[@]}"; do timeout 3000 python3 descent3.py $j > "log3_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
( for j in "${q2[@]}"; do timeout 3000 python3 descent3.py $j > "log3_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
wait
echo ALLDONE
