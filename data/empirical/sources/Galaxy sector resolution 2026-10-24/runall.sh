#!/bin/bash
cd /tmp/claude-0/c25
q1=("MW 0 0 4000 12 0 1" "MW 1 15000 4000 12 175 1" "MW 3 15000 4000 12 175 1" "MW 10 15000 4000 12 175 1" "MW 10 15000 4000 12 175 2" "MW 10 15000 4000 12 175 3" "massive_spiral 10 25700 4000 12 175 1" "group_small 10 25700 4000 12 175 1")
q2=("dwarf 0 0 4000 12 0 1" "dwarf 10 1000 4000 12 175 1" "dwarf 10 1000 4000 12 175 2" "dwarf 10 1000 4000 12 175 3" "MW 10 15000 8000 12 175 1" "massive_spiral_heavy 10 25700 4000 12 175 1" "cluster 10 500000 4000 12 175 1")
( for j in "${q1[@]}"; do timeout 3000 python3 descent2.py $j > "log2_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
( for j in "${q2[@]}"; do timeout 3000 python3 descent2.py $j > "log2_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
wait
echo ALLDONE
