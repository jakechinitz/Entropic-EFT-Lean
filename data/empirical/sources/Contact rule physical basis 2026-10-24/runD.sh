#!/bin/bash
cd /tmp/claude-0/c25
q1=("MW 1 15000 4000 12 175 1 D" "MW 1 15000 4000 12 175 2 D" "massive_spiral 3 25700 4000 12 175 1 D")
q2=("dwarf 3 1000 4000 12 175 1 D" "dwarf 3 1000 4000 12 175 2 D")
( for j in "${q1[@]}"; do timeout 3000 python3 descent3.py $j > "log3D_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
( for j in "${q2[@]}"; do timeout 3000 python3 descent3.py $j > "log3D_$(echo $j|tr ' ' _).txt" 2>&1; done ) &
wait
echo ALLDONE
