cd /home/claude/de2
python3 grid_mass.py 7.66 25 b25.json 7.6 8.61 > b25.log 2>&1 &
python3 grid_mass.py 7.66 35 b35.json 7.6 8.61 > b35.log 2>&1 &
python3 grid_mass.py 8.4 30 b84.json 6.8 8.61 > b84.log 2>&1 &
wait
