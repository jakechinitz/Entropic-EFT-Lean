cd /home/claude/frz
export STEP=0.1 NT=40000
pair() { python3 make_frozen.py run $1 $2 frozen_vp$2_zre$1.npy > v$2_$1.log 2>&1 & python3 make_frozen.py run $3 $4 frozen_vp$4_zre$3.npy > v$4_$3.log 2>&1 & wait; }
pair 7.66 30 7.66 35
pair 7.00 35 7.66 25
pair 7.33 35 8.00 25
pair 8.40 25 8.80 25
