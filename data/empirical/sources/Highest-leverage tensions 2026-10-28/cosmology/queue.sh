#!/bin/bash
# usage: queue.sh listfile ; each line = args to harness.py ; 2 workers
cd /home/claude/cos
export OMP_NUM_THREADS=1
cat "$1" | xargs -P 2 -L 1 bash -c 'python3 harness.py "$@" > "run/log_$(echo "$@" | tr " =" "_-").txt" 2>&1' _
echo QUEUE_DONE
