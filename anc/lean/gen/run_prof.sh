#!/bin/bash
# Profile of the order-8 join (see gen/Prof8.lean). Run in formal/proof. About 1.2 hours with 144
# processes, 70 process-hours. Writes data/k8_profile.txt.
set -e
mkdir -p scratch/prof
for lo in $(seq 0 9 1289); do
  hi=$((lo + 9)); [ $hi -gt 1290 ] && hi=1290
  sed "s/#eval part LO HI/#eval part $lo $hi/" gen/Prof8.lean > scratch/prof/P$lo.lean
done
ls scratch/prof/P*.lean | xargs -P 150 -I{} sh -c 'lake env lean {} > {}.log 2>&1'
for lo in $(seq 0 9 1289); do cat scratch/prof/p$lo.txt; done > data/k8_profile.txt
wc -l data/k8_profile.txt     # 136800 lines
