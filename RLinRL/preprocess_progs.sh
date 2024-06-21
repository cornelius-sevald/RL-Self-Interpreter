#!/bin/bash

for f in progs/*.rl
do
  PERevFlow-exe preprocess -v "$f" "progs/$(basename "$f" ".rl").spec" "prep_progs/$(basename "$f" ".rl").spec"
done
