#!/bin/bash

prog=./progs/fib_pair.rl
sint=./sint_opt.rl

int_benchmark=./benchmarks/int_benchmark.csv
sint_benchmark=./benchmarks/sint_benchmark.csv

echo "Benchmarking haskell interpreter"
for n in {0,1,2,3,4,5,6,7,8,9,10,20,40,80,160,320}
do
  printf "$n "
  PERevFlow-exe interpret "$prog" <(echo "n = '$n") | tail -n1
done | cut -d ' ' -f 1,4,7,10 | sed 's/,//g' | sed 's/ /\t/g' | tee "$int_benchmark"

echo "Benchmarking self-interpreter"
for n in {0,1,2,3,4,5,6,7,8,9,10,20,40,80,160,320}
do
  printf "$n "
  PERevFlow-exe interpret "$sint" <(sed "s/(n.10)/(n.$n)/" ./prep_progs/fib_pair.spec) | tail -n1
done | cut -d ' ' -f 1,4,7,10 | sed 's/,//g' | sed 's/ /\t/g' | tee "$sint_benchmark"
