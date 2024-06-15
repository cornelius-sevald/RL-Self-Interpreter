#!/bin/bash

specfile=$(mktemp)
progfile=$(mktemp)

printf "input vars:  "
read -r input_vars
input_vars=($input_vars)
printf "input vals:  "
read -r input_vals
input_vals=($input_vals)
printf "output vars: "
read -r output_vars
output_vars=($output_vars)
printf "temp vars:   "
read -r temp_vars
temp_vars=($temp_vars)

if [[ ${#input_vars[@]} -ne ${#input_vals[@]} ]]
then
  echo "# of variable names must match values" > /dev/stderr
  exit 1
fi

for i in $(seq 0 $((${#input_vars[@]} - 1)))
do
  printf "%s = '%s\n" "${input_vars[$i]}" "${input_vals[$i]}" >> "$specfile"
done

printf "(${input_vars[*]}) -> (${output_vars[*]}) with (${temp_vars[*]})\n" >> "$progfile"
cat /dev/stdin >> "$progfile"

PERevFlow-exe interpret -v "$progfile" "$specfile"
