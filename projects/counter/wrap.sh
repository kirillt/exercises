#!/bin/bash

LINE="lw 4 pt 6"

if [[ $@ == *plot* ]]
then
  $@ > raw.gp
  sed -i '1s/^/set terminal png medium size 1366,768;\n/' raw.gp
  sed -i 's/lc\ rgb/lw 4 pt 6 lc rgb/g' raw.gp
  sed -i '$ d' raw.gp
  gnuplot raw.gp &> /dev/null
  rm raw.gp
  rm *.dat
else
  $@
fi

