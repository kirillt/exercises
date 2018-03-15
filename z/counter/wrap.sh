#!/bin/bash

LINE="lw 4 pt 6"

if [[ $@ == *plot* ]]
then
  $@ > raw.gp
  #N=`tail -1 raw.gp | awk '{print $4}'`
  #N=`expr $N + 5`
  N=4
  sed -i '1s/^/set terminal png medium size 1366,768;\n/' raw.gp
  sed -i 's/lc\ rgb/####/g' raw.gp
  
  sed -i 's/@all\"\ ####/@all\" lw 20 pt 20 lc rgb/' raw.gp
  sed -i 's/@positive\"\ ####/@positive\" lw 8 pt 8 lc rgb/' raw.gp
  sed -i 's/@negative\"\ ####/@negative\" lw 8 pt 8 lc rgb/' raw.gp

  while [[ `cat raw.gp` == *####* ]] 
  do
    #K=`expr $N / 3`
    K=$N
    sed -i "s/####/lw $K pt $K lc rgb/" raw.gp
    #N=`expr $N - 1`
  done
  sed -i '$ d' raw.gp
  gnuplot raw.gp &> /dev/null
  rm raw.gp
  rm *.dat
else
  $@
fi

