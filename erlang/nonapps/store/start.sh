#!/bin/bash

erl -sname master -s server master -detached
for i in `seq 1 $1`;
   do erl -sname slave$i -s server slave -detached;
done