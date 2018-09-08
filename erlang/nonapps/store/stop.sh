#!/bin/bash
for pid in `./show.sh | awk '{print $2}'`;
   do kill -9 $pid;
done