#!/bin/bash
cp $1 $1.res
sed s/\,//g   -i $1
sed s/\"//g   -i $1
sed s/\;/\,/g -i $1
