#!/bin/bash
sed s/\,//g   -i $1
sed s/\"//g   -i $1
sed s/\;/\,/g -i $1
