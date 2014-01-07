#!/bin/bash
java \
  -cp .:/usr/share/jade/lib/jade.jar:/usr/share/jade/lib/iiop.jar:/usr/share/jade/lib/http.jar:/usr/share/jade/lib/jadeTools.jar:/usr/share/jade/lib/Base64.jar \
jade.Boot \
q:AverageCalculator\(5.123 "<-z" "->w"\) w:AverageCalculator\(9.96 "<-q" "<-x" "->y" "->z"\) x:AverageCalculator\(6.78 "<-y" "<-z" "->w"\) y:AverageCalculator\(8.2 "<-w" "->x"\) z:AverageCalculator\(0.5 "<-w" "->q" "->x"\) manager:AverageCalculator\("manager" 1000 0.08 "q" "w" "x" "y" "z"\)
#x:AverageCalculator\(5.123 "<-z" "->y"\) y:AverageCalculator\(6.96 "<-x" "->z"\) z:AverageCalculator\(8.2 "<-y" "->x"\) manager:AverageCalculator\("manager" 10000 0.001 "x" "y" "z"\)
