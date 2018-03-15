#!/bin/bash
function work() {
    ls *.class | xargs rm
    ls *.txt   | xargs rm
}

work &> /dev/null
