#!/bin/bash

function launch() {
    jade=/usr/share/jade/lib/jade.jar
    iiop=/usr/share/jade/lib/iiop.jar
    http=/usr/share/jade/lib/http.jar
    tool=/usr/share/jade/lib/jadeTools.jar
    base=/usr/share/jade/lib/Base64.jar
    jars=$jade:$iiop:$http:$tool:$base
    java -cp .:$jars jade.Boot $@
}

function tasks() {
    link_cost=100
    message_cost=0.1

    function average() {
        function args() {
            state="start"
            for x in $@
            do
                #echo "[$x] $state"
                if [ $x = "!" ]
                then
                    echo -n ") "
                    state="start"
                elif [ $state = "start" ]
                then
                    echo -n $x":AverageCalculator("
                    state="number"
                elif [ $state = "number" ]
                then
                    echo -n $x
                    state="topology"
                elif [ $state = "topology" ]
                then
                    echo -n " \"$x\""
                fi
            done
        }

        function summary() {
            cat .log | sed -n -e '/after/,$p' | sed s/.*\\r//g | grep -v "\=" > .temp
            rm .log

            iterations=`cat .temp | head -1 | awk '{print $3}'`
            proportion=`cat .temp | head -1 | awk '{print $7}' | sed s/\://g`
            agents=`cat .temp | head -2 | tail -1 | awk '{print $3}'`
            links=`cat .temp | head -3 | tail -1 | awk '{print $3}'`
            messages=`cat .temp | head -4 | tail -1 | awk '{print $3}'`
            rm .temp

            cost=`echo "$link_cost * $links + $message_cost * $messages" | bc`
            echo "Input: $iterations iterations; proportion $proportion; $agents agents; $links links. Sended $messages messages. Cost of topology: $cost"
        }
        
        launch $(args $@) &> .log
        summary
    }

    limit=10
    proportion=0.5

    echo "Cost of link: $link_cost; cost of message: $message_cost."

    average \
        x 5.123 "<-z" "->y" ! \
        y 6.96  "<-x" "->z" ! \
        z 8.2   "<-y" "->x" ! \
        manager "manager" $limit $proportion "x" "y" "z" !

    average \
        q 5.123 "<-z"       "->w"       ! \
        w 9.96  "<-q" "<-x" "->y" "->z" ! \
        x 6.78  "<-y" "<-z" "->w"       ! \
        y 8.2   "<-w"       "->x"       ! \
        z 0.5   "<-w"       "->q" "->x" ! \
        manager "manager" $limit $proportion "q" "w" "x" "y" "z" !
    echo "Done."
}

tasks &> tasks.log & tail -f tasks.log
