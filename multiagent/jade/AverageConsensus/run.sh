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
            error=`cat .log | grep "[eE]xception" | tr '\n' ' '`
            if [ -z "$error" ]
            then
                cat .log | sed -n -e '/after/,$p' | sed s/.*\\r//g | grep -v "\=" > .temp
                #rm .log

                iterations=`cat .temp | head -1 | awk '{print $3}'`
                proportion=`cat .temp | head -1 | awk '{print $7}' | sed s/\://g`
                agents=`cat .temp | head -2 | tail -1 | awk '{print $3}'`
                links=`cat .temp | head -3 | tail -1 | awk '{print $3}'`
                messages=`cat .temp | head -4 | tail -1 | awk '{print $3}'`
                rm .temp

                cost=`echo "$link_cost * $links + $message_cost * $messages" | bc`
                echo -n "Input: $iterations iterations; proportion $proportion; "
                echo -n "$agents agents; $links links. "
                echo    "Sended $messages messages. Cost of topology: $cost"
            else
                echo "Failed."
                cat  .log  >> .failed
                echo "***" >> .failed
            fi
        }
        
        launch $(args $@) &> .log
        summary
    }

    limit=1000
    proportion=0.5

    function manager() {
        echo -n "manager \"manager\" $limit $proportion"
        for i in `seq 1 $1`
        do
            echo -n " agent$i"
        done
        echo -n " !"
    }

    function cycle()  {
        k=$1 # max number
        p=$k # previous number
        for i in $(seq 1 $(expr $k - 1))
        do
            n=$(expr $i + 1) # next number
            echo -n "agent$i $RANDOM \"<-agent$p\" \"->agent$n\" ! "
            p=$i
        done
        echo -n "agent$k $RANDOM \"<-agent$p\" \"->agent1\" ! "
        manager $n
    }

    function full() {
        n=$1
    }

    rm .failed &> /dev/null

    echo "Cost of link: $link_cost; cost of message: $message_cost."

    for i in `seq 1 100`
    do
        echo -n "Topology: cycle of $i vertices. "
        average `cycle $i`
    done

    #average \
        #x 5.123 "<-z" "->y" ! \
        #y 6.96  "<-x" "->z" ! \
        #z 8.2   "<-y" "->x" ! \
        #manager "manager" $limit $proportion "x" "y" "z" !

    #average \
        #q 5.123 "<-z"       "->w"       ! \
        #w 9.96  "<-q" "<-x" "->y" "->z" ! \
        #x 6.78  "<-y" "<-z" "->w"       ! \
        #y 8.2   "<-w"       "->x"       ! \
        #z 0.5   "<-w"       "->q" "->x" ! \
        #manager "manager" $limit $proportion "q" "w" "x" "y" "z" !
    echo "Done."
}

> tasks.log
tasks &> tasks.log & tail -f tasks.log
