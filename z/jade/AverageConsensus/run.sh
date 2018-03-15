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
                rm .log

                agents=`cat .temp | head -2 | tail -1 | awk '{print $3}'`
                links=`cat .temp | head -3 | tail -1 | awk '{print $3}'`
                messages=`cat .temp | head -4 | tail -1 | awk '{print $3}'`
                rm .temp

                cost=`echo "$link_cost * $links + $message_cost * $messages" | bc`
                echo -n "Input: $agents agents; $links links. "
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

    limit=10
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
        for i in $(seq 1 $k)
        do
            n=$(expr $i + 1) # next number
            if [ $n -gt $k ]
            then
                n=$(expr $n - $k)
            fi

            echo -n "agent$i $RANDOM "
            echo -n "\"<-agent$p\" "
            echo -n "\"->agent$n\" "
            echo -n "! "

            p=$i
        done
        manager $k
    }

    function cycle2() { # 2-transitive closure of cycle
        k=$1 # max number
        p=$k # previous number
        pp=$(expr $k - 1) # previous-previous number (2-transitive)
        for i in $(seq 1 $(expr $k - 1))
        do
            n=$(expr $i + 1) # next number
            nn=$(expr $i + 2) # next-next number (2-transitive)
            if [ $n -gt $k ]
            then
                n=$(expr $n - $k)
            fi
            if [ $nn -gt $k ]
            then
                nn=$(expr $nn - $k)
            fi

            echo -n "agent$i $RANDOM "
            echo -n "\"<-agent$p\" "
            echo -n "\"<-agent$pp\" "
            echo -n "\"->agent$n\" "
            echo -n "\"->agent$nn\" "
            echo -n "! "

            pp=$p
            p=$i
        done
        echo -n "agent$k $RANDOM \"<-agent$p\" \"->agent1\" ! "
        manager $k
    }

    rm .failed &> /dev/null

    echo "Cost of link: $link_cost; cost of message: $message_cost."
    echo "Iterations limit: $limit; proportion: $proportion."

    echo -e "***\nSection I. Cycle topologies.\n***"
    for i in `seq 1 50`
    do
        average `cycle $i`
    done

    echo -e "***\nSection II. 2-transitive closures of cycle topologies.\n***"
    for i in `seq 5 50`
    do
        echo -n "Topology: 2-transitive closure of cycle of $i vertices. "
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
    #echo "Done."
}

> tasks.log
tasks &> tasks.log & tail -f tasks.log
