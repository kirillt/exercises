import jade.core.AID;
import jade.core.Agent;
import jade.core.behaviours.*;

import jade.lang.acl.ACLMessage;
import jade.lang.acl.UnreadableException;

import java.io.Serializable;
import java.io.IOException;

//System.out.println(getLocalName() + " is ok!");
//System.out.println("Topology of " + myAgent.getLocalName() + "\n" + unit);

public class AverageCalculator extends Agent {
    public double number = 0;
    protected void setup() {
        final Object[] args = getArguments();
        number = Double.parseDouble((String)args[0]);
        final TopologyUnit unit = new TopologyUnit(args, 1);
        addBehaviour(new SimpleBehaviour(this) {
            private boolean finished = false;
            public void action() {
                Sum sum = new Sum();
                int handled = 0;
                while (handled < unit.fromSize) {
                    ACLMessage msg = blockingReceive();
                    sum.inc(Sum.parseSum(msg.getContent()));
                    handled++;
                }
                sum.inc(number);
                ACLMessage msg = new ACLMessage(ACLMessage.PROPOSE);
                msg.setContent(sum.toString());
                for (AID to : unit.to) {
                    msg.addReceiver(to);
                }
                send(msg);
                System.out.println("Average of "
                    + getLocalName() + "'s predecessors and itself is "
                    + sum.average());
                number = sum.average();
                finished = true;
            }
            public boolean done() {
                return finished;
            }
        });
    }

    private static class Sum {
        public double sum = 0;
        public int count = 0;
        public Sum() {
        }
        public void inc(final double value) {
            sum += value;
            count += 1;
        }
        public void inc(final Sum value) {
            sum += value.sum;
            count += value.count;
        }
        public double average() {
            return sum / count;
        }

        @Override
        public String toString() {
            return String.valueOf(sum) + " " + String.valueOf(count);
        }
        public static Sum parseSum(final String input) {
            String[] parts = input.split("\\s+");
            if (parts.length != 2) {
                throw new IllegalStateException("Wrong serialization.");
            }
            Sum result = new Sum();
            result.sum = Double.parseDouble(parts[0]);
            result.count = Integer.parseInt(parts[1]);
            return result;
        }
    }
}
