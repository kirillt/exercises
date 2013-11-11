import jade.core.Agent;
import jade.core.behaviours.*;

public class GoodHelloWorldAgent extends Agent {
    protected void setup() {
        addBehaviour(new SimpleBehaviour(this) {
            public void action() {
                System.out.println("Hello from " + myAgent.getLocalName());
                finished = true;
            }
            private boolean finished = false;
            public boolean done() {
                return finished;
            }
        });
    }
}

