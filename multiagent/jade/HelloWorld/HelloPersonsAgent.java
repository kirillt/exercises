import jade.core.Agent;
import jade.core.behaviours.*;

public class HelloPersonsAgent extends Agent {
    protected void setup() {
        Object[] args = getArguments();
        String mutableName = "";
        if (args != null) {
            for (int i = 0; i < args.length - 1; i++) {
                mutableName += (String)args[i] + ", ";
            }
            mutableName += (String)args[args.length - 1] + "!";
        } else {
            mutableName = "all!";
        }

        final String name = mutableName;
        addBehaviour(new SimpleBehaviour(this) {
            public void action() {
                System.out.println("Hello " + name);
                finished = true;
            }
            private boolean finished = false;
            public boolean done() {
                return finished;
            }
        });
    }
}

