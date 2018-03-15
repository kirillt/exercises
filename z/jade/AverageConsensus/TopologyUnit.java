import jade.core.AID;

import java.util.Set;
import java.util.HashSet;

public class TopologyUnit {
    public final Iterable<AID> from;
    public final Iterable<AID> to;

    public final int fromSize;
    public final int toSize;

    public TopologyUnit(final Set<AID> from, final Set<AID> to) {
        fromSize = from.size();
        toSize = to.size();
        this.from = from;
        this.to = to;
    }

    public TopologyUnit(final Object[] args, final int start) {
        final Set<AID> from = new HashSet<AID>();
        final Set<AID> to = new HashSet<AID>();
        for (int i = start; i < args.length; i++) {
            final String arg  = (String)args[i];
            final String mark = arg.substring(0,2);
            final String name = arg.substring(2);
            final AID aid = new AID(name, false);
            if ("<-".equals(mark)) {
               from.add(aid);
            } else
            if ("->".equals(mark)) {
               to.add(aid);
            } else {
                badInput(args[i]);
            }
        }
        fromSize = from.size();
        toSize = to.size();
        this.from = from;
        this.to = to;
    }

    private void badInput(final Object arg) {
        throw new IllegalStateException("Don't understand \""
            + arg + "\"");
    }

    @Override
    public String toString() {
        String output = "";
        output += toString("from", from);
        output += toString("to", to);
        return output;
    }

    private String toString(final String label, final Iterable<AID> list) {
        String output = "\t" + label + "\n";
        for (final AID aid : list) {
            output += "\t\t" + aid.toString() + "\n";
        }
        return output;
    }
}
