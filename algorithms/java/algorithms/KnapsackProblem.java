package algorithms;

import java.util.List;
import java.util.LinkedList;

public class KnapsackProblem {
    public static class Item {
        public final int value;
        public final int weight;
        public Item(int v, int w) {
            value  = v;
            weight = w;
        }
    }

    public KnapsackProblem(final Item[] is, final int l, final Type t) {
        items = is;
        limit = l;
        count = items.length;
    }

    public int solve() {
        w2v = new int[limit+1];
        search(limit);
        return w2v[limit];
    }

    private void search(final int l) {
        if (w2v[l] != 0) { return; }
        int max = 0;
        for (int i = 0; i < count; i++) {
            Item it = items[i];
            int w = it.weight;
            if (l >= w) {
                int t = l - w;
                search(t);
                int m = w2v[t] + it.value;
                if (m > max) {
                    max = m;
                }
            }
        }
        w2v[l] = max;
    }

    public List<Integer> backtrack() {
        return null; //TODO
    }

    private int[] w2v;

    private final Item[] items;
    private final int    count;
    private final int    limit;
}
