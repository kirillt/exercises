package algorithms;

import algorithms.DistancesSearchIface;
import algorithms.DistancesSearchIface.Distance;

import static algorithms.DistancesSearchIface.Distance.d;
import static algorithms.DistancesSearchIface.Distance.inf;

public class Dijkstra implements DistancesSearchIface {
    public void findAllDistances(final Distance[][] graph) {
        final int n = graph.length;
        for (int i = 0; i < n; i++) {
            findDistancesFrom(graph, i, n);
        }
    }
    public void findDistancesFrom(final Distance[][] graph, final int from, final int n) {
        final boolean[] visited = new boolean[n];
        for (int i = 0; i < n; i++) { visited[i] = false; }
        Queue<Integer> queue = new Queue(from);
        while (!queue.empty()) {
            final int curr = queue.del();
            for (int i = 0; i < n; i++) {
                if (!visited[i] && graph[curr][i].compareTo(inf) < 0) {
                    final Distance sum = graph[from][curr].plus(graph[curr][i]);
                    if (sum.compareTo(graph[from][i]) < 0) {
                        graph[from][i] = sum;
                    }
                    queue.add(i);
                }
            }
            visited[curr] = true;
        }
    }

    private static class Queue<T> {
        private static class Node<T> {
            public final T value;
            public Node<T> next = null;

            public Node(final T v) {
                value = v;
            }
        }
        private Node<T> first;
        private Node<T> last;

        public Queue(final T t) {
            init(t);
        }
        public void init(final T t) {
            first = new Node(t);
            last = first;
        }

        public void add(final T t) {
            if (first == null && last == null) {
                init(t);
            } else {
                last.next = new Node(t);
                last = last.next;
            }
        }
        public T    del() {
            final T value = first.value;
            if (first == last) {
                first = null;
                last  = null;
            } else {
                first = first.next;
            }
            return value;
        }
        public boolean empty() {
            return first == null;
        }
    }
}
