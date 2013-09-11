package algorithms;

import algorithms.DistancesSearchIface;
import algorithms.DistancesSearchIface.Distance;

import static algorithms.DistancesSearchIface.Distance.d;
import static algorithms.DistancesSearchIface.Distance.inf;

public class FloydWarshall implements DistancesSearchIface {
    public void findAllDistances(final Distance[][] graph) {
        final int n = graph.length;
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    final Distance ij  = graph[i][j];
                    final Distance ik  = graph[i][k];
                    final Distance kj  = graph[k][j];
                    final Distance sum = ik.plus(kj);
                    if (sum.compareTo(ij) < 0) {
                        graph[i][j] = sum;
                    }
                }
            }
        }
    }
}
