package algorithms.test;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

import algorithms.DistancesSearchIface;
import algorithms.DistancesSearchIface.Distance;

import algorithms.Dijkstra;
import algorithms.FloydWarshall;

import static algorithms.DistancesSearchIface.Distance.d;
import static algorithms.DistancesSearchIface.Distance.inf;

import java.lang.StringBuilder;

public class DistancesSearchTest {
    private List<DistancesSearchIface> getAllAlgorithms() {
        List<DistancesSearchIface> algorithms = new LinkedList<DistancesSearchIface>();
        algorithms.add(new FloydWarshall());
        algorithms.add(new Dijkstra());
        return algorithms;
    }

    private void print(final Distance[][] graph) {
        final int n = graph.length;
        for (int i = 0; i < n; i++) {
            final StringBuilder line = new StringBuilder("");
            for (int j = 0; j < n; j++) {
                line.append(graph[i][j] + " ");
            }
            System.out.println(line);
        }
    }

    @Test
    public void test() {
        for (DistancesSearchIface algorithm : getAllAlgorithms()) {
            Distance[][] graph = {
                {d(0), inf,d(2), inf},
                {d(1),d(0),d(4), inf},
                { inf,d(3),d(0),d(5)},
                { inf,d(7), inf,d(0)}
            };
            Distance[][] result = {
                {d(0),d(5),d(2) ,d(7)},
                {d(1),d(0),d(3) ,d(8)},
                {d(4),d(3),d(0) ,d(5)},
                {d(8),d(7),d(10),d(0)}
            };
            algorithm.findAllDistances(graph);
            for (int i = 0; i < 4; i++) {
                for (int j = 0; j < 4; j++) {
                    assertEquals(0, graph[i][j].compareTo(result[i][j]));
                }
            }
        }
    }
}
