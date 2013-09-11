package algorithms.test;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

import algorithms.KnapsackProblem;

public class KnapsackProblemTest {

    private KnapsackProblem.Item item(int v, int w) {
        return new KnapsackProblem.Item(v, w);
    }

    @Test
    public void test() {
        KnapsackProblem.Item[] items1 = {item( 74,51), item(50,25), item(25,50), item(1,100)};
        KnapsackProblem.Item[] items2 = {item(200,51), item(50,25), item(25,50), item(1,100)};
        KnapsackProblem.Item[] items3 = {item(1,1)};
        KnapsackProblem.Item[] items4 = {};

        assertEquals(150, new KnapsackProblem(items1, 75).solve());
        assertEquals(200, new KnapsackProblem(items2, 75).solve());
        assertEquals( 75, new KnapsackProblem(items3, 75).solve());
        assertEquals(  0, new KnapsackProblem(items4, 75).solve());
    }
}
