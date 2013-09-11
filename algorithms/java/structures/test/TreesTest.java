package structures.test;

import structures.TreeIface;
import structures.BinaryTree;
import exceptions.NoSuchElement;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

public class TreesTest {

    public List<TreeIface<Integer>> createTestTrees() {
        List<TreeIface<Integer>> testTrees = new LinkedList();
        testTrees.add(new BinaryTree(0));
        return testTrees;
    }

    @Test
    public void test() {
        for (TreeIface<Integer> ts : createTestTrees()) {
            try {
                ts.add(1).add(2).add(3).add(4).add(5).del(2).del(4).del(1).del(3).add(1);
                assertEquals("{null|0|{{null|1|null}|5|null}}", ts.toString());
            } catch (NoSuchElement e) {
                fail("Deletion of unexistent element.");
            }
            boolean catched = false;
            try {
                ts.del(2);
            } catch (NoSuchElement e) {
                catched = true;
            }
            assertTrue(catched);
        }
    }
}
