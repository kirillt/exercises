package structures.test;

import structures.ListIface;
import structures.SinglePtrList;
import structures.DoublePtrList;
import exceptions.NoSuchElement;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

public class ListsTest {

    public List<ListIface<Integer>> createTestLists() {
        List<ListIface<Integer>> testLists = new LinkedList();
        testLists.add(new SinglePtrList());
        testLists.add(new DoublePtrList());
        return testLists;
    }

    @Test
    public void test1() {
        for (ListIface<Integer> ts : createTestLists()) {
            try {
                ts.add(1).add(2).add(3).add(4).add(5).del(2).del(4).del(1).del(3).add(1);
                assertEquals("{5->{1->null}}", ts.toString());
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

    @Test
    public void test2() {
        for (ListIface<Integer> ts : createTestLists()) {
            assertEquals("{4->{3->{2->{1->null}}}}", ts.add(1).add(2).add(3).add(4).reverse().toString());
        }
    }
}
