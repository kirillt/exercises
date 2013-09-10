package structures.test;

import structures.SinglePtrList;
import exceptions.NoSuchElement;

import org.junit.Test;

public class SinglePtrListTest {
    @Test
    public void testOne() {
        SinglePtrList<Integer> ts = new SinglePtrList<Integer>();
        try {
            ts.add(1).add(2).add(3).add(4).del(2).del(4).del(1).del(3);
            System.out.println("ok");
        } catch (NoSuchElement e) {
            System.out.println("bad");
        }
        try {
            ts.del(2);
        } catch (NoSuchElement e) {
            System.out.println("ok");
        }
    }
}
