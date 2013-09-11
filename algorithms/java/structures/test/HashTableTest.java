package structures.test;

import structures.HashTable;
import exceptions.NoSuchElement;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

public class HashTableTest {

    @Test
    public void test() {
        HashTable<String,Integer> ts = new HashTable(15);
        try {
            ts.add("ONE",1)
              .add("TWO AND FOUR",2)
              .add("THREE AND FIVE",3)
              .add("TWO AND FOUR",4)
              .add("THREE AND FIVE",5)
              .del("ONE")
              .del("TWO AND FOUR");
            assertEquals("[<THREE AND FIVE;3>, <THREE AND FIVE;5>]", ts.toString());
        } catch (NoSuchElement e) {
            fail("Deletion of unexistent element.");
        }
        boolean catched = false;
        try {
            ts.del("WRONG KEY");
        } catch (NoSuchElement e) {
            catched = true;
        }
        assertTrue(catched);
    }
}
