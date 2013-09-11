package algorithms.test;

import org.junit.Test;
import static org.junit.Assert.*;

import java.util.*;

import algorithms.HeapSort;
import algorithms.QuickSort;
import algorithms.MergeSort;
import algorithms.ComparisonSortIface;

public class ComparisonSortsTest {

    private List<ComparisonSortIface<Integer>> getAllSorts() {
        List<ComparisonSortIface<Integer>> sorts = new LinkedList<ComparisonSortIface<Integer>>();
        sorts.add(new MergeSort());
        sorts.add(new QuickSort());
        sorts.add(new HeapSort());
        return sorts;
    }

    @Test
    public void test() {
        for (ComparisonSortIface<Integer> sort : getAllSorts()) {
            Integer[] array1 = {5,3,8,1,10,2,9,9,0};
            Integer[] array2 = {10,9,8,1,2,3,7,6,5,4};
            Integer[] array3 = {4};
            Integer[] array4 = {};
            sort.sort(array1);
            sort.sort(array2);
            sort.sort(array3);
            sort.sort(array4);
            assertEquals("[0, 1, 2, 3, 5, 8, 9, 9, 10]"   , Arrays.toString(array1));
            assertEquals("[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]", Arrays.toString(array2));
            assertEquals("[4]"                            , Arrays.toString(array3));
            assertEquals("[]"                             , Arrays.toString(array4));
        }
    }
}
