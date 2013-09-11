package algorithms;

import java.lang.Comparable;

public interface ComparisonSortIface<T extends Comparable> {
    void sort(T[] array);
}
