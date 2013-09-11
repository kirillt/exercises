package algorithms;

import algorithms.ComparisonSortIface;

import java.util.Arrays;

import java.lang.StringBuilder;

public class HeapSort<T extends Comparable> implements ComparisonSortIface<T> {
    public  void sort(T[] array) {
        final int size = array.length;
        if (size < 2) {
            return;
        }
        build(array, size);
        sort(array, size);

    }
    private void fixheap(T[] array, final int i, final int n) {
        int p = i;                 // p stands for "parent"
        while (p <= n/2) {
            int g  = 2*p;          // g stands for "greater"
            T   gv = array[g];
            if (g < n) {
                int l  = g + 1;    // l stands for "lower"
                T   lv = array[l];
                if (lv.compareTo(gv) > 0) {
                    int t; T tv;
                    t  = l ; l  = g ; g  = t ;
                    tv = lv; lv = gv; gv = tv;
                }
            }
            final T pv = array[p];
            if (gv.compareTo(pv) > 0) {
                array[p] = gv;
                array[g] = pv;
                p = g;
            } else {
                break;
            }
        }
    }
    private void build(T[] array, final int size) {
        final int n = size-1;
        for (int i = size/2; i > -1; i--) {
            fixheap(array, i, n);
        }
    }
    private void sort(T[] array, final int size) {
        if (size < 2) {
            return;
        }
        final int n = size-1;
        T t = array[n];
        array[n] = array[0];
        array[0] = t;
        fixheap(array, 0, n-1);
        sort(array, size-1);
    }
}
