package algorithms;

import algorithms.ComparisonSortIface;

import java.util.Arrays;

import java.lang.StringBuilder;

public class QuickSort<T extends Comparable> implements ComparisonSortIface<T> {
    public  void sort(T[] array) {
        sort(array, 0, array.length-1);
    }
    private void swap(T[] array, final int left, final int right) {
        T t = array[left];
        array[left]  = array[right];
        array[right] = t;
    }
    private void sort(T[] array, final int left, final int right) {
        final int size = right - left + 1;
        if (size == 2 && array[left].compareTo(array[right]) > 0) {
            swap(array, left, right);
            return;
        }
        if (size < 2) {
            return;
        }

        int p = left + size/2;
        p = partition(array, left, p, right);
        sort(array, left,  p-1);
        sort(array, p+1, right);
    }
    private int  partition(T[] array, final int left, final int p, final int right) {
       final T pv = array[p];
       swap(array, p, right);
       int n = left;
       for (int i = left; i < right; i++) {
           if (array[i].compareTo(pv) < 0) {
               swap(array, n, i);
               n++;
           }
       }
       swap(array, n, right);
       return n;
    }
}
