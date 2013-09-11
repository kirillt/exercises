package algorithms;

import algorithms.ComparisonSortIface;

import java.util.Arrays;

import java.lang.StringBuilder;

public class MergeSort<T extends Comparable> implements ComparisonSortIface<T> {
    public  void sort(T[] array) {
        sort(array, 0, array.length);
    }
    private void sort(T[] array, final int left, final int right) {
        final int size = right - left;
        if (size > 2) {
            int middle = left + size/2;
            sort(array, left  , middle);
            sort(array, middle, right );

            int j = left;
            int k = middle;
            T[] temp = (T[]) new Comparable[size];
            int i = 0;
            for (; i < size && j < middle && k < right; i++) {
                if (array[j].compareTo(array[k]) > 0) {
                    temp[i] = array[k];
                    k++;
                } else {
                    temp[i] = array[j];
                    j++;
                }
            }
            for (; i < size && j < middle; i++) {
                temp[i] = array[j];
                j++;
            }
            for (; i < size && k < right; i++) {
                temp[i] = array[k];
                k++;
            }
            i = 0;
            for (; i < size; i++) {
                array[left + i] = temp[i];
            }
        } else {
            if (size == 2 && array[left].compareTo(array[left+1]) > 0) {
                T temp        = array[left];
                array[left]   = array[left+1];
                array[left+1] = temp;
            }
        }
    }
}
