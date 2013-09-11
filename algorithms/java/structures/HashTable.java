package structures;

import structures.Pair;
import exceptions.NoSuchElement;

import java.util.LinkedList;
import java.lang.reflect.Array;

public class HashTable<K,V> {
    public HashTable(int approximateSize) {
        for (int i = 0; i < PRIMES_COUNT; i++) {
            if (primes[i] > approximateSize) {
                size  = primes[i];
                array = (EntryList[]) Array.newInstance(EntryList.class, size);
                break;
            }
        }
    }

    public HashTable<K,V> add(K k, V v) {
        int i = hash(k);
        EntryList ks = array[i];
        if (ks == null) {
            ks = new EntryList();
            array[i] = ks;
        }
        ks.add(new Entry(k,v));
        return this;
    }

    public HashTable<K,V> del(K k) throws NoSuchElement {
        int i = hash(k);
        EntryList ks = array[i];
        if (ks == null) {
            throw new NoSuchElement();
        }
        Entry x = new Entry(k,null);
        if (!ks.remove(x)) {
            throw new NoSuchElement();
        }
        while (ks.remove(x)) {}
        return this;
    }

    public String toString() {
        final StringBuilder result = new StringBuilder("");
        for (int i = 0; i < size; i++) {
            EntryList ks = array[i];
            if (ks != null && !ks.isEmpty()) {
                result.append(ks);
            }
        }
        return result.toString();
    }

    private int hash(K k) {
        int h = k.hashCode();
        return h >= 0 ? h % size : ((-1) * h) % size;
    }

    private final class Entry {
        public final K key;
        public final V value;
        public Entry(K k, V v) {
            key   = k;
            value = v;
        }
        public boolean equals(Object obj) {
            return ((Entry) obj).key.equals(key);
        }
        public String toString() {
            return "<" + key + ";" + value + ">";
        }
    }

    // type synonym
    private final class EntryList extends LinkedList<Entry> {}

    private int size;
    private EntryList[] array;

    private final static int[] primes = {
        2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
        101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,
        211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,
        307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,
        401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,
        503,509,521,523,541,547,557,563,569,571,577,587,593,599,
        601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,
        701,709,719,727,733,739,743,751,757,761,769,773,787,797,
        809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,
        907,911,919,929,937,941,947,953,967,971,977,983,991,997,
        1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,
        1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,
        1201,1213,1217,1223
    };
    private final static int PRIMES_COUNT = primes.length;
}
