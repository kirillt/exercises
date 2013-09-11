package structures;

import java.lang.Comparable;

import exceptions.NoSuchElement;

public interface TreeIface<T extends Comparable> {
    TreeIface<T> add(T value);
    TreeIface<T> del(T value) throws NoSuchElement;
}
