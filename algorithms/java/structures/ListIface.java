package structures;

import exceptions.NoSuchElement;

public interface ListIface<T> {
    ListIface<T> add(T value);
    ListIface<T> del(T value) throws NoSuchElement;
    ListIface<T> reverse(); // common interview problem
}
