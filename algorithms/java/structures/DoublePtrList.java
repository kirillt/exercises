package structures;

import exceptions.NoSuchElement;

public class DoublePtrList<T> implements ListIface<T> {
    class Node<T> {
        Node(final T value) {
            this.value = value;
            this.prev  = null;
            this.next  = null;
        }

        public String toString() {
            return "{" + value + "->" + (next == null ? "null" : next) + "}";
        }

        public final T value;
        private Node<T> prev;
        private Node<T> next;
    }

    public DoublePtrList() {
        this.begin = null;
        this.end   = null;
    }

    public DoublePtrList<T> add(T value) {
        Node<T> curr = this.begin;
        while (curr != null) {
            if (curr.value == value) {
                return this;
            }
            curr = curr.next;
        }
        curr = new Node<T>(value);
        if (begin != null) {
            this.end.next = curr;
            curr.prev = this.end;
            this.end = curr;
            curr.next = null;
        } else {
            this.begin = curr;
            this.end   = curr;
            curr.prev  = null;
            curr.next  = null;
        }
        return this;
    }
    public DoublePtrList<T> del(T value) throws NoSuchElement {
        Node<T> curr = this.begin;
        while (curr != null) {
            if (curr.value == value) {
                Node<T> prev = curr.prev;
                Node<T> next = curr.next;
                if (prev != null) {
                    prev.next = next;
                } else {
                    this.begin = next;
                }
                if (next != null) {
                    next.prev = prev;
                } else {
                    this.end = prev;
                }
                curr = next;
                return this;
            }
            curr = curr.next;
        }
        throw new NoSuchElement();
    }
    public DoublePtrList<T> reverse() {
        Node<T> curr = this.begin;
        while (curr != null) {
            Node<T> prev = curr.prev;
            Node<T> next = curr.next;
            curr.next = prev;
            curr.prev = next;
            curr = next;
        }
        curr = this.end;
        this.end = this.begin;
        this.begin = curr;
        return this;
    }

    public String toString() {
        return begin != null ? begin.toString() : "null";
    }

    private Node<T> begin;
    private Node<T> end;
}
