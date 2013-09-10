package structures;

import exceptions.NoSuchElement;

public class SinglePtrList<T> {
    class Node<T> {
        Node(final T value) {
            this.value = value;
            this.next  = null;
        }

        Pair<Node<T>,Node<T>> find(Node<T> prev, final T value) throws NoSuchElement {
            if (this.value == value) {
                return new Pair(prev, this);
            } else {
                if (next != null) {
                    return next.find(this, value);
                } else {
                    throw new NoSuchElement();
                }
            }
        }

        public String toString() {
            return "{" + value + "->" + (next == null ? "null" : next) + "}";
        }

        public final T value;
        private Node<T> next;
    }

    public SinglePtrList() {
        this.begin = null;
        this.end   = null;
    }

    public SinglePtrList<T> add(final T value) {
        try {
            Pair<Node<T>,Node<T>> nodes = find(value);
        } catch (NoSuchElement e) {
            Node<T> n = new Node<T>(value);
            if (begin == null) {
                begin = n;
                end = begin;
            } else {
                end.next = n;
                end = n;
            }
        }
        return this;
    }
    public SinglePtrList<T> del(final T value) throws NoSuchElement {
        Pair<Node<T>,Node<T>> nodes = find(value);
        Node<T> prev;
        if (nodes.left != null) {
            if (nodes.right.next != null) {
                nodes.left.next = nodes.right.next;
            } else {
                nodes.left.next = null;
                end = nodes.left;
            }
        } else {
            if (nodes.right.next != null) {
                begin = nodes.right.next;
            } else {
                begin = null;
                end = null;
            }
        }
        nodes.right.next = null;
        return this;
    }

    public String toString() {
        return begin.toString();
    }

    // common interview problem
    public SinglePtrList<T> reverse() {
        if (begin == null) {
            return this;
        }
        this.end = this.begin;
        Node<T> curr = this.begin;
        Node<T> prev = null;
        while (curr != null) {
            Node<T> next = curr.next;
            curr.next = prev;
            prev = curr;
            curr = next;
        }
        this.begin = prev;
        return this;
    }

    private Pair<Node<T>,Node<T>> find(final T value) throws NoSuchElement {
        if (begin != null) {
            return begin.find(null, value);
        } else {
            throw new NoSuchElement();
        }
    }
    
    private Node<T> begin;
    private Node<T> end;
}
