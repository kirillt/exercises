package structures;

import java.lang.Comparable;

import exceptions.NoSuchElement;

public class BinaryTree<T extends Comparable> implements TreeIface<T> {
    public BinaryTree(T value) {
        this.value = value;
    }

    public BinaryTree<T> add(T value) {
        return add(new BinaryTree(value));
    }
    private BinaryTree<T> add(BinaryTree<T> tree) {
        if (tree == null) {
            return this;
        }
        switch (tree.value.compareTo(this.value)) {
            case -1: {
                if (left != null) {
                    left.add(tree);
                } else {
                    left = tree;
                }
                break;
            }
            case +1: {
                if (right != null) {
                    right.add(tree);
                } else {
                    right = tree;
                }
                break;
            }
        }
        return this;
    }

    private static Integer last;
    public BinaryTree<T> del(final T value) throws NoSuchElement {
        if (value instanceof Integer && last != (Integer)value) {
            last = (Integer)value;
        }
        switch (value.compareTo(this.value)) {
            case -1: {
                if (left != null) {
                    left.del(value);
                    if (left.toDelete) {
                        left = null;
                    }
                } else {
                    throw new NoSuchElement();
                }
                break;
            }
            case +1: {
                if (right != null) {
                    right.del(value);
                    if (right.toDelete) {
                        right = null;
                    }
                } else {
                    throw new NoSuchElement();
                }
                break;
            }
            case  0: {
                if (right != null) {
                    BinaryTree<T> rl = right.left;
                    this.value = right.value;
                    right = right.right;
                    if (left != null) {
                        left.add(rl);
                    } else {
                        left = rl;
                    }
                } else {
                    if (left != null) {
                        this.value = left.value;
                        left  = left.left;
                        right = left.right;
                    } else {
                        toDelete = true;
                    }
                }
                break;
            }
        }
        return this;
    }

    public String toString() {
        String leftS  = left  == null ? "null" : left.toString();
        String rightS = right == null ? "null" : right.toString();
        return "{" + leftS + "|" + this.value + "|" + rightS + "}";
    }

    protected T value;
    protected boolean toDelete = false;
    protected BinaryTree<T> left  = null;
    protected BinaryTree<T> right = null;
}
