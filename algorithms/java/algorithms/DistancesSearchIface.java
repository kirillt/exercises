package algorithms;

import java.lang.Integer;

public interface DistancesSearchIface {
    class Distance implements Comparable<Distance> {
        public final boolean infinite;
        public final int     distance;

        public Distance() {
            infinite = true;
            distance = 0;
        }
        public Distance(int d) {
            infinite = false;
            distance = d;
        }

        @Override
        public int compareTo(final Distance other) {
            if (this.infinite && other.infinite) { return 0; }
            if (this.infinite ) { return +1; }
            if (other.infinite) { return -1; }
            return Integer.compare(this.distance, other.distance);
        }
        public String toString() {
            return infinite ? "inf" : Integer.toString(distance);
        }

        public static final Distance inf = new Distance();
        public static       Distance d(int x) {
            return new Distance(x);
        }

        public Distance plus(final Distance other) {
            if (this.infinite || other.infinite) { return inf; }
            return d(this.distance + other.distance);
        }
    }

    void findAllDistances(Distance[][] graph);
}
