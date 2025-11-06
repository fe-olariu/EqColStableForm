
public class Pair implements Comparable<Pair> {// from could be an id, to could be a size
	int from, to;
	double val;

	Pair(int from, int to) {
		this.from = from;
		this.to = to;
	}

	Pair() {
		this.from = -1;
		this.to = -1;
	}

	Pair(int from, int to, double val) {
		this.from = from;
		this.to = to;
		this.val = val;
	}

	public int compareTo(Pair _pair) {
		if (val == _pair.val)
			return 0;
		else if (val < _pair.val)
			return -1;
		else
			return 1;
	}

	public String toString() {
		String toStr = " (" + this.from + ", " + this.to + ")";
		System.out.print(toStr);
		// System.out.println();
		return toStr;
	}
}