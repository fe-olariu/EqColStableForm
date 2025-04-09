import java.util.ArrayList;
import java.util.Iterator;

public class Pair {// from could be an id, to could be a size
	int from, to;

	Pair(int from, int to) {
		this.from = from;
		this.to = to;
	}

	Pair() {
		this.from = -1;
		this.to = -1;
	}

	public String toString() {
		String toStr = " (" + this.from + ", " + this.to + ")";
		System.out.print(toStr);
		// System.out.println();
		return toStr;
	}
}
