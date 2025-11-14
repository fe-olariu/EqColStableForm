import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import org.graph4j.util.Clique;
import org.graph4j.util.VertexSet;

public class ColorClass {
	public HashSet<Integer> vertices;
	public double cost;
	public int size;
	public int id;

	public ColorClass() {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		this.size = 0;
		this.id = -1;
	}

	public ColorClass(Clique clique, int id) {
		// System.out.println(clique);
		Iterator<Integer> it = clique.iterator();
		this.vertices = new HashSet<Integer>();
		while (it.hasNext())
			this.vertices.add(it.next().intValue());
		this.cost = -1;
		this.size = vertices.size();
		this.id = id;
	}

	public ColorClass(Clique clique, int id, double[] weights) {
		// System.out.println(clique);
		int vertex;
		double weight = 0;
		Iterator<Integer> it = clique.iterator();
		this.vertices = new HashSet<Integer>();
		while (it.hasNext()) {
			vertex = it.next().intValue();
			this.vertices.add(vertex);
			weight += weights[vertex];
			// weight_1 += (1 - weights[vertex]);
		}
		// System.out.println("Weight_1: " + weight_1);
		this.cost = weight;
		this.size = vertices.size();
		this.id = id;
	}

	public ColorClass(VertexSet set, double weight, int id) {
		// System.out.println(clique);
		Iterator<Integer> it = set.iterator();
		this.vertices = new HashSet<Integer>();
		while (it.hasNext())
			this.vertices.add(it.next().intValue());
		this.cost = weight;
		this.size = vertices.size();
		this.id = id;
	}

	public ColorClass(HashSet<Integer> vertices) {
		if (vertices != null) {
			this.vertices = new HashSet<Integer>();
			this.cost = -1;
			this.size = vertices.size();
			this.id = -1;
			int i;

			Iterator<Integer> iterator = vertices.iterator();
			while (iterator.hasNext()) {
				i = iterator.next().intValue();
				this.vertices.add(i);
			}
		}
	}

	public ColorClass(HashSet<Integer> vertices, int id) {
		if (vertices != null && vertices.size() > 0) {
			HashSet<Integer> newVertices = new HashSet<Integer>();
			Iterator<Integer> iter1 = vertices.iterator();
			iter1 = vertices.iterator();
			while (iter1.hasNext())
				newVertices.add(iter1.next().intValue());
			this.vertices = newVertices;
			this.cost = -1;
			this.size = vertices.size();
			this.id = id;
		}
	}

	public ColorClass(ArrayList<Integer> vertices) {
		if (vertices != null) {
			this.vertices = new HashSet<Integer>();
			this.cost = -1;
			this.size = vertices.size();
			this.id = -1;
			int i;

			Iterator<Integer> iterator = vertices.iterator();
			while (iterator.hasNext()) {
				i = iterator.next().intValue();
				this.vertices.add(i);
			}
		}
	}

	public ColorClass(List<Integer> vertices) {
		if (vertices != null) {
			this.vertices = new HashSet<Integer>();
			this.cost = -1;
			this.size = vertices.size();
			this.id = -1;
			int i;

			Iterator<Integer> iterator = vertices.iterator();
			while (iterator.hasNext()) {
				i = iterator.next().intValue();
				this.vertices.add(i);
			}
		}
	}

	public boolean check(boolean[][] adj, int _n) {
		boolean[] currentSet = new boolean[_n];
		Iterator<Integer> iter1;
		if (this.vertices != null) {
			iter1 = this.vertices.iterator();
			while (iter1.hasNext()) {
				currentSet[iter1.next().intValue()] = true;
			}
		}
		for (int u = 0; u < _n; u++)
			for (int v = 0; v < u; v++)
				if (currentSet[u] && currentSet[v] && adj[u][v]) {
					System.out.println("NOT a stable set: u = " + u + ", v = " + v);
					return false;
				}
		// System.out.println("Stable SET.");
		return true;
	}

	public boolean check(ColorClass stableSet, int n) {
		// returns true if stableSet equals this
		int i;
		boolean[] currentSet = new boolean[n], newSet = new boolean[n];
		Iterator<Integer> iter1;
		if (this.vertices != null) {
			iter1 = this.vertices.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				currentSet[i] = true;
			}
		}
		if (stableSet != null && stableSet.vertices != null) {
			iter1 = stableSet.vertices.iterator();
			while (iter1.hasNext()) {
				i = iter1.next().intValue();
				newSet[i] = true;
			}

			for (i = 0; i < n; i++)
				if (currentSet[i] != newSet[i])
					return false;
			return true;
		}
		if (stableSet == null && stableSet.vertices == null)
			return true;
		return false;
	}

	public ColorClass(ColorClass colorClass) {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		this.size = colorClass.vertices.size();
		this.id = colorClass.id;
		int i;

		Iterator<Integer> iterator = colorClass.vertices.iterator();
		if (colorClass != null)
			while (iterator.hasNext()) {
				i = iterator.next().intValue();
				this.vertices.add(i);
			}
	}

	public ColorClass(HashSet<Integer> colorClass, boolean[][] adj, double cost) {
		this.vertices = colorClass;
		this.cost = cost;
		this.size = colorClass.size();
		this.id = -1;
	}

	public ColorClass(boolean[] characteristicSet) {
		this.vertices = new HashSet<Integer>();
		this.cost = -1;
		int n = characteristicSet.length;
		for (int h = 0; h < n; h++)
			if (characteristicSet[h])
				this.vertices.add(h);
		this.size = this.vertices.size();
		this.id = -1;
	}

	public boolean isEqual(ColorClass colorClass, int n) {
		boolean result = true;
		boolean[] charactThis = new boolean[n];
		boolean[] charactThat = new boolean[n];
		int i;
		Iterator<Integer> iter = this.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			charactThis[i] = true;
		}
		iter = colorClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			charactThat[i] = true;
		}
		for (int j = 0; j < n; j++) {
			if (charactThis[j] != charactThat[j])
				return false;
		}
		// TODO: check first the ids!
		return result;
	}

	public String toString(RMP rmp) {
		String toStr = "";
		Iterator<Integer> iter;
		iter = this.vertices.iterator();
		int id;
		System.out.println(":");
		while (iter.hasNext()) {
			id = iter.next().intValue();
			rmp.colorClasses.get(id).toString();
			toStr += " " + id;
		}
		System.out.print(toStr + " | size: " + this.vertices.size() + " | id: " + this.id);
		System.out.println(":");
		System.out.println();
		return toStr;
	}

	public String toString() {
		String toStr = "";
		Iterator<Integer> iter;
		iter = this.vertices.iterator();
		while (iter.hasNext()) {
			toStr += " " + iter.next().intValue();
		}
		System.out.print(toStr + " | size: " + this.vertices.size() + " | cost: " + this.cost + " | id: " + this.id);
		System.out.println();
		return toStr;
	}
}