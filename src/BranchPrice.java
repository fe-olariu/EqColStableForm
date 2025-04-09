import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

import org.graph4j.Graph;
import org.graph4j.GraphBuilder;
import org.graph4j.clique.DFSCliqueIterator;
import org.graph4j.util.Clique;
import org.graph4j.util.IntArrays;
import org.graph4j.util.StableSet;
import org.graph4j.util.VertexSet;

import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;

import com.gurobi.gurobi.GRB;
import com.gurobi.gurobi.GRBConstr;
import com.gurobi.gurobi.GRBEnv;
import com.gurobi.gurobi.GRBException;
import com.gurobi.gurobi.GRBLinExpr;
import com.gurobi.gurobi.GRBModel;
import com.gurobi.gurobi.GRBVar;
import com.gurobi.gurobi.GRB.DoubleAttr;
import com.gurobi.gurobi.GRB.IntParam;
import com.gurobi.gurobi.GRB.StringAttr;

public class BranchPrice {
	// noOfClasses is the number of generated variables (-1);
	// n is the order of the graph;
	// m is the number of edges (the size);
	// k is the number of clusters;
	public static int n, m, k, noOfCreatedClasses = 0, rho = 0, Delta, k_down, k_up, p_down = -1, p_up = -1, p,
			noOfStableSets_BK = 0, maxNoOfStableSets_BK = 20000, subproblemVerbosity = 0, poolSize = 0,
			eqColNumber = -1, currentEqColNumber = -1, n_max, stagesUp = 0, stagesDown = 0;
	public static boolean betaIsNull = true, multiple = true, verbosity = true, checkStableSets = false,
			heuristic = false, flag = false;
	public static long timeout = 10000, sleepTime = 50000, initialDFSTimeout = 1000, minTimeUp, maxTimeUp, minTimeDown,
			maxTimeDown, avgTime;
	public static boolean[][] adjacency;// adjacency matrix
	public static Stack<RMP> stackRMPb;
	public static HashMap<Integer, ColorClass> colorClasses_BK;
	public static double precisionRC = 1e-5;// the reduced cost precision (if the reduced cost of a new variable is
											// > beta + precisionRC, then that variable can be added to the model
	public static double precisionVar = 1e-7;
	public static double precisionOpt = 1e-9;
	public static double precisionClassCheck = 1e-5;
	public static double precisionBB = 1e-9;
	public static double precisionLB = 1e-5;
	public static double precisionBeta = 1e-7;
	public static double upperB = 1e20;
	public static double rootLowerB = -1e20;
	public static double miu = n * n * n;

	public static String fileName, path = "../data/EqCol/", writeLUp, writeLDown;

	public static void createFile(String fileName) {
		try {
			File file = new File(fileName);
			if (file.createNewFile()) {
				System.out.println("File created: " + file.getName());
			} else {
				System.out.println("File already exists.");
			}
		} catch (IOException e) {
			System.out.println("An error occurred.");
			e.printStackTrace();
		}
	}

	public static void readFile(String dataFile) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		int[] size = readGfF.readGraphSize(dataFile);
		n = size[0];
		m = size[1];
		System.out.println("File " + dataFile + " n = " + n + " m = " + m);
		adjacency = new boolean[n][n];
		Delta = readGfF.readGraph(dataFile, adjacency, Delta);
		System.out.println("Delta = " + Delta);
	}

	public static void readFileK(String dataFile) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		int[] size = readGfF.readGraphSize(dataFile);
		n = size[0];
		m = size[1];
		int s = n / k;
		rho = 0;
		if (s * k < n) {
			s++;
			rho = s * k - n;
		}
		System.out.println("File " + dataFile + " n = " + n + " m = " + m);
		adjacency = new boolean[n + rho][n + rho];
		Delta = readGfF.readGraphK(dataFile, adjacency, Delta, k, rho);
	}

	public static void generateGraph(int v, double p, int h) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		// int[] size = readGfF.readGraphSize(dataFile);
		n = v;
		m = 0;
		adjacency = new boolean[n][n];
		Delta = 0;
		int delta = 0;
		String path = "../data/EqCol/instances/", nume = "random_" + v + "_" + p + "_" + h + ".col";
		for (int i = 0; i < n; i++) {
			delta = 0;
			for (int j = 0; j < i; j++)
				if ((new Random()).nextDouble() < p) {
					adjacency[i][j] = true;
					adjacency[j][i] = true;
					m++;
					delta++;
				}
			if (delta > Delta)
				Delta = delta;
		}
		System.out.println("Delta = " + Delta);
		String lp_sol_fileName = path + "/" + nume;
		File lp_sol_file = new File(lp_sol_fileName);
		BufferedWriter writer = null;
		try {
			if (!lp_sol_file.exists()) {
				lp_sol_file.createNewFile();
			}
			FileWriter fw = new FileWriter(lp_sol_file);
			writer = new BufferedWriter(fw);
			writer.write("c FILE: " + nume);
			writer.newLine();
			// writer.newLine();
			writer.write("c SOURCE: E. F. Olariu (olariu@info.uic.ro");
			writer.newLine();
			// writer.newLine();
			writer.write("c DESCRIPTION: random graph with " + n + " vertices and edge probability " + p);
			// writer.newLine();
			writer.newLine();
			writer.write("p edge " + n + " " + m);
			writer.newLine();
			for (int i = 0; i < n; i++)
				for (int j = i + 1; j < n; j++)
					if (adjacency[i][j]) {
						writer.write("e " + (i + 1) + " " + (j + 1));
						writer.newLine();
					}
		} catch (IOException e) {
			System.out.println("Error code: " + e.getMessage());
		} finally {
			try {
				if (writer != null) {
					writer.close();
				}
			} catch (IOException e) {
			}
		}
	}

	public static void createDir(String path) {
		// Creating a File object
		File file = new File(path);
		// Creating the directory
		boolean bool = file.mkdir();
		if (bool) {
			System.out.println("Results directory created successfully");
		} else {
			System.out.println("Sorry couldn't create results directory. Maybe already there?");
		}
	}

	public static double formSec(double val) {// formatting the time intervals
		return Math.floor(val * 1000) / 1000;
	}

	public static Graph buildGraph() {
		Graph graph = GraphBuilder.numVertices(n).estimatedNumEdges(m).buildGraph();
		for (int v = 0; v < n; v++)
			for (int u = 0; u < v; u++)
				if (!adjacency[u][v]) {
					graph.addEdge(u, v);
				}
		return graph;
	}

	public static Graph buildGraph(double[] weights) {
		Graph graph = GraphBuilder.numVertices(n).estimatedNumEdges(m).buildGraph();
		for (int v = 0; v < n; v++)
			graph.setVertexWeight(v, weights[v]);
		for (int v = 0; v < n; v++)
			for (int u = 0; u < v; u++)
				if (!adjacency[u][v]) {
					graph.addEdge(u, v);
				}
		return graph;
	}

	public static void stableSetIterator(int minSize, int maxSize, int maxStablesPerIter) {
		long DFSTime = System.nanoTime();
		int max = -1, _node;
		var graph = buildGraph();
		colorClasses_BK = new HashMap<Integer, ColorClass>();
		while (max != 0 && graph.numVertices() >= minSize) {
			int first = IntArrays.min(graph.vertices()), _u = -1, k = 0;
			var cliqueIt = new DFSCliqueIterator(graph, minSize, maxSize, initialDFSTimeout);
			int count = 0;
			long t0 = System.currentTimeMillis();
			int[] visited = new int[n];
			while (count < maxStablesPerIter && cliqueIt.hasNext() && noOfStableSets_BK < maxNoOfStableSets_BK) {
				ColorClass _colCls = new ColorClass(cliqueIt.next(), noOfCreatedClasses);
				_colCls.check(adjacency, n);
				// _colCls.toString();
				colorClasses_BK.put(noOfCreatedClasses, _colCls);
				noOfCreatedClasses++;
				noOfStableSets_BK++;
				Iterator<Integer> itVertex = _colCls.vertices.iterator();
				while (itVertex.hasNext()) {
					_node = itVertex.next();
					visited[_node]++;
				}
				k++;
				count++;
				if (System.currentTimeMillis() - t0 > initialDFSTimeout) {
					break;
				}
			}
			max = 0;
			_u = -1;
			for (int u = 0; u < n; u++) {
				if (max < visited[u]) {
					max = visited[u];
					_u = u;
				}
			}
			System.out.println("u: " + _u + ", max: " + max + ", k: " + k);
			if (max != 0)
				graph.removeVertex(_u);
		}
		System.out.println("Total DFS time: " + (System.nanoTime() - DFSTime) * 1e-9);
	}

	public static HashMap<Integer, ColorClass> hashMLCopy(HashMap<Integer, ColorClass> hMap) {
		HashMap<Integer, ColorClass> mapCopy = new HashMap<Integer, ColorClass>();
		for (HashMap.Entry<Integer, ColorClass> entry : hMap.entrySet())
			mapCopy.put(entry.getKey().intValue(), new ColorClass(entry.getValue()));
		return mapCopy;
	}

	public static ArrayList<Pair>[] arrayLIntCopy(ArrayList<Pair>[] aList) {
		// create a deep copy of aList
		int q = aList.length;
		ArrayList<Pair>[] newList = new ArrayList[q];
		ArrayList<Pair> listV;
		Pair _pair;
		if (aList != null)
			for (int i = 0; i < q; i++) {
				listV = new ArrayList<Pair>();
				if (aList[i] != null) {
					Iterator<Pair> iterV = aList[i].iterator();
					while (iterV.hasNext()) {
						_pair = iterV.next();
						listV.add(new Pair(_pair.from, _pair.to));
					}
				}
				newList[i] = listV;
			}
		return newList;
	}

	public static Pair[] arrayPCopy(Pair[] aList) {
		// create a deep copy of aList
		Pair[] newList = null;
		if (aList != null) {
			int q = aList.length;
			newList = new Pair[q];
			for (int i = 0; i < q; i++)
				if (aList[i] != null)
					newList[i] = new Pair(aList[i].from, aList[i].to);
		}
		return newList;
	}

	public static ArrayList<Pair> arrayLPairCopy(ArrayList<Pair> pairList) {
		// create a deep copy of pairList
		ArrayList<Pair> newPairList = new ArrayList<Pair>();
		Pair _pair;
		if (pairList != null) {
			Iterator<Pair> iterV = pairList.iterator();
			while (iterV.hasNext()) {
				_pair = iterV.next();
				newPairList.add(new Pair(_pair.from, _pair.to));
			}
		}
		return newPairList;
	}

	public static double lowerBound(double _obj) {
		double lBound = Math.floor(_obj);
		if (_obj - Math.floor(_obj) > precisionLB)
			lBound = Math.ceil(_obj);
		return lBound;
	}

	public static void listColorClasses(HashMap<Integer, ColorClass> _colorClasses) {
		if (_colorClasses != null) {
			System.out.println();
			HashMap<Integer, ColorClass> coalitionList = new HashMap<Integer, ColorClass>();
			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				// System.out.print("id: " + pairE.getKey());
				pairE.getValue().toString();
			}
		}
	}

	public static int[] manageColors(RMP _rmp) {
		int[] _colors = new int[n];
		int _u, _v, i, j, col = 0;
		Pair _pair;
		ArrayList<ColorClass> _coloring = new ArrayList<ColorClass>();

		Iterator<Pair> _iterP = _rmp.sameColNodes.iterator();
		while (_iterP.hasNext()) {
			_pair = _iterP.next();
			_u = _pair.from;
			_v = _pair.to;
			i = _colors[_u];
			j = _colors[_v];
			if (i == 0 && j == 0) {
				col++;
				_colors[_u] = col;
				_colors[_v] = col;
			}
			if (i == 0 && j != 0)
				_colors[_u] = _colors[_v];
			if (i != 0 && j == 0)
				_colors[_v] = _colors[_u];
			if (i != 0 && j != 0 && i < j) {
				for (int w = 0; w < n; w++)
					if (_colors[w] == j)
						_colors[w] = i;
			}
			if (i != 0 && j != 0 && i > j) {
				for (int w = 0; w < n; w++)
					if (_colors[w] == i)
						_colors[w] = j;
			}
		}
		System.out.println("Number of colors: " + col);
		i = 0;
		for (int w = 0; w < n; w++)
			if (_colors[w] != 0)
				i++;
		System.out.println("Number of colored vertices: " + i);

		for (int c = 1; c <= col; c++) {
			ColorClass _class = new ColorClass();
			for (int u = 0; u < n; u++)
				if (_colors[u] == c)
					_class.vertices.add(u);
			_class.id = c;
			_coloring.add(_class);
		}
		Iterator<ColorClass> _iterC = _coloring.iterator();
		while (_iterC.hasNext())
			_iterC.next().toString();
		return _colors;
	}

	public static void RemovePairFromList(ArrayList<Pair> _list, Pair _pair) {
		Iterator<Pair> iterP = _list.iterator();
		Pair pair;
		if (_list != null)
			while (iterP.hasNext()) {
				pair = iterP.next();
				if (_pair.from == pair.from && _pair.to == pair.to) {
					iterP.remove();
					break;
				}
			}
	}

	public static void ShowCPCProblem(int[] _vertex, int _noVertices, int _noClusters, int[] _clustersV,
			GRBModel _model, HashMap<Integer, ColorClass> _colClList, int pbNo) throws GRBException {
		Integer tt;
		double val, sum;
		int t;
		ColorClass _colClass;
		String path = "../data/EqCol/results/";
		System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
		System.out.println("No of vertices: " + _noVertices + " | No of clusters: " + _noClusters);
		System.out.print("Optimum for rmp: " + _model.get(DoubleAttr.ObjVal) + " | No of colors: "
				+ (_noClusters - _model.get(DoubleAttr.ObjVal)));
		System.out.println();
		System.out.println("----------------------------------------------------------");
		for (HashMap.Entry<Integer, ColorClass> entry : _colClList.entrySet()) {
			tt = entry.getKey();
			_colClass = entry.getValue(); // use key and value
			val = _model.getVarByName("x" + tt.intValue()).get(GRB.DoubleAttr.X);
			if (val > 1 - precisionBB) {
				System.out.print("Coloring class: " + tt.intValue() + "|");
				Iterator<Integer> iter = _colClass.vertices.iterator();
				while (iter.hasNext()) {
					t = iter.next().intValue();
					System.out.print(" " + _vertex[t] + "(" + _clustersV[t] + ")");
				}
				System.out.println();
			}
		}
		System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
	}

	public static RMP buildRootProblem() throws GRBException {
		// Build the initial LP model for the Equitable Coloring Problem (EqCP)
		long rootPbBuildTime = System.nanoTime();
		ArrayList<Pair>[] _vertexColCl = new ArrayList[n];
		Pair[] _vertexPartialCol = new Pair[n];
		ArrayList<Pair> _sameCol = new ArrayList<Pair>();
		ArrayList<Pair> _diffCol = new ArrayList<Pair>();
		HashMap<Integer, ColorClass> _colorClasses = new HashMap<Integer, ColorClass>();
		HashMap<Integer, ColorClass> _partialCol = new HashMap<Integer, ColorClass>();
		ColorClass _class;
		int id, size;

		if (colorClasses_BK != null && colorClasses_BK.size() > 0) {
			_colorClasses = colorClasses_BK;
			for (int u = 0; u < n; u++)
				_vertexColCl[u] = new ArrayList<Pair>();

			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				id = pairE.getKey();
				_class = (ColorClass) pairE.getValue();
				size = _class.vertices.size();

				Iterator<Integer> iterV = _class.vertices.iterator();
				while (iterV.hasNext())
					_vertexColCl[iterV.next()].add(new Pair(id, size));
			}
		}

		ColorClass stable;
		HashSet<Integer> set;
		Pair _pair;

		for (int u = 0; u < n; u++) {
			_pair = new Pair(u, 1);
			_vertexPartialCol[u] = _pair;
			set = new HashSet<Integer>();
			set.add((Integer) u);
			stable = new ColorClass(set);
			stable.size = 1;
			stable.id = u;
			_partialCol.put((Integer) u, stable);
		}

		RMP _rmp = new RMP(-1, n, _vertexColCl, _diffCol, _sameCol, _colorClasses, _vertexPartialCol, _partialCol,
				"root", -1, -1);
		System.out.println(
				"*******Build time for the initial problem: " + formSec((System.nanoTime() - rootPbBuildTime) * 1e-9));
		return _rmp;
	}

	// TODO: stable sets containing vertex u but not v could be extended with v (and
	// viceversa): if the stable set has cardinality k_up < k_down
	public static RMP buildRMP_Contraction(RMP rmp, Pair pair, int noPb) throws GRBException {
		HashMap<Integer, ColorClass> _colorClasses = hashMLCopy(rmp.colorClasses);
		ArrayList<Pair> _sameCol = arrayLPairCopy(rmp.sameColNodes), _diffCol = arrayLPairCopy(rmp.diffColNodes),
				_toDelete_u = new ArrayList<Pair>(), _toDelete_v = new ArrayList<Pair>();
		ArrayList<Pair>[] _vertexColCl = arrayLIntCopy(rmp.vertexColCl);
		int u = pair.from, v = pair.to, x, id, size, _noVertices = rmp.noVirtualVertices;
		Pair _pair;
		ColorClass stableSet;
		boolean found;

		_sameCol.add(new Pair(u, v));

		Iterator<Pair> iterP = _vertexColCl[u].iterator();
		while (iterP.hasNext()) {
			_pair = iterP.next();
			id = _pair.from;
			size = _pair.to;
			stableSet = _colorClasses.get((Integer) id);
			Iterator<Integer> iterV = stableSet.vertices.iterator();
			found = false;
			while (iterV.hasNext())
				if (iterV.next() == v) {
					found = true;
					break;
				}
			if (!found)
				_toDelete_u.add(_pair);
		}
		iterP = _vertexColCl[v].iterator();
		while (iterP.hasNext()) {
			_pair = iterP.next();
			id = _pair.from;
			size = _pair.to;
			stableSet = _colorClasses.get((Integer) id);
			Iterator<Integer> iterV = stableSet.vertices.iterator();
			found = false;
			while (iterV.hasNext())
				if (iterV.next() == u) {
					found = true;
					break;
				}
			if (!found)
				_toDelete_v.add(_pair);
		}

		if (_toDelete_u != null) {
			iterP = _toDelete_u.iterator();
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				while (iterV.hasNext()) {
					x = iterV.next();
					RemovePairFromList(_vertexColCl[x], _pair);// TODO: check!!
				}
				_colorClasses.remove((Integer) id);
			}
		}
		if (_toDelete_v != null) {
			iterP = _toDelete_v.iterator();
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				while (iterV.hasNext()) {
					x = iterV.next();
					RemovePairFromList(_vertexColCl[x], _pair);// TODO: check!!
				}
				_colorClasses.remove((Integer) id);
			}
		}

		RMP _rmp = new RMP(noPb, _noVertices - 1, _vertexColCl, _diffCol, _sameCol, _colorClasses, "contract_pair", u,
				v);
		return _rmp;
	}

	public static RMP buildRMP_AddEdge(RMP rmp, Pair pair, int noPb) throws GRBException {
		HashMap<Integer, ColorClass> _colorClasses = hashMLCopy(rmp.colorClasses),
				_partialCol = hashMLCopy(rmp.partialCol);
		ArrayList<Pair> _sameCol = arrayLPairCopy(rmp.sameColNodes), _diffCol = arrayLPairCopy(rmp.diffColNodes),
				_toDelete_u = new ArrayList<Pair>(), _toAdd_u = new ArrayList<Pair>();
		ArrayList<Pair>[] _vertexColCl = arrayLIntCopy(rmp.vertexColCl);
		int u = pair.from, v = pair.to, x, id, _noVertices = rmp.noVirtualVertices, size;
		boolean found = false;
		Pair _pair, _newPair;
		ColorClass stableSet, newStableSet1, newStableSet2;

		_diffCol.add(new Pair(u, v));
		Iterator<Pair> iterP = _vertexColCl[u].iterator();
		if (multiple)
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				while (iterV.hasNext())
					if (iterV.next() == v) {
						_toDelete_u.add(_pair);
						break;
					} // TODO: check this break!!
			}
		else {
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				found = false;
				if (_pair.to == k_up) {
					newStableSet1 = new ColorClass();
					newStableSet2 = new ColorClass();
					while (iterV.hasNext()) {
						x = iterV.next();
						if (x == v) {
							_toDelete_u.add(_pair);
							found = true;
						}
						if (x != u)
							newStableSet2.vertices.add(x);
						if (x != v)
							newStableSet1.vertices.add(x);
					}
					if (found) {
						if (newStableSet1 != null && newStableSet1.vertices != null
								&& newStableSet1.vertices.size() > 0) {
							size = newStableSet1.vertices.size();
							_newPair = new Pair(noOfCreatedClasses, size);
							iterV = newStableSet1.vertices.iterator();
							while (iterV.hasNext()) {
								x = iterV.next();
								if (x != u)
									_vertexColCl[x].add(_newPair);
							}
							_colorClasses.put(noOfCreatedClasses, newStableSet1);
							_toAdd_u.add(_newPair);
							noOfCreatedClasses++;
						}
						if (newStableSet2 != null && newStableSet2.vertices != null
								&& newStableSet2.vertices.size() > 0) {
							size = newStableSet2.vertices.size();
							_newPair = new Pair(noOfCreatedClasses, size);
							iterV = newStableSet2.vertices.iterator();
							while (iterV.hasNext()) {
								x = iterV.next();
								_vertexColCl[x].add(_newPair);
							}
							_colorClasses.put(noOfCreatedClasses, newStableSet2);
							noOfCreatedClasses++;
						}

					}
				} else
					while (iterV.hasNext()) {
						x = iterV.next();
						if (x == v) {
							_toDelete_u.add(_pair);
							break;
						}
					}
			}
		}

		if (_toAdd_u != null) {
			iterP = _toAdd_u.iterator();
			while (iterP.hasNext()) {
				_pair = iterP.next();
				_vertexColCl[u].add(_pair);
			}
		}

		if (_toDelete_u != null) {
			iterP = _toDelete_u.iterator();
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				while (iterV.hasNext()) {
					x = iterV.next();
					RemovePairFromList(_vertexColCl[x], _pair);// TODO: check!!
				}
				_colorClasses.remove((Integer) id);
			}
		}

		RMP _rmp = new RMP(noPb, _noVertices, _vertexColCl, _diffCol, _sameCol, _colorClasses, "add_edge", u, v);
		return _rmp;
	}

	public static boolean checkStableSet(boolean characteristic[]) {
		int n = characteristic.length;
		for (int i = 0; i < n; i++)
			if (characteristic[i])
				for (int j = i; j < n; j++) {
					if (characteristic[j] && adjacency[i][j])
						return false;
				}
		return true;
	}

	public static boolean checkStableSet(ColorClass newClass) {

		boolean[] characteristic = new boolean[n];
		int i;
		Iterator<Integer> iter = newClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
			characteristic[i] = true;
		}
		return checkStableSet(characteristic);
	}

	public static boolean isStable(int[] clustersV, boolean[][] adjacency, boolean[] charColClass, int v) {
		// using a characteristic vector
		int n = charColClass.length;
		for (int i = 0; i < n; i++)
			if ((charColClass[i] && adjacency[i][v]) || (charColClass[i] && (clustersV[i] == clustersV[v])))
				return false;
		return true;
	}

	public static boolean[] characteristicV(ColorClass colClass, int n) {
		boolean[] _characteristicV = new boolean[n];
		Iterator<Integer> iter = colClass.vertices.iterator();
		int i, t;
		while (iter.hasNext()) {
			i = iter.next().intValue();
			_characteristicV[i] = true;
		}
		return _characteristicV;
	}

	public static GRBModel buildModel(GRBEnv env, RMP rmp, int p) throws GRBException {
		GRBModel model = new GRBModel(env);
		GRBLinExpr lin_expr, objFunction = new GRBLinExpr();
		GRBVar var, var1;
		Iterator<Pair> iterV;
		Iterator<Entry<Integer, ColorClass>> iterVarCoal;
		int id;
		long buildTime = System.nanoTime();

		// Variables and number of colors constraint:
		lin_expr = new GRBLinExpr();
		var = model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "z");
		lin_expr.addTerm(1, var);
		if (rmp.colorClasses != null && rmp.colorClasses.size() > 0) {
			iterVarCoal = rmp.colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				var1 = model.addVar(0, GRB.INFINITY, 1, GRB.CONTINUOUS, "x_" + pairE.getKey());
				lin_expr.addTerm(1, var1);
			}
		}
		model.addConstr(lin_expr, GRB.EQUAL, p, "p-coloring");
		model.update();

		// The remaining constraints:
		for (int u = 0; u < n; u++) {
			lin_expr = new GRBLinExpr();
			var = model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "z_" + u);// slack variables
			lin_expr.addTerm(1, var);
			if (rmp.vertexColCl[u] != null) {
				iterV = rmp.vertexColCl[u].iterator();
				while (iterV.hasNext()) {
					id = iterV.next().from;
					if (model.getVarByName("x_" + id) == null)
						System.out.println("Null var, id: " + id);
					lin_expr.addTerm(1, model.getVarByName("x_" + id));
				}
				model.addConstr(lin_expr, GRB.EQUAL, 1.0, "Vertex_" + u);
			}
		}

		model.update();
		if (rmp.colorClasses != null && rmp.colorClasses.size() > 0) {
			iterVarCoal = rmp.colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				objFunction.addTerm(pairE.getValue().vertices.size(), model.getVarByName("x_" + pairE.getKey()));
			}
		}
		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		model.update();
		System.out.println("RMP model building time: " + (System.nanoTime() - buildTime) * 1e-9);
		return model;
	}

	public static GRBModel solveRMP(String fileName, RMP rmp, int p, int pbNo, int poolSize) throws GRBException {
		// model.write(path + "/results/" + fileName + "/model_pb_A_" + pbNo + ".lp");
		double[] alpha = new double[n], alphaNew = new double[n];
		ColorClass[] newStableSet = null;
		long start = System.nanoTime(), auxTime, subPrSolvingTime = System.nanoTime();
		int h = 0, optStat;
		double rmpOpt = -1, beta;
		boolean flag = false;
		GRBEnv env = new GRBEnv();
		GRBModel model = buildModel(env, rmp, p);
		// if (pbNo == 0)
		// model.write(path + "/results/" + fileName + "/model_pb_AYY_root" + pbNo +
		// ".lp");
		do {
			model.set(GRB.IntParam.Method, 0); // 0 = primal
			model.set(GRB.IntParam.OutputFlag, 0);
			model.update();
			auxTime = System.nanoTime();
			model.optimize();// solve the RMP
			optStat = model.get(GRB.IntAttr.Status);
			System.out.println("______________________________________________");
			System.out.println("RMP (problem " + pbNo + ") solving time in step " + h + " is: "
					+ formSec((System.nanoTime() - auxTime) * 1e-9));
			rmp.mStatus = optStat;
			System.out.println("STATUS: " + optStat);
			if (optStat == GRB.Status.OPTIMAL) {
				rmpOpt = model.get(DoubleAttr.ObjVal);
				System.out.println("RMP_opt: " + rmpOpt + " (#vars: " + model.getVars().length + ", #constrs: "
						+ model.getConstrs().length + ")");
				// get the dual variables in order to build the subproblem:
				for (int v = 0; v < n; v++)
					if (model.getConstrByName("Vertex_" + v) != null) {
						alphaNew[v] = model.getConstrByName("Vertex_" + v).get(GRB.DoubleAttr.Pi);
						alpha[v] = 1 - alphaNew[v];
					}
				beta = model.getConstrByName("p-coloring").get(GRB.DoubleAttr.Pi);
				System.out.println("Beta: " + beta);
				// build the subproblem:
				auxTime = System.nanoTime();
				SubProblem _subProblem = new SubProblem(env, fileName, rmp, pbNo, adjacency, alpha, n, h, k_down, k_up,
						multiple);
				auxTime = (System.nanoTime() - auxTime);
				subPrSolvingTime = System.nanoTime();
				newStableSet = _subProblem.solvePool(fileName, n, precisionRC, beta, adjacency, h, pbNo, poolSize,
						subproblemVerbosity);
				subPrSolvingTime = (System.nanoTime() - subPrSolvingTime);
				System.out.println("SubPb step " + h + " | build_time: " + formSec(auxTime * 1e-9) + "s | solve_time: "
						+ formSec(subPrSolvingTime * 1e-9) + "s | elapsed_time: "
						+ formSec((System.nanoTime() - start) * 1e-9) + "s");
				flag = false;
				if (newStableSet != null)
					for (int q = 0; q < newStableSet.length; q++) {
						if (checkStableSets) {
							if (newStableSet[q] != null)
								if (addClassSelectiveCheckAll(rmp, model, newStableSet[q], subproblemVerbosity,
										beta) != null)
									flag = true;
						} else if (newStableSet[q] != null) {
							addClass(rmp, model, newStableSet[q], subproblemVerbosity);
							flag = true;
						}
					}
			} else
				System.out.println("Infeasible or unbounded RMP!");
			h++;
		} while (flag && newStableSet != null && optStat != GRB.Status.INFEASIBLE && optStat != GRB.Status.UNBOUNDED
				&& Math.abs(rmpOpt - n) > precisionOpt);
		if (newStableSet != null)
			model.optimize();
		System.out.println("Flag: " + flag + ", status: " + optStat + ", abs_error = " + Math.abs(rmpOpt - n)
				+ ", new stable_set: " + newStableSet + ", CG total execution time = "
				+ formSec((System.nanoTime() - start) * 1e-9));
		rmp.noSubProblems = h;
		return model;
	}

	public static RMP addClassSelectiveCheckAll(RMP rmp, GRBModel model, ColorClass newStableSet, int verbosity,
			double beta) throws GRBException {
		int o = 0;
		ColorClass currentClass;
		if (newStableSet != null && Math.abs(beta - newStableSet.cost) > precisionClassCheck) {
			Iterator<Entry<Integer, ColorClass>> _class = rmp.colorClasses.entrySet().iterator();
			while (_class.hasNext()) {
				// System.out.println("o: " + o);
				// o++;
				HashMap.Entry<Integer, ColorClass> pair = (HashMap.Entry<Integer, ColorClass>) _class.next();
				currentClass = (ColorClass) pair.getValue();
				if (currentClass.check(newStableSet, n)) {
					System.out.println("Already added stable set!");
					newStableSet.toString();
					return null;
				}
			}
		} else {
			System.out.println("NULL!");
			return null;
		}

		int p = newStableSet.vertices.size(), h = 0, u;
		double[] coeffConstr = new double[p + 1];
		GRBConstr[] newConstr = new GRBConstr[p + 1];
		newStableSet.id = noOfCreatedClasses;
		if (verbosity == 1)
			newStableSet.toString();
		boolean[] characteristic = new boolean[n];

		newConstr[0] = model.getConstrByName("p-coloring");
		coeffConstr[0] = 1.0;
		h = 1;
		Iterator<Integer> iter = newStableSet.vertices.iterator();
		while (iter.hasNext()) {
			u = iter.next().intValue();
			characteristic[u] = true;
			rmp.vertexColCl[u].add(new Pair(noOfCreatedClasses, p));
			if (model.getConstrByName("Vertex_" + u) != null)
				newConstr[h] = model.getConstrByName("Vertex_" + u);
			else
				newConstr[h] = model.addConstr(new GRBLinExpr(), GRB.EQUAL, 1.0, "Vertex_" + u);
			coeffConstr[h] = 1.0;
			h++;
		}

		model.update();
		model.addVar(0, GRB.INFINITY, p, GRB.CONTINUOUS, newConstr, coeffConstr, "x_" + noOfCreatedClasses);
		model.update();
		rmp.colorClasses.put(noOfCreatedClasses, newStableSet);
		noOfCreatedClasses++;
		return rmp;
	}

	public static RMP addClass(RMP rmp, GRBModel model, ColorClass newStableSet, int verbosity) throws GRBException {
		int p = newStableSet.vertices.size(), h = 0, u;
		double[] coeffConstr = new double[p + 1];
		GRBConstr[] newConstr = new GRBConstr[p + 1];
		newStableSet.id = noOfCreatedClasses;
		if (verbosity == 1)
			newStableSet.toString();
		boolean[] characteristic = new boolean[n];

		newConstr[0] = model.getConstrByName("p-coloring");
		coeffConstr[0] = 1.0;
		h = 1;
		Iterator<Integer> iter = newStableSet.vertices.iterator();
		while (iter.hasNext()) {
			u = iter.next().intValue();
			characteristic[u] = true;
			rmp.vertexColCl[u].add(new Pair(noOfCreatedClasses, p));
			if (model.getConstrByName("Vertex_" + u) != null)
				newConstr[h] = model.getConstrByName("Vertex_" + u);
			else
				newConstr[h] = model.addConstr(new GRBLinExpr(), GRB.EQUAL, 1.0, "Vertex_" + u);
			coeffConstr[h] = 1.0;
			h++;
		}

		model.update();
		model.addVar(0, GRB.INFINITY, p, GRB.CONTINUOUS, newConstr, coeffConstr, "x_" + noOfCreatedClasses);
		model.update();
		rmp.colorClasses.put(noOfCreatedClasses, newStableSet);
		noOfCreatedClasses++;
		return rmp;
	}

	public static void integerSolution(GRBModel _model) throws GRBException {
		boolean isInteger = true;
		int h, hh;
		double val;

		GRBVar[] vars = _model.getVars();
		GRBVar var;
		String varName;
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('x');
			if (h != -1) {
				hh = Integer.valueOf(varName.substring(h + 1));
				val = var.get(GRB.DoubleAttr.X);
				if (Math.abs(val) > 1e-7 && Math.abs(1 - val) > 1e-7) {
					System.out.println("Non integral solution, x" + hh + " = " + val);
					isInteger = false;
					break;
				}
			}
		}
		if (isInteger)
			System.out.println("INTEGER solution.");
	}

	public static Pair branchingMehrotra(RMP rmp, GRBModel _model) throws GRBException {
		Pair pair = new Pair();
		Iterator<Integer> _iter1, _iter2;
		ColorClass _class1, _class2, _class;
		int _u = -1, _v = -1, _w = -1, h, hh = -1, _bestId = -1, _id = -1, color = 0;
		int[] colors = new int[n];
		double val, _closestToHalf = 1, _bestVal = -1;
		boolean found = false;
		boolean[] _class1Chr = new boolean[n], _class2Chr = new boolean[n];

		GRBVar[] vars = _model.getVars();
		GRBVar var;
		String varName;
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('_');
			if (h != -1) {
				hh = Integer.valueOf(varName.substring(h + 1));
				val = var.get(GRB.DoubleAttr.X);
				if (Math.abs(val) > 1e-7 && Math.abs(1 - val) > 1e-7 && Math.abs(val - 0.5) < _closestToHalf) {
					_closestToHalf = Math.abs(val - 0.5);
					_bestVal = val;
					_bestId = hh;
				}
				if (Math.abs(1 - val) <= precisionVar) {
					color++;
					_class = rmp.colorClasses.get((Integer) hh);
					Iterator<Integer> iterV = _class.vertices.iterator();
					while (iterV.hasNext()) {
						colors[iterV.next()] = color;
					}
				}
			}
		}
		if (_bestId != -1) {
			System.out.println("Non integral solution, x_" + _bestId + " = " + _bestVal);
			_class1 = rmp.colorClasses.get((Integer) _bestId);
			_class1.toString();
			_u = _class1.vertices.iterator().next().intValue();

			_closestToHalf = 1;
			Iterator<Pair> iterV = rmp.vertexColCl[_u].iterator();
			while (iterV.hasNext()) {
				pair = iterV.next();
				if (pair.from != _bestId) {
					var = _model.getVarByName("x_" + pair.from);
					val = var.get(GRB.DoubleAttr.X);
					if (Math.abs(val) > 1e-7 && Math.abs(1 - val) > 1e-7 && Math.abs(val - 0.5) < _closestToHalf) {
						_closestToHalf = Math.abs(val - 0.5);
						_id = pair.from;
						_bestVal = val;
					}
				}
			}
			_class2 = rmp.colorClasses.get((Integer) _id);
			_class2.toString();

			_iter1 = _class1.vertices.iterator();
			while (_iter1.hasNext())
				_class1Chr[_iter1.next()] = true;
			_iter2 = _class2.vertices.iterator();
			while (_iter2.hasNext())
				_class2Chr[_iter2.next()] = true;

			if (_class2.vertices.size() >= _class1.vertices.size()) {
				_iter2 = _class2.vertices.iterator();
				while (_iter2.hasNext()) {
					_v = _iter2.next();
					if (!_class1Chr[_v])
						break;
				}
			} else {
				_iter1 = _class1.vertices.iterator();
				while (_iter1.hasNext()) {
					_v = _iter1.next();
					if (!_class2Chr[_v])
						break;
				}
			}
		}

		if (_u != -1 && _v != -1)
			System.out.println("Branching on u, v: " + _u + ", " + _v);
		else {
			_v = color;
			eqColNumber = color;
			currentEqColNumber = eqColNumber;
			checkColoring(colors, color);
			System.out.println("Number of colors: " + color);
			for (int u = 0; u < n; u++)
				System.out.println("color[" + u + "] = " + colors[u]);
		}
		pair = new Pair(_u, _v);
		return pair;
	}

	public static void printPairs(ArrayList<Pair> pairList) {
		if (pairList != null && pairList.size() > 0) {
			Iterator<Pair> iterP = pairList.iterator();
			while (iterP.hasNext())
				iterP.next().toString();
		}
	}

	public static boolean checkColoring(int[] colors, int color) {
		int[] cardinality = new int[color];
		for (int u = 0; u < n; u++) {
			for (int v = 0; v < n; v++)
				if (adjacency[u][v] && colors[u] == colors[v]) {
					System.out.println("NOT a coloring! Conflict on " + u + " and " + v);
					return false;
				}
			cardinality[colors[u] - 1]++;
		}
		System.out.println("p: " + p + ", k_up: " + k_up + ", k_down: " + k_down);
		for (int i = 0; i < p; i++) {
			System.out.println("cardinality[" + i + "] = " + cardinality[i]);
			if (cardinality[i] != k_down && cardinality[i] != k_up) {
				System.out.println("NOT an equitable coloring!");
				return false;
			}
		}
		System.out.println("True equitable coloring");
		return true;
	}

	public static void printInitial(RMP _rmp, int _pbNo) {
		System.out.println("******* Problem " + _pbNo + " | No of virtual nodes: " + _rmp.noVirtualVertices
				+ " | Type: " + _rmp.type + "(" + _rmp.u + ", " + _rmp.v + ") | father pb: " + _rmp.fatherProblem
				+ " ******* ");
		System.out.println("Different color vertices: ");
		printPairs(_rmp.diffColNodes);
		System.out.println();
		System.out.println("Same color vertices: ");
		printPairs(_rmp.sameColNodes);
	}

	public static int round(double x) {
		int k = 0;
		k = (int) x;
		if (Math.abs(x - k) > .5)
			k++;
		return k;
	}

	public static void initialize() {
		noOfCreatedClasses = 0;
		noOfStableSets_BK = 0;
		stackRMPb = new Stack<RMP>();
	}

	public static void branchAndPrice(int p) throws GRBException, IOException {
		int pbNo = 0, _mstatus = -1, maxStableSetsPerIteration;
		double crtOpt = 0.0, root_time1 = 0, root_time2 = 0, noOfVariables = 0, rootNoOfVariables = 0,
				_noSubProblems = 0, _rootNoSubProblems = 0;
		boolean found = false;
		long exTime1 = System.nanoTime(), exTime2 = System.nanoTime(), BKTime = System.nanoTime();
		String path = "../data/EqCol/results/" + fileName;
		Pair branchPair;
		GRBModel model;
		initialize();

		multiple = false;
		k_down = Math.floorDiv(n, p);
		if (p * k_down == n) {
			k_up = k_down;
			multiple = true;
		} else
			k_up = k_down + 1;

		maxStableSetsPerIteration = Math.floorDiv(maxNoOfStableSets_BK, k_down);
		System.out.println("p = " + p + ", k_down = " + k_down + ", k_up = " + k_up + ", multiple: " + multiple
				+ ", maximum no. of stable sets/iteration: " + maxStableSetsPerIteration);
		System.out.println("Pool size: " + poolSize + " | p_down: " + p_down + " | p_up: " + p_up);

		BKTime = System.nanoTime();
		stableSetIterator(k_down, k_up, maxStableSetsPerIteration);
		System.out.println("BK time: " + formSec((System.nanoTime() - BKTime) * 1e-9)
				+ " | number of stable sets (BK) = " + noOfStableSets_BK);

		RMP rmp = buildRootProblem();
		stackRMPb.add(rmp);
		currentEqColNumber = -1;
		while (!stackRMPb.isEmpty() && pbNo < n_max && !found) {
			rmp = stackRMPb.pop();
			manageColors(rmp);
			printInitial(rmp, pbNo);
			exTime1 = System.nanoTime();
			model = solveRMP(fileName, rmp, p, pbNo, poolSize);
			System.out.println(
					"******* Solving time for pb. " + pbNo + ": " + formSec((System.nanoTime() - exTime1) * 1e-9)
							+ "| elapsed_time:" + formSec((System.nanoTime() - exTime2) * 1e-9));

			_mstatus = model.get(GRB.IntAttr.Status);
			System.out.println("Status: " + _mstatus);
			if (_mstatus != GRB.Status.INFEASIBLE && _mstatus != GRB.Status.UNBOUNDED
					&& _mstatus != GRB.Status.INF_OR_UNBD) {
				crtOpt = model.get(DoubleAttr.ObjVal);
				if (Math.abs(crtOpt - n) < precisionOpt) {
					if (pbNo == 0) {
						root_time1 = System.nanoTime() - exTime1;
						_rootNoSubProblems = rmp.noSubProblems;
					}
					// model.write(path + "/model_problem_" + pbNo + ".sol");
					noOfVariables += rmp.colorClasses.size();
					_noSubProblems += rmp.noSubProblems;
					System.out.println("#vars (total): " + rmp.colorClasses.size() + "(" + noOfVariables + ") | opt.: "
							+ crtOpt + ", #subpbs (total): " + rmp.noSubProblems + "(" + _noSubProblems + ")");
					branchPair = branchingMehrotra(rmp, model);// TODO
					if (branchPair.from != -1) {
						System.out.println("Branching!");
						stackRMPb.add(buildRMP_AddEdge(rmp, branchPair, pbNo));
						stackRMPb.add(buildRMP_Contraction(rmp, branchPair, pbNo));
					} else {
						model.write(path + "/model_problem_integral_sol_" + pbNo + ".sol");
						System.out.println();
						System.out.println("***************************Integral Solution****************************");
						System.out.println("Number of colors: " + currentEqColNumber);
						break;
					}
				} else {
					System.out.println("No branching!");
					if (pbNo == 0)
						break;
				}
			}
			exTime1 = System.nanoTime() - exTime1;
			if (pbNo == 0) {
				root_time2 = exTime1;
				rootNoOfVariables = rmp.colorClasses.size();
			}
			System.out.println(
					"**************Total (including branching) time for problem " + pbNo + ": " + exTime1 * 1e-9);
			pbNo++;
		}
		exTime2 = System.nanoTime() - exTime2;
		System.out.println();
		System.out.println("***************************END****************************");
		System.out.println();

		System.out.println("Total time: " + formSec(exTime2 * 1e-9) + " s | time per problem: "
				+ formSec(exTime2 * 1e-9 / pbNo) + " s | time per problem (without root): "
				+ formSec((exTime2 - root_time2) * 1e-9 / (pbNo - 1)) + " s");
		System.out.println("Root - time: " + formSec(root_time1 * 1e-9) + " s | total time (including branching): "
				+ formSec(root_time2 * 1e-9) + " s | no of variables: " + rootNoOfVariables);
		System.out.println("Subproblems - #total: " + _noSubProblems + " | #root: " + _rootNoSubProblems
				+ "# per node: " + (_noSubProblems / pbNo) + " | # per node (without root): "
				+ (_noSubProblems - _rootNoSubProblems) / (pbNo - 1));
		System.out.println("***********************************************************");
	}

	public static int searchUpBound(int p_0, int p_up) throws GRBException, IOException {
		int q = p_0;
		while (q + 1 <= p_up) {
			System.out.println("div p_0: " + Math.floorDiv(n, p_0) + " | div q + 1: " + Math.floorDiv(n, q + 1));
			if (Math.floorDiv(n, p_0) == Math.floorDiv(n, q + 1) && Math.floorDiv(n, q + 1) * (q + 1) != n) {
				q++;
			} else
				break;
		}
		return q;
	}

	public static int searchEqChromatic_down(String fileName) throws GRBException, IOException, InterruptedException {
		int p_0 = p_down, p_1 = searchUpBound(p_0, p_up), t;
		System.out.println("Down-coming");
		long time, totalTime = System.nanoTime();
		while (p_1 <= p_up) {
			stagesDown++;
			System.out.println();
			System.out.println();
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			System.out.println("The interval [" + p_0 + ", " + p_1 + "]");
			time = System.nanoTime();
			branchAndPrice(p_1);
			time = (System.nanoTime() - time);
			if (time < minTimeUp)
				minTimeUp = time;
			if (time > maxTimeUp)
				maxTimeUp = time;
			System.out.println("currentEqColNumber :" + currentEqColNumber);
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			if (currentEqColNumber == -1) {
				p_0 = p_1 + 1;
				p_1 = searchUpBound(p_0, p_up);
			} else { // an eq-coloring was found
				writeStageData(totalTime);
				return binarySearch_down(p_0, p_1);
			}
			// Thread.sleep(sleepTime);
			writeStageData(totalTime);
		}
		return -1;
	}

	public static int binarySearch_down(int q_0, int q_1) throws GRBException, IOException {// in q_1 the answer is yes
		if (q_0 == q_1)
			return q_0;
		else {
			int q = Math.floorDiv(q_0 + q_1, 2);
			long time = System.nanoTime();
			branchAndPrice(q);
			time = (System.nanoTime() - time);
			if (time < minTimeUp)
				minTimeUp = time;
			if (time > maxTimeUp)
				maxTimeUp = time;
			if (currentEqColNumber == -1) {
				if (q == q_0)
					return q_1;
				return binarySearch_down(q, q_1);
			} else
				return binarySearch_down(q_0, currentEqColNumber);
		}
	}

	public static int searchEqChromatic_up(String fileName) throws GRBException, IOException, InterruptedException {
		int p_0 = p_down, p_1 = searchUpBound(p_0, p_up), t;
		System.out.println("Up-coming");
		long time, totalTime = System.nanoTime();
		while (p_1 <= p_up) {
			stagesUp++;
			System.out.println();
			System.out.println();
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			System.out.println("The interval [" + p_0 + ", " + p_1 + "]");
			time = System.nanoTime();
			branchAndPrice(p_0);
			time = (System.nanoTime() - time);
			if (time < minTimeUp)
				minTimeUp = time;
			if (time > maxTimeUp)
				maxTimeUp = time;
			System.out.println("currentEqColNumber :" + currentEqColNumber);
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			if (currentEqColNumber == -1) {
				t = binarySearch_up(p_0, p_1);
				if (t > 0) {
					writeStageData(totalTime);
					return t;
				}
			} else { // an eq-coloring was found
				writeStageData(totalTime);
				return p_0;
			}
			p_0 = p_1 + 1;
			p_1 = searchUpBound(p_0, p_up);
			// Thread.sleep(sleepTime);
			writeStageData(totalTime);
		}
		return -1;
	}

	public static int binarySearch_up(int q_0, int q_1) throws GRBException, IOException {// in q_0 the answer is no
		if (q_0 != q_1) {
			int q = Math.floorDiv(q_0 + q_1, 2);
			if ((q_1 - q_0) % 2 == 1)
				q++;
			long time = System.nanoTime();
			branchAndPrice(q);
			time = (System.nanoTime() - time);
			if (time < minTimeUp)
				minTimeUp = time;
			if (time > maxTimeUp)
				maxTimeUp = time;
			if (currentEqColNumber == -1)
				return binarySearch_up(q, q_1);
			else {
				if (q_0 == currentEqColNumber - 1)
					return currentEqColNumber;
				return binarySearch_down(q_0, currentEqColNumber);
			}
		} else
			return 0;

	}

	public static void writeStageData(double totalTime) {
		createFile("../data/EqCol/results/finalSolutions.txt");
		NumberFormat nrformat = NumberFormat.getInstance();
		nrformat.setMaximumFractionDigits(2);
		try (BufferedWriter writer = new BufferedWriter(
				new FileWriter("../data/EqCol/results/" + fileName + "/finalSolutions_" + fileName + ".txt", true))) {
			writer.newLine();
			// writer.newLine();
			// String nLine = "Input file: " + fileName + ", " + n + " vertices" + ", " + m
			// + " edges ("+ (n * (n - 1) / 2 - m) + " non-adjacencies)";
			// writer.write(nLine);
			// writer.newLine();

			String nLine;

			nLine = "Stage: " + stagesUp + ", ";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "max_time: " + nrformat.format(maxTimeUp * 1e-9) + "s, ";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "min_time: " + nrformat.format(minTimeUp * 1e-9) + "s, ";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "average_time: " + nrformat.format((System.nanoTime() - totalTime) * 1e-9 / stagesUp) + "s.";
			System.out.println(nLine);
			writer.write(nLine);

		} catch (IOException ex) {
			ex.printStackTrace();
		}
	}

	public static void main(String[] args) throws GRBException, IOException, InterruptedException {

		// Eligible files: "r1000.5.col"; "le450_25c.col"; "mulsol.i.2.col";
		// "dsjc250.5.col";"dsjc250.1.col" (?); "dsjc500.5.col" (mai greu);
		// "dsjc500.9.col" (?); "inithx.i.2.col" (greu? fii); "inithx.i.3.col"
		// (greu? fii); "flat300_28_0.col" (out of memory fii); "flat1000_60_0.col"
		// (greu fii); "wap07a.col" (greu fii); "wap08a.col" (out of memory fii);
		// "wap04a.col" (out of memory fii); "wap03a.col" (out of memory fii from the
		// begining/BK reduced to 20000 but still very slow);"wap02a.col" (out of memory
		// fii from the
		// begining/BK reduced to 20000 but still very slow); "DSJR500.5.col" (out of
		// memory fii);

		// closed instances:
		// "flat300_28_0.col": [11 - 33]: 11, 12, ..., 27 out, 28?,..., 32?
		// "dsjc250.5.col": [12 - 29]: 12, 13,..., 25 out, 26?,
		// "dsjc250.1.col": [5 - 8]: 5 out, 6?
		// "mulsol.i.2.col": [34 - 36]: 34, 35 out, 36 in
		// "le450_25c.col": [25 - 26]: 25 out, 26?
		// "le450_25d.col": [25 - 26]: 25 out, 26?
		// simplified
		// "inithx.i.2.col": [31 - 35]: 31, 32, 33, 34 out, 35?
		// "inithx.i.3.col": [31 - 35]: 31, 32, 33, 34, 35 out
		// "dsjr500.5.col": [120 - 125]: 120, 121, out, 122 in

		// "dsjc500.1.col": [5 - 13]: 5, 6? 12?
		// "dsjc1000.9.col": [126 - 251]: 126, ..., 215 out 216? **///

		// "wap06a.col": [40 - 41]: 40?
		// "DSJC500.5.col" 13 52
		// "dsjc125.5.col"; 9 18
		// "dsjc1000.1.col";
		// "dsjc500.9.col";// "dsjc250.1.col";//"le450_25d.col";// "dsjc250.5.col";//
		// "le450_25d.col";//
		// "inithx.i.2.col";//
		// "dsjc500.9.col";//
		// "1-Insertions_6.col";//
		// "mulsol.i.2.col";//
		// "DSJR500.5.col";//
		// "wap02a.col";// "flat1000_60_0.col";//
		// "inithx.i.3.col";//
		// "DSJC500.1.col";//
		// "le450_25c.col";// "r1000.5.col";//
		// "latin_square_10.col";//
		// "DSJC500.9.col";// "dsjc500.9.col";// "flat300_28_0.col";//
		// "dsjc1000.9.col";//
		// "dsjc250.1.col";//
		// "dsjc125.5.col";// "dsjc250.1.col"; //
		// "1-FullIns_3.col";//

		// *************

		// "r1000.5.col": 201/ unfinished// 235*
		// "le450_25c.col": 16 unfinished
		// "le450_25d.col": ?
		// "dsjc250.1.col": 6 unfinished
		// "dsjc250.5.col": 26 unfinished
		// "dsjc500.1.col": 6 unfinished
		// "dsjc500.5.col": 36 unfinished
		// "dsjc500.9.col": 123? unfinished
		// "dsjc1000.1.col": 6 unfinished
		// "dsjc1000.5.col": 17, unfinished
		// "dsjc1000.9.col": 201, unfinished
		// "dsjr500.5.col": 120, 121, unfinished
		// "inithx.i.2.col"; 34, unfinished + 35 (liniar);
		// "inithx.i.3.col"; 4, unfinished;
		// "1-Insertions_6.col": ? unfinished
		// "2-Insertions_5.col": ? unfinished
		// "3-Insertions_5.col": -, -
		// "mulsol.i.2.col": 36 ??
		// "latin_square_10.col": - -
		// "flat300_28_0.col": 28, unfinished
		// "wap01a.col": -, -
		// "wap03a.col": -, -
		// "wap04a.col": 18, unfinished
		// "wap07a.col": 26, unfinished
		// "wap08a.col": 15, unfinished
		// "flat1000_50_0.col": 11, unfinished
		// "flat1000_60_0.col": 11, unfinished
		// "flat1000_76_0.col": ?, unfinished
		// "C2000.5.col": 11, unfinished

		// *************

		fileName = "r1000.5.col";
		createDir(path + "results/" + fileName);
		readFile(fileName);
		// createFile(path + "results/finalSolutions.txt");

		stagesUp = 0;
		stagesDown = 0;
		poolSize = 400;
		n_max = 30000;
		verbosity = false;

		subproblemVerbosity = 0;
		checkStableSets = false;

		// milliseconds:
		sleepTime = 5000;
		timeout = 5000;
		initialDFSTimeout = 1000;
		minTimeUp = 1000000000;
		maxTimeUp = -1;

		noOfStableSets_BK = 0;
		maxNoOfStableSets_BK = 10000;

		p_down = 3;
		p_up = 249;

		// searchEqChromatic_down(fileName);
		searchEqChromatic_up(fileName);
		System.out.println("File name: " + fileName);
	}
}