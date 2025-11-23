import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import java.text.NumberFormat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Stack;
import java.util.Map.Entry;

import org.graph4j.Graph;
import org.graph4j.GraphBuilder;
import org.graph4j.clique.DFSCliqueIterator;

import com.gurobi.gurobi.GRB;
import com.gurobi.gurobi.GRBConstr;
import com.gurobi.gurobi.GRBEnv;
import com.gurobi.gurobi.GRBException;
import com.gurobi.gurobi.GRBLinExpr;
import com.gurobi.gurobi.GRBModel;
import com.gurobi.gurobi.GRBVar;
import com.gurobi.gurobi.GRB.DoubleAttr;

public class BranchPrice {

	public static int n, m, Delta;// the order, the size, and the max. degree of the graph;
	public static int noOfCreatedClasses = 0; // number of stable sets created during the execution;
	public static int k_down, k_up; // the cardinalities of stable sets for the current value of p;
	public static int p_down, p_up; // lower and upper bounds for chi_eq - to be initialized;
	public static int noOfStableSets_init, maxNoOfStableSets_init; // number of initial (generated) stables sets and
																	// max. number of such sets;
	public static int subproblemVerbosity, currentEqColNumber, eqColNumber, n_max, bestStageLowerBound, stages = 0;
	public static int poolSize; // the max. number of stable sets added after solving a subproblem;

	public static boolean multiple = true;// true if n is a multiple of p (the current value during binary search);
	public static boolean direction_up = true;// search direction
	public static long initialStableSetsGeneratingTime, minTimeUp, maxTimeUp, minTimeDown, maxTimeDown, avgTime;
	public static boolean[][] adjacency;// adjacency matrix
	public static Stack<RMP> stackRMPb;// the stack containing the problems during the Branch&Price algorithm
	public static HashMap<Integer, ColorClass> initColorClasses; // the initial (generated) color classes

	public static double timeLimit;// time limit in hours;
	public static double precisionRC = 1e-5;// the reduced cost precision
	public static double precisionVar = 1e-7;// the variables precision
	public static double precisionOpt = 1e-9;// the optimum value precision
	public static double precisionClassCheck = 1e-5;// the coloring classes weight precision

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
		}
	}

	@SuppressWarnings("static-access")
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

	@SuppressWarnings("rawtypes")
	public static Graph buildGraph() {
		Graph graph = GraphBuilder.numVertices(n).estimatedNumEdges(m).buildGraph();
		for (int v = 0; v < n; v++) {
			for (int u = 0; u < v; u++) {
				if (!adjacency[u][v]) {
					graph.addEdge(u, v);
				}
			}
		}
		return graph;
	}

	@SuppressWarnings("rawtypes")
	public static Graph buildGraph(double[] weights) {
		Graph graph = GraphBuilder.numVertices(n).estimatedNumEdges(m).buildGraph();
		for (int v = 0; v < n; v++) {
			graph.setVertexWeight(v, weights[v]);
		}
		for (int v = 0; v < n; v++) {
			for (int u = 0; u < v; u++) {
				if (!adjacency[u][v]) {
					graph.addEdge(u, v);
				}
			}
		}
		return graph;
	}

	public static void stableSetIterator(int minSize, int maxSize, int maxStablesPerIter) {
		long DFSTime = System.nanoTime();
		int max = -1, _node;
		var graph = buildGraph();
		initColorClasses = new HashMap<>();
		while (max != 0 && graph.numVertices() >= minSize) {
			int _u, k = 0;
			var cliqueIt = new DFSCliqueIterator(graph, minSize, maxSize, initialStableSetsGeneratingTime);
			int count = 0;
			long t0 = System.currentTimeMillis();
			int[] visited = new int[n];
			while (count < maxStablesPerIter && cliqueIt.hasNext() && noOfStableSets_init < maxNoOfStableSets_init) {
				ColorClass _colCls = new ColorClass(cliqueIt.next(), noOfCreatedClasses);
				_colCls.check(adjacency, n);
				// _colCls.toString();
				initColorClasses.put(noOfCreatedClasses, _colCls);
				noOfCreatedClasses++;
				noOfStableSets_init++;
				Iterator<Integer> itVertex = _colCls.vertices.iterator();
				while (itVertex.hasNext()) {
					_node = itVertex.next();
					visited[_node]++;
				}
				k++;
				count++;
				if (System.currentTimeMillis() - t0 > initialStableSetsGeneratingTime) {
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
			if (max != 0) {
				graph.removeVertex(_u);
			}
		}
	}

	public static HashMap<Integer, ColorClass> hashMLCopy(HashMap<Integer, ColorClass> hMap) {
		HashMap<Integer, ColorClass> mapCopy;
		mapCopy = new HashMap<>();
		for (HashMap.Entry<Integer, ColorClass> entry : hMap.entrySet()) {
			mapCopy.put(entry.getKey(), new ColorClass(entry.getValue()));
		}
		return mapCopy;
	}

	@SuppressWarnings({ "unchecked", "unchecked" })
	public static ArrayList<Pair>[] arrayLIntCopy(ArrayList<Pair>[] aList) {
		// create a deep copy of aList
		int q;
		ArrayList<Pair>[] newList;
		newList = null;
		ArrayList<Pair> listV;
		Pair _pair;
		if (aList != null && aList.length > 0) {
			q = aList.length;
			newList = new ArrayList[q];
			for (int i = 0; i < q; i++) {
				listV = new ArrayList<>();
				if (aList[i] != null) {
					Iterator<Pair> iterV = aList[i].iterator();
					while (iterV.hasNext()) {
						_pair = iterV.next();
						listV.add(new Pair(_pair.from, _pair.to));
					}
				}
				newList[i] = listV;
			}
		}
		return newList;
	}

	public static Pair[] arrayPCopy(Pair[] aList) {
		// create a deep copy of aList
		Pair[] newList = null;
		if (aList != null) {
			int q = aList.length;
			newList = new Pair[q];
			for (int i = 0; i < q; i++) {
				if (aList[i] != null) {
					newList[i] = new Pair(aList[i].from, aList[i].to);
				}
			}
		}
		return newList;
	}

	public static ArrayList<Pair> arrayLPairCopy(ArrayList<Pair> pairList) {
		// create a deep copy of pairList
		ArrayList<Pair> newPairList;
		Pair _pair;

		newPairList = new ArrayList<>();
		if (pairList != null) {
			Iterator<Pair> iterV = pairList.iterator();
			while (iterV.hasNext()) {
				_pair = iterV.next();
				newPairList.add(new Pair(_pair.from, _pair.to));
			}
		}
		return newPairList;
	}

	public static void listColorClasses(HashMap<Integer, ColorClass> _colorClasses) {
		if (_colorClasses != null) {
			System.out.println();
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
		ArrayList<ColorClass> _coloring;
		_coloring = new ArrayList<>();

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
			if (i == 0 && j != 0) {
				_colors[_u] = _colors[_v];
			}
			if (i != 0 && j == 0) {
				_colors[_v] = _colors[_u];
			}
			if (i != 0 && j != 0 && i < j) {
				for (int w = 0; w < n; w++) {
					if (_colors[w] == j) {
						_colors[w] = i;
					}
				}
			}
			if (i != 0 && j != 0 && i > j) {
				for (int w = 0; w < n; w++) {
					if (_colors[w] == i) {
						_colors[w] = j;
					}
				}
			}
		}
		i = 0;
		for (int w = 0; w < n; w++) {
			if (_colors[w] != 0) {
				i++;
			}
		}
		System.out.println("Number of colors: " + col + ", number of colored vertices: " + i);

		for (int c = 1; c <= col; c++) {
			ColorClass _class = new ColorClass();
			for (int u = 0; u < n; u++) {
				if (_colors[u] == c) {
					_class.vertices.add(u);
				}
			}
			_class.id = c;
			_coloring.add(_class);
		}
		Iterator<ColorClass> _iterC = _coloring.iterator();
		while (_iterC.hasNext()) {
			_iterC.next().toString();
		}
		return _colors;
	}

	public static void RemovePairFromList(ArrayList<Pair> _list, Pair _pair) {
		Pair pair;
		if (_list != null) {
			Iterator<Pair> iterP = _list.iterator();
			while (iterP.hasNext()) {
				pair = iterP.next();
				if (_pair.from == pair.from && _pair.to == pair.to) {
					iterP.remove();
					break;
				}
			}
		}
	}

	public static RMP buildRootProblem() throws GRBException {
		// Build the initial LP model for the Equitable Coloring Problem (EqCP)
		long rootPbBuildTime = System.nanoTime();
		ArrayList<Pair>[] _vertexColCl = new ArrayList[n];
		Pair[] _vertexPartialCol = new Pair[n];
		ArrayList<Pair> _sameCol, _diffCol;
		HashMap<Integer, ColorClass> _colorClasses, _partialCol;

		ColorClass _class;
		int id, size;

		_partialCol = new HashMap<>();
		_colorClasses = new HashMap<>();
		_sameCol = new ArrayList<>();
		_diffCol = new ArrayList<>();

		if (initColorClasses != null && !initColorClasses.isEmpty()) {
			_colorClasses = initColorClasses;
			for (int u = 0; u < n; u++) {
				_vertexColCl[u] = new ArrayList<>();
			}

			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				id = pairE.getKey();
				_class = (ColorClass) pairE.getValue();
				size = _class.vertices.size();

				Iterator<Integer> iterV = _class.vertices.iterator();
				while (iterV.hasNext()) {
					_vertexColCl[iterV.next()].add(new Pair(id, size));
				}
			}
		}

		ColorClass stable;
		HashSet<Integer> set;
		Pair _pair;

		for (int u = 0; u < n; u++) {
			_pair = new Pair(u, 1);
			_vertexPartialCol[u] = _pair;
			set = new HashSet<>();
			set.add((Integer) u);
			stable = new ColorClass(set);
			stable.size = 1;
			stable.id = u;
			_partialCol.put((Integer) u, stable);
		}

		RMP _rmp = new RMP(-1, n, _vertexColCl, _diffCol, _sameCol, _colorClasses, _vertexPartialCol, _partialCol,
				"root", -1, -1);
		System.out.println(
				"Build time for the root problem: " + formSec((System.nanoTime() - rootPbBuildTime) * 1e-9) + "s");
		return _rmp;
	}

	// TODO: stable sets containing vertex u but not v could be extended with v (and
	// viceversa): if the stable set has cardinality k_up < k_down
	public static RMP buildRMP_Contraction(RMP rmp, Pair pair, int noPb) throws GRBException {
		HashMap<Integer, ColorClass> _colorClasses = hashMLCopy(rmp.colorClasses);
		ArrayList<Pair> _sameCol = arrayLPairCopy(rmp.sameColNodes), _diffCol = arrayLPairCopy(rmp.diffColNodes),
				_toDelete_u, _toDelete_v;
		ArrayList<Pair>[] _vertexColCl = arrayLIntCopy(rmp.vertexColCl);
		int u = pair.from, v = pair.to, x, id, _noVertices = rmp.noVirtualVertices;
		Pair _pair;
		ColorClass stableSet;
		boolean found;

		_toDelete_u = new ArrayList<>();
		_toDelete_v = new ArrayList<>();

		_sameCol.add(new Pair(u, v));

		Iterator<Pair> iterP = _vertexColCl[u].iterator();
		while (iterP.hasNext()) {
			_pair = iterP.next();
			id = _pair.from;
			stableSet = _colorClasses.get((Integer) id);
			Iterator<Integer> iterV = stableSet.vertices.iterator();
			found = false;
			while (iterV.hasNext()) {
				if (iterV.next() == v) {
					found = true;
					break;
				}
			}
			if (!found) {
				_toDelete_u.add(_pair);
			}
		}
		iterP = _vertexColCl[v].iterator();
		while (iterP.hasNext()) {
			_pair = iterP.next();
			id = _pair.from;
			stableSet = _colorClasses.get((Integer) id);
			Iterator<Integer> iterV = stableSet.vertices.iterator();
			found = false;
			while (iterV.hasNext()) {
				if (iterV.next() == u) {
					found = true;
					break;
				}
			}
			if (!found) {
				_toDelete_v.add(_pair);
			}
		}

		if (!_toDelete_v.isEmpty()) {
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
		if (!_toDelete_v.isEmpty()) {
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

		return new RMP(noPb, _noVertices - 1, _vertexColCl, _diffCol, _sameCol, _colorClasses, "contract_pair", u, v);
	}

	public static RMP buildRMP_AddEdge(RMP rmp, Pair pair, int noPb) throws GRBException {
		HashMap<Integer, ColorClass> _colorClasses = hashMLCopy(rmp.colorClasses);
		ArrayList<Pair> _sameCol = arrayLPairCopy(rmp.sameColNodes), _diffCol = arrayLPairCopy(rmp.diffColNodes),
				_toDelete_u, _toAdd_u;
		ArrayList<Pair>[] _vertexColCl = arrayLIntCopy(rmp.vertexColCl);
		int u = pair.from, v = pair.to, x, id, _noVertices = rmp.noVirtualVertices, size;
		boolean found;
		Pair _pair, _newPair;
		ColorClass stableSet, newStableSet1, newStableSet2;
		_toDelete_u = new ArrayList<>();
		_toAdd_u = new ArrayList<>();

		_diffCol.add(new Pair(u, v));
		Iterator<Pair> iterP = _vertexColCl[u].iterator();
		if (multiple) {
			while (iterP.hasNext()) {
				_pair = iterP.next();
				id = _pair.from;
				stableSet = _colorClasses.get((Integer) id);
				Iterator<Integer> iterV = stableSet.vertices.iterator();
				while (iterV.hasNext()) {
					if (iterV.next() == v) {
						_toDelete_u.add(_pair);
						break;
					} // TODO: check this break!!
				}
			}
		} else {
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
						if (x != u) {
							newStableSet2.vertices.add(x);
						}
						if (x != v) {
							newStableSet1.vertices.add(x);
						}
					}
					if (found) {
						if (!newStableSet1.vertices.isEmpty()) {
							size = newStableSet1.vertices.size();
							_newPair = new Pair(noOfCreatedClasses, size);
							iterV = newStableSet1.vertices.iterator();
							while (iterV.hasNext()) {
								x = iterV.next();
								if (x != u) {
									_vertexColCl[x].add(_newPair);
								}
							}
							_colorClasses.put(noOfCreatedClasses, newStableSet1);
							_toAdd_u.add(_newPair);
							noOfCreatedClasses++;
						}
						if (!newStableSet2.vertices.isEmpty()) {
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
				} else {
					while (iterV.hasNext()) {
						x = iterV.next();
						if (x == v) {
							_toDelete_u.add(_pair);
							break;
						}
					}
				}
			}
		}

		if (!_toAdd_u.isEmpty()) {
			iterP = _toAdd_u.iterator();
			while (iterP.hasNext()) {
				_pair = iterP.next();
				_vertexColCl[u].add(_pair);
			}
		}

		if (!_toDelete_u.isEmpty()) {
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

		return new RMP(noPb, _noVertices, _vertexColCl, _diffCol, _sameCol, _colorClasses, "add_edge", u, v);
	}

	public static boolean checkStableSet(boolean characteristic[]) {
		int _n;
		_n = characteristic.length;
		for (int i = 0; i < _n; i++) {
			if (characteristic[i]) {
				for (int j = i; j < _n; j++) {
					if (characteristic[j] && adjacency[i][j]) {
						return false;
					}
				}
			}
		}
		return true;
	}

	public static boolean checkStableSet(ColorClass newClass) {

		boolean[] characteristic = new boolean[n];
		int i;
		Iterator<Integer> iter = newClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next();
			characteristic[i] = true;
		}
		return checkStableSet(characteristic);
	}

	public static boolean isStable(int[] clustersV, boolean[][] adjacency, boolean[] charColClass, int v) {
		int _n;
		_n = charColClass.length;
		for (int i = 0; i < _n; i++) {
			if ((charColClass[i] && adjacency[i][v]) || (charColClass[i] && (clustersV[i] == clustersV[v]))) {
				return false;
			}
		}
		return true;
	}

	public static boolean[] characteristicV(ColorClass colClass, int n) {
		boolean[] _characteristicV = new boolean[n];
		Iterator<Integer> iter = colClass.vertices.iterator();
		int i;
		while (iter.hasNext()) {
			i = iter.next();
			_characteristicV[i] = true;
		}
		return _characteristicV;
	}

	public static GRBModel buildModel(GRBEnv env, RMP rmp, int p, int pbNo) throws GRBException {
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
		if (rmp.colorClasses != null && !rmp.colorClasses.isEmpty()) {
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
					if (model.getVarByName("x_" + id) == null) {
						System.out.println("Null var, id: " + id);
					}
					lin_expr.addTerm(1, model.getVarByName("x_" + id));
				}
				model.addConstr(lin_expr, GRB.EQUAL, 1.0, "Vertex_" + u);
			}
		}

		model.update();
		if (rmp.colorClasses != null && !rmp.colorClasses.isEmpty()) {
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
		// model.write(path + "/results/" + fileName + "/model_pb_" + pbNo + ".lp");
		return model;
	}

	public static GRBModel solveRMP(String fileName, RMP rmp, int p, int pbNo, int poolSize, long time)
			throws GRBException {
		double[] alpha = new double[n], alphaNew = new double[n];
		ColorClass[] newStableSet = null;
		long start = System.nanoTime(), auxTime, subPrSolvingTime;
		int h = 0, optStat;
		double rmpOpt = -1, beta;
		boolean flag = false;
		GRBEnv env = new GRBEnv();
		GRBModel model = buildModel(env, rmp, p, pbNo);
		do {
			model.set(GRB.IntParam.Method, 0); // 0 = primal
			model.set(GRB.IntParam.OutputFlag, 0);
			model.update();
			auxTime = System.nanoTime();
			model.set(GRB.DoubleParam.TimeLimit, timeLimit * 3600 - (System.nanoTime() - time) * 1e-9);
			model.optimize();// solve the RMP
			optStat = model.get(GRB.IntAttr.Status);
			System.out.println();
			System.out.println("Step " + h + ", RMP (problem " + pbNo + ") solving time: "
					+ formSec((System.nanoTime() - auxTime) * 1e-9) + "s");
			rmp.mStatus = optStat;
			System.out.println("STATUS: " + optStat);
			if (optStat == GRB.Status.OPTIMAL) {
				rmpOpt = model.get(DoubleAttr.ObjVal);
				System.out.println("RMP_opt: " + rmpOpt + " (#vars: " + model.getVars().length + ", #constrs: "
						+ model.getConstrs().length + ")");
				// get the dual variables in order to build the subproblem:
				for (int v = 0; v < n; v++) {
					if (model.getConstrByName("Vertex_" + v) != null) {
						alphaNew[v] = model.getConstrByName("Vertex_" + v).get(GRB.DoubleAttr.Pi);
						alpha[v] = 1 - alphaNew[v];
					}
				}
				beta = model.getConstrByName("p-coloring").get(GRB.DoubleAttr.Pi);
				// build the subproblem:
				auxTime = System.nanoTime();
				SubProblem _subProblem = new SubProblem(env, fileName, rmp, pbNo, adjacency, alpha, n, h, k_down, k_up,
						multiple);
				auxTime = (System.nanoTime() - auxTime);
				subPrSolvingTime = System.nanoTime();
				newStableSet = _subProblem.solvePool(fileName, n, precisionRC, beta, adjacency, h, pbNo, poolSize,
						subproblemVerbosity, timeLimit, time);
				subPrSolvingTime = (System.nanoTime() - subPrSolvingTime);
				System.out.println("SubPb step " + h + " | build_time: " + formSec(auxTime * 1e-9) + "s | solve_time: "
						+ formSec(subPrSolvingTime * 1e-9) + "s | elapsed_time: "
						+ formSec((System.nanoTime() - start) * 1e-9) + "s");
				flag = false;
				if (newStableSet != null && checkTime(time)) {
					for (var colClass : newStableSet)
						if (colClass != null) {
							addClass(rmp, model, colClass, subproblemVerbosity);
							flag = true;
						}
				}
			} else {
				System.out.println("Infeasible/unbounded RMP! or times's out!!");
			}
			h++;
		} while (flag && newStableSet != null && optStat != GRB.Status.INFEASIBLE && optStat != GRB.Status.UNBOUNDED
				&& Math.abs(rmpOpt - n) > precisionOpt && checkTime(time));

		System.out.println("Flag: " + flag + ", status: " + optStat + ", abs_error = " + Math.abs(rmpOpt - n)
				+ ", CG total execution time = " + formSec((System.nanoTime() - start) * 1e-9));
		rmp.noSubProblems = h;

		if (!checkTime(time)) {
			newStableSet = null;
			return null;
		}
		if (newStableSet != null) {
			model.optimize();
		}
		return model;
	}

	public static RMP addClass(RMP rmp, GRBModel model, ColorClass newStableSet, int verbosity) throws GRBException {
		int q, h, u;
		q = newStableSet.vertices.size();
		double[] coeffConstr = new double[q + 1];
		GRBConstr[] newConstr = new GRBConstr[q + 1];
		newStableSet.id = noOfCreatedClasses;
		if (verbosity == 1) {
			newStableSet.toString();
		}

		newConstr[0] = model.getConstrByName("p-coloring");
		coeffConstr[0] = 1.0;
		h = 1;
		Iterator<Integer> iter = newStableSet.vertices.iterator();
		while (iter.hasNext()) {
			u = iter.next();
			rmp.vertexColCl[u].add(new Pair(noOfCreatedClasses, q));
			if (model.getConstrByName("Vertex_" + u) != null) {
				newConstr[h] = model.getConstrByName("Vertex_" + u);
			} else {
				newConstr[h] = model.addConstr(new GRBLinExpr(), GRB.EQUAL, 1.0, "Vertex_" + u);
			}
			coeffConstr[h] = 1.0;
			h++;
		}

		model.update();
		model.addVar(0, GRB.INFINITY, q, GRB.CONTINUOUS, newConstr, coeffConstr, "x_" + noOfCreatedClasses);
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
		String varName;
		for (var var_ : vars) {
			varName = var_.get(GRB.StringAttr.VarName);
			h = varName.indexOf('x');
			if (h != -1) {
				hh = Integer.parseInt(varName.substring(h + 1));
				val = var_.get(GRB.DoubleAttr.X);
				if (Math.abs(val) > 1e-7 && Math.abs(1 - val) > 1e-7) {
					System.out.println("Non integral solution, x" + hh + " = " + val);
					isInteger = false;
					break;
				}
			}
		}
		if (isInteger) {
			System.out.println("INTEGER solution.");
		}
	}

	public static Pair branchingMehrotra(RMP rmp, GRBModel _model) throws GRBException {
		Pair pair;
		Iterator<Integer> _iter1, _iter2;
		ColorClass _class1, _class2, _class;
		int _u = -1, _v = -1, h, hh, _bestId = -1, _id = -1, color = 0;
		int[] colors = new int[n];
		double val, _closestToHalf = 1, _bestVal = -1;
		boolean[] _class1Chr = new boolean[n], _class2Chr = new boolean[n];

		GRBVar[] vars = _model.getVars();
		GRBVar var;
		String varName;
		for (var var_ : vars) {
			varName = var_.get(GRB.StringAttr.VarName);
			h = varName.indexOf('_');
			if (h != -1) {
				hh = Integer.parseInt(varName.substring(h + 1));
				val = var_.get(GRB.DoubleAttr.X);
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
			_u = _class1.vertices.iterator().next();

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
						// _bestVal = val;
					}
				}
			}
			_class2 = rmp.colorClasses.get((Integer) _id);
			_class2.toString();

			_iter1 = _class1.vertices.iterator();
			while (_iter1.hasNext()) {
				_class1Chr[_iter1.next()] = true;
			}
			_iter2 = _class2.vertices.iterator();
			while (_iter2.hasNext()) {
				_class2Chr[_iter2.next()] = true;
			}

			if (_class2.vertices.size() >= _class1.vertices.size()) {
				_iter2 = _class2.vertices.iterator();
				while (_iter2.hasNext()) {
					_v = _iter2.next();
					if (!_class1Chr[_v]) {
						break;
					}
				}
			} else {
				_iter1 = _class1.vertices.iterator();
				while (_iter1.hasNext()) {
					_v = _iter1.next();
					if (!_class2Chr[_v]) {
						break;
					}
				}
			}
		}

		if (_u != -1 && _v != -1) {
			System.out.println("Branching on u, v: " + _u + ", " + _v);
		} else {
			_v = color;
			eqColNumber = currentEqColNumber;
			currentEqColNumber = color;
			checkColoring(colors, color);
			System.out.println("Number of colors: " + color);
			for (int u = 0; u < n; u++) {
				System.out.println("color[" + u + "] = " + colors[u]);
			}
		}
		pair = new Pair(_u, _v);
		return pair;
	}

	public static void printPairs(ArrayList<Pair> pairList) {
		if (pairList != null && !pairList.isEmpty()) {
			Iterator<Pair> iterP = pairList.iterator();
			while (iterP.hasNext()) {
				iterP.next().toString();
			}
		}
	}

	public static boolean checkColoring(int[] colors, int color) {
		int[] cardinality = new int[color];
		for (int u = 0; u < n; u++) {
			for (int v = 0; v < n; v++) {
				if (adjacency[u][v] && colors[u] == colors[v]) {
					System.out.println("NOT a coloring! Conflict on " + u + " and " + v);
					return false;
				}
			}
			cardinality[colors[u] - 1]++;
		}
		System.out.println("p: " + color + ", k_up: " + k_up + ", k_down: " + k_down);
		for (int i = 0; i < color; i++) {
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
		System.out.println("Problem " + _pbNo + " | No of virtual vertices: " + _rmp.noVirtualVertices + " | Type: "
				+ _rmp.type + "(" + _rmp.u + ", " + _rmp.v + ") | father pb: " + _rmp.fatherProblem);
		System.out.println("Different color vertices: ");
		if (_rmp.diffColNodes != null && !_rmp.diffColNodes.isEmpty()) {
			printPairs(_rmp.diffColNodes);
		}
		System.out.println();
		System.out.println("Same color vertices: ");
		if (_rmp.sameColNodes != null && !_rmp.sameColNodes.isEmpty()) {
			printPairs(_rmp.sameColNodes);
		}
		System.out.println();
	}

	public static int round(double x) {
		int k = (int) x;
		if (Math.abs(x - k) > .5) {
			k++;
		}
		return k;
	}

	public static void initialize() {
		noOfCreatedClasses = 0;
		noOfStableSets_init = 0;
		stackRMPb = new Stack<>();
		multiple = false;
		maxNoOfStableSets_init = 10000;
		noOfStableSets_init = 0;
		initialStableSetsGeneratingTime = 1000;
		minTimeUp = 1000000000;
		poolSize = 400;

	}

	public static int branchAndPrice(int p, long time) throws GRBException, IOException {
		int pbNo = 0, _mstatus, maxStableSetsPerIteration;
		double crtOpt, noOfVariables = 0, _noSubProblems = 0;
		boolean found = false;
		long exTime1, exTime2 = System.nanoTime(), initStableSetsTime;
		Pair branchPair;
		GRBModel model;
		initialize();

		k_down = Math.floorDiv(n, p);
		if (p * k_down == n) {
			k_up = k_down;
			multiple = true;
		} else
			k_up = k_down + 1;

		maxStableSetsPerIteration = Math.floorDiv(maxNoOfStableSets_init, k_down);
		System.out.println("Call B&P with p = " + p + " | k_down = " + k_down + " | k_up = " + k_up + " | multiple: "
				+ multiple + " | max. #stables/iteration: " + maxStableSetsPerIteration + " | pool size: " + poolSize
				+ " | p_down: " + p_down + " | p_up: " + p_up);

		initStableSetsTime = System.nanoTime();
		stableSetIterator(k_down, k_up, maxStableSetsPerIteration);
		System.out.println(
				"Initial stable sets generating time: " + formSec((System.nanoTime() - initStableSetsTime) * 1e-9)
						+ " | number of initial stable sets = " + noOfStableSets_init);

		RMP rmp = buildRootProblem();
		stackRMPb.add(rmp);
		currentEqColNumber = -1;
		while (!stackRMPb.isEmpty() && pbNo < n_max && !found && checkTime(time)) {
			rmp = stackRMPb.pop();
			manageColors(rmp);
			System.out.println();
			printInitial(rmp, pbNo);
			exTime1 = System.nanoTime();
			model = solveRMP(fileName, rmp, p, pbNo, poolSize, time);
			if (checkTime(time) && model != null) {
				System.out.println("Solving time for pb. " + pbNo + ": " + formSec((System.nanoTime() - exTime1) * 1e-9)
						+ " | elapsed_time: " + formSec((System.nanoTime() - exTime2) * 1e-9));

				_mstatus = model.get(GRB.IntAttr.Status);
				System.out.println("Status: " + _mstatus);
				if (_mstatus != GRB.Status.INFEASIBLE && _mstatus != GRB.Status.UNBOUNDED
						&& _mstatus != GRB.Status.INF_OR_UNBD) {
					crtOpt = model.get(DoubleAttr.ObjVal);
					if (Math.abs(crtOpt - n) < precisionOpt) {
						noOfVariables += rmp.colorClasses.size();
						_noSubProblems += rmp.noSubProblems;
						System.out.println("#vars (total): " + rmp.colorClasses.size() + "(" + noOfVariables
								+ ") | opt.: " + crtOpt + ", #subpbs (total): " + rmp.noSubProblems + "("
								+ _noSubProblems + ")");
						branchPair = branchingMehrotra(rmp, model);// TODO
						if (branchPair.from != -1) {
							System.out.println("Branching!");
							stackRMPb.add(buildRMP_AddEdge(rmp, branchPair, pbNo));
							stackRMPb.add(buildRMP_Contraction(rmp, branchPair, pbNo));
						} else {
							model.write(path + "results/" + fileName + "/model_problem_integral_sol_" + pbNo + ".sol");
							System.out.println();
							System.out.println(
									"***************************Integral Solution****************************");
							System.out.println("Number of colors: " + currentEqColNumber);
							break;
						}
					} else {
						System.out.println("No branching!");
						if (pbNo == 0) {
							break;
						}
					}
				}
				pbNo++;
			} else {
				System.out.println("Time's out!");
				return -1;
			}
		}
		return 0;
	}

	public static int searchUpBound(int p_0, int p_up) throws GRBException, IOException {
		int q = p_0;
		while (q + 1 <= p_up) {
			if (Math.floorDiv(n, p_0) == Math.floorDiv(n, q + 1) && Math.floorDiv(n, q + 1) * (q + 1) != n)
				q++;
			else
				break;
		}
		return q;
	}

	public static int searchEqChromatic_up(String fileName) throws GRBException, IOException, InterruptedException {
		int p_0 = p_down, p_1 = searchUpBound(p_0, p_up), t;
		System.out.println();
		System.out.println("Up-coming");
		long totalTime = System.nanoTime();
		while (p_1 <= p_up && checkTime(totalTime)) {
			stages++;
			System.out.println();
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			System.out.println("Stage " + stages + ": the interval [" + p_0 + ", " + p_1 + "]");
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			if (branchAndPrice(p_0, totalTime) != -1) {
				bestStageLowerBound = p_0;
				if (currentEqColNumber == -1 && checkTime(totalTime)) {
					bestStageLowerBound = p_0 + 1;
					writeStageData(totalTime);
					t = binarySearch_up(p_0, p_1, totalTime);
					// writeStageData(totalTime);
					if (t > 0)
						return t;// this must be chi_eq
				} else { // an eq-coloring was found
					writeStageData(totalTime);
					return p_0;// this must be chi_eq
				}
				p_0 = p_1 + 1;
				p_1 = searchUpBound(p_0, p_up);
			}
			continue;
		}
		return -1;
	}

	public static int binarySearch_up(int q_0, int q_1, long totalTime) throws GRBException, IOException {
		// there exists no q_0 eq-coloring
		if (q_0 != q_1) {
			int q = Math.floorDiv(q_0 + q_1, 2), t;
			if ((q_1 - q_0) % 2 == 1)
				q++;
			if (branchAndPrice(q, totalTime) != -1) {
				if (currentEqColNumber == -1) {
					bestStageLowerBound = q + 1;
					writeStageData(totalTime);
					return binarySearch_up(q, q_1, totalTime);
				} else {
					bestStageLowerBound = currentEqColNumber;
					writeStageData(totalTime);
					if (q_0 == currentEqColNumber - 1)
						return currentEqColNumber;
					t = binarySearch_up(q_0, eqColNumber - 1, totalTime);
					if (t == -1)
						return currentEqColNumber;
					return t;
				}
			} else
				return -1;
		}
		return -1;
	}

	public static int searchEqChromatic_down(String fileName) throws GRBException, IOException, InterruptedException {
		int p_0 = p_down, p_1 = searchUpBound(p_0, p_up), t;
		System.out.println("Down-coming");
		long totalTime = System.nanoTime();
		while (p_0 <= p_up && checkTime(totalTime)) {
			stages++;
			System.out.println();
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			System.out.println("Stage " + stages + ": the interval [" + p_0 + ", " + p_1 + "]");
			System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
			if (branchAndPrice(p_1, totalTime) != -1) {
				bestStageLowerBound = p_0;
				if (currentEqColNumber == -1 && checkTime(totalTime)) {// the current stage is finished, chi_eq was not
					// found
					bestStageLowerBound = p_1 + 1;
					p_0 = p_1 + 1;
					p_1 = searchUpBound(p_0, p_up);
					writeStageData(totalTime);
				} else { // an eq-coloring was found => the stage will finish with finding chi_eq
					t = binarySearch_down(p_0, eqColNumber, totalTime);
					writeStageData(totalTime);
					return t;
				}
			}
			continue;
		}
		return -1;
	}

	public static int searchEqChromatic(String fileName) throws GRBException, IOException, InterruptedException {
		if (direction_up)
			return searchEqChromatic_up(fileName);
		else
			return searchEqChromatic_down(fileName);
	}

	public static int binarySearch_down(int q_0, int q_1, long totalTime) throws GRBException, IOException {
		// there exists a q_1 eq-coloring
		if (q_0 == q_1) {
			bestStageLowerBound = q_1;
			writeStageData(totalTime);
			return q_1;
		}
		int q = Math.floorDiv(q_0 + q_1, 2);
		branchAndPrice(q, totalTime);
		if (currentEqColNumber == -1) {
			bestStageLowerBound = q + 1;
			writeStageData(totalTime);
			if (q == q_1 - 1)
				return q_1;
			return binarySearch_down(q, q_1, totalTime);
		}
		return binarySearch_down(q_0, currentEqColNumber, totalTime);
	}

	public static boolean checkTime(double totalTime) {
		if ((System.nanoTime() - totalTime) * 1e-9 > timeLimit * 3600)
			return false;
		return true;
	}

	public static void writeStageData(double totalTime) {
		createFile("../data/EqCol/results/finalSolutions.txt");
		NumberFormat nrformat = NumberFormat.getInstance();
		nrformat.setMaximumFractionDigits(2);
		try (BufferedWriter writer = new BufferedWriter(
				new FileWriter("../data/EqCol/results/" + fileName + "/finalSolutions_" + fileName + ".txt", true))) {
			writer.newLine();
			String nLine;

			System.out.println();
			nLine = "Stage " + stages + " information:";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "elapsed_time: " + nrformat.format((System.nanoTime() - totalTime) * 1e-9) + "s, ";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "average_time: " + nrformat.format(((System.nanoTime() - totalTime) * 1e-9) / stages) + "s, ";
			System.out.println(nLine);
			writer.write(nLine);

			nLine = "best stage lower bound: " + bestStageLowerBound;
			System.out.println(nLine);
			writer.write(nLine);

		} catch (IOException ex) {
		}
	}

	public static void main(String[] args) throws GRBException, IOException, InterruptedException {
		
		//fileName = "le450_25c.col";		
		if (args.length == 0) {
			System.err.println("Please specify the filename.");
			return;
		}
		fileName = args[0];		
		
		timeLimit = 4;// in hours
		n_max = 300000;		
		subproblemVerbosity = 0;
		direction_up = true;

		System.out.println(new File(path + "results/" + fileName).getCanonicalPath());
		createDir(path + "results");
		readFile(fileName);
		stages = 0;
		p_down = 3;
		p_up = 26;
		searchEqChromatic(fileName);
		System.out.println("File name: " + fileName);
	}
}