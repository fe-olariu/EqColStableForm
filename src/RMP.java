import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import com.gurobi.gurobi.GRBException;

public class RMP {
	// the number of solved subproblems:
	public int noSubProblems;
	public int fatherProblem;
	// the number of virtual vertices:
	public int noVirtualVertices;
	// the real id's of vertices:
	public int[] vertex;
	// vertexColCl[i] keeps the id(s) for the active stable sets containing
	// vertex i:
	public ArrayList<Pair>[] vertexColCl;// from is the id and to is the size of the class
	// pairs of vertices having the same color:
	public ArrayList<Pair> sameColNodes;
	// pairs of vertices having different colors:
	public ArrayList<Pair> diffColNodes;
	// the index of variables for the active coloring classes:
	public HashMap<Integer, ColorClass> colorClasses = new HashMap<Integer, ColorClass>();
	public Pair[] vertexPartialCol;
	public HashMap<Integer, ColorClass> partialCol = new HashMap<Integer, ColorClass>();
	// the model status:
	public int mStatus;
	// type of the problem (root, contraction, edge-adding)
	public String type;
	// problem pair of non-adjacent vertices:
	public int u;
	public int v;
	// the maximum cardinality of a color class;
	public int maxClassCard;
	// color classes by cardinality:
	public LinkedList<ArrayList<Integer>> classesByCard = new LinkedList<ArrayList<Integer>>();

	// public RMP(GRBEnv env, int n, int k) throws GRBException {
	// this.model = new GRBModel(env);
	// this.vertexColCl = new ArrayList[n];
	// }

	public RMP() {

	}

	@SuppressWarnings("unchecked")
	public RMP(int _fatherProblem, int _noVertices, ArrayList<Pair>[] _vertexColCl, ArrayList<Pair> _diffCol,
			ArrayList<Pair> _sameCol, HashMap<Integer, ColorClass> _colorClasses, String _type, int _u, int _v)
			throws GRBException {

		this.fatherProblem = _fatherProblem;
		this.type = _type;
		this.u = _u;
		this.v = _v;
		this.noVirtualVertices = _noVertices;

		ArrayList<Pair> listV;
		ArrayList<Pair>[] listVertex = new ArrayList[_vertexColCl.length];
		for (int i = 0; i < _vertexColCl.length; i++) {
			listV = new ArrayList<Pair>();
			if (_vertexColCl[i] != null) {
				Iterator<Pair> iterV = _vertexColCl[i].iterator();
				while (iterV.hasNext())
					listV.add(iterV.next());
			}
			listVertex[i] = listV;
		}
		this.vertexColCl = listVertex;

		ArrayList<Pair> listDiff = new ArrayList<Pair>();
		if (_diffCol != null) {
			Iterator<Pair> iterD = _diffCol.iterator();
			while (iterD.hasNext())
				listDiff.add(iterD.next());
		}
		this.diffColNodes = listDiff;

		ArrayList<Pair> listSame = new ArrayList<Pair>();
		if (_sameCol != null) {
			Iterator<Pair> iterS = _sameCol.iterator();
			while (iterS.hasNext())
				listSame.add(iterS.next());
		}
		this.sameColNodes = listSame;

		if (_colorClasses != null) {
			HashMap<Integer, ColorClass> coalitionList = new HashMap<Integer, ColorClass>();
			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				coalitionList.put((Integer) pairE.getKey(), (ColorClass) pairE.getValue());
			}
			this.colorClasses = coalitionList;
		}
	}

	@SuppressWarnings("unchecked")
	public RMP(int _fatherProblem, int _noVertices, ArrayList<Pair>[] _vertexColCl, ArrayList<Pair> _diffCol,
			ArrayList<Pair> _sameCol, HashMap<Integer, ColorClass> _colorClasses, Pair[] _vertexPartialCol,
			HashMap<Integer, ColorClass> _partialCol, String _type, int _u, int _v) throws GRBException {

		this.fatherProblem = _fatherProblem;
		this.type = _type;
		this.u = _u;
		this.v = _v;
		this.noVirtualVertices = _noVertices;

		ArrayList<Pair> listV;
		ArrayList<Pair>[] listVertex = new ArrayList[_vertexColCl.length];
		for (int i = 0; i < _vertexColCl.length; i++) {
			listV = new ArrayList<Pair>();
			if (_vertexColCl[i] != null) {
				Iterator<Pair> iterV = _vertexColCl[i].iterator();
				while (iterV.hasNext())
					listV.add(iterV.next());
			}
			listVertex[i] = listV;
		}
		this.vertexColCl = listVertex;

		Pair[] listVertexPartial = new Pair[_vertexPartialCol.length];
		for (int i = 0; i < _vertexPartialCol.length; i++)
			if (_vertexPartialCol[i] != null)
				listVertexPartial[i] = new Pair(_vertexPartialCol[i].from, _vertexPartialCol[i].to);
		this.vertexPartialCol = listVertexPartial;

		ArrayList<Pair> listDiff = new ArrayList<Pair>();
		if (_diffCol != null) {
			Iterator<Pair> iterD = _diffCol.iterator();
			while (iterD.hasNext())
				listDiff.add(iterD.next());
		}
		this.diffColNodes = listDiff;

		ArrayList<Pair> listSame = new ArrayList<Pair>();
		if (_sameCol != null) {
			Iterator<Pair> iterS = _sameCol.iterator();
			while (iterS.hasNext())
				listSame.add(iterS.next());
		}
		this.sameColNodes = listSame;

		if (_colorClasses != null) {
			HashMap<Integer, ColorClass> coalitionList = new HashMap<Integer, ColorClass>();
			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _colorClasses.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				coalitionList.put((Integer) pairE.getKey(), (ColorClass) pairE.getValue());
			}
			this.colorClasses = coalitionList;
		}

		// _partialCol
		if (_partialCol != null) {
			HashMap<Integer, ColorClass> stableSetList = new HashMap<Integer, ColorClass>();
			Iterator<Entry<Integer, ColorClass>> iterVarCoal = _partialCol.entrySet().iterator();
			while (iterVarCoal.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pairE = (HashMap.Entry<Integer, ColorClass>) iterVarCoal.next();
				stableSetList.put((Integer) pairE.getKey(), (ColorClass) pairE.getValue());
			}
			this.partialCol = stableSetList;
		}

	}

	public boolean check(ColorClass stableSet, int n) {
		ColorClass currentClass;
		if (stableSet != null) {
			Iterator<Entry<Integer, ColorClass>> _class = this.colorClasses.entrySet().iterator();
			while (_class.hasNext()) {
				HashMap.Entry<Integer, ColorClass> pair = (HashMap.Entry<Integer, ColorClass>) _class.next();
				currentClass = (ColorClass) pair.getValue();
				if (currentClass.check(stableSet, n))
					return false;
			}
			return true;
		}
		return false;
	}

	public ColorClass remove(int no_, ColorClass colClass, int[] _vertex, boolean[] cluster_u_Or_v) {
		ColorClass modClass = new ColorClass();
		HashSet<Integer> toRemove = new HashSet<Integer>();
		int i;
		if (colClass != null) {
			Iterator<Integer> iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();

		}
		return modClass;

	}

	public ColorClass modify(int newN, int uId, int vId, int no_, ColorClass colClass, int[] _vertex,
			boolean[] cluster_u_Or_v, boolean[][] adjacencyM) {
		int i;
		ColorClass modClass = new ColorClass();
		HashSet<Integer> toRemove = new HashSet<Integer>();

		Iterator<Integer> iter = colClass.vertices.iterator();
		while (iter.hasNext()) {
			i = iter.next().intValue();
		}

		if (colClass.vertices.contains((Integer) uId) && colClass.vertices.contains((Integer) vId)) {
			colClass.vertices.remove((Integer) uId);
			colClass.vertices.remove((Integer) vId);
			colClass.vertices.add((Integer) newN);
		} else if (colClass.vertices.contains((Integer) uId)) {
			iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();
		}

		if (colClass != null) {
			iter = colClass.vertices.iterator();
			while (iter.hasNext()) {
				i = iter.next().intValue();
				if (cluster_u_Or_v[i])
					toRemove.add(i);
			}
			iter = toRemove.iterator();

		}
		return modClass;

	}

	public void printDiffSame() {
		// int fromId, toId;
		Pair pair;
		if (this.sameColNodes != null) {
			Iterator<Pair> iterS = this.sameColNodes.iterator();
			System.out.println();
			System.out.println("Same color vertices");
			while (iterS.hasNext()) {
				pair = iterS.next();
				System.out.println("True names: (" + pair.from + ", " + pair.to + ")");
			}
		}
		if (this.diffColNodes != null) {
			Iterator<Pair> iterS = this.diffColNodes.iterator();
			System.out.println();
			System.out.println("Different color vertices");
			while (iterS.hasNext()) {
				pair = iterS.next();
				System.out.println("(" + pair.from + ", " + pair.to + ")");
			}
		}
	}
}