import java.util.HashSet;
import java.util.Iterator;

import com.gurobi.gurobi.GRB;
import com.gurobi.gurobi.GRBEnv;
import com.gurobi.gurobi.GRBException;
import com.gurobi.gurobi.GRBLinExpr;
import com.gurobi.gurobi.GRBModel;
import com.gurobi.gurobi.GRBVar;
import com.gurobi.gurobi.GRB.DoubleAttr;
import com.gurobi.gurobi.GRB.IntParam;

public class SubProblem {

	public GRBModel qModel;
	public static double precisionVar = 1e-5;
	public static String path = "../data/EqCol/";

	public SubProblem() {
	}

	public SubProblem(GRBEnv env, String fileName, RMP rmp, int NoPb, boolean[][] adjacency, double[] alpha, int _n,
			int nrH, int k_down, int k_up, boolean _multiple) throws GRBException {
		GRBModel model = new GRBModel(env);
		model.set(GRB.IntParam.OutputFlag, 1);
		GRBVar[] chrsVars_w = new GRBVar[_n];
		GRBLinExpr expr_cardinality_up = new GRBLinExpr(), expr_cardinality_down = new GRBLinExpr(),
				expr_edge = new GRBLinExpr(), expr_pair = new GRBLinExpr(), objFunction = new GRBLinExpr();
		Pair pair;
		int _u, _v;
		for (int v = 0; v < _n; v++)
			chrsVars_w[v] = model.addVar(0, 1, 0, GRB.BINARY, "w" + v);
		model.update();
		if (_multiple) {
			for (int v = 0; v < _n; v++)
				expr_cardinality_up.addTerm(1, chrsVars_w[v]);
			model.addConstr(expr_cardinality_up, GRB.EQUAL, k_up, "Cardinality_eq");
		} else {
			for (int v = 0; v < _n; v++) {
				expr_cardinality_up.addTerm(1, chrsVars_w[v]);
				expr_cardinality_down.addTerm(1, chrsVars_w[v]);
			}
			model.addConstr(expr_cardinality_down, GRB.GREATER_EQUAL, k_down, "Cardinality_down");
			model.addConstr(expr_cardinality_up, GRB.LESS_EQUAL, k_up, "Cardinality_up");
		}

		for (int u = 0; u < _n; u++) {
			objFunction.addTerm(alpha[u], chrsVars_w[u]);
			for (int v = 0; v < _n; v++) {
				if (adjacency[u][v] && u < v) {
					expr_edge = new GRBLinExpr();
					expr_edge.addTerm(1, chrsVars_w[u]);
					expr_edge.addTerm(1, chrsVars_w[v]);
					model.addConstr(expr_edge, GRB.LESS_EQUAL, 1.0, "Adj_" + u + "_" + v);
				}
			}
		}
		if (rmp.diffColNodes != null && rmp.diffColNodes.size() > 0) {
			Iterator<Pair> iter = rmp.diffColNodes.iterator();
			while (iter.hasNext()) {
				pair = iter.next();
				_u = pair.from;
				_v = pair.to;
				expr_pair = new GRBLinExpr();
				expr_pair.addTerm(1, chrsVars_w[_u]);
				expr_pair.addTerm(1, chrsVars_w[_v]);
				model.addConstr(expr_pair, GRB.LESS_EQUAL, 1.0, "Edge_" + _u + "_" + _v);
			}
		}
		if (rmp.sameColNodes != null && rmp.sameColNodes.size() > 0) {
			Iterator<Pair> iter = rmp.sameColNodes.iterator();
			while (iter.hasNext()) {
				pair = iter.next();
				_u = pair.from;
				_v = pair.to;
				expr_pair = new GRBLinExpr();
				expr_pair.addTerm(1, chrsVars_w[_u]);
				expr_pair.addTerm(-1, chrsVars_w[_v]);
				model.addConstr(expr_pair, GRB.EQUAL, 0.0, "Contraction_" + _u + "_" + _v);
			}
		}

		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		model.set(GRB.IntParam.OutputFlag, 0);
		// model.write(path + "results/" + fileName + "/model_subproblem_" + NoPb + "_"
		// + nrH + ".lp");
		model.update();

		this.qModel = model;
	}

	public SubProblem(GRBEnv env, String fileName, RMP rmp, int NoPb, boolean[][] adjacency, double[] alphaNew, int _n,
			int nrH, int k, boolean _multiple) throws GRBException {
		GRBModel model = new GRBModel(env);
		model.set(GRB.IntParam.OutputFlag, 1);
		GRBVar[] chrsVars_w = new GRBVar[_n];
		GRBLinExpr expr_cardinality_up_down = new GRBLinExpr(), expr_edge = new GRBLinExpr(),
				expr_pair = new GRBLinExpr(), objFunction = new GRBLinExpr();
		Pair pair;
		int _u, _v;
		for (int v = 0; v < _n; v++)
			chrsVars_w[v] = model.addVar(0, 1, 0, GRB.BINARY, "w" + v);
		model.update();
		for (int v = 0; v < _n; v++)
			expr_cardinality_up_down.addTerm(1, chrsVars_w[v]);
		model.addConstr(expr_cardinality_up_down, GRB.EQUAL, k, "Cardinality_eq_updown_" + k);

		for (int u = 0; u < _n; u++) {
			objFunction.addTerm(alphaNew[u], chrsVars_w[u]);
			for (int v = 0; v < _n; v++) {
				if (adjacency[u][v] && u < v) {
					expr_edge = new GRBLinExpr();
					expr_edge.addTerm(1, chrsVars_w[u]);
					expr_edge.addTerm(1, chrsVars_w[v]);
					model.addConstr(expr_edge, GRB.LESS_EQUAL, 1.0, "Adj_" + u + "_" + v);
				}
			}
		}
		if (rmp.diffColNodes != null && rmp.diffColNodes.size() > 0) {
			Iterator<Pair> iter = rmp.diffColNodes.iterator();
			while (iter.hasNext()) {
				pair = iter.next();
				_u = pair.from;
				_v = pair.to;
				expr_pair = new GRBLinExpr();
				expr_pair.addTerm(1, chrsVars_w[_u]);
				expr_pair.addTerm(1, chrsVars_w[_v]);
				model.addConstr(expr_pair, GRB.LESS_EQUAL, 1.0, "Edge_" + _u + "_" + _v);
			}
		}
		if (rmp.sameColNodes != null && rmp.sameColNodes.size() > 0) {
			Iterator<Pair> iter = rmp.sameColNodes.iterator();
			while (iter.hasNext()) {
				pair = iter.next();
				_u = pair.from;
				_v = pair.to;
				expr_pair = new GRBLinExpr();
				expr_pair.addTerm(1, chrsVars_w[_u]);
				expr_pair.addTerm(-1, chrsVars_w[_v]);
				model.addConstr(expr_pair, GRB.EQUAL, 0.0, "Contraction_" + _u + "_" + _v);
			}
		}

		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		model.set(GRB.IntParam.OutputFlag, 0);
		model.write(path + "results/" + fileName + "/model_subproblem_up_down_" + k + "_" + NoPb + "_" + nrH + ".lp");
		model.update();

		this.qModel = model;
	}

	public ColorClass[] solvePool(String fileName, int _n, double precision, double beta, boolean[][] adjacency,
			int nrH, int pbNo, int poolSize, int _subproblemVerbosity, double timeLimit, long time)
			throws GRBException {
		int h, k, s = 0;
		String varName;
		ColorClass[] colorClasses = null;

		this.qModel.set(IntParam.PoolSearchMode, 2);
		this.qModel.set(IntParam.PoolSolutions, poolSize);
		this.qModel.set(GRB.IntParam.OutputFlag, _subproblemVerbosity);
		this.qModel.set(GRB.DoubleParam.TimeLimit, timeLimit * 3600 - (System.nanoTime() - time) * 1e-9);
		this.qModel.optimize();
		// System.out.println("Status: " + this.qModel.get(GRB.IntAttr.Status));
		int sol_count = this.qModel.get(GRB.IntAttr.SolCount);
		for (int l = 0; l < sol_count; l++) {// compute the number of valid solutions
			this.qModel.set(IntParam.SolutionNumber, l);
			// if (_subproblemVerbosity == 1)
			// System.out.println("Solution " + l + " objective value: " +
			// this.qModel.get(DoubleAttr.PoolObjVal));
			if (this.qModel.get(DoubleAttr.PoolObjVal) > beta + precision)
				s++;
		}
		// System.out.println("No of solutions: " + sol_count);
		this.qModel.update();
		// model.write(path + "results/" + fileName + "/model_subproblem_up_down_" + k +
		// "_" + NoPb + "_" + nrH + ".lp");
		if (this.qModel.get(GRB.IntAttr.Status) != 2 || sol_count == 0)
			return null;
		System.out.println("Subproblem optimal value: " + this.qModel.get(DoubleAttr.ObjVal) + "(#vars: "
				+ this.qModel.getVars().length + ", #constrs: " + this.qModel.getConstrs().length + ")");
		if (this.qModel.get(DoubleAttr.ObjVal) > beta + precision) {
			colorClasses = new ColorClass[sol_count];
			for (int l = 0; l < s; l++) {
				this.qModel.set(IntParam.SolutionNumber, l);
				GRBVar[] vars = this.qModel.getVars();
				HashSet<Integer> nodes = new HashSet<Integer>();
				for (int p = 0; p < vars.length; p++) {
					varName = vars[p].get(GRB.StringAttr.VarName);
					h = varName.indexOf('w');
					if (h != -1) {
						k = Integer.valueOf(varName.substring(h + 1));
						if (vars[p].get(GRB.DoubleAttr.Xn) > 1.0 - precisionVar)
							nodes.add((Integer) k);
					}
				}
				colorClasses[l] = new ColorClass(nodes, adjacency, this.qModel.get(DoubleAttr.PoolObjVal));
			}
		}
		this.qModel.dispose();
		return colorClasses;
	}

	public ColorClass[] solvePool(String fileName, int _n, int _k, double precision, double beta, boolean[][] adjacency,
			int nrH, int pbNo, int poolSize, int _subproblemVerbosity) throws GRBException {
		int h, k, s = 0;
		String varName;
		ColorClass[] colorClasses = null;

		this.qModel.set(IntParam.PoolSearchMode, 2);
		this.qModel.set(IntParam.PoolSolutions, poolSize);
		this.qModel.set(GRB.IntParam.OutputFlag, _subproblemVerbosity);
		this.qModel.optimize();
		// System.out.println("Status: " + this.qModel.get(GRB.IntAttr.Status));
		int sol_count = this.qModel.get(GRB.IntAttr.SolCount);
		for (int l = 0; l < sol_count; l++) {// compute the number of valid solutions
			this.qModel.set(IntParam.SolutionNumber, l);
			// if (_subproblemVerbosity == 1)
			// System.out.println("Solution " + l + " objective value: " +
			// this.qModel.get(DoubleAttr.PoolObjVal));
			if (_k - this.qModel.get(DoubleAttr.PoolObjVal) > beta + precision)
				s++;
		}
		// System.out.println("No of solutions: " + sol_count);
		this.qModel.update();
		if (this.qModel.get(GRB.IntAttr.Status) != 2 || sol_count == 0)
			return null;
		System.out.println("Subproblem optimal value: " + this.qModel.get(DoubleAttr.ObjVal) + "(#vars: "
				+ this.qModel.getVars().length + ", #constrs: " + this.qModel.getConstrs().length + ")");
		if (_k - this.qModel.get(DoubleAttr.ObjVal) > beta + precision) {
			colorClasses = new ColorClass[sol_count];
			for (int l = 0; l < s; l++) {
				this.qModel.set(IntParam.SolutionNumber, l);
				GRBVar[] vars = this.qModel.getVars();
				HashSet<Integer> nodes = new HashSet<Integer>();
				for (int p = 0; p < vars.length; p++) {
					varName = vars[p].get(GRB.StringAttr.VarName);
					h = varName.indexOf('w');
					if (h != -1) {
						k = Integer.valueOf(varName.substring(h + 1));
						if (vars[p].get(GRB.DoubleAttr.Xn) > 1.0 - precisionVar)
							nodes.add((Integer) k);
					}
				}
				colorClasses[l] = new ColorClass(nodes, adjacency, this.qModel.get(DoubleAttr.PoolObjVal));
			}
		}
		this.qModel.dispose();
		return colorClasses;
	}
}