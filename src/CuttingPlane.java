import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import com.gurobi.gurobi.GRB;
import com.gurobi.gurobi.GRBEnv;
import com.gurobi.gurobi.GRBException;
import com.gurobi.gurobi.GRBLinExpr;
import com.gurobi.gurobi.GRBModel;
import com.gurobi.gurobi.GRBVar;
import com.gurobi.gurobi.GRB.DoubleAttr;

public class CuttingPlane {
	public static int n, m, Delta;// the order, the size, and the max. degree of the graph;
	// the number of different cuts:
	public static int no_cuts, no_cliqueCuts, no_lazyConstraints, no_S_colorCuts, no_blockCuts, no_2_rankCuts;
	public static int step, max_steps, kClique, verbosity, chi_UpperBound;
	public static boolean[][] adjacency;// adjacency matrix
	public static int[] degrees;// the degrees of the graph

	public static double timeLimit;// time limit in hours;
	public static double currentObj = -1;// the current value of the objective function
	public static double precisionVar = 1e-7;// the variables precision
	public static double precisionOpt = 1e-9;// the optimum value precision
	public static double precisionCut = 1e-7;// the violated cut precision

	public static GRBModel M_model; // the LP model
	public static double[][] solutionX;// the values for x variables
	public static double[] solutionW;// the values for w variables
	public static String fileName, path = "../data/EqCol/", writeLUp, writeLDown;

	public static void createFile(String fileName) {
		try {
			File file = new File(fileName);
			if (file.exists()) {
				file.delete();
				file.createNewFile();
				System.out.println("File already exists. Deleted and recreated.");
			} else if (file.createNewFile())
				System.out.println("File created: " + file.getName());
		} catch (IOException e) {
			System.out.println("An error occurred.");
			e.printStackTrace();
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
		// M_adjacency = new boolean[n][n];
		degrees = new int[n];
		Delta = readGfF.readGraph(dataFile, adjacency, degrees, Delta);
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
		createFile(path + "/finalSolutions_" + fileName + ".txt");
	}

	public static double formSec(double val) {// formatting the time intervals
		return Math.floor(val * 1000) / 1000;
	}

	public static ArrayList<Integer> M_orderDegrees() {
		Integer[] indices = new Integer[n];
		for (int i = 0; i < n; i++)
			indices[i] = i;
		Arrays.sort(indices, Comparator.comparingInt(i -> degrees[i]));
		ArrayList<Integer> indexList = new ArrayList<Integer>();
		for (int i = 0; i < n; i++)
			indexList.add(indices[n - i - 1]);
		return indexList;
	}

	public static boolean add_lazyConstraints() throws GRBException {
		double sum = 0;
		GRBLinExpr lin_expr;
		boolean addedCuts = false;

		for (int j = 1; j < chi_UpperBound; j++) {
			for (int v = j; v < n; v++) {
				sum = 0;
				for (int i = j - 1; i < v; i++)
					sum += solutionX[i][j - 1];
				if (sum < solutionX[v][j]) {
					lin_expr = new GRBLinExpr();
					for (int i = j - 1; i < v; i++)
						lin_expr.addTerm(1, M_model.getVarByName("x_" + i + "_" + (j - 1)));
					lin_expr.addTerm(-1, M_model.getVarByName("x_" + v + "_" + j));
					M_model.addConstr(lin_expr, GRB.GREATER_EQUAL, 0.0,
							"Lazy_" + v + "_" + j + "_" + no_lazyConstraints);
					no_lazyConstraints++;
					addedCuts = true;
				}
			}
		}
		no_cuts += no_lazyConstraints;
		if (addedCuts)
			M_model.update();
		return addedCuts;
	}

	public static boolean add_cliqueCuts(double totalTime) throws GRBException {
		Integer[] indices;
		int[] oldIndices, oVertices;
		boolean toAdd, kCliqueFlag, addedCuts = false;
		int s, k, w, v = -1, kCl, l;
		double sum;
		ColorClass currentClique;
		Iterator<Integer> iterClique;
		GRBLinExpr lin_expr;

		for (int j = 0; j < chi_UpperBound - 1; j++)
			if (checkTime(totalTime)) {
				s = 0;
				sum = 0;
				for (int u = 0; u < n; u++)
					if (Math.abs(solutionX[u][j]) > precisionVar && Math.abs(1 - solutionX[u][j]) > precisionVar) {
						s++;
						sum += solutionX[u][j];
					}
				if (sum > solutionW[j] && s > 0) {
					kCl = Math.min(kClique, s);
					k = 0;
					indices = new Integer[s];
					oldIndices = new int[s];
					Double[] sol = new Double[s];
					for (int u = 0; u < n; u++)
						if (Math.abs(solutionX[u][j]) > precisionVar && Math.abs(1 - solutionX[u][j]) > precisionVar) {
							indices[k] = k;
							sol[k] = solutionX[u][j];
							oldIndices[k] = u;
							k++;
						}
					Arrays.sort(indices, Comparator.comparingDouble(h -> sol[h]));
					oVertices = new int[s];
					for (int u = 0; u < s; u++)// the ordered candidate vertices
						oVertices[u] = oldIndices[indices[s - u - 1]];
					//
					for (int i = 0; i < s; i++) {
						w = oVertices[i];
						kCliqueFlag = true;
						for (int p = 0; p < kCl && kCliqueFlag; p++) {// find the (p + 1)th vertex adjacent with w
							l = 0;
							for (int h = i + 1; h < s && l < p + 1; h++)
								if (adjacency[w][oVertices[h]]) {
									l++;
									v = h;
								}
							if (l == p + 1 && v + 1 < s) {
								currentClique = new ColorClass();
								currentClique.vertices.add(w);
								currentClique.vertices.add(oVertices[v]);
								sum = solutionX[w][j] + solutionX[oVertices[v]][j];
								toAdd = true;
								for (int h = v + 1; h < s; h++) {
									iterClique = currentClique.vertices.iterator();
									while (iterClique.hasNext())
										if (!adjacency[iterClique.next()][oVertices[h]]) {
											toAdd = false;
											break;
										}
									if (toAdd) {
										currentClique.vertices.add(oVertices[h]);
										sum += solutionX[oVertices[h]][j];
									}
								}
								if (sum > solutionW[j] + precisionCut && currentClique.vertices.size() > 2) {
									lin_expr = new GRBLinExpr();
									iterClique = currentClique.vertices.iterator();
									while (iterClique.hasNext()) {
										v = iterClique.next();
										lin_expr.addTerm(1, M_model.getVarByName("x_" + v + "_" + j));
									}
									lin_expr.addTerm(-1, M_model.getVarByName("w_" + j));
									// add the clique cut:
									M_model.addConstr(lin_expr, GRB.LESS_EQUAL, 0, "Clique_" + no_cliqueCuts);
									no_cliqueCuts++;
									addedCuts = true;
								}
							}
						}
					}
				}
			}
		no_cuts += no_cliqueCuts;
		if (addedCuts)
			M_model.update();
		return addedCuts;
	}

	public static boolean add_2RankCuts(double totalTime) throws GRBException {
		double sum, val;
		int v1 = -1, v2 = -1, q = 0, c = 0, r, vertForbidden = 0, x, y;
		boolean[] characteristicS, characteristicQ, forbiddenV;
		boolean flag = true, S_flag, addedCuts = false;
		List<Pair> varPairs;
		List<Integer> sSet, qSet;
		Iterator<Integer> iterQ, iterS1, iterS2;
		GRBLinExpr lin_expr;
		Pair _pair;

		for (int j = 0; j < chi_UpperBound - 1; j++)
			if (checkTime(totalTime)) {
				vertForbidden = 0;
				forbiddenV = new boolean[n];
				varPairs = new ArrayList<Pair>();

				for (int u = 0; u < n; u++)
					for (int v = u + 1; v < n; v++) {
						val = solutionX[u][j] + solutionX[v][j];
						if (val < 1 - precisionVar && val > 0) {
							varPairs.add(new Pair(u, v, val));
						}
					}
				Collections.sort(varPairs);

				while (vertForbidden < n - 5 && varPairs != null && varPairs.size() > 0) {
					sSet = new ArrayList<Integer>();
					qSet = new ArrayList<Integer>();
					characteristicQ = new boolean[n];
					characteristicS = new boolean[n];

					_pair = varPairs.remove(varPairs.size() - 1);

					while ((forbiddenV[_pair.from] || forbiddenV[_pair.to])
							&& varPairs != null & varPairs.size() > precisionVar)
						_pair = varPairs.remove(varPairs.size() - 1);
					v1 = _pair.from;
					v2 = _pair.to;
					if (!forbiddenV[v1] && !forbiddenV[v2]) {
						// System.out.println("Max: " + _pair.val + ", (" + v1 + ", " + v2 + ") - color
						// " + j);
						characteristicS[v1] = true;
						characteristicS[v2] = true;
						sSet.add(v1);
						sSet.add(v2);
						q = 0;// Q cardinality
						S_flag = false;
						c = 0;// c is the number of candidates
						for (int u = 0; u < n; u++)
							if (!forbiddenV[u] && Math.abs(solutionX[u][j]) > precisionVar
									&& Math.abs(1 - solutionX[u][j]) > precisionVar && u != v1 && u != v2)
								c++;
						if (c > 0) {
							Integer[] indices = new Integer[c];
							Double[] sol = new Double[c];
							int[] oldIndices = new int[c], oVertices = new int[c];
							r = 0;
							for (int u = 0; u < n; u++)
								if (!forbiddenV[u] && Math.abs(solutionX[u][j]) > precisionVar
										&& Math.abs(1 - solutionX[u][j]) > precisionVar && u != v1 && u != v2) {
									indices[r] = r;
									sol[r] = solutionX[u][j];
									oldIndices[r] = u;
									r++;
								}
							Arrays.sort(indices, Comparator.comparingDouble(h -> sol[h]));
							// the candidate vertices are ordered w.r.t. their decreasing (variable)
							// fractional values;
							for (int u = 0; u < c; u++)
								oVertices[u] = oldIndices[indices[c - u - 1]];

							// if (adjacency[_pair.from][_pair.to])
							// System.out.println();
							for (int u = 0; u < c; u++)
								if (!characteristicS[oVertices[u]]) {// try to add oVertices[u] to S or Q;
									flag = true;
									if (qSet != null && qSet.size() > 0) {
										iterQ = qSet.iterator();
										while (iterQ.hasNext())
											if (!adjacency[oVertices[u]][iterQ.next()]) {
												flag = false;
												break;
											}
									}

									if (flag) {// oVertices[u] is adjacent with all vertices from Q (or Q is empty)
										// check if alpha(S U {oVertices[u]}) >= 2
										S_flag = false;
										if (characteristicS[oVertices[u]])// oVertices[u] is already in S
											S_flag = true;
										else// temporarily, for simplifying the code from below
											sSet.add(oVertices[u]);

										flag = false;
										iterS1 = sSet.iterator();
										while (iterS1.hasNext()) {
											x = iterS1.next();
											iterS2 = sSet.iterator();
											while (iterS2.hasNext()) {
												y = iterS2.next();
												if (x != y && !adjacency[x][y]) {
													flag = true;
													break;
												}
											}
										}
										if (!S_flag)// revert, if necessary, the status of oVertices[u]
											sSet.remove(sSet.size() - 1);

										if (flag) {// S U {oVertices[u]} contains a stable set of cardinality 2.
											// check if alpha(S U {oVertices[u]}) = 2
											iterS1 = sSet.iterator();
											loop1: while (iterS1.hasNext()) {
												x = iterS1.next();
												iterS2 = sSet.iterator();
												while (iterS2.hasNext()) {
													y = iterS2.next();
													if (x != y && oVertices[u] != x && oVertices[u] != y
															&& !adjacency[x][y] && !adjacency[x][oVertices[u]]
															&& !adjacency[y][oVertices[u]]) {
														flag = false;// S U {oVertices[u]} has a stable of cardinality 3
																		// through
																		// oVertices[u]!
														break loop1;
													}
												}
											}

											if (flag) {// alpha(S U {u}) = 2 and we can check the 2-maximality (flag =
														// true):
												S_flag = false;
												if (characteristicS[oVertices[u]])// oVertices[u] is already in S
													S_flag = true;
												else {// temporarily for simplifying the code from below
													sSet.add(oVertices[u]);
													characteristicS[oVertices[u]] = true;
												}

												loop3: for (int z = 0; z < n; z++)
													loop2: if (!characteristicS[z]) {
														flag = false;
														iterS1 = sSet.iterator();
														while (iterS1.hasNext()) {
															x = iterS1.next();
															iterS2 = sSet.iterator();
															while (iterS2.hasNext()) {
																y = iterS2.next();
																if (x != y && !adjacency[x][y] && !adjacency[x][z]
																		&& !adjacency[y][z]) {
																	flag = true;
																	break loop2;
																}
															}
														}
														if (!flag) {
															if (q == 0) {
																sSet.add(z);
																characteristicS[z] = true;
															}
															break loop3;

														}
													}
												if (!S_flag) {
													sSet.remove(sSet.size() - 1);
													characteristicS[oVertices[u]] = false;
												}
												if (flag) {// S U {u} is 2-maximal (flag = true)
													// add vOrder[u] to S (if it's not there):
													characteristicS[oVertices[u]] = true;
													sSet.add(oVertices[u]);
													iterS1 = sSet.iterator();
													while (iterS1.hasNext()) {
														x = iterS1.next();
														if (x != oVertices[u] && !adjacency[x][oVertices[u]]) {
															flag = false;
															break;
														}
													}
													if (flag) {// vOrder[u] is added to Q
														characteristicQ[oVertices[u]] = true;
														qSet.add(oVertices[u]);
														q++;
													}
												}
											}
										}
									}
								}
							if (q > 0) {// we finished building S
								sum = 0;
								for (int v = 0; v < n; v++) {
									if (characteristicS[v] && !characteristicQ[v]) {
										sum += solutionX[v][j];
										forbiddenV[v] = true;
										vertForbidden++;
									}
									if (characteristicQ[v]) {
										sum += 2 * solutionX[v][j];
										forbiddenV[v] = true;
										vertForbidden++;
									}
								}

								// new ColorClass(sSet).toString();
								// new ColorClass(qSet).toString();
								if (sum > 2 * solutionW[j] + precisionCut) {// add the 2-rank cut
									lin_expr = new GRBLinExpr();
									for (int v = 0; v < n; v++) {
										if (characteristicS[v] && !characteristicQ[v])
											lin_expr.addTerm(1.0, M_model.getVarByName("x_" + v + "_" + j));
										if (characteristicQ[v])
											lin_expr.addTerm(2.0, M_model.getVarByName("x_" + v + "_" + j));
									}
									lin_expr.addTerm(-2.0, M_model.getVarByName("w_" + j));
									M_model.addConstr(lin_expr, GRB.LESS_EQUAL, 0, "2Rank_" + no_2_rankCuts);
									// System.out.println("Added 2-rank cut no. " + no_2_rankCuts);
									no_2_rankCuts++;
									addedCuts = true;

								}
							} else {

							}
						}
					} else
						vertForbidden = n;
				}
			}
		no_cuts += no_2_rankCuts;
		if (addedCuts)
			M_model.update();
		return addedCuts;
	}

	public static boolean add_blockColorCuts() throws GRBException {
		double sum;
		GRBLinExpr lin_expr;
		boolean addedCuts = false;

		for (int j0 = 1; j0 < chi_UpperBound; j0++)
			if (Math.abs(solutionW[j0]) > precisionVar && Math.abs(1 - solutionW[j0]) > precisionVar)
				for (int v0 = j0; v0 < n; v0++) {
					sum = 0;
					for (int j = j0; j <= v0; j++)
						sum += solutionX[v0][j];
					// System.out.println("sum: " + sum + ", solW: " + solutionW[i]);
					if (sum > solutionW[j0] + precisionCut) {// add the block-color inequality:
						lin_expr = new GRBLinExpr();
						for (int j = j0; j <= Math.min(v0, chi_UpperBound - 1); j++)
							lin_expr.addTerm(1, M_model.getVarByName("x_" + v0 + "_" + j));
						lin_expr.addTerm(-1, M_model.getVarByName("w_" + j0));
						M_model.addConstr(lin_expr, GRB.LESS_EQUAL, 0, "Block_" + v0 + "_" + j0 + "_" + no_blockCuts);
						no_blockCuts++;
						addedCuts = true;
					}
				}
		no_cuts += no_blockCuts;
		if (addedCuts)
			M_model.update();
		return addedCuts;
	}

	public static boolean add_SColorCuts(double totalTime) throws GRBException {
		boolean addedCuts = false;
		int t = -1, min = 2 * n, f;
		double sumLeft = 0, sumRight = 0, cutGap;
		GRBLinExpr best_lin_expr;
		ArrayList<Integer> S_list, best_S_list = new ArrayList<Integer>();
		int[] best_dS = new int[n], best_bS = new int[n];

		for (int j = 0; j < chi_UpperBound; j++)
			if (Math.abs(solutionW[j]) > precisionVar && Math.abs(1 - solutionW[j]) > precisionVar
					&& Math.abs(solutionW[j + 1]) < precisionVar) {
				t = j + 1;
				break;
			}

		if (t >= 4) {
			Integer[] colorInd = new Integer[t];
			Integer[] fracSol = new Integer[t];
			for (int j = 0; j < t; j++) {
				colorInd[j] = j;
				fracSol[j] = 0;
				for (int u = 0; u < n; u++)
					if (Math.abs(solutionX[u][j]) > precisionVar && Math.abs(1 - solutionX[u][j]) > precisionVar) {
						fracSol[j]++;
					}
			}
			Arrays.sort(colorInd, Comparator.comparingInt(h -> fracSol[h]));
			int[] decreasingInd = new int[t];
			for (int j = 0; j < t; j++) {
				decreasingInd[j] = colorInd[t - j - 1];
				if (Math.floorDiv(n, j + 1) * (j + 1) != n && min > n - (j + 1) * Math.floorDiv(n, j + 1))
					min = n - (j + 1) * Math.floorDiv(n, j + 1);
			}
			for (int s = 2; s < t - 1; s++)
				if (checkTime(totalTime)) {
					cutGap = -1;
					best_lin_expr = null;
					if (s >= 1 + min) {
						// Find S with |S|=s and containing most fractional classes.
						for (int i = 0; i < t - s; i++) {
							sumLeft = 0;
							sumRight = 0;
							S_list = new ArrayList<Integer>();
							int[] dS = new int[chi_UpperBound], bS = new int[chi_UpperBound];
							for (int h = 0; h < s; h++) {
								S_list.add(decreasingInd[i + h]);
								for (int v = 0; v < n; v++) {
									sumLeft += solutionX[v][decreasingInd[i + h]];
									if (decreasingInd[i + h] <= v && v < chi_UpperBound)
										dS[v]++;
								}
							}
							for (int l = 0; l < chi_UpperBound; l++) {
								bS[l] = dS[l] * Math.floorDiv(n, l + 1)
										+ Math.min(dS[l], n - (l + 1) * Math.floorDiv(n, l + 1));
								sumRight += bS[l] * (solutionW[l] - solutionW[l + 1]);
							}
							if (sumLeft - sumRight > precisionCut && sumLeft - sumRight > cutGap + precisionCut) {
								cutGap = sumLeft - sumRight;
								best_S_list = new ArrayList<Integer>();
								for (int l = 0; l < chi_UpperBound; l++) {
									best_dS[l] = dS[l];
									best_bS[l] = bS[l];
								}
								Iterator<Integer> sIter = S_list.iterator();
								while (sIter.hasNext())
									best_S_list.add(sIter.next());
							}
						}
					}
					if (cutGap > 0) {
						// add the most violated S-color cut:
						best_lin_expr = new GRBLinExpr();
						Iterator<Integer> sIter = best_S_list.iterator();
						while (sIter.hasNext()) {
							f = sIter.next();
							for (int v = 0; v < n; v++)
								best_lin_expr.addTerm(1.0, M_model.getVarByName("x_" + v + "_" + f));
						}
						for (int i = 0; i < chi_UpperBound; i++) {
							best_lin_expr.addTerm(-best_bS[i], M_model.getVarByName("w_" + i));
							best_lin_expr.addTerm(best_bS[i], M_model.getVarByName("w_" + (i + 1)));
						}
						M_model.addConstr(best_lin_expr, GRB.LESS_EQUAL, 0, "S-ColorCut_" + no_S_colorCuts);
						no_S_colorCuts++;
						addedCuts = true;
					}
				}
		}
		no_cuts += no_S_colorCuts;
		if (addedCuts)
			M_model.update();
		return addedCuts;
	}

	public static void M_buildInitialModelO(GRBEnv env) throws GRBException {
		// M_newOrder();
		GRBModel _model = new GRBModel(env);
		GRBLinExpr lin_expr, objFunction = new GRBLinExpr();
		long buildTime = System.nanoTime();

		// Variables:
		for (int i = 0; i < chi_UpperBound + 1; i++)
			_model.addVar(0, 1, 1, GRB.CONTINUOUS, "w_" + i);
		for (int i = 0; i < chi_UpperBound; i++) {
			for (int v = 0; v < n; v++)
				_model.addVar(0, GRB.INFINITY, 0, GRB.CONTINUOUS, "x_" + v + "_" + i);
		}
		_model.update();

		// Constraints:
		for (int v = 0; v < n; v++) {
			lin_expr = new GRBLinExpr();
			for (int i = 0; i < chi_UpperBound; i++)
				lin_expr.addTerm(1.0, _model.getVarByName("x_" + v + "_" + i));
			_model.addConstr(lin_expr, GRB.EQUAL, 1.0, "Vertex_" + v);
		}

		for (int i = 0; i < chi_UpperBound; i++) {
			lin_expr = new GRBLinExpr();
			lin_expr.addTerm(1.0, _model.getVarByName("w_" + i));
			lin_expr.addTerm(-1.0, _model.getVarByName("w_" + (i + 1)));
			_model.addConstr(lin_expr, GRB.GREATER_EQUAL, 0.0, "Color_" + i);
		}

		for (int i = 0; i < chi_UpperBound; i++)
			for (int v = 0; v < n; v++)
				for (int u = 0; u < v; u++)
					if (adjacency[v][u]) {
						lin_expr = new GRBLinExpr();
						lin_expr.addTerm(1.0, _model.getVarByName("x_" + u + "_" + i));
						lin_expr.addTerm(1.0, _model.getVarByName("x_" + v + "_" + i));
						lin_expr.addTerm(-1, _model.getVarByName("w_" + i));
						_model.addConstr(lin_expr, GRB.LESS_EQUAL, 0.0, "Adj" + u + "_" + v + "_" + i);
					}

		for (int i = 0; i < chi_UpperBound; i++)
			for (int v = 0; v < i; v++) {
				lin_expr = new GRBLinExpr();
				lin_expr.addTerm(1.0, _model.getVarByName("x_" + v + "_" + i));
				_model.addConstr(lin_expr, GRB.EQUAL, 0.0, "UnderColor_" + v + "_" + i);
			}

		for (int i = 0; i < chi_UpperBound - 1; i++) {
			lin_expr = new GRBLinExpr();
			for (int v = 0; v < n; v++)
				lin_expr.addTerm(1.0, _model.getVarByName("x_" + v + "_" + i));
			for (int h = i; h < chi_UpperBound; h++) {
				lin_expr.addTerm(-Math.floorDiv(n, (h + 1)), _model.getVarByName("w_" + h));
				lin_expr.addTerm(Math.floorDiv(n, (h + 1)), _model.getVarByName("w_" + (h + 1)));
			}
			_model.addConstr(lin_expr, GRB.GREATER_EQUAL, 0.0, "Lower_" + i);
		}

		for (int i = 0; i < chi_UpperBound - 1; i++) {
			lin_expr = new GRBLinExpr();
			for (int v = 0; v < n; v++)
				lin_expr.addTerm(1.0, _model.getVarByName("x_" + v + "_" + i));
			for (int h = i; h < chi_UpperBound; h++) {
				lin_expr.addTerm(Math.floorDiv(-n, (h + 1)), _model.getVarByName("w_" + h));
				lin_expr.addTerm(-Math.floorDiv(-n, (h + 1)), _model.getVarByName("w_" + (h + 1)));
			}
			_model.addConstr(lin_expr, GRB.LESS_EQUAL, 0.0, "Upper_" + i);
		}

		lin_expr = new GRBLinExpr();
		lin_expr.addTerm(1, _model.getVarByName("w_" + chi_UpperBound));
		_model.addConstr(lin_expr, GRB.EQUAL, 0.0, "LastColor");

		_model.update();

		// Objective:
		for (int i = 0; i < chi_UpperBound; i++)
			objFunction.addTerm(1.0, _model.getVarByName("w_" + i));

		_model.setObjective(objFunction);
		_model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		_model.update();
		System.out.println("Model building time: " + (System.nanoTime() - buildTime) * 1e-9);
		M_model = _model;
		// M_model.write(path + "/results/" + fileName + "/model_original.lp");
	}

	public static boolean M_retrieveSolution() throws GRBException {
		GRBVar var;
		double val;
		boolean intSolution = true;

		solutionW = new double[chi_UpperBound + 1];
		solutionX = new double[n][n];

		solutionW[chi_UpperBound] = M_model.getVarByName("w_" + chi_UpperBound).get(GRB.DoubleAttr.X);
		for (int i = 0; i < chi_UpperBound; i++) {
			var = M_model.getVarByName("w_" + i);
			val = var.get(GRB.DoubleAttr.X);
			solutionW[i] = val;
			if (Math.abs(val) > precisionVar || Math.abs(1 - val) > precisionVar)
				intSolution = false;
			for (int v = 0; v < n; v++) {
				var = M_model.getVarByName("x_" + v + "_" + i);// TODO??!
				val = var.get(GRB.DoubleAttr.X);
				solutionX[v][i] = val;
				if (Math.abs(val) > precisionVar || Math.abs(1 - val) > precisionVar)
					intSolution = false;
			}
		}
		if (intSolution)
			System.out.println("Integer solution!");
		return intSolution;
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
		System.out.println("True equitable coloring");
		return true;
	}

	public static boolean checkTime(double totalTime) {
		if ((System.nanoTime() - totalTime) * 1e-9 > timeLimit * 3600)
			return false;
		return true;
	}

	public static void writeStepData(double totalTime) {
		NumberFormat nrformat = NumberFormat.getInstance();
		nrformat.setMaximumFractionDigits(2);
		try (BufferedWriter writer = new BufferedWriter(
				new FileWriter("../data/EqCol/results/" + fileName + "/finalSolutions_" + fileName + ".txt", true))) {
			writer.newLine();
			String nLine;
			System.out.println();
			nLine = "Step: " + step + ", #cuts: " + no_cuts + ", objective value: " + currentObj;
			System.out.println(nLine);
			writer.write(nLine);
			writer.newLine();

			nLine = "Lazy constraints: " + no_lazyConstraints + "; clique cuts: " + no_cliqueCuts + ", S-color cuts: "
					+ no_S_colorCuts + ", block cuts: " + no_blockCuts + ", 2-rank cuts: " + no_2_rankCuts + ".";
			System.out.println(nLine);
			writer.write(nLine);
			writer.newLine();

			nLine = "Time: " + nrformat.format((System.nanoTime() - totalTime) * 1e-9) + "s." + " Average time: "
					+ nrformat.format((System.nanoTime() - totalTime) * 1e-9 / step) + "s.";
			System.out.println(nLine);
			writer.write(nLine);
			writer.newLine();
			writer.close();

		} catch (IOException ex) {
			ex.printStackTrace();
		}
	}

	public static void initialize() {
		no_cuts = 0;
		no_cliqueCuts = 0;
		no_lazyConstraints = 0;
		no_S_colorCuts = 0;
		no_blockCuts = 0;
		no_2_rankCuts = 0;
		step = 0;
		max_steps = 30000;
		kClique = 7;
	}

	public static void cuttingPlaneAlg() throws GRBException {
		NumberFormat nrformat = NumberFormat.getInstance();
		nrformat.setMaximumFractionDigits(2);
		GRBEnv env = new GRBEnv();
		M_buildInitialModelO(env);
		int _mstatus;
		boolean newCuts = true;
		long totalTime = System.nanoTime();
		M_model.set(GRB.IntParam.OutputFlag, verbosity);
		while (step < max_steps && checkTime(totalTime)) {
			step++;
			M_model.set(GRB.DoubleParam.TimeLimit, timeLimit * 3600 - (System.nanoTime() - totalTime) * 1e-9);
			M_model.optimize();
			_mstatus = M_model.get(GRB.IntAttr.Status);
			newCuts = false;
			if (checkTime(totalTime) && _mstatus != GRB.Status.INFEASIBLE && _mstatus != GRB.Status.UNBOUNDED
					&& _mstatus != GRB.Status.INF_OR_UNBD) {
				currentObj = M_model.get(DoubleAttr.ObjVal);
				if (!M_retrieveSolution() && !newCuts) {
					no_cuts = 0;
					newCuts = add_lazyConstraints() || newCuts;
					newCuts = add_cliqueCuts(totalTime) || newCuts;
					newCuts = add_SColorCuts(totalTime) || newCuts;
					newCuts = add_blockColorCuts() || newCuts;
					newCuts = add_2RankCuts(totalTime) || newCuts;
					writeStepData(totalTime);
				}
				if (!newCuts) {
					System.out.println("No more cuts!");
					break;
				}
			}
			System.out.println();
		}
	}

	public static void main(String[] args) throws GRBException, IOException, InterruptedException {

		fileName = "dsjc250.5.col";
		/*
		if (args.length == 0) {
			System.err.println("Please specify the filename.");
			return;
		}
		fileName = args[0];
		*/
		
		verbosity = 0;
		timeLimit = 4;// hours

		initialize();
		chi_UpperBound = 29;
		createDir(path + "results");
		readFile(fileName);
		cuttingPlaneAlg();

	}
}