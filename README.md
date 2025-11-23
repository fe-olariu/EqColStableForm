
# Equitable coloring LP model (for Column Generation)

This repository contains two Java implementations of optimization algorithms for solving the Equitable Coloring Problem: **CuttingPlane** and **BranchPrice**.

# Repository Structure

```
project/
│
├── src/                      # The .java source files
├── bin/                      # Compiled .class files (CuttingPlane.class, BranchPrice.class)
└── lib/                      # The libraries required: gurobi.jar, grah4j.jar, etc.
└── run.bat                   # Utility file for running the algorithms in Windows
└── run.sh                    # Utility file for running the algorithms in Linux
│
data/
│
└── EqCol/
    ├── instances/            # Input .col files
    └── results/              # Output results

```

# Running the algorithms
Running the algorithms can be done using **run.bat** or **run.sh** files.

The **first argument** is name of the algorithm, the **second argument** is the name of the input file.

Examples:

```
run.bat BranchPrice le450_25c.col     # Windows
.\run.sh CuttingPlane dsjc250.5.col   # Linux

```

If running on Linux make sure run.sh is executable: 

```
chmod +x run.sh

```


# Requirements
- **Java 11 or newer**
- **Gurobi Optimizer 13**
    - Must be installed and licensed.
    - Gurobi Java bindings must be correctly set in your environment.
 