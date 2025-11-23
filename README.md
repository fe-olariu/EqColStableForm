
# Equitable coloring LP model (for Column Generation)

This repository contains two Java implementations of optimization algorithms for solving the Equitable Coloring Problem: **CuttingPlane** and **BranchPrice**.

# Repository Structure

```
project/
│
├── bin/                      # Compiled .class files (CuttingPlane.class, BranchPrice.class)
└── lib/                      # The libraries required: gurobi.jar, graph4j-1.0.8.jar, etc.
├── src/                      # The .java source files
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

If running on Linux, make sure run.sh is executable: 

```
chmod +x run.sh

```

Benchmark instances can be obtained at: [https://mat.tepper.cmu.edu/COLOR02/INSTANCES](https://mat.tepper.cmu.edu/COLOR02/INSTANCES)


# Requirements
- [Java 11](https://www.oracle.com/java/technologies/downloads/) or newer
- [Gurobi Optimizer 13](https://www.gurobi.com/solutions/gurobi-optimizer/)
    - Must be installed and licensed.
    - Gurobi Java bindings must be correctly set in your environment.

Windows:

```
GUROBI_HOME="C:\Apps\gurobi1300\win64"    # Modify path accordingly
PATH="%PATH%;%GUROBI_HOME%\bin"
```

Linux:

```
GUROBI_HOME="/opt/gurobi1300/linux64"     # Modify path accordingly
PATH="$PATH:$GUROBI_HOME/bin"
```