# DFRScoq

This project aims at providing a Coq characterisation for models of timed data-flow reactive systems, a class of embedded systems whose inputs and outputs are always available as signals. Input signals can be seen as data provided by sensors, whereas the output data are provided to system actuators. The Coq characterisation allows for a scalable and single framework for specifying, validating, verifying and testing such systems. For a comprehensive explanation of DFRS models, we refer to:

- Modelling timed reactive systems from natural-language requirements ([`link`](https://doi.org/10.1007/s00165-016-0387-x))

## Repository structure

- [`analyses`](/analyses): contains the necessary files to reproduce our empirical analyses;
- [`run`](/run): contains Python scripts to automate the execution of our empirical analyses;
- [`src`](/src): contains the *.v files related to our characterisation of DFRSs in Coq.

## Reproducing our empirical analyses

In order to reproduce our empirical analyses, one should perform the following steps:

1. Compile our Coq characterisation of timed data-flow reactive systems (see [`link`](/src));

2. Copy all folders from [`analyses`](/analyses) to the directory where SRCIROR has been installed;

3. Configure the parameters declared in [`run.py`](/run/run.py) 

\# List of examples (possibilities = "vm", "tis" and/or "npp")\
examplesToRun = ["vm","tis","npp"]\
\# List of number of Sample calls for each example\
samplesNumber = [1,5,10]\
\# Number of replications for each Sample call and for each example\
replications = 5\
\# Path to SRCIROR\
srcirorPath = "/home/ghpc/Documents/srciror"

4. Run the main Python script: python run.py

This script will perform the following tasks:

- generate test cases for the selected examples;
- process the QuickChick output and save test data into *.csv files;
- generate mutants from C reference implementations;
- run all test cases against all mutants;
- collect and summarise empirical data.

The obtained results are summarised in the file [`all_results.csv`](/run/Analyses/all_results.csv).\
R code for creating box plots is made available in the directory [`R`](/run/R).

Dependencies:

- Coq: [`link`](https://coq.inria.fr/) (tested with version 8.8.1)
- QuickChick: [`link`](https://github.com/QuickChick/QuickChick) (tested with version 1.0.1)
- Python: [`link`](https://www.python.org/) (tested with version 2.7.12)
- Python 3: [`link`](https://www.python.org/) (tested with version 3.5.2)
- Java: [`link`](https://www.oracle.com/technetwork/java/javase/downloads/index.html) (tested with version 1.8.0_121)
- SRCIROR: [`link`](https://github.com/TestingResearchIllinois/srciror/)
