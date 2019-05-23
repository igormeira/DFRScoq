## Performing performance and mutant-based strength analyses

Generated test cases can be evaluated, considering a mutant-based strength analysis, according to the following steps (for instance, considering the VM):

- Copy all test data (csv files) into the testcases directory ([`VM_srciror/testcases`](VM_srciror/testcases))
- Open main.c ([`VM_srciror`](VM_srciror)), and change "NUM_TCs" (line 2) to the number of csv files
- Run mutateSRC.sh to generate mutants for the *.c file in /mutants ([`VM_srciror/mutants`](VM_srciror/mutants))
- Open renamer.java, and change "MUTANTS" (line 12) to the number of generated mutants
- Compile renamer.java (javac renamer.java)
- Run renamer.class (java renamer)
- Run the script run.sh to perform mutant-based strength analysis (performance data printed to the console)

The last command produces a file "output.txt" (in [`VM_srciror`](VM_srciror)) with "Passed" or "Failed" (one per line) for each generated mutant. The ratio (\# Failed)/(\# mutants) is the so-called mutation score metric. The aforementioned scripts (*.sh) are for Linux only. If using other operating systems, these should be adapted accordingly.

The folder [`VM_srciror/raw_testcases`](VM_srciror/raw_testcases) contains all test cases considered by our submission to [`SEFM 2019`](http://sefm2019.inria.fr/), grouped by 1, 5 and 10 calls to the QuickChick Sample function. The archive [`VM_srciror/raw_testcases/analyses.ods`](VM_srciror/raw_testcases/) has some post-processed data (performance analysis and mutation score).

Dependencies:

- Java: [`link`](https://www.oracle.com/technetwork/java/javase/downloads/index.html) (tested with version 1.8.0_121)
- Python 3: [`link`](https://www.python.org/) (tested with version 3.5.2)
- SRCIROR: [`link`](https://github.com/TestingResearchIllinois/srciror/)
