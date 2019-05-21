# DFRScoq
DFRScoq is a representation of DFRS in Coq. This repository also contains files to running tests to a Vending Machine, written in Python, and files to performs mutations on tests, written in C and Java, using the SRCIROR project.  

### Runnig DFRScoq:

0. Need dependencies:
    * Coq 8.8.1
    * QuickChick
    * Python
    * Python3
    * clang
    * lib32z1-dev (If you are in Linux)
    * wget (If you are in MacOS)
    * srciror
    
1. Run the samples to the VM example. See src/README.

2. Run the mutator for VM example. See analyses/README.
    
### Own Analyses:

Our own analyses can be found in analyses/VM_srciror/raw_testcases/analyses.ods.
