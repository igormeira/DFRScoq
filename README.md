# DFRScoq

This project aims at providing a Coq characterisation for models of data-flow reactive systems, a class of embedded systems whose inputs and outputs are always available as signals. Input signals can be seen as data provided by sensors, whereas the output data are provided to system actuators. The Coq characterisation allows for a single framework for specifying, analysing and testing such systems. For a comprehensive explanation of DFRS models, we refer to:

- Modelling timed reactive systems from natural-language requirements ([link](https://doi.org/10.1007/s00165-016-0387-x))

## Repository structure

The directory [`src`](src) contains the *.v files related to the characterisation of DFRSs in Coq.<br>
The directory [`analyses`](analyses) contains empirical data related to performance and mutant-based strength analyses.
