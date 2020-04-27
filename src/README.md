# Loading DFRS models in Coq

The Coq environment should be configured first (see Coq's documentation). To test whether it has been properly configured, try opening the CoqIDE. Our Coq characterisation of DFRS models can be loaded according to the following steps:

- Run configure.sh (Linux): compiles all needed Coq files
- Run coqide.sh (Linux): opens CoqIDE considering our directory structure

The aforementioned scripts are for Linux only. If using other operating systems, these should be adapted accordingly: compile all *.v files, and run CoqIDE considering our directory structure (see -R and -Q: [`link`](https://coq.inria.fr/refman/practical-tools/coq-commands.html)).

Three models are available in [`examples`](https://github.com/igormeira/DFRScoq/tree/master/src/examples):

- NPP: control system for safety injection in a nuclear power plant (described in this [`paper`](https://doi.org/10.1023/A:1023072104553));
- TIS: part of the turn indicator system of Mercedes vehicles (specification: [`link`](http://www.informatik.uni-bremen.de/agbs/testingbenchmarks/turn_indicator/index_e.html));
- VM: vending machine (adapted from this [`paper`](https://doi.org/10.1007/978-3-540-31848-4_6)).

Dependencies:

- Coq: [`link`](https://coq.inria.fr/) (tested with version 8.8.1)
- QuickChick: [`link`](https://github.com/QuickChick/QuickChick) (tested with version 1.0.1)
- CoqIDE: [`link`](https://coq.inria.fr/download) (tested with version 8.8.1)
