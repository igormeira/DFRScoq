## Loading DFRS models in Coq

The Coq environment should be configured first (as typically performed -- see Coq's documentation). To test whether it has been properly configured, try opening the CoqIDE. Our Coq characterisation of DFRS models can be loaded according to the following steps:
- Run configure.sh (Linux): compiles all needed Coq files
- Run coqide.sh (Linux): opens CoqIDE considering our directory structure

The aforementioned scripts are for Linux only. If using other operating systems, these should be adapted accordingly. In summary, one should compile all *.v files, besides running the CoqIDE, considering our directory structure (see -R and -Q: [`link`](https://coq.inria.fr/refman/practical-tools/coq-commands.html)).

An example model is available in [`examples/vm`](examples/vm): it is a vending machine (VM), adapted from the coffee machine presented in [`Online Testing of Real-time Systems Using Uppaal`](https://doi.org/10.1007/978-3-540-31848-4_6).

Dependencies:
- Coq: [`link`](https://coq.inria.fr/) (tested with version 8.8.1)
- QuickChick: [`link`](https://github.com/QuickChick/QuickChick) (tested with version 1.0.1)
- CoqIDE [`link`](https://coq.inria.fr/download) (tested with version 8.8.1)

## Generating test cases

Test cases are generated according to the following steps (for instance, considering the VM):
- Open vm_samples.py (in [`examples/vm`](examples/vm))
- Change the variable "samplesNumber" (line 121) to the desired number of samples call
- Run vm_samples.py (python vm_samples.py) to generate raw test data
- Run vm_samples_csv.py (python vm_samples_csv.py) to generate formatted test data (files saved in /CSV)

Additional dependencies:
- Python: [`link`](https://www.python.org/) (tested with version 2.7.12)

