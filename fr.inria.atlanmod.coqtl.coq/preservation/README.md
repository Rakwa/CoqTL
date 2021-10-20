This folder contains an evaluation for the article entitled **Deep Specification and Proof Preservation for the CoqTL Transformation Language**.

The goal of this evaluation is to show that CoqTL, under different evolution scenarios, can preserve or don't preserve 4 kinds of artifact:
  * User proofs on base specification (USoBS)
  * User proofs on child specification (USoCS)
  * Base specification certification (BSC)
  * Child specification certification (CSC)

The considered evolution scenarios are:
  * Child specification add/modify (CS_add/CS_modify)
  * Base specification certification add/modify (BSC_add/BSC_modify)
  * Child specification certification add/modify (CSC_add/CSC_modify)

To perform this evaluation, we:
  * create a snapshot of CoqTL ([this folder](./clean/))
  * simulate a evolution scenario (each under its specific folder, e.g. [this folder](./bsc/add/))
  * run a test driver (e.g. [this file](./bsc_add.py))) for each scenario to recompile the snapshot of coqtl, to see any artifects are break. 

To reproduce the result that is summarized in the table.3 of our article.

  1. first, navigate to the `clean` folder in the command line

  2. `./compile.sh` to create a compiled snapshot of CoqTL

  3. run each test driver that corresponds to each evolution scenario, the expected result is all tests pass (the oracle of each test specifies whether it should break or not).