# The super_sketch tool manual
Super_sketch is a tool for automatically generating a proof for a lemma which can be proven using a method that breaks down the goal into multiple subgoals.
It makes use of the Sledgehammer tool in Isabelle.
Currently supports both Isabelle2023 and Isabelle2024.
## super_sketch versions:

To make it work for Isabelle2024, copy the files `Super.thy` and `Sledgehammer_Commands1.ML` into your working folder and import the theory as `Super`.

To make it work for Isabelle2023, copy the files `Super2023.thy` and `SC2023.ML` into your working folder and impor the theory as `Super2023`.

## Getting started
Invoke the utility by the command `super_sketch(...)`, where you fill in the `...` with some methods like `intro conjI`,`induct $VAR`, `cases $VAR` (where $VAR is a variable appearing in your theorem/lemma) and etc.
