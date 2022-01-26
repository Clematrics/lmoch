# *lmoch* project - synchronous systems

## INSTALLATION

The build system used is `dune`. `Z3`, version `4.8.11` is required, and can be installed with opam.
Alt-ergo Zero requires the packages `num` and `unix`.
```sh
opam install dune z3
dune build # to build the project
```

# USAGE

Run the program with the command
```sh
dune exec lmoch -- <file> <node_name> [options]
```

Example:

To check the property on the node `cnt` in the file `nodes` using the Z3 and Alt-ergo Zero solvers, use
```
dune exec lmoch -- bin/nodes.lus cnt -z3 -aez
```

# DOCUMENTATION

The documentation can be compiled with the command `dune build @doc` and found at `_build/default/_doc/_html/index.html`