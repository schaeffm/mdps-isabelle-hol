# Verified Solver for Explicit MDPs
This project provides 
- a formalization of solution algorithms for MDPs in Isabelle/HOL.
- wrapper programs to parse MDPs and call the verified implementations.
- a Rust implementation of Gauss-Seidel value iteration.
- a Prism modification implementing discount factors.
- example MDPs compiled from the International Planning Competition 2018.

## Installation of Build Tools
### MLton
- Install [MLton](http://mlton.org/) from [here](https://github.com/MLton/mlton) (from binary package) or via the package manager of your system.

### Isabelle (optional)
- Install Isabelle 2021-1 from [here](https://isabelle.in.tum.de/installation.html)
- Make sure to install TeXLive for Isabelle/LaTeX document preparation
- Add the `isabelle` command to `PATH`, specifically `/path/to/installation/Isabelle2021-1/bin`.
- Download the AFP (version for Isabelle 2021-1) from [here](https://www.isa-afp.org/download.html)
- Follow the [instructions](https://www.isa-afp.org/using.html) to add it to Isabelle

## Verified Solvers
### Building
- The SML code exported from Isabelle/HOL is provided as part of this project.
- Thus exporting it is an optional step.

#### Build Solvers + Export Code from Isabelle (optional)
- To export the code yourself, first install Isabelle with the instructions above.
- Then run `./build_with_export.sh`, to build (recommended: 16G of memory and a recent CPU)

#### Build Solvers
- run `./build.sh` to build the verified solver
- the executables `MDP_Solver` and `MDP_Solver_Fin` are placed in `src/verified_solver/MDP_Solver`

### Running

#### File Format
We use a simple format to represent explicit MDPs:
- The 1st line gives the number of states
- The 2nd line gives the number of actions
- Each subsequent line describes a state-action pair: `<state> <action> <list of transitions> <reward>`
- Every transition has the form `(<successor> <probability>)`

An example can be found in the file `examples/states_wildlife-preserve_inst_mdp__01`.

#### Finite-Horizon Solver
The finite-horizon solver can be called as follows:

`
MDP_Solver_Fin FILE MODE HORIZON
`

where
- `FILE` is the path to the file with the MDP description
- `MODE` toggles precise arithmetic, it is one of
	- `float` (floating-point arithmetic)
	- `rational` (precise arithmetic)
- `HORIZON` a nonnegative number that sets the horizon of the MDP

Example invocations:
- `./MDP_Solver_Fin "states_game_of_life_inst_mdp__1" rational 10`
- `./MDP_Solver_Fin "states_navigation_inst_mdp__2" float 50`

##### Output
The solver reports on the progress of parsing and converting the MDP to the representation used by the verified solvers.
After the algorithm has completed, it outputs a list optimal decision rules for each epoch.


#### Infinite-Horizon Solver
The infinite-horizon solver can be called as follows:

`
MDP_Solver FILE ALGO DISC EPS MODE [INIT]
`

where
- `FILE` is the path to the file with the MDP description
- `ALGO` specifies the algorithm to be used, it is one of 
	- `vi` (Value Iteration)
	- `pi` (Policy Iteration)
	- `mpi` (Modified Policy Iteration)
	- `gs` (Gauss-Seidel Value Iteration)
- `DISC` is the discount factor in decimal notation (`0 <= DISC < 1`)
- `EPS` is the accuracy in decimal notation (`EPS > 0`, it has no effect if `ALGO` is `pi`)
- `MODE` toggles precise arithmetic, it is one of
	- `float` (floating-point arithmetic)
	- `rational` (precise arithmetic)
- `INIT` is an optional argument with a path to a file of initial values
	- this argument only works when ALGO is either `vi` or `gs`
	- each line of the file corresponds to a state of the MDP
	- the file contains a single initial value per line

Example invocations:
- `./MDP_Solver "states_game_of_life_inst_mdp__1" gs 0.8 0.05 rational`
- `./MDP_Solver "states_navigation_inst_mdp__2" vi 0.9 0.01 float values.txt`

##### Output
The solver reports on the progress of parsing and converting the MDP to the representation used by the verified solvers. After the algorithm has completed, it outputs a list with an optimal decision for each state.

### Examples
- You can find example MDPs and invocations of the solver in the directory `examples`.
- All MDPs are available [here](https://home.in.tum.de/~schaeffm/mdp/exhaustive-mdps.tar.gz)

## Rust Implementation (Infinite-Horizon MDPs)
### Building
- Install Rust (1.60) via [rustup](https://www.rust-lang.org/tools/install)
- Run `./build_rust.sh`
- The executable is placed at `src/rust_solver/target/release/solver_rust`

### Running
- Run `rust_solver FILE DISC EPS [OUTPUT]`
where
- `FILE`, `DISC`, `EPS` work as described above
- `OUTPUT` is an optional argument to output the state values of the solution line-by-line into the file `OUTPUT`
- this file can then be passed to the verified infinite-horizon solver `MDP_Solver

## PRISM
Our modified PRISM variant can be found at `src/prism`.
