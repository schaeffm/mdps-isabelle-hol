echo "Solving states_wildlife-preserve_inst_mdp__01 
	using Gauss-Seidel Value Iteration, 
	with a discount factor of 0.9, 
	accuracy of 0.001,
	precise arithmetic"
../src/verified_solver/MDP_Solver states_wildlife-preserve_inst_mdp__01 gs 0.9 0.001 rational

