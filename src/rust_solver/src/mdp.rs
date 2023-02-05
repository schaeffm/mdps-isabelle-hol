pub mod mdp{

use std::collections::HashMap;
pub type S = usize;
pub type A = usize;

#[derive(Clone, Debug)]
pub struct Action {
    pub reward : f64,
    pub probs : Vec<(S, f64)>,
}

#[derive(Clone, Debug)]
pub struct State {
    pub transitions : HashMap<A, Action>
}

#[derive(Clone, Debug)]
pub struct MDP {
    pub states : Vec<State>,
    
    pub values: Vec<f64>,
    pub values_old: Vec<f64>,
    pub disc: f64,
    pub eps : f64
}
}
