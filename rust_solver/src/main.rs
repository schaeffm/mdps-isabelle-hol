mod parser;
mod mdp;
use mdp::mdp::*;
use std::env;
use std::fs::File;
use std::io::Write;

impl MDP {

    fn la(self : &Self, a : &Action) -> f64 {
        let exp : f64 = a.probs.iter().map(|(s, p)| -> f64 {p * self.values[*s]}).sum();
        a.reward + self.disc * exp
    }

    fn bellman_step(self : &Self, s : &State) -> f64 {
        s.transitions.iter().map(|(_, ts)| -> f64 {self.la(ts)}).fold(f64::NEG_INFINITY, f64::max)
    }
    
    fn bellman_argmax(self : &Self, s : &State) -> A {
        let mut max = f64::NEG_INFINITY;
        let mut am = 0;
        
        for (a,ts) in s.transitions.iter() {
            let va = self.la(ts);
            if max < va {
                max = va;
                am = *a;
            }
        }

        am
    }

    fn find_policy(self : &Self) -> Vec<A> {
        let mut d = vec!(0; self.states.len());

        for (i, a) in d.iter_mut().enumerate() {
            *a = self.bellman_argmax(&self.states[i]);
            //println!{"{}", a_opt}
        }
        
        d
    }

    fn vi_step(self : &mut Self) -> f64 {
        //println!{"."};
        let mut change:f64 = 0.0;
        for (s, _) in self.states.iter().enumerate() {
            let old = self.values[s];
            let new = self.bellman_step(&self.states[s]);
            change = f64::max(change, f64::abs(old-new));
            self.values[s] = new;
        }
        change
    }

    fn check_dist(self : &Self, change : f64) -> bool {
        2.0 * self.disc * change < self.eps * (1.0 - self.disc) 
    }

    pub fn solve(self : &mut Self) -> Vec<A> {
        let mut change;

        loop {
            change = MDP::vi_step(self);
            if MDP::check_dist(self, change) {
                break
            }
        }

        self.find_policy()
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    
    let disc : f64= str::parse(&args[2]).unwrap(); 
    let eps : f64= str::parse(&args[3]).unwrap(); 
    
    let path = &args[1];
    let input = std::fs::read_to_string(path).unwrap();
    //println!("read file: {}", input);

    let (_, states) = parser::parse_mdp_states(&input).unwrap();

    let mut mdp = MDP {
        values : vec!(0.0; states.len()),
        values_old : vec!(0.0; states.len()),
        disc,
        eps,
        states,
    };

    let d = mdp.solve();
    println!("{:?}", d);

    if args.len() >= 5 {
    let mut write_data = String::new();
    use std::fmt::Write;
    for v in mdp.values{
        writeln!(write_data, "{}", v).unwrap();
    }

    let value_path = &args[4];
    let mut f = File::create(value_path).expect("Unable to create file");
    f.write_all(write_data.as_bytes()).expect("Unable to write data");
    }

}
