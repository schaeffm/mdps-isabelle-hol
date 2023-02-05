use crate::mdp::mdp::*;

use nom::{
    IResult,
    multi::{many0, many1},
    combinator::{recognize, map_res, },
    sequence::{ delimited, pair},
    character::complete::{digit1},
    number::complete::double,
    bytes::complete::tag,
    error::ParseError,
    character::complete::multispace0,
  };
/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and 
/// trailing whitespace, returning the output of `inner`.
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
  where
  F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
  delimited(
    multispace0,
    inner,
    multispace0
  )
}

  fn parse_u64(input : &str) -> IResult<&str, u64> {
    map_res(recognize(digit1), str::parse)(input)
}


fn parse_usize(input : &str) -> IResult<&str, usize> {
    map_res(recognize(digit1), str::parse)(input)
}

fn parse_transition(input : &str) -> IResult<&str, (usize, f64)> {
    let (input, _) = multispace0(input)?;
    let (input, (s, p)) = delimited(tag("("), pair(ws(parse_u64), ws(double)) , tag(")"))(input)?;
    let (input, _) = multispace0(input)?;

    Ok((input, (s as usize, p)))
}

fn parse_transitions(input : &str) -> IResult<&str, Vec<(usize, f64)>> {
    many1(parse_transition)(input)
}

fn parse_reward(input : &str) -> IResult<&str, f64> {
    double(input)
}

fn parse_act(input: &str) -> IResult<&str, (S, A, Action)> {
    let (input, s) = ws(parse_usize)(input)?;
    let (input, a) = ws(parse_usize)(input)?;

    let (input, mut ts) = parse_transitions(input)?;
    let p_total : f64 = ts.iter().map(|p| p.1).sum();
    ts.sort_by(|(k, v), (k2, v2)| f64::partial_cmp(&-v, &-v2).unwrap());
    ts[0] = (ts[0].0, ts[0].1 + (1.0 - p_total));

    let (input, r) = ws(parse_reward)(input)?;

    let act = Action {
        probs : ts,
        reward : r,
    };

    Ok((input, (s,a,act)))
  }

pub fn parse_mdp_states(input: &str) -> IResult<&str, Vec<State>> {
    let (input, num_states) = ws(parse_usize)(input)?;
    //println!{"number of states {}", num_states};
    let (input, _num_actions) = ws(parse_usize)(input)?;
    //println!{"number of actions {}", _num_actions};

    let (input, ts) = many0(parse_act)(input)?;
    
    let mut states : Vec<State> = vec!(State{transitions: std::collections::HashMap::new()}; num_states);

    for (s,a,act) in ts {
        let t = &mut states[s].transitions;
        t.insert(a, act);
    }

    //println!{"ts {:?}", states[0]};

    Ok((input, states))
}
