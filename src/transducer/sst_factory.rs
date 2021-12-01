use super::sst::Sst;
use super::term::{FunctionTerm, Lambda, OutputComp, UpdateComp, VariableImpl};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::char_util::FromChar;
use crate::regular::{regex::Regex, symbolic_automata::Sfa};
use crate::smt2::{ReplaceTarget, Transduction, TransductionOp};
use crate::state::{StateImpl, StateMachine, Mutable};
use std::{
  collections::{HashMap, HashSet},
  rc::Rc,
};

pub struct SstBuilder<T: FromChar, S: StateImpl, V: VariableImpl> {
  ssts: Vec<Sst<T, S, V>>,
  vars: Vec<V>,
  init_states: Vec<S>
}
impl<T: FromChar, S: StateImpl, V: VariableImpl> SstBuilder<T, S, V> {
  pub(crate) fn blank() -> Self {
    SstBuilder {
      ssts: vec![],
      vars: vec![],
      init_states: vec![]
    }
  }

  pub fn replace_all_reg(&self, reg: Regex<T>, replace: Vec<OutputComp<T, V>>) -> Sst<T, S, V> {
    assert_ne!(reg, Regex::Empty);
    assert_ne!(reg, Regex::Epsilon);

    let replace_update = replace
      .iter()
      .map(|out| match out {
        OutputComp::A(a) => UpdateComp::F(Lambda::constant(T::clone(a))),
        OutputComp::X(var) => UpdateComp::X(V::clone(var)),
      })
      .collect::<Vec<_>>();
    let sfa = reg.to_sym_fa();
    /*
     * used for back to initial state when failing to match.
     * calculate all predicate which is not used for any transition from given state
     */
    let not_predicates = sfa
      .states()
      .iter()
      .map(|state| (S::clone(state), sfa.state_predicate(state).not()))
      .collect::<HashMap<_, _>>();
    let Sfa {
      states,
      transition,
      initial_state,
      final_states,
    } = sfa;
    /* whole result variable */
    let res = V::new();
    /* accumulator variable of current matches */
    let acc = V::new();
    let variables = HashSet::from([V::clone(&res), V::clone(&acc)]);
    let initial_maps = transition
      .iter()
      .filter(|((p, _), _)| *p == initial_state)
      .collect::<Vec<_>>();
    let transition = transition
      .iter()
      .flat_map(|((p, phi), q)| {
        if final_states.contains(p) {
          /* transition for final states is created by next chain */
          vec![]
        } else {
          /*
           * variable maps
           */
          let update = HashMap::from([
            (V::clone(&res), vec![UpdateComp::X(V::clone(&res))]),
            (
              V::clone(&acc),
              vec![
                UpdateComp::X(V::clone(&acc)),
                UpdateComp::F(Lambda::identity()),
              ],
            ),
          ]);
          let reset = HashMap::from([
            (
              V::clone(&res),
              vec![
                UpdateComp::X(V::clone(&res)),
                UpdateComp::X(V::clone(&acc)),
                UpdateComp::F(Lambda::identity()),
              ],
            ),
            (V::clone(&acc), vec![]),
          ]);
          let start = HashMap::from([
            (
              V::clone(&res),
              vec![UpdateComp::X(V::clone(&res)), UpdateComp::X(V::clone(&acc))],
            ),
            (V::clone(&acc), vec![UpdateComp::F(Lambda::identity())]),
          ]);
          /* v - result of this iteration */
          let mut v = initial_maps
            .iter()
            .map(|((_, sphi), sq)| {
              /* they're first char of a given regex */
              (
                (
                  S::clone(p),
                  not_predicates.get(p).unwrap_or(&Predicate::bot()).and(sphi),
                ),
                (S::clone(*sq), start.clone()),
              )
            })
            .collect::<Vec<_>>();
          v.push((
            /* failed to match next and any first char of the regex */
            (
              S::clone(p),
              not_predicates.get(p).unwrap_or(&Predicate::bot()).and(
                not_predicates
                  .get(&initial_state)
                  .unwrap_or(&Predicate::bot()),
              ),
            ),
            (S::clone(&initial_state), reset),
          ));
          /* matches current target char and go to next state. */
          v.push(((S::clone(p), Rc::clone(phi)), (S::clone(q), update)));
          v
        }
      })
      .chain(final_states.iter().flat_map(|p| {
        /* succeed to match and try to next match */
        let start = HashMap::from([
          (V::clone(&res), {
            let mut v = vec![UpdateComp::X(V::clone(&res))];
            v.extend(replace_update.iter().map(|up| up.clone()));
            v
          }),
          (V::clone(&acc), vec![UpdateComp::F(Lambda::identity())]),
        ]);
        let reset = HashMap::from([
          (V::clone(&res), {
            let mut v = vec![UpdateComp::X(V::clone(&res))];
            v.extend(replace_update.iter().map(|up| up.clone()));
            v.push(UpdateComp::F(Lambda::identity()));
            v
          }),
          (V::clone(&acc), vec![]),
        ]);
        let mut v = initial_maps
          .iter()
          .map(|((_, phi), q)| ((S::clone(p), Rc::clone(phi)), (S::clone(*q), start.clone())))
          .collect::<Vec<_>>();
        v.push((
          (
            S::clone(p),
            Rc::clone(
              not_predicates
                .get(&initial_state)
                .unwrap_or(&Predicate::bot()),
            ),
          ),
          (S::clone(&initial_state), reset),
        ));
        v
      }))
      .collect();
    let output_function = states
      .iter()
      .map(|state| {
        if final_states.contains(state) {
          /* if ending at the final state of given regex, replace it with output and dump acc */
          (S::clone(state), {
            let mut v = vec![OutputComp::X(V::clone(&res))];
            v.extend(replace.iter().map(|out| out.clone()));
            v
          })
        } else {
          (
            S::clone(state),
            vec![OutputComp::X(V::clone(&res)), OutputComp::X(V::clone(&acc))],
          )
        }
      })
      .collect();
    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn replace_reg(&self, reg: Regex<T>, replace: Vec<OutputComp<T, V>>) -> Sst<T, S, V> {
    assert_ne!(reg, Regex::Empty);
    assert_ne!(reg, Regex::Epsilon);

    let replace_update = replace
      .iter()
      .map(|out| match out {
        OutputComp::A(a) => UpdateComp::F(Lambda::constant(T::clone(a))),
        OutputComp::X(var) => UpdateComp::X(V::clone(var)),
      })
      .collect::<Vec<_>>();

    let sfa = reg.to_sym_fa();
    /*
     * used for back to initial state when failing to match.
     * calculate all predicate which is not used for any transition from given state
     */
    let not_predicates = sfa
      .states()
      .iter()
      .map(|state| (S::clone(state), sfa.state_predicate(state).not()))
      .collect::<HashMap<_, _>>();
    let Sfa {
      mut states,
      transition,
      initial_state,
      final_states,
    } = sfa;
    /* whole result variable */
    let res = V::new();
    /* accumulator variable of current matches */
    let acc = V::new();
    let variables = HashSet::from([V::clone(&res), V::clone(&acc)]);
    let initial_maps = transition
      .iter()
      .filter(|((p, _), _)| *p == initial_state)
      .collect::<Vec<_>>();
    /* once matches given regex, cycle and stack the rest of input on result */
    let cycle_state = S::new();
    let top = Predicate::top();
    let mut transition = transition
      .iter()
      .flat_map(|((p, phi), q)| {
        if final_states.contains(p) {
          /* transition for final states is created by next chain */
          vec![]
        } else {
          /*
           * variable maps
           */
          let update = HashMap::from([
            (V::clone(&res), vec![UpdateComp::X(V::clone(&res))]),
            (
              V::clone(&acc),
              vec![
                UpdateComp::X(V::clone(&acc)),
                UpdateComp::F(Lambda::identity()),
              ],
            ),
          ]);
          let reset = HashMap::from([
            (
              V::clone(&res),
              vec![
                UpdateComp::X(V::clone(&res)),
                UpdateComp::X(V::clone(&acc)),
                UpdateComp::F(Lambda::identity()),
              ],
            ),
            (V::clone(&acc), vec![]),
          ]);
          let start = HashMap::from([
            (
              V::clone(&res),
              vec![UpdateComp::X(V::clone(&res)), UpdateComp::X(V::clone(&acc))],
            ),
            (V::clone(&acc), vec![UpdateComp::F(Lambda::identity())]),
          ]);
          /* v - result of this iteration */
          let mut v = initial_maps
            .iter()
            .map(|((_, sphi), sq)| {
              /* they're first char of a given regex */
              (
                (
                  S::clone(p),
                  not_predicates.get(p).unwrap_or(&Predicate::bot()).and(sphi),
                ),
                (S::clone(*sq), start.clone()),
              )
            })
            .collect::<Vec<_>>();
          v.push((
            /* failed to match next and any first char of the regex */
            (
              S::clone(p),
              not_predicates.get(p).unwrap_or(&Predicate::bot()).and(
                not_predicates
                  .get(&initial_state)
                  .unwrap_or(&Predicate::bot()),
              ),
            ),
            (S::clone(&initial_state), reset),
          ));
          /* matches current target char and go to next state. */
          v.push(((S::clone(p), Rc::clone(phi)), (S::clone(q), update)));
          v
        }
      })
      .chain(final_states.iter().flat_map(|p| {
        /* succeed to match and go to cycle state */
        let to_cycle = HashMap::from([(V::clone(&res), {
          let mut v = vec![UpdateComp::X(V::clone(&res))];
          v.extend(replace_update.iter().map(|up| up.clone()));
          v.push(UpdateComp::F(Lambda::identity()));
          v
        })]);
        vec![(
          (S::clone(&p), Rc::clone(&top)),
          (S::clone(&cycle_state), to_cycle),
        )]
      }))
      .collect::<HashMap<_, _>>();
    transition.insert(
      (S::clone(&cycle_state), Rc::clone(&top)),
      (
        S::clone(&cycle_state),
        HashMap::from([(
          V::clone(&res),
          vec![
            UpdateComp::X(V::clone(&res)),
            UpdateComp::F(Lambda::identity()),
          ],
        )]),
      ),
    );
    let mut output_function = states
      .iter()
      .map(|state| {
        if final_states.contains(state) {
          (S::clone(state), {
            let mut v = vec![OutputComp::X(V::clone(&res))];
            v.extend(replace.iter().map(|out| out.clone()));
            v
          })
        } else {
          (
            S::clone(state),
            vec![OutputComp::X(V::clone(&res)), OutputComp::X(V::clone(&acc))],
          )
        }
      })
      .collect::<HashMap<_, _>>();
    /* states is used in above iteration, so update it at this line */
    states.insert(S::clone(&cycle_state));
    output_function.insert(S::clone(&cycle_state), vec![OutputComp::X(V::clone(&res))]);
    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn reverse(&self) -> Sst<T, S, V> {
    let initial_state = S::new();
    let res = V::new();
    let mut states = HashSet::new();
    states.insert(S::clone(&initial_state));
    let mut variables = HashSet::new();
    variables.insert(V::clone(&res));
    let mut output_function = HashMap::new();
    output_function.insert(
      S::clone(&initial_state),
      vec![OutputComp::X(V::clone(&res))],
    );
    let mut transition = HashMap::new();
    let mut map = HashMap::new();
    map.insert(
      V::clone(&res),
      vec![UpdateComp::F(Lambda::identity()), UpdateComp::X(res)],
    );
    transition.insert(
      (S::clone(&initial_state), Predicate::top()),
      (S::clone(&initial_state), map),
    );

    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn identity(&self) -> Sst<T, S, V> {
    let initial_state = S::new();
    let res = V::new();

    let mut states = HashSet::new();
    states.insert(S::clone(&initial_state));
    let mut variables = HashSet::new();
    variables.insert(V::clone(&res));
    let mut output_function = HashMap::new();
    output_function.insert(
      S::clone(&initial_state),
      vec![OutputComp::X(V::clone(&res))],
    );
    let mut transition = HashMap::new();
    let mut map = HashMap::new();
    map.insert(
      V::clone(&res),
      vec![UpdateComp::X(res), UpdateComp::F(Lambda::identity())],
    );
    transition.insert(
      (S::clone(&initial_state), Predicate::top()),
      (S::clone(&initial_state), map),
    );

    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn constant(&self, output: &str) -> Sst<T, S, V> {
    let initial_state = S::new();
    let mut states = HashSet::new();
    states.insert(S::clone(&initial_state));
    let mut variables = HashSet::new();
    let mut output_function = HashMap::new();
    output_function.insert(
      S::clone(&initial_state),
      output
        .chars()
        .map(|c| OutputComp::A(T::from_char(c)))
        .collect(),
    );
    let mut transition = HashMap::new();
    transition.insert(
      (S::clone(&initial_state), Predicate::top()),
      (S::clone(&initial_state), HashMap::new()),
    );

    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }
}

#[cfg(test)]
mod tests {
  use super::super::term::Variable;
  use super::*;
  use crate::state::State;
  use std::iter::FromIterator;

  fn chars(s: &str) -> Vec<char> {
    s.chars().collect::<Vec<char>>()
  }

  type TestBuilder = SstBuilder<char, Rc<State>, Rc<Variable>>;

  #[test]
  fn identity() {
    let test = TestBuilder::blank();
    let id = test.identity();

    assert_eq!(
      String::from_iter(&id.run(&chars("")[..])[0]),
      "".to_string()
    );
    assert_eq!(
      String::from_iter(&id.run(&chars("xyx")[..])[0]),
      "xyx".to_string()
    );
    assert_eq!(
      String::from_iter(&id.run(&chars("abcdefg")[..])[0]),
      "abcdefg".to_string()
    );
  }

  #[test]
  fn constant() {
    let test = TestBuilder::blank();
    let cnst = "this is a constant".to_string();
    let id = test.constant(&cnst);

    assert_eq!(String::from_iter(&id.run(&chars("")[..])[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("xyx")[..])[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("abcdefg")[..])[0]), cnst);
  }

  #[test]
  fn reverse() {
    let test = TestBuilder::blank();
    let rev = test.reverse();

    assert_eq!(
      String::from_iter(&rev.run(&chars("")[..])[0]),
      "".to_string()
    );
    assert_eq!(
      String::from_iter(&rev.run(&chars("xyx")[..])[0]),
      "xyx".to_string()
    );
    assert_eq!(
      String::from_iter(&rev.run(&chars("abcdefg")[..])[0]),
      "gfedcba".to_string()
    );
  }

  #[test]
  #[should_panic]
  fn reject_empty_substr_all_reg() {
    let test = TestBuilder::blank();
    let _rep = test.replace_all_reg(Regex::Empty, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_all_reg() {
    let test = TestBuilder::blank();
    let _rep = test.replace_all_reg(Regex::Epsilon, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_all_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_all_reg(
      Regex::parse("abc").unwrap(),
      "xyz".chars().map(|c| OutputComp::A(c)).collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc")[..])[0]),
      "xyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a")[..])[0]),
      "a".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc")[..])[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcababc")[..])[0]),
      "xyzabxyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg")[..])[0]),
      "xyzxyzxyzaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn a_to_many_all_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_all_reg(
      Regex::parse("a").unwrap(),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\"
        .chars()
        .map(|c| OutputComp::A(c))
        .collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc")[..])[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a")[..])[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc")[..])[0]),
      "bc".to_string()
    );
    assert_eq!(
            String::from_iter(
                &rep.run(&chars("abcabcabcaaabbaccbackljhg")[..])[0]
            ),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ccbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ckljhg".to_string()
        );
  }

  #[test]
  fn abcxyz_to_1_all_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_all_reg(
      Regex::parse("abcxyz").unwrap(),
      "1".chars().map(|c| OutputComp::A(c)).collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxyz")[..])[0]),
      "1".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxy")[..])[0]),
      "abcxy".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcyz")[..])[0]),
      "abcyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("aaaabcxyzabcxyabcxyzzzabcxyz")[..])[0]),
      "aaa1abcxy1zz1".to_string()
    );
  }

  #[test]
  #[should_panic]
  fn reject_empty_substr_reg() {
    let test = TestBuilder::blank();
    let _rep = test.replace_reg(Regex::Empty, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_reg() {
    let test = TestBuilder::blank();
    let _rep = test.replace_reg(Regex::Epsilon, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_reg(
      Regex::parse("abc").unwrap(),
      "xyz".chars().map(|c| OutputComp::A(c)).collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc")[..])[0]),
      "xyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a")[..])[0]),
      "a".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc")[..])[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcababc")[..])[0]),
      "xyzababc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg")[..])[0]),
      "xyzabcabcaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn a_to_many_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_reg(
      Regex::parse("a").unwrap(),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\"
        .chars()
        .map(|c| OutputComp::A(c))
        .collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc")[..])[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a")[..])[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc")[..])[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg")[..])[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcabcabcaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn abcxyz_to_1_reg() {
    let test = TestBuilder::blank();
    let rep = test.replace_reg(
      Regex::parse("abcxyz").unwrap(),
      "1".chars().map(|c| OutputComp::A(c)).collect(),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxyz")[..])[0]),
      "1".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxy")[..])[0]),
      "abcxy".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcyz")[..])[0]),
      "abcyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("aaaabcxyzabcxyabcxyzzzabcxyz")[..])[0]),
      "aaa1abcxyabcxyzzzabcxyz".to_string()
    );
  }
}
