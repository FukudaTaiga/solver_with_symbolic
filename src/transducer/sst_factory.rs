use super::sst::Sst;
use super::term::{FunctionTerm, FunctionTermImpl, Lambda, OutputComp, UpdateComp, VariableImpl};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::char_util::FromChar;
use crate::regular::{regex::Regex, symbolic_automata::Sfa};
use crate::smt2::{ReplaceTarget, StraightLineConstraint, Transduction, TransductionOp};
use crate::state::{StateImpl, StateMachine};
use std::{
  collections::{HashMap, HashSet},
  rc::Rc,
};

pub struct SstBuilder<T: FromChar, S: StateImpl, V: VariableImpl> {
  ssts: Vec<Sst<T, S, V>>,
  var_num: usize,
}
impl<T: FromChar, S: StateImpl, V: VariableImpl> SstBuilder<T, S, V> {
  pub fn blank() -> Self {
    SstBuilder {
      ssts: vec![],
      var_num: 0,
    }
  }

  pub fn replace_all_reg(reg: Regex<T>, replace: Vec<OutputComp<T, V>>) -> Sst<T, S, V> {
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

  pub fn replace_reg(reg: Regex<T>, replace: Vec<OutputComp<T, V>>) -> Sst<T, S, V> {
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

  pub fn reverse() -> Sst<T, S, V> {
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

  pub fn identity() -> Sst<T, S, V> {
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

  pub fn constant(output: &str) -> Sst<T, S, V> {
    let initial_state = S::new();
    let mut states = HashSet::new();
    states.insert(S::clone(&initial_state));
    let variables = HashSet::new();
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

  pub fn init(var_num: usize) -> Self {
    let mut builder = SstBuilder {
      ssts: Vec::with_capacity(var_num),
      var_num,
    };

    for _ in 0..var_num {
      builder.ssts.push(SstBuilder::identity());
    }

    builder
  }

  pub fn generate(mut self, sl_cons: Vec<StraightLineConstraint<T, S>>) -> Vec<Sst<T, S, V>> {
    eprintln!("sl {:?}", sl_cons);
    for StraightLineConstraint(idx, transduction) in sl_cons {
      self.update(idx, transduction)
    }

    self.ssts
  }

  pub fn update(&mut self, idx: usize, transduction: Transduction<T, S>) {
    let mut vars = Vec::with_capacity(idx);
    let mut ssts = Vec::with_capacity(idx);
    for _ in 0..idx {
      ssts.push(self.empty(&mut vars).merge(Self::identity()));
    }
    let mut idx_sst = Sst::empty();

    for transduction_op in transduction.0 {
      match transduction_op {
        TransductionOp::Var(id) => {
          for (_, output) in idx_sst.final_set_mut() {
            if let Some(var) = vars.get(id) {
              output.push(OutputComp::X(V::clone(var)));
            } else {
              unreachable!();
            }
          }
        }
        TransductionOp::Str(s) => {
          for (_, output) in idx_sst.final_set_mut() {
            for c in s.chars() {
              output.push(OutputComp::A(T::from_char(c)));
            }
          }
        }
        TransductionOp::Replace(id, reg, target) => {
          let replace = match target {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(T::from_char(c))).collect(),
            ReplaceTarget::Var(id) => vec![OutputComp::X(V::clone(vars.get(id).unwrap()))],
          };
          let result_var = V::new();
          *ssts.get_mut(id).unwrap() = Self::merge(
            ssts.get(id).unwrap().clone(),
            SstBuilder::replace_reg(reg, replace),
            &result_var,
          );
          for (_, output) in idx_sst.final_set_mut() {
            output.push(OutputComp::X(V::clone(&result_var)));
          }
        }
        TransductionOp::ReplaceAll(id, reg, target) => {
          let replace = match target {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(T::from_char(c))).collect(),
            ReplaceTarget::Var(id) => vec![OutputComp::X(V::clone(vars.get(id).unwrap()))],
          };
          let result_var = V::new();
          *ssts.get_mut(id).unwrap() = Self::merge(
            ssts.get(id).unwrap().clone(),
            SstBuilder::replace_all_reg(reg, replace),
            &result_var,
          );
          for (_, output) in idx_sst.final_set_mut() {
            output.push(OutputComp::X(V::clone(&result_var)));
          }
        }
        TransductionOp::Reverse(id) => {
          let result_var = V::new();
          *ssts.get_mut(id).unwrap() = Self::merge(
            ssts.get(id).unwrap().clone(),
            SstBuilder::reverse(),
            &result_var,
          );
          for (_, output) in idx_sst.final_set_mut() {
            output.push(OutputComp::X(V::clone(&result_var)));
          }
        }
        TransductionOp::UserDef(_) => unimplemented!(),
      }
    }

    *self.ssts.get_mut(idx).unwrap() =
      if let Some(sst) = ssts.into_iter().reduce(|result, sst| result.chain(sst)) {
        /*
         * TODO -- consider how to pre-imaging automata and what is the form of input
         * currently, both the given transduction form and returned sst's output form are awesome
         */
        for (_, output) in idx_sst.final_set_mut() {
          if output.len() != 0 {
            output.push(OutputComp::A(T::separator()));
          }
        }

        sst
      } else {
        Self::identity()
      }
      .chain(idx_sst)
  }

  /**
   * merging two sst.
   * output function is first one's,
   * and second one's is into the given result variable.
   * to say short, create a new sst that is based on first sst,
   * but have second one's info like transition, variables, output.
   * the sst will refuse a input if either one sst refuse it.
   */
  pub fn merge(sst1: Sst<T, S, V>, sst2: Sst<T, S, V>, result: &V) -> Sst<T, S, V> {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let Sst {
      states: s1,
      variables: v1,
      initial_state: i1,
      output_function: o1,
      transition: t1,
    } = sst1;

    let Sst {
      states: s2,
      variables: v2,
      initial_state: i2,
      output_function: o2,
      transition: t2,
    } = sst2;

    let cartesian = s1
      .iter()
      .flat_map(|p| {
        s2.iter()
          .map(move |q| ((S::clone(p), S::clone(q)), S::new()))
      })
      .collect::<HashMap<_, _>>();

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let mut variables = v1.into_iter().chain(v2.into_iter()).collect::<HashSet<_>>();
    variables.insert(V::clone(result));

    let mut output_function = HashMap::new();
    let mut transition = t1
      .iter()
      .flat_map(|((p1, phi1), (q1, u1))| {
        t2.iter()
          .map(|((p2, phi2), (q2, u2))| {
            let p = S::clone(
              cartesian
                .get(&(S::clone(p1), S::clone(p2)))
                .expect(error_msg),
            );
            let q = S::clone(
              cartesian
                .get(&(S::clone(q1), S::clone(q2)))
                .expect(error_msg),
            );

            (
              (p, phi1.and(phi2)),
              (
                q,
                u1.iter()
                  .chain(u2.into_iter())
                  .map(|(v, uc)| (V::clone(&v), uc.clone()))
                  .collect(),
              ),
            )
          })
          .collect::<Vec<_>>()
      })
      .collect::<HashMap<_, (S, HashMap<V, Vec<UpdateComp<FunctionTermImpl<T>, V>>>)>>();

    for (fs1, o1) in o1.iter() {
      for (fs2, o2) in o2.iter() {
        let fs = cartesian
          .get(&(S::clone(fs1), S::clone(fs2)))
          .expect(error_msg);

        output_function.insert(S::clone(fs), o1.clone());

        if let Some((_, update)) =
          transition.get_mut(&(S::clone(fs), Predicate::eq(T::separator())))
        {
          update.insert(
            V::clone(result),
            o2.into_iter()
              .map(|out| match out {
                OutputComp::A(a) => UpdateComp::F(Lambda::constant(T::clone(a))),
                OutputComp::X(var) => UpdateComp::X(V::clone(var)),
              })
              .collect(),
          );
        } else {
          transition.insert(
            (S::clone(fs), Predicate::eq(T::separator())),
            (
              S::clone(fs),
              HashMap::from([(
                V::clone(result),
                o2.into_iter()
                  .map(|out| match out {
                    OutputComp::A(a) => UpdateComp::F(Lambda::constant(T::clone(a))),
                    OutputComp::X(var) => UpdateComp::X(V::clone(var)),
                  })
                  .collect(),
              )]),
            ),
          );
        }
      }
    }

    let states = cartesian.into_values().collect();

    Sst::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  fn empty(&mut self, vars: &mut Vec<V>) -> Sst<T, S, V> {
    let initial_state = S::new();
    let var = V::new();

    let mut states = HashSet::new();
    states.insert(S::clone(&initial_state));
    let mut variables = HashSet::new();
    variables.insert(V::clone(&var));
    let mut output_function = HashMap::new();
    output_function.insert(S::clone(&initial_state), vec![]);
    let mut transition = HashMap::new();
    let mut map = HashMap::new();
    map.insert(
      V::clone(&var),
      vec![
        UpdateComp::X(V::clone(&var)),
        UpdateComp::F(Lambda::identity()),
      ],
    );
    transition.insert(
      (S::clone(&initial_state), Predicate::top()),
      (S::clone(&initial_state), map),
    );

    vars.push(var);

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
    let id = TestBuilder::identity();

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
    let cnst = "this is a constant".to_string();
    let id = TestBuilder::constant(&cnst);

    assert_eq!(String::from_iter(&id.run(&chars("")[..])[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("xyx")[..])[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("abcdefg")[..])[0]), cnst);
  }

  #[test]
  fn reverse() {
    let rev = TestBuilder::reverse();

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
    let _rep = TestBuilder::replace_all_reg(Regex::Empty, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_all_reg() {
    let _rep = TestBuilder::replace_all_reg(Regex::Epsilon, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_all_reg() {
    let rep = TestBuilder::replace_all_reg(
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
    let rep = TestBuilder::replace_all_reg(
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
    let rep = TestBuilder::replace_all_reg(
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
    let _rep = TestBuilder::replace_reg(Regex::Empty, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_reg() {
    let _rep = TestBuilder::replace_reg(Regex::Epsilon, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_reg() {
    let rep = TestBuilder::replace_reg(
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
    let rep = TestBuilder::replace_reg(
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
    let rep = TestBuilder::replace_reg(
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
