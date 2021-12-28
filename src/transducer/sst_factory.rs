use super::sst::Sst;
use super::term::{FunctionTerm, Lambda, OutputComp, UpdateComp, Variable};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::char_util::FromChar;
use crate::regular::{regex::Regex, symbolic_automata::Sfa};
use crate::smt2::{ReplaceTarget, StraightLineConstraint, Transduction, TransductionOp};
use crate::state::{State, StateMachine};
use std::collections::{HashMap, HashSet};

pub struct SstBuilder<T: FromChar, S: State, V: Variable> {
  ssts: Vec<Sst<T, S, V>>,
}
impl<T: FromChar, S: State, V: Variable> SstBuilder<T, S, V> {
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
      transition: transition_,
      initial_state,
      final_states,
    } = sfa;

    /* whole result variable */
    let res = V::new();
    /* accumulator variable of current matches */
    let acc = V::new();
    let variables = HashSet::from([V::clone(&res), V::clone(&acc)]);

    let initial_maps = transition_
      .iter()
      .filter(|((p, _), _)| *p == initial_state)
      .collect::<Vec<_>>();

    let mut transition = HashMap::new();

    let suc_next = {
      let mut v = vec![UpdateComp::X(V::clone(&res))];
      v.extend(replace_update.iter().cloned());
      v
    };
    let suc_reset = {
      let mut v = vec![UpdateComp::X(V::clone(&res))];
      v.extend(replace_update.iter().cloned());
      v.push(UpdateComp::F(Lambda::identity()));
      v
    };
    for p in &final_states {
      /*
       * succeed to match and try to next match
       * variable maps
       */
      let start = HashMap::from([
        (V::clone(&res), suc_next.clone()),
        (V::clone(&acc), vec![UpdateComp::F(Lambda::identity())]),
      ]);
      let reset = HashMap::from([
        (V::clone(&res), suc_reset.clone()),
        (V::clone(&acc), vec![]),
      ]);

      for ((_, phi), target) in &initial_maps {
        transition.insert(
          (S::clone(p), phi.clone()),
          target
            .into_iter()
            .map(|q| (S::clone(q), start.clone()))
            .collect(),
        );
      }

      transition.insert(
        (
          S::clone(p),
          not_predicates.get(&initial_state).unwrap().clone(),
        ),
        vec![(S::clone(&initial_state), reset)],
      );
    }

    for ((p, phi), target) in &transition_ {
      if !final_states.contains(p) {
        /* variable maps */
        let step = HashMap::from([
          (V::clone(&res), vec![UpdateComp::X(V::clone(&res))]),
          (
            V::clone(&acc),
            vec![
              UpdateComp::X(V::clone(&acc)),
              UpdateComp::F(Lambda::identity()),
            ],
          ),
        ]);
        let start = HashMap::from([
          (
            V::clone(&res),
            vec![UpdateComp::X(V::clone(&res)), UpdateComp::X(V::clone(&acc))],
          ),
          (V::clone(&acc), vec![UpdateComp::F(Lambda::identity())]),
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

        /* matches current target char and go to next state. */
        transition.insert(
          (S::clone(p), phi.clone()),
          target
            .into_iter()
            .map(|q| (S::clone(q), step.clone()))
            .collect(),
        );

        let not_pred_p = not_predicates.get(p).unwrap();
        for ((_, phi), target) in &initial_maps {
          /* first char of a given regex */
          transition.insert(
            (S::clone(p), not_pred_p.and(phi)),
            target
              .into_iter()
              .map(|q| (S::clone(q), start.clone()))
              .collect(),
          );
        }

        let not_pred_init = not_predicates.get(&initial_state).unwrap();
        /* failed to match next and any first char of the regex */
        transition.insert(
          (S::clone(p), not_pred_p.and(not_pred_init)),
          vec![(S::clone(&initial_state), reset)],
        );
      }
    }

    let match_out = {
      let mut v = vec![OutputComp::X(V::clone(&res))];
      v.extend(replace.into_iter());
      v
    };

    let unmatch_out = vec![OutputComp::X(V::clone(&res)), OutputComp::X(V::clone(&acc))];

    let output_function = states
      .iter()
      .map(|state| {
        if final_states.contains(state) {
          /* if ending at the final state of given regex, replace it with output and dump acc */
          (S::clone(state), match_out.clone())
        } else {
          (S::clone(state), unmatch_out.clone())
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
      transition: transition_,
      initial_state,
      final_states,
    } = sfa;

    /* whole result variable */
    let res = V::new();
    /* accumulator variable of current matches */
    let acc = V::new();
    let variables = HashSet::from([V::clone(&res), V::clone(&acc)]);

    let initial_maps = transition_
      .iter()
      .filter(|((p, _), _)| *p == initial_state)
      .collect::<Vec<_>>();

    /* once matches given regex, cycle and stack the rest of input on result */
    let cycle_state = S::new();
    let top = Predicate::all_char();

    let mut transition = HashMap::new();

    for p in &final_states {
      /* succeed to match and go to cycle state */
      let to_cycle = HashMap::from([(V::clone(&res), {
        let mut v = vec![UpdateComp::X(V::clone(&res))];
        v.extend(replace_update.iter().map(|up| up.clone()));
        v.push(UpdateComp::F(Lambda::identity()));
        v
      })]);
      transition.insert(
        (S::clone(p), top.clone()),
        vec![(S::clone(&cycle_state), to_cycle)],
      );
    }

    for ((p, phi), target) in &transition_ {
      if !final_states.contains(p) {
        /* variable maps */
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

        for ((_, phi), target) in &initial_maps {
          /* they're first char of a given regex */
          for q in *target {
            transition.insert(
              (
                S::clone(p),
                not_predicates.get(p).unwrap_or(&Predicate::bot()).and(phi),
              ),
              vec![(S::clone(q), start.clone())],
            );
          }
        }

        /* failed to match next and any first char of the regex */
        transition.insert(
          (
            S::clone(p),
            not_predicates.get(p).unwrap_or(&Predicate::bot()).and(
              not_predicates
                .get(&initial_state)
                .unwrap_or(&Predicate::bot()),
            ),
          ),
          vec![(S::clone(&initial_state), reset)],
        );
        /* matches current target char and go to next state. */
        transition.insert(
          (S::clone(p), phi.clone()),
          target
            .into_iter()
            .map(|q| (S::clone(q), update.clone()))
            .collect(),
        );
      }
    }

    transition.insert(
      (S::clone(&cycle_state), top.clone()),
      vec![(
        S::clone(&cycle_state),
        HashMap::from([(
          V::clone(&res),
          vec![
            UpdateComp::X(V::clone(&res)),
            UpdateComp::F(Lambda::identity()),
          ],
        )]),
      )],
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
    let states = HashSet::from([S::clone(&initial_state)]);
    let variables = HashSet::from([V::clone(&res)]);
    let output_function = HashMap::from([(
      S::clone(&initial_state),
      vec![OutputComp::X(V::clone(&res))],
    )]);
    let map = HashMap::from([(
      V::clone(&res),
      vec![UpdateComp::F(Lambda::identity()), UpdateComp::X(res)],
    )]);
    let transition = HashMap::from([(
      (S::clone(&initial_state), Predicate::all_char()),
      vec![(S::clone(&initial_state), map)],
    )]);

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

    let states = HashSet::from([S::clone(&initial_state)]);
    let variables = HashSet::from([V::clone(&res)]);
    let output_function = HashMap::from([(
      S::clone(&initial_state),
      vec![OutputComp::X(V::clone(&res))],
    )]);
    let map = HashMap::from([(
      V::clone(&res),
      vec![UpdateComp::X(res), UpdateComp::F(Lambda::identity())],
    )]);
    let transition = HashMap::from([(
      (S::clone(&initial_state), Predicate::all_char()),
      vec![(S::clone(&initial_state), map)],
    )]);

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
    let states = HashSet::from([S::clone(&initial_state)]);
    let variables = HashSet::new();
    let output_function = HashMap::from([(
      S::clone(&initial_state),
      output
        .chars()
        .map(|c| OutputComp::A(T::from_char(c)))
        .collect(),
    )]);
    let transition = HashMap::from([(
      (S::clone(&initial_state), Predicate::all_char()),
      vec![(S::clone(&initial_state), HashMap::new())],
    )]);

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
      ssts.push(Self::register(&mut vars));
    }
    let mut idx_sst = Sst::empty();

    if transduction.0.len() == 0 {
      idx_sst = Self::identity();
    } else {
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
            *ssts.get_mut(id).unwrap() = ssts
              .get(id)
              .unwrap()
              .clone()
              .merge(SstBuilder::replace_reg(reg, replace), &result_var);
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
            *ssts.get_mut(id).unwrap() = ssts
              .get(id)
              .unwrap()
              .clone()
              .merge(SstBuilder::replace_all_reg(reg, replace), &result_var);
            for (_, output) in idx_sst.final_set_mut() {
              output.push(OutputComp::X(V::clone(&result_var)));
            }
          }
          TransductionOp::Reverse(id) => {
            let result_var = V::new();
            *ssts.get_mut(id).unwrap() = ssts
              .get(id)
              .unwrap()
              .clone()
              .merge(SstBuilder::reverse(), &result_var);
            for (_, output) in idx_sst.final_set_mut() {
              output.push(OutputComp::X(V::clone(&result_var)));
            }
          }
          TransductionOp::UserDef(_) => unimplemented!(),
        }
      }

      for (_, output) in idx_sst.final_set_mut() {
        output.push(OutputComp::A(T::separator()));
      }
    }

    *self.ssts.get_mut(idx).unwrap() =
      if let Some(sst) = ssts.into_iter().reduce(|result, sst| result.chain(sst)) {
        sst.chain(idx_sst)
      } else {
        idx_sst
      }
  }

  fn register(vars: &mut Vec<V>) -> Sst<T, S, V> {
    let initial_state = S::new();
    let var = V::new();

    let states = HashSet::from([S::clone(&initial_state)]);
    let variables = HashSet::from([V::clone(&var)]);
    let output_function = HashMap::from([(
      S::clone(&initial_state),
      vec![OutputComp::X(V::clone(&var))],
    )]);
    let map = HashMap::from([(
      V::clone(&var),
      vec![
        UpdateComp::X(V::clone(&var)),
        UpdateComp::F(Lambda::identity()),
      ],
    )]);
    let transition = HashMap::from([(
      (S::clone(&initial_state), Predicate::all_char()),
      vec![(S::clone(&initial_state), map)],
    )]);

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
pub mod tests {
  use super::*;
  use crate::tests::helper::*;
  use std::iter::FromIterator;

  type Builder = SstBuilder<char, StateImpl, VariableImpl>;

  #[test]
  fn identity() {
    let id = Builder::identity();

    assert_eq!(String::from_iter(&id.run(&chars(""))[0]), "".to_string());
    assert_eq!(
      String::from_iter(&id.run(&chars("xyx"))[0]),
      "xyx".to_string()
    );
    assert_eq!(
      String::from_iter(&id.run(&chars("abcdefg"))[0]),
      "abcdefg".to_string()
    );
  }

  #[test]
  fn constant() {
    let cnst = "this is a constant".to_string();
    let id = Builder::constant(&cnst);

    assert_eq!(String::from_iter(&id.run(&chars(""))[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("xyx"))[0]), cnst);
    assert_eq!(String::from_iter(&id.run(&chars("abcdefg"))[0]), cnst);
  }

  #[test]
  fn reverse() {
    let rev = Builder::reverse();

    assert_eq!(String::from_iter(&rev.run(&chars(""))[0]), "".to_string());
    assert_eq!(
      String::from_iter(&rev.run(&chars("xyx"))[0]),
      "xyx".to_string()
    );
    assert_eq!(
      String::from_iter(&rev.run(&chars("abcdefg"))[0]),
      "gfedcba".to_string()
    );
  }

  #[test]
  #[should_panic]
  fn reject_empty_substr_all_reg() {
    let _rep = Builder::replace_all_reg(Regex::Empty, vec![]);
    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_all_reg() {
    let _rep = Builder::replace_all_reg(Regex::Epsilon, vec![]);
    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_all_reg() {
    let rep = Builder::replace_all_reg(Regex::seq("abc"), to_replacer("xyz"));

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc"))[0]),
      "xyz".to_string()
    );
    assert_eq!(String::from_iter(&rep.run(&chars("a"))[0]), "a".to_string());
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc"))[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcababc"))[0]),
      "xyzabxyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg"))[0]),
      "xyzxyzxyzaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn a_to_many_all_reg() {
    let rep = Builder::replace_all_reg(
      Regex::element('a'),
      to_replacer("qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\"),
    );

    eprintln!("{:#?}", rep);

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc"))[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a"))[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc"))[0]),
      "bc".to_string()
    );
    assert_eq!(
            String::from_iter(
                &rep.run(&chars("abcabcabcaaabbaccbackljhg"))[0]
            ),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ccbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ckljhg".to_string()
        );
  }

  #[test]
  fn abcxyz_to_1_all_reg() {
    let rep = Builder::replace_all_reg(Regex::seq("abcxyz"), to_replacer("1"));

    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxyz"))[0]),
      "1".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxy"))[0]),
      "abcxy".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcyz"))[0]),
      "abcyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("aaaabcxyzabcxyabcxyzzzabcxyz"))[0]),
      "aaa1abcxy1zz1".to_string()
    );
  }

  #[test]
  #[should_panic]
  fn reject_empty_substr_reg() {
    let _rep = Builder::replace_reg(Regex::Empty, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  #[should_panic]
  fn reject_epsilon_substr_reg() {
    let _rep = Builder::replace_reg(Regex::Epsilon, vec![]);

    eprintln!("unreachable");
  }

  #[test]
  fn abc_to_xyz_reg() {
    let rep = Builder::replace_reg(Regex::seq("abc"), to_replacer("xyz"));

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc"))[0]),
      "xyz".to_string()
    );
    assert_eq!(String::from_iter(&rep.run(&chars("a"))[0]), "a".to_string());
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc"))[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcababc"))[0]),
      "xyzababc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg"))[0]),
      "xyzabcabcaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn a_to_many_reg() {
    let rep = Builder::replace_reg(
      Regex::element('a'),
      to_replacer("qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\"),
    );

    assert_eq!(
      String::from_iter(&rep.run(&chars("abc"))[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("a"))[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("bc"))[0]),
      "bc".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcabcabcaaabbaccbackljhg"))[0]),
      "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcabcabcaaabbaccbackljhg".to_string()
    );
  }

  #[test]
  fn abcxyz_to_1_reg() {
    let rep = Builder::replace_reg(Regex::seq("abcxyz"), to_replacer("1"));

    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxyz"))[0]),
      "1".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcxy"))[0]),
      "abcxy".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("abcyz"))[0]),
      "abcyz".to_string()
    );
    assert_eq!(
      String::from_iter(&rep.run(&chars("aaaabcxyzabcxyabcxyzzzabcxyz"))[0]),
      "aaa1abcxyabcxyzzzabcxyz".to_string()
    );
  }
}
