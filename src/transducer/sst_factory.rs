use super::{
  sst::Sst,
  term::{FunctionTerm, Lambda, OutputComp, UpdateComp, Variable},
};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::regular::regex::Regex;
use crate::smt2::{ReplaceTarget, Transduction, TransductionOp};
use crate::state::{State, StateMachine};
use crate::util::{
  extention::{ImmutableValueMap, MultiMap},
  Domain,
};
use std::{
  collections::{HashMap, HashSet},
  marker::PhantomData,
};

pub struct SstBuilder<D: Domain, S: State, V: Variable> {
  _domain: PhantomData<D>,
  _state: PhantomData<S>,
  _variable: PhantomData<V>,
}
impl<D: Domain, S: State, V: Variable> SstBuilder<D, S, V> {
  pub fn init() -> Self {
    SstBuilder {
      _domain: PhantomData,
      _state: PhantomData,
      _variable: PhantomData,
    }
  }

  pub fn generate(&self, idx: usize, transduction: Transduction<D, S>) -> Sst<D, S, V> {
    let mut ssts = Vec::with_capacity(idx - 1);
    let mut identities = HashMap::new();
    let mut reverses = HashMap::new();
    let prefix = V::new();
    for _ in 0..idx {
      ssts.push(Self::register(&prefix));
    }
    let mut pre_id = 0;
    let result = V::new();

    assert!(transduction.0.len() != 0 && idx != 0);

    for transduction_op in transduction.0 {
      match transduction_op {
        TransductionOp::Var(id) => {
          identities.entry(id).or_insert({
            let var = V::new();
            *ssts.get_mut(id).unwrap() = ssts
              .get(id)
              .unwrap()
              .clone()
              .merge(SstBuilder::identity(&var), &result);
            var
          });
          pre_id = id;
        }
        TransductionOp::Str(s) => {
          *ssts.get_mut(pre_id).unwrap() = ssts
            .get(pre_id)
            .unwrap()
            .clone()
            .merge(SstBuilder::constant(&s), &result);
        }
        TransductionOp::Replace(id, reg, target) => {
          let replace = match target {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(D::from(c))).collect(),
            ReplaceTarget::Var(id) => {
              let id_var = identities.entry(id).or_insert({
                let var = V::new();
                *ssts.get_mut(id).unwrap() = ssts
                  .get(id)
                  .unwrap()
                  .clone()
                  .merge(SstBuilder::identity(&var), &result);
                var
              });
              vec![OutputComp::X(V::clone(id_var))]
            }
          };
          *ssts.get_mut(id).unwrap() = ssts
            .get(id)
            .unwrap()
            .clone()
            .merge(SstBuilder::replace_reg(reg, replace), &result);
          pre_id = id;
        }
        TransductionOp::ReplaceAll(id, reg, target) => {
          let replace = match target {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(D::from(c))).collect(),
            ReplaceTarget::Var(id) => {
              let id_var = identities.entry(id).or_insert({
                let var = V::new();
                *ssts.get_mut(id).unwrap() = ssts
                  .get(id)
                  .unwrap()
                  .clone()
                  .merge(SstBuilder::identity(&var), &var);
                var
              });
              vec![OutputComp::X(V::clone(id_var))]
            }
          };
          *ssts.get_mut(id).unwrap() = ssts
            .get(id)
            .unwrap()
            .clone()
            .merge(SstBuilder::replace_all_reg(reg, replace), &result);
          pre_id = id;
        }
        TransductionOp::Reverse(id) => {
          reverses.entry(id).or_insert({
            let reverse = V::new();
            *ssts.get_mut(id).unwrap() = ssts
              .get(id)
              .unwrap()
              .clone()
              .merge(SstBuilder::reverse(&reverse), &result);
            reverse
          });
          pre_id = id;
        }
        TransductionOp::UserDef(_) => unimplemented!(),
      }
    }

    ssts
      .into_iter()
      .reduce(|result, sst| result.chain(sst))
      .unwrap()
      .chain_output(
        vec![
          OutputComp::X(V::clone(&prefix)),
          OutputComp::A(D::separator()),
          OutputComp::X(V::clone(&result)),
          OutputComp::A(D::separator()),
        ],
        HashSet::from([prefix, result]),
      )
  }

  pub fn replace_all_reg(reg: Regex<D>, replace: Vec<OutputComp<D, V>>) -> Sst<D, S, V> {
    assert_ne!(reg, Regex::Empty);
    assert_ne!(reg, Regex::Epsilon);

    let replace_update = super::to_update(&replace);

    let sfa = reg.to_sfa();
    /*
     * used for back to initial state when failing to match.
     * calculate all predicate which is not of all transition from given state
     */
    let not_predicates: HashMap<_, _> = sfa
      .states()
      .into_iter()
      .map(|state| (state, sfa.state_predicate(state).not()))
      .collect();

    /* matches */
    let rep = V::new();
    /* not matches */
    let not_rep = V::new();
    let variables = HashSet::from([V::clone(&rep), V::clone(&not_rep)]);

    let initial_maps: Vec<_> = sfa
      .transition()
      .into_iter()
      .filter(|((p, _), _)| *p == *sfa.initial_state())
      .collect();
    let mut transition = HashMap::new();

    let start = super::macros::make_update! {
      rep -> {
        let mut v = Vec::with_capacity(1 + replace_update.len());
        v.push(UpdateComp::X(V::clone(&rep)));
        v.extend(replace_update.iter().cloned());
        v
      },
      not_rep -> {
        let mut v = Vec::with_capacity(2 + replace_update.len());
        v.push(UpdateComp::X(V::clone(&rep)));
        v.extend(replace_update.iter().cloned());
        v.push(UpdateComp::F(Lambda::identity()));
        v
      }
    };
    let reset = super::macros::make_update! {
      rep -> {
        let mut v = Vec::with_capacity(2 + replace_update.len());
        v.push(UpdateComp::X(V::clone(&rep)));
        v.extend(replace_update.iter().cloned());
        v.push(UpdateComp::F(Lambda::identity()));
        v
      },
      not_rep -> {
        let mut v = Vec::with_capacity(2 + replace_update.len());
        v.push(UpdateComp::X(V::clone(&rep)));
        v.extend(replace_update.iter().cloned());
        v.push(UpdateComp::F(Lambda::identity()));
        v
      }
    };
    sfa.final_set().into_iter().for_each(|p| {
      /*
       * succeed to match and try to next match
       * variable maps
       */
      initial_maps.iter().for_each(|((_, phi), target)| {
        transition.safe_insert(
          (S::clone(p), phi.clone()),
          target
            .into_iter()
            .map(|q| (S::clone(q), start.clone()))
            .collect(),
        );
      });

      let not_pred_init = not_predicates.get(sfa.initial_state()).unwrap();
      if not_pred_init.satisfiable() {
        transition.safe_insert(
          (S::clone(p), not_pred_init.clone()),
          vec![(S::clone(sfa.initial_state()), reset.clone())],
        );
      }
    });

    /* variable maps */
    let step = super::macros::make_update! {
      not_rep -> vec![
        UpdateComp::X(V::clone(&not_rep)),
        UpdateComp::F(Lambda::identity()),
      ]
    };
    let start = super::macros::make_update! {
      rep -> vec![UpdateComp::X(V::clone(&not_rep))],
      not_rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())]
    };
    let reset = super::macros::make_update! {
      rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())],
      not_rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())]
    };
    sfa.transition().into_iter().for_each(|((p, phi), target)| {
      if !sfa.final_set().contains(p) {
        /* matches current target char and go to next state. */
        transition.insert_with_check(
          (S::clone(p), phi.clone()),
          target.into_iter().map(|q| (S::clone(q), step.clone())),
        );

        let not_pred_p = not_predicates.get(p).unwrap();

        initial_maps.iter().for_each(|((_, phi), target)| {
          let phi = not_pred_p.and(phi);
          if phi.satisfiable() {
            /* first char of a given regex */
            transition.insert_with_check(
              (S::clone(p), phi),
              target.into_iter().map(|q| (S::clone(q), start.clone())),
            );
          }
        });

        let not_pred_init = not_predicates.get(sfa.initial_state()).unwrap();
        let phi = not_pred_p.and(not_pred_init);
        if phi.satisfiable() {
          /* failed to match next and any first char of the regex */
          transition.insert_with_check(
            (S::clone(p), phi),
            [(S::clone(sfa.initial_state()), reset.clone())],
          );
        }
      }
    });

    let match_out = {
      let mut v = vec![OutputComp::X(rep)];
      v.extend(replace);
      v
    };

    let unmatch_out = vec![OutputComp::X(not_rep)];

    let output_function = sfa
      .states()
      .into_iter()
      .map(|state| {
        if sfa.final_set().contains(state) {
          /* if ending at the final state of given regex, replace it with output and dump acc */
          (S::clone(state), match_out.clone())
        } else {
          (S::clone(state), unmatch_out.clone())
        }
      })
      .collect();

    Sst::new(
      sfa.states,
      variables,
      sfa.initial_state,
      output_function,
      transition,
    )
  }

  pub fn replace_reg(reg: Regex<D>, replace: Vec<OutputComp<D, V>>) -> Sst<D, S, V> {
    assert_ne!(reg, Regex::Empty);
    assert_ne!(reg, Regex::Epsilon);

    let replace_update = super::to_update(&replace);

    let sfa = reg.to_sfa();
    /*
     * used for back to initial state when failing to match.
     * calculate all predicate which is not used for any transition from given state
     */
    let not_predicates: HashMap<_, _> = sfa
      .states()
      .iter()
      .map(|state| (state, sfa.state_predicate(state).not()))
      .collect();

    /* matches */
    let rep = V::new();
    /* not matches */
    let not_rep = V::new();
    let variables = HashSet::from([V::clone(&rep), V::clone(&not_rep)]);

    let initial_maps: Vec<_> = sfa
      .transition()
      .into_iter()
      .filter(|((p, _), _)| *p == *sfa.initial_state())
      .collect();

    /* once matches given regex, cycle and stack the rest of input on result */
    let cycle_state = S::new();

    let mut transition = HashMap::new();

    let to_cycle = super::macros::make_update! {
      rep -> {
        let mut v = Vec::with_capacity(1 + replace_update.len());
        v.push(UpdateComp::X(V::clone(&rep)));
        v.extend(replace_update.iter().cloned());
        v.push(UpdateComp::F(Lambda::identity()));
        v
      }
    };
    sfa.final_set().into_iter().for_each(|p| {
      /* succeed to match and go to cycle state */
      transition.safe_insert(
        (S::clone(p), Predicate::top()),
        vec![(S::clone(&cycle_state), to_cycle.clone())],
      );
    });

    transition.safe_insert(
      (S::clone(&cycle_state), Predicate::top()),
      vec![(
        S::clone(&cycle_state),
        super::macros::make_update! {
          rep -> vec![UpdateComp::X(V::clone(&rep)), UpdateComp::F(Lambda::identity())]
        },
      )],
    );

    /* variable maps */
    let update = super::macros::make_update! {
      not_rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())]
    };
    let reset = super::macros::make_update! {
      rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())],
      not_rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())]
    };
    let start = super::macros::make_update! {
      rep -> vec![UpdateComp::X(V::clone(&not_rep))],
      not_rep -> vec![UpdateComp::X(V::clone(&not_rep)), UpdateComp::F(Lambda::identity())]
    };
    sfa.transition().into_iter().for_each(|((p, phi), target)| {
      if !sfa.final_set().contains(p) {
        initial_maps.iter().for_each(|((_, phi), target)| {
          let phi = not_predicates.get(p).unwrap_or(&Predicate::bot()).and(phi);
          if phi.satisfiable() {
            /* they're first char of a given regex */
            transition.insert_with_check(
              (S::clone(p), phi.clone()),
              target.into_iter().map(|q| (S::clone(q), start.clone())),
            );
          }
        });

        let return_init_pred = not_predicates.get(p).unwrap_or(&Predicate::bot()).and(
          not_predicates
            .get(sfa.initial_state())
            .unwrap_or(&Predicate::bot()),
        );
        /* failed to match next and any first char of the regex */
        if return_init_pred.satisfiable() {
          transition.insert_with_check(
            (S::clone(p), return_init_pred),
            [(S::clone(sfa.initial_state()), reset.clone())],
          );
        }
        /* matches current target char and go to next state. */
        transition.insert_with_check(
          (S::clone(p), phi.clone()),
          target.into_iter().map(|q| (S::clone(q), update.clone())),
        );
      }
    });

    let mut output_function: HashMap<_, _> = sfa
      .states()
      .into_iter()
      .map(|state| {
        if sfa.final_set().contains(state) {
          (S::clone(state), {
            let mut v = Vec::with_capacity(1 + replace.len());
            v.push(OutputComp::X(V::clone(&rep)));
            v.extend(replace.iter().cloned());
            v
          })
        } else {
          (S::clone(state), vec![OutputComp::X(V::clone(&not_rep))])
        }
      })
      .collect();

    /* states is used in above iteration, so update it at this line */
    let mut states = sfa.states;
    states.insert(S::clone(&cycle_state));

    output_function.safe_insert(cycle_state, vec![OutputComp::X(rep)]);

    Sst::new(
      states,
      variables,
      sfa.initial_state,
      output_function,
      transition,
    )
  }

  pub fn identity(var: &V) -> Sst<D, S, V> {
    super::macros::sst! {
      { initial },
      HashSet::from([V::clone(var)]),
      {
        -> initial,
        (initial, Predicate::top()) -> [(
          initial,
          super::macros::make_update! {
            var -> vec![UpdateComp::X(V::clone(&var)), UpdateComp::F(Lambda::identity())]
          }
        )]
      },
      { initial -> vec![OutputComp::X(V::clone(&var))] }
    }
  }

  pub fn reverse(var: &V) -> Sst<D, S, V> {
    super::macros::sst! {
      { initial },
      HashSet::from([V::clone(var)]),
      {
        -> initial,
        (initial, Predicate::top()) -> [(
          initial,
          super::macros::make_update! {
            var -> vec![UpdateComp::F(Lambda::identity()), UpdateComp::X(V::clone(var))]
          }
        )]
      },
      { initial -> vec![OutputComp::X(V::clone(var))] }
    }
  }

  pub fn constant(output: &str) -> Sst<D, S, V> {
    super::macros::sst! {
      { initial },
      HashSet::new(),
      {
        -> initial,
        (initial, Predicate::top()) -> [(initial, super::macros::make_update! {})]
      },
      { initial -> output.chars().map(|c| OutputComp::A(D::from(c))).collect() }
    }
  }

  fn register(var: &V) -> Sst<D, S, V> {
    super::macros::sst! {
      { initial },
      HashSet::from([V::clone(var)]),
      {
        -> initial,
        (initial, Predicate::all_char()) -> [(
          initial,
          super::macros::make_update! {
            var -> vec![UpdateComp::X(V::clone(&var)), UpdateComp::F(Lambda::identity())]
          }
        )]
      },
      { initial -> vec![OutputComp::X(V::clone(&var))] }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tests::helper::*;

  type Builder = SstBuilder<char, StateImpl, VariableImpl>;

  macro_rules! basics {
    (
      names: [$id:ident, $cnst:ident, $rev:ident],
      constant: $constant:expr,
      cases: [$( $case:expr ),+]
    ) => {
      #[test]
      fn $id() {
          let sst = Builder::identity(&VariableImpl::new());
          $(
            assert!(sst.run(&chars($case)).contains(&chars($case)));
          )+
      }

      #[test]
      fn $cnst() {
          let sst = Builder::constant($constant);
          $(
            assert!(sst.run(&chars($case)).contains(&chars($constant)));
          )+
      }

      #[test]
      fn $rev() {
          let sst = Builder::reverse(&VariableImpl::new());
          $(
            assert!(
              sst.run(&chars($case)).contains(&$case.chars().rev().collect())
            );
          )+
      }
    };
  }

  /* ident concatenation is stil nightly https://doc.rust-lang.org/std/macro.concat_idents.html */
  macro_rules! replace_test {
    (
      names: [$name:ident, $name_all:ident],
      from: $from:expr,
      to: $to:expr,
      cases: [ $( $case:expr ),+ ]
    ) => {
      #[test]
      fn $name() {
        let replace = Builder::replace_reg(Regex::seq($from), to_replacer($to));
        eprintln!("{:?}", replace);
        $(
          let result = replace.run(&chars($case));
          eprintln!("result: {:?}", result);
          assert!(
            result.contains(&chars(&$case.replacen($from, $to, 1)))
          );
        )+
      }

      #[test]
      fn $name_all() {
        let replace_all = Builder::replace_all_reg(Regex::seq($from), to_replacer($to));
        eprintln!("{:?}", replace_all);
        $(
          let result = replace_all.run(&chars($case));
          eprintln!("result: {:?}", result);
          assert!(
            result.contains(&chars(&$case.replace($from, $to)))
          );
        )+
      }
    };
  }

  basics! {
    names: [identity, constant, reverse],
    constant: "this is a constant",
    cases: ["", "xyz", "abcdefg", "palindromemordnilap", "baaaaaaaaaaaaaaaa"]
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

  replace_test! {
    names: [abc_to_xyz, abc_to_xyz_all],
    from: "abc",
    to: "xyz",
    cases: ["abc", "bc", "abcababc", "abcabcabcaaabbaccbackljhg"]
  }

  replace_test! {
    names: [a_to_many, a_to_many_all],
    from: "a",
    to: "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\",
    cases: ["abc", "a", "bc", "abcabcabcaaabbaccbackljhg"]
  }

  replace_test! {
    names: [abcxyz_to_1, abcxyz_to_1_all],
    from: "abcxyz",
    to: "1",
    cases: ["abcxyz", "abcxy", "abcyz", "aaaabcxyzabcxyabcxyzzzabcxyz"]
  }

  replace_test! {
    names: [abcxyz_to_eps, abcxyz_to_eps_all],
    from: "abcxyz",
    to: "",
    cases: ["abcxyz", "abcxy", "abcyz", "aaaabcxyzabcxyabcxyzzzabcxyz"]
  }
}
