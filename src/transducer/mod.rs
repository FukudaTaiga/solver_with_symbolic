pub mod sst;
pub mod sst_factory;
pub mod term;
pub mod transducer;

pub(crate) fn to_update<
  D: crate::util::Domain,
  V: term::Variable,
  F: term::FunctionTerm<Domain = D>,
>(
  output: &Vec<term::OutputComp<D, V>>,
) -> Vec<term::UpdateComp<F, V>> {
  output.into_iter().map(|out| out.clone().into()).collect()
}

pub(crate) mod macros {
  macro_rules! make_update {
    ( $( $var:ident -> $seq:expr ),* ) => {
      HashMap::from([
        $( (V::clone(&$var), $seq) ),*
      ])
    };
  }

  /* for readability need import SymSst */
  macro_rules! sst {
    ( { $( $state:ident ),+ },
      $variables:expr,
      {
        -> $initial:ident
        $(, ($source:ident, $predicate:expr) -> [$( ( $target:ident, $update:expr ) )*] )*
      },
      { $( $fs:ident -> $output:expr ),* }
    ) => {{
      use crate::transducer::sst::SymSst;

      let mut states = HashSet::new();
      $( let $state = S::new(); states.insert(S::clone(&$state)); )+
      let transition = HashMap::from([
        $( ((S::clone(&$source), $predicate), vec![$( (S::clone(&$target), $update) ),*]) ),*
      ]);
      let output_function = HashMap::from([$( (S::clone(&$fs), $output) ),*]);
      SymSst::new(states, $variables, $initial, output_function, transition)
    }};
  }

  pub(crate) use make_update;
  pub(crate) use sst;
}

#[cfg(test)]
pub(crate) mod tests {
  use super::*;
  use crate::{
    regular::regex::Regex,
    smt2::{ReplaceTarget, Transduction, TransductionOp},
    state::StateMachine,
    tests::helper::*,
    util::{CharWrap, Domain},
  };
  use sst::Sst;
  use sst_factory::{self, SstBuilder};
  use std::collections::{HashMap, HashSet};
  use term::{FunctionTerm, OutputComp, UpdateComp};

  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;

  impl<T: Domain> Sst<T, StateImpl, VariableImpl> {
    fn run_with_var<'a>(
      &'a self,
      vars: &HashSet<VariableImpl>,
      input: impl IntoIterator<Item = &'a T>,
    ) -> Vec<(Vec<T>, HashMap<VariableImpl, Vec<T>>)> {
      let initial_map: HashMap<VariableImpl, Vec<T>> = self
        .variables
        .iter()
        .map(|var| (VariableImpl::clone(var), vec![]))
        .collect();

      self.generalized_run(
        input.into_iter(),
        vec![(self.initial_state.clone(), initial_map)],
        |(_, map), c, (q, alpha)| {
          let var_map = self
            .variables
            .iter()
            .map(|var| {
              (
                var.clone(),
                alpha
                  .get(var)
                  .unwrap_or(&vec![UpdateComp::X(var.clone())])
                  .into_iter()
                  .flat_map(|out| match out {
                    UpdateComp::F(f) => vec![f.apply(c).clone()],
                    UpdateComp::X(var) => map.get(var).unwrap_or(&vec![]).clone(),
                  })
                  .collect(),
              )
            })
            .collect();

          (q.clone(), var_map)
        },
        move |possibilities| {
          eprintln!("{:#?}", possibilities);
          let mut results = vec![];
          possibilities.into_iter().for_each(|(q, f)| {
            if let Some(output) = self.output_function.get(&q) {
              let result = (
                output
                  .into_iter()
                  .flat_map(|o| match o {
                    OutputComp::A(a) => vec![a.clone()],
                    OutputComp::X(x) => f.get(x).unwrap_or(&Vec::new()).clone(),
                  })
                  .collect::<Vec<_>>(),
                vars
                  .into_iter()
                  .map(move |var| (var.clone(), f[var].clone()))
                  .collect(),
              );

              if !results.contains(&result) {
                results.push(result);
              }
            }
          });
          results
        },
      )
    }
  }

  /* dropping last char of vars_expect is required because of to_charwrap() implementation */
  macro_rules! check_merge {
    (
      sst: $sst:expr,
      vars: $vars:expr,
      cases: [
        $( $input:expr => ($output:expr, { $( $var:ident -> $var_expected:expr ),* }) ),+
      ]
    ) => {
      $(
        let mut input = chars($input);
        input.push(Domain::separator());
        let results = $sst.run_with_var(&$vars, &input);
        let output = chars($output);
        let expected = (output, HashMap::from([
          $( ($var.clone(), chars($var_expected)) ),*
        ]));
        assert!({
          let result = results.contains(&expected);
          if !result {
            eprintln!("{:?}", $sst);
            eprintln!("expected{:?}", expected);
            eprintln!("results{:?}", results);
          }
          result
        });
      )+
    };
  }

  macro_rules! assertion {
    (
      $sst:expr,
      [$( $input:expr ),+],
      $var_len_expected:expr,
      $expected_output:expr
    ) => {{
      let run = run!($sst, [$( $input ),+], wrap);
      let var_len_is_expected = $sst.variables.len() == $var_len_expected;
      if !var_len_is_expected {
        eprintln!("{:#?}", $sst);
        eprintln!("var len\nexpected: {}, result: {}", $var_len_expected, $sst.variables.len());
      }
      assert!(var_len_is_expected);
      let result = run.len() == 1 && run[0] == $expected_output;
      if !result {
        eprintln!("{:#?}", $sst);
        eprintln!("output\nexpected: {:?}\nresult: {:?}", $expected_output, run);
      }
      assert!(result);
    }};
  }

  #[test]
  fn merge() {
    let from = Regex::seq("abc").or(Regex::seq("kkk"));
    let to = to_replacer("xyz");

    let rev = VariableImpl::new();
    let mut sst = Builder::identity(&VariableImpl::new());
    sst.merge(Builder::reverse(&VariableImpl::new()), &rev);
    check_merge! {
      sst: sst,
      vars: HashSet::from([rev.clone()]),
      cases: [
        "" => ("", { rev -> "" }),
        "abc" => ("abc", { rev -> "cba" }),
        "kkk" => ("kkk", { rev -> "kkk" }),
        "ddabcee" => ("ddabcee", { rev -> "eecbadd" }),
        "abcababcbcc" => ("abcababcbcc", { rev -> "ccbcbabacba" })
      ]
    }

    let one = VariableImpl::new();
    sst.merge(Builder::replace_reg(from.clone(), to.clone()), &one);
    check_merge! {
      sst: sst,
      vars: HashSet::from([rev.clone(), one.clone()]),
      cases: [
        "" => ("", { rev -> "", one -> "" }),
        "abc" => ("abc", { rev -> "cba", one -> "xyz" }),
        "kkk" => ("kkk", { rev -> "kkk", one -> "xyz" }),
        "ddabcee" => ("ddabcee", { rev -> "eecbadd", one -> "ddxyzee" }),
        "abcababcbcc" => ("abcababcbcc", { rev -> "ccbcbabacba", one -> "xyzababcbcc" })
      ]
    }

    let all = VariableImpl::new();
    sst.merge(Builder::replace_all_reg(from, to), &all);
    check_merge! {
      sst: sst,
      vars: HashSet::from([rev.clone(), one.clone(), all.clone()]),
      cases: [
        "" => (
          "",
          { rev -> "", one -> "", all -> "" }
        ),
        "abc" => (
          "abc",
          { rev -> "cba", one -> "xyz", all -> "xyz" }
        ),
        "kkk" => (
          "kkk",
          { rev -> "kkk", one -> "xyz", all -> "xyz" }
        ),
        "ddabcee" => (
          "ddabcee",
          { rev -> "eecbadd", one -> "ddxyzee", all -> "ddxyzee" }
        ),
        "abcababcbcc" => (
          "abcababcbcc",
          { rev -> "ccbcbabacba", one -> "xyzababcbcc", all -> "xyzabxyzbcc" }
        )
      ]
    }
  }

  #[test]
  fn generate_simple() {
    let builder = Builder::init();

    let cons = Transduction(vec![TransductionOp::Str("abc".to_owned())]);
    let sst = builder.generate(1, &cons);
    assertion!(sst, ["prefix"], 1 + 0, to_charwrap(["prefix", "abc"]));

    let cons = Transduction(vec![TransductionOp::Var(0)]);
    let sst = builder.generate(1, &cons);
    assertion!(sst, ["prefix"], 1 + 1, to_charwrap(["prefix", "prefix"]));

    let cons = Transduction(vec![TransductionOp::Reverse(0)]);
    let sst = builder.generate(1, &cons);
    assertion!(sst, ["prefix"], 1 + 1, to_charwrap(["prefix", "xiferp"]));

    let cons = Transduction(vec![TransductionOp::Replace(
      0,
      Regex::seq("p"),
      ReplaceTarget::Str("r".to_owned()),
    )]);
    let sst = builder.generate(1, &cons);
    assertion! {
      sst,
      ["prefix,prefix"],
      1 + 3,
      to_charwrap(["prefix,prefix", "rrefix,prefix"])
    };

    let cons = Transduction(vec![TransductionOp::Replace(
      1,
      Regex::seq("0"),
      ReplaceTarget::Var(0),
    )]);
    let sst = builder.generate(2, &cons);
    assertion! {
      sst,
      ["prefix", "0one0"],
      1 + 3 + 1,
      to_charwrap(["prefix", "0one0", "prefixone0"])
    };

    let cons = Transduction(vec![TransductionOp::ReplaceAll(
      0,
      Regex::seq("p"),
      ReplaceTarget::Str("r".to_owned()),
    )]);
    let sst = builder.generate(1, &cons);
    assertion! {
      sst,
      ["prefix,prefix"],
      1 + 3,
      to_charwrap(["prefix,prefix", "rrefix,rrefix"])
    };

    let cons = Transduction(vec![TransductionOp::ReplaceAll(
      1,
      Regex::seq("0"),
      ReplaceTarget::Var(0),
    )]);
    let sst = builder.generate(2, &cons);
    assertion! {
      sst,
      ["prefix", "0one0"],
      1 + 3 + 1,
      to_charwrap(["prefix", "0one0", "prefixoneprefix"])
    };

    let cons = Transduction(vec![
      TransductionOp::Var(0),
      TransductionOp::Var(1),
      TransductionOp::Var(0),
    ]);
    let sst = builder.generate(2, &cons);
    assertion! {
      sst,
      ["one", "two"],
      1 + 1 + 1,
      to_charwrap(["one", "two", "onetwoone"])
    };
  }

  #[test]
  /* including test of chain, chain_output */
  fn generate() {
    let builder = Builder::init();

    let cons = Transduction(vec![TransductionOp::Var(0), TransductionOp::Reverse(0)]);
    let sst = builder.generate(1, &cons);
    assertion! {
      sst,
      ["abc"],
      /* var: prefix + 0 id + 0 rev */
      1 + 1 + 1,
      to_charwrap(["abc", "abccba"])
    };

    let cons = Transduction(vec![
      TransductionOp::Var(0),
      TransductionOp::ReplaceAll(1, Regex::seq("abc"), ReplaceTarget::Str("xyz".to_owned())),
    ]);
    let sst = builder.generate(2, &cons);
    assertion! {
      sst,
      ["kkk", "wwwabcababcxyz"],
      /* var: prefix + 0 id + 1 replace */
      1 + 1 + 3,
      to_charwrap(["kkk", "wwwabcababcxyz", "kkkwwwxyzabxyzxyz"])
    }

    let cons = Transduction(vec![
      TransductionOp::Var(0),
      TransductionOp::ReplaceAll(2, Regex::seq("abc"), ReplaceTarget::Str("xyz".to_owned())),
      TransductionOp::Reverse(1),
    ]);
    let sst = builder.generate(3, &cons);
    assertion! {
      sst,
      ["https", "http", "wwwabcababcxyz"],
      /* var: prefix + 0 id + 2 replace + 1 rev */
      1 + 1 + 3 + 1,
      to_charwrap(["https", "http", "wwwabcababcxyz", "httpswwwxyzabxyzxyzptth"])
    }

    let cons = Transduction(vec![
      TransductionOp::Var(0),
      TransductionOp::Replace(3, Regex::seq("e"), ReplaceTarget::Var(0)),
      TransductionOp::Str("plp".to_owned()),
      TransductionOp::ReplaceAll(3, Regex::seq("e"), ReplaceTarget::Var(2)),
      TransductionOp::Reverse(0),
    ]);
    let sst = builder.generate(4, &cons);
    let mut prefixes = vec![
      "0zero".to_owned(),
      "1one".to_owned(),
      "2two".to_owned(),
      "3three".to_owned(),
    ];
    let result = format!(
      "{}{}{}{}{}",
      prefixes[0],
      prefixes[3].to_owned().replacen("e", &prefixes[0], 1),
      "plp",
      prefixes[3].to_owned().replace("e", &prefixes[2]),
      &prefixes[0].chars().rev().collect::<String>()
    );
    prefixes.push(result);
    assertion! {
      sst,
      ["0zero", "1one", "2two", "3three"],
      /* var: prefix + 0 id + 3 replace + 3 replaceall + 2 id + 0 rev */
      1 + 1 + 3 + 3 + 1 + 1,
      to_charwrap(prefixes.iter().map(|s| s.as_ref()))
    }
  }
}
