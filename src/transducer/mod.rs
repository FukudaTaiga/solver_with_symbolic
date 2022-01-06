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

mod macros {
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
        $(, ($source:ident, $predicate:expr) -> [$( ( $target:ident, $update:expr ) )*] ),*
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
        &mut |(_, map), c, (q, alpha)| {
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
            eprintln!("{:#?}", $sst);
            eprintln!("expected{:?}", expected);
            eprintln!("results{:?}", results);
          }
          result
        });
      )+
    };
    (
      sst: $sst:expr,
      vars: $vars:expr,
      cases: [
        $(
          $input:expr => ( $output:expr, { $( $var:ident -> $var_expected:expr ),* } )
        ),*
      ],
      $(
        rejects: [
          $(
            $input_emp:expr
          ),*
        ],
      )?
      wrap
    ) => {
      $(
        let input = to_charwrap($input);
        let results = $sst.run_with_var(&$vars, &input);
        let output = to_charwrap($output);
        let expected = (output, HashMap::from([
          $(
            (
              $var.clone(),
              {
                let v = to_charwrap($var_expected);
                Vec::from(&v[..v.len().max(1) - 1])
              }
            )
          ),*
        ]));
        assert!({
          let result = results.contains(&expected);
          if !result {
            eprintln!("{:#?}", $sst);
            eprintln!("expected{:?}", expected);
            eprintln!("results{:?}", results);
          }
          result
        });
      )*
      $(
        $(
          let input = to_charwrap($input_emp);
          let results = $sst.run_with_var(&$vars, &input);
          assert!(results.is_empty());
        )*
      )?
    };
  }

  #[test]
  fn merge() {
    let from = Regex::seq("abc").or(Regex::seq("kkk"));
    let to = to_replacer("xyz");

    let rev = VariableImpl::new();
    let sst =
      Builder::identity(&VariableImpl::new()).merge(Builder::reverse(&VariableImpl::new()), &rev);
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
    let sst = sst.merge(Builder::replace_reg(from.clone(), to.clone()), &one);
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
    let sst = sst.merge(Builder::replace_all_reg(from, to), &all);
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
  fn duplicating_correctly() {
    let mut vars = HashSet::new();
    let result = VariableImpl::new();
    vars.insert(VariableImpl::clone(&result));
    let sst = Builder::identity(&result);
    assert!(sst.states().len() == 1 && sst.variables().len() == 1);
    let sst = sst.merge(Builder::constant("abc"), &result);
    let sst_ = sst.clone();
    check_merge! {
      sst: sst_,
      vars: HashSet::new(),
      cases: [
        "xyz" => ("xyzabc", {})
      ]
    };
  }

  #[test]
  fn chain() {
    let replace_from = Regex::seq("abc").or(Regex::seq("kkk"));
    let replace_to = to_replacer("xyz");

    let var = VariableImpl::new();
    let vars = HashSet::from([var.clone()]);

    let sst = Builder::identity(&VariableImpl::new())
      .merge(Builder::replace_reg(replace_from, replace_to), &var);
    let sst_ = sst.clone().chain_output(vec![], HashSet::new());
    check_merge! {
      sst: sst_,
      vars: vars,
      cases: [
        &["abcabc"] => (&["abcabc"], { var -> &["xyzabc"] }),
        &["abdkkkkhjkkkk"] => (&["abdkkkkhjkkkk"], { var -> &["abdxyzkhjkkkk"] })
      ],
      rejects: [],
      wrap
    }
    let sst = sst.chain(Builder::reverse(&VariableImpl::new()));
    let sst_ = sst.clone().chain_output(vec![], HashSet::new());
    check_merge! {
      sst: sst_,
      vars: vars,
      cases: [
        &["abcabc", "edf"] => (&["abcabc", "fde"], { var -> &["xyzabc"] }),
        &["abdkkkkhjkkkk", "palindromemordnilap"] => (
          &["abdkkkkhjkkkk", "palindromemordnilap"], { var -> &["abdxyzkhjkkkk"] }
        )
      ],
      rejects: [ &["aaaa"], &["abdkkkkhjkkkk"] ],
      wrap
    }
    let replace_from = Regex::seq("start1")
      .or(Regex::seq("start2"))
      .concat(Regex::all().star())
      .concat(Regex::seq("end"));
    let replace_to = to_replacer("");
    let sst = sst.chain(Builder::replace_all_reg(replace_from, replace_to));
    let sst_ = sst.chain_output(vec![], HashSet::new());
    check_merge! {
      sst: sst_,
      vars: vars,
      cases: [
        &["abcabc", "abcabc", "abcabc"] => (
          &["abcabc", "cbacba", "abcabc"], { var -> &["xyzabc"] }
        ),
        &[
          "abdkkkkhjkkkk",
          "palindromemordnilap",
          "nottrancate,start1trancate1end,start2trancate2end,nottrancate"
        ] => (
          &[
            "abdkkkkhjkkkk",
            "palindromemordnilap",
            "nottrancate,,,nottrancate"
          ], { var -> &["abdxyzkhjkkkk"] }
        )
      ],
      rejects: [ &["aaaa", "aaaa"] ],
      wrap
    }
  }
}
