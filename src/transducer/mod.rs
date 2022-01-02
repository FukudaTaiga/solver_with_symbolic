pub mod sst;
pub mod sst_factory;
pub mod term;
pub mod transducer;

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
          possibilities
            .into_iter()
            .filter_map(|(q, f)| {
              self.output_function.get(&q).map(|seq| {
                (
                  seq
                    .iter()
                    .flat_map(|o| match o {
                      OutputComp::A(a) => vec![a.clone()],
                      OutputComp::X(x) => f.get(x).unwrap_or(&Vec::new()).clone(),
                    })
                    .collect::<Vec<_>>(),
                  vars
                    .into_iter()
                    .map(move |var| (var.clone(), f[var].clone()))
                    .collect(),
                )
              })
            })
            .collect()
        },
      )
    }
  }

  /*
   * merge is used in generating whole sst and it is stil incomplete.
   * so it is ok that there is ambiguity due to the separator.
   */
  macro_rules! check_merge {
    (
      sst: $sst:ident,
      vars: $vars:expr,
      cases: [ $( $input:expr => ($output:expr, { $( $var:ident -> $var_expected:expr ),* }) ),+ ]
    ) => {
      $(
        let mut input = chars($input);
        let results = $sst.run_with_var(&$vars, &input);
        let expected = (chars($output), HashMap::from([
          $( ($var.clone(), vec![]) ),*
        ]));
        eprintln!("expected{:#?}", expected);
        eprintln!("{:#?}", results);
        assert!(results.into_iter().all(|seq| seq == expected));
        input.push(Domain::separator());
        let results = $sst.run_with_var(&$vars, &input);
        let output = chars($output);
        let expected = (output, HashMap::from([
          $( ($var.clone(), chars($var_expected)) ),*
        ]));
        eprintln!("expected{:#?}", expected);
        eprintln!("results{:#?}", results);
        assert!(results.contains(&expected));
      )+
    };
    (
      sst: $sst:ident,
      vars: $vars:expr,
      cases: [ $( $input:expr => ($output:expr, { $( $var:ident -> $var_expected:expr ),* }) ),+ ],
      wrap
    ) => {
      $(
        let input = to_charwrap($input);
        let results = $sst.run_with_var(&$vars, &input);
        let mut output = to_charwrap($output);
        output.pop();
        let expected = (output, HashMap::from([
          $(
            (
              $var.clone(),
              {
                let mut var_expected = to_charwrap($var_expected);
                var_expected.pop();
                var_expected
              }
            )
          ),*
        ]));
        eprintln!("expected{:#?}", expected);
        eprintln!("results{:#?}", results);
        assert!(results.contains(&expected));
      )+
    };
  }

  //TODO -- ensure merge and chain work fine
  #[test]
  fn merge() {
    let replace_from = Regex::seq("abc").or(Regex::seq("kkk"));
    let replace_to = to_replacer("xyz");

    let rev = VariableImpl::new();
    let rep_rev = Builder::replace_reg(replace_from.clone(), replace_to.clone())
      .merge(Builder::reverse(), &rev);

    eprintln!("{:?}\n{:?}", rep_rev, rev);

    check_merge! {
      sst: rep_rev,
      vars: HashSet::from([rev.clone()]),
      cases: [
        "" => ("", { rev -> "" }),
        "abc" => ("xyz", { rev -> "cba" }),
        "kkk" => ("xyz", { rev -> "kkk" }),
        "ddabcee" => ("ddxyzee", { rev -> "eecbadd" }),
        "abcababcbcc" => ("xyzababcbcc", { rev -> "ccbcbabacba" })
      ]
    }

    let rep = VariableImpl::new();
    let id_all =
      Builder::identity().merge(Builder::replace_all_reg(replace_from, replace_to), &rep);

    check_merge! {
      sst: id_all,
      vars: HashSet::from([rep.clone()]),
      cases: [
        "" => ("", { rep -> "" }),
        "abc" => ("abc", { rep -> "xyz" }),
        "kkk" => ("kkk", { rep -> "xyz" }),
        "ddabcee" => ("ddabcee", { rep -> "ddxyzee" }),
        "abcababcbcc" => ("abcababcbcc", { rep -> "xyzabxyzbcc" })
      ]
    }
  }

  #[test]
  fn duplicating_correctly() {
    let mut vars = HashSet::new();
    let sst = Builder::identity();
    eprintln!(
      "states len: {}, vars len: {}",
      sst.states().len(),
      sst.variables().len()
    );
    assert!(sst.states().len() == 1 && sst.variables().len() == 1);
    let var1 = VariableImpl::new();
    vars.insert(var1.clone());
    let sst = sst.merge(Builder::identity(), &var1);
    eprintln!(
      "states len: {}, vars len: {}",
      sst.states().len(),
      sst.variables().len()
    );
    /*
     * variables len is id's var = 1 + id's var = 1 + var1 = 3
     * such rebunduned var is not produced when used by SstBuilder
     */
    assert!(sst.states().len() == 1 && sst.variables().len() == 3);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        "xyz" => ("xyz", { var1 -> "xyz" })
      ]
    }
    let var2 = VariableImpl::new();
    vars.insert(var2.clone());
    let sst = sst.merge(Builder::identity(), &var2);
    eprintln!(
      "states len: {}, vars len: {}",
      sst.states().len(),
      sst.variables().len()
    );
    assert!(sst.states().len() == 1 && sst.variables().len() == 5);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        "xyz" => ("xyz", { var1 -> "xyz", var2 -> "xyz" })
      ]
    }
    let var3 = VariableImpl::new();
    vars.insert(var3.clone());
    let sst = sst.merge(Builder::identity(), &var3);
    eprintln!(
      "states len: {}, vars len: {}",
      sst.states().len(),
      sst.variables().len()
    );
    assert!(sst.states().len() == 1 && sst.variables().len() == 7);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        "xyz" => ("xyz", { var1 -> "xyz", var2 -> "xyz", var3 -> "xyz" })
      ]
    }
  }

  #[test]
  fn chain() {
    let replace_from = Regex::seq("abc").or(Regex::seq("kkk"));
    let replace_to = to_replacer("xyz");

    let var = VariableImpl::new();
    let vars = HashSet::from([var.clone()]);

    let sst = Builder::identity().merge(
      Builder::replace_reg(replace_from.clone(), replace_to.clone()),
      &var,
    );
    eprintln!("{:?}", sst);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        &["abcabc"] => (&["abcabc"], { var -> &["xyzabc"] })
      ],
      wrap
    }
    let sst = sst.chain(Builder::reverse());
    eprintln!("{:?}", sst);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        &["abcabc", "edf"] => (&["abcabc", "fde"], { var -> &["xyzabc"] })
      ],
      wrap
    }

    let sst = sst.chain(Builder::replace_all_reg(replace_from, replace_to));
    eprintln!("{:?}", sst);
    check_merge! {
      sst: sst,
      vars: vars,
      cases: [
        &[] => (&[], { var -> &[] }),
        &["abcabc", "abcabc", "abcabc"] => (
          &["abcabc", "cbacba", "xyzxyz"], { var -> &["xyzabc"] }
        )
      ],
      wrap
    }
  }
}
