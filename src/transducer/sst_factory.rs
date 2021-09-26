#![allow(dead_code)]

use super::sst::SymSST;
use super::term::{FunctionTerm, Lambda, OutputComp, UpdateComp, Variable};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::State;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use std::rc::Rc;

pub fn replace_all<'a>(old: String, new: String) -> SymSST<'a, Lambda<Predicate<'a, char>>> {
    if old.len() == 0 {
        panic!("Invalid Input");
    }

    let accumulator = Rc::new(Variable::new("acc"));
    let result = Rc::new(Variable::new("res"));
    let variables = HashSet::from_iter(vec![Rc::clone(&accumulator), Rc::clone(&result)]);

    let output_unmatch = Rc::new(vec![
        OutputComp::X(Rc::clone(&result)),
        OutputComp::X(Rc::clone(&accumulator)),
    ]);

    let mut states = HashSet::new();
    let mut output_function = HashMap::new();
    let mut transition = HashMap::new();
    let initial_state = Rc::new(State::new());
    states.insert(Rc::clone(&initial_state));
    let mut current = Rc::clone(&initial_state);
    let mut chars = old.chars().enumerate();

    let acc_alpha = Rc::new(vec![
        UpdateComp::X(Rc::clone(&accumulator)),
        UpdateComp::F(Lambda::<Predicate<'a, char>>::identity()),
    ]);
    let res_alpha = Rc::new(vec![UpdateComp::X(Rc::clone(&result))]);

    let acc_beta = Rc::new(vec![]);
    let res_beta = Rc::new(vec![
        UpdateComp::X(Rc::clone(&result)),
        UpdateComp::X(Rc::clone(&accumulator)),
        UpdateComp::F(Lambda::<Predicate<'a, char>>::identity()),
    ]);
    let mut first = None;

    while let Some((i, c)) = chars.next() {
        let next = Rc::new(State::new());
        let p = Rc::new(Predicate::eq(c));
        let not_p = Rc::new(p.not());
        states.insert(Rc::clone(&next));

        let mut alpha = HashMap::new();
        alpha.insert(Rc::clone(&accumulator), Rc::clone(&acc_alpha));
        alpha.insert(Rc::clone(&result), Rc::clone(&res_alpha));
        let mut beta = HashMap::new();
        beta.insert(Rc::clone(&accumulator), Rc::clone(&acc_beta));
        beta.insert(Rc::clone(&result), Rc::clone(&res_beta));

        output_function.insert(Rc::clone(&current), Rc::clone(&output_unmatch));

        transition.insert(
            (Rc::clone(&current), Rc::clone(&p)),
            (Rc::clone(&next), alpha),
        );

        if i == 1 {
            if let Some((_, p1, not_p1)) = &first {
                let not_p = Rc::new(not_p.and(not_p1));
                let mut gamma = HashMap::new();
                gamma.insert(
                    Rc::clone(&accumulator),
                    Rc::new(vec![UpdateComp::F(
                        Lambda::<Predicate<'a, char>>::identity(),
                    )]),
                );
                gamma.insert(
                    Rc::clone(&result),
                    Rc::new(vec![
                        UpdateComp::X(Rc::clone(&result)),
                        UpdateComp::X(Rc::clone(&accumulator)),
                    ]),
                );
                transition.insert(
                    (Rc::clone(&current), Rc::clone(&not_p)),
                    (Rc::clone(&initial_state), beta),
                );
                transition.insert(
                    (Rc::clone(&current), Rc::clone(p1)),
                    (Rc::clone(&current), gamma),
                );
            }
        } else {
            transition.insert(
                (Rc::clone(&current), Rc::clone(&not_p)),
                (Rc::clone(&initial_state), beta),
            );
            if i == 0 {
                first = Some((Rc::clone(&next), p, not_p));
            }
        }

        current = Rc::clone(&next);
    }

    if let Some((first, p, not_p)) = first {
        let last_acc_alpha = Rc::new(vec![UpdateComp::F(
            Lambda::<Predicate<'a, char>>::identity(),
        )]);
        let last_res_alpha = Rc::new({
            let mut v1 = vec![UpdateComp::X(Rc::clone(&result))];
            v1.extend(
                new.chars()
                    .map(|c| UpdateComp::F(Lambda::<Predicate<'a, char>>::constant(c))),
            );
            v1
        });
        let last_res_beta = Rc::new({
            let mut v1 = vec![UpdateComp::X(Rc::clone(&result))];
            v1.extend(
                new.chars()
                    .map(|c| UpdateComp::F(Lambda::<Predicate<'a, char>>::constant(c))),
            );
            v1.push(UpdateComp::F(Lambda::identity()));
            v1
        });
        let mut alpha_l = HashMap::new();
        alpha_l.insert(Rc::clone(&accumulator), Rc::clone(&last_acc_alpha));
        alpha_l.insert(Rc::clone(&result), Rc::clone(&last_res_alpha));
        let mut beta_l = HashMap::new();
        beta_l.insert(Rc::clone(&accumulator), Rc::clone(&acc_beta));
        beta_l.insert(Rc::clone(&result), Rc::clone(&last_res_beta));
        transition.insert(
            (Rc::clone(&current), Rc::clone(&p)),
            (Rc::clone(&first), alpha_l),
        );
        transition.insert(
            (Rc::clone(&current), Rc::clone(&not_p)),
            (Rc::clone(&initial_state), beta_l),
        );
    }

    let output_match = Rc::new({
        let mut v1 = vec![OutputComp::X(Rc::clone(&result))];
        let v2 = new.chars().map(|c| OutputComp::A(c));
        v1.extend(v2);
        v1
    });

    output_function.insert(Rc::clone(&current), Rc::clone(&output_match));

    SymSST::new(
        states,
        variables,
        initial_state,
        output_function,
        transition,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "Invalid Input")]
    fn empty_substr_test() {
        let _rep = replace_all("".to_string(), "aaa".to_string());

        unreachable!();
    }

    #[test]
    fn abc_to_xyz_sst_test() {
        let rep = replace_all("abc".to_string(), "xyz".to_string());

        assert_eq!(
            String::from_iter(&rep.run(&"abc".chars().collect::<Vec<char>>()[..])[0]),
            "xyz".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"a".chars().collect::<Vec<char>>()[..])[0]),
            "a".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"bc".chars().collect::<Vec<char>>()[..])[0]),
            "bc".to_string()
        );
        assert_eq!(
            String::from_iter(
                &rep.run(&"abcabcabcaaabbaccbackljhg".chars().collect::<Vec<char>>()[..])[0]
            ),
            "xyzxyzxyzaaabbaccbackljhg".to_string()
        );
    }

    #[test]
    fn a_to_many_sst_test() {
        let rep = replace_all(
            "a".to_string(),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string(),
        );

        assert_eq!(
            String::from_iter(&rep.run(&"abc".chars().collect::<Vec<char>>()[..])[0]),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bc".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"a".chars().collect::<Vec<char>>()[..])[0]),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"bc".chars().collect::<Vec<char>>()[..])[0]),
            "bc".to_string()
        );
        assert_eq!(
            String::from_iter(
                &rep.run(&"abcabcabcaaabbaccbackljhg".chars().collect::<Vec<char>>()[..])[0]
            ),
            "qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bcqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\qwertyuiop@[asdfghjkl;:]zxcvbnm,./\\bbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ccbqwertyuiop@[asdfghjkl;:]zxcvbnm,./\\ckljhg".to_string()
        );
    }

    #[test]
    fn abcxyz_to_1_sst_test() {
        let rep = replace_all("abcxyz".to_string(), "1".to_string());

        assert_eq!(
            String::from_iter(&rep.run(&"abcxyz".chars().collect::<Vec<char>>()[..])[0]),
            "1".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"abcxy".chars().collect::<Vec<char>>()[..])[0]),
            "abcxy".to_string()
        );
        assert_eq!(
            String::from_iter(&rep.run(&"abcyz".chars().collect::<Vec<char>>()[..])[0]),
            "abcyz".to_string()
        );
        assert_eq!(
            String::from_iter(
                &rep.run(&"aaaabcxyzzzzabcxyz".chars().collect::<Vec<char>>()[..])[0]
            ),
            "aaa1zzz1".to_string()
        );
    }
}
