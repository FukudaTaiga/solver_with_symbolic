pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

#[cfg(test)]
mod tests {
    use super::recognizable::Recognizable;
    use super::regex::Regex;

    #[test]
    fn reg_sfa_all_test() {
        let reg = Regex::parse("_").unwrap();
        let reg2 = Regex::parse("_*").unwrap();
        println!("regex:\n{:#?}", reg2);
        let sfa = reg.to_sym_fa();
        let sfa2 = reg2.to_sym_fa();
        println!("sfa:\n{:#?}", sfa2);

        {
            assert!(sfa.member(&"a".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"x".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"$".chars().collect::<Vec<char>>()[..]));
            assert!(sfa2.member(&"cdsnjcdskcnsdjk".chars().collect::<Vec<char>>()[..]));
            assert!(sfa2.member(&"xxxxxxx".chars().collect::<Vec<char>>()[..]));
            assert!(sfa2.member(&":cdskoapcd".chars().collect::<Vec<char>>()[..]));
        }

        {
            assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"ax".chars().collect::<Vec<char>>()[..]));
        }
    }

    #[test]
    fn reg_sfa_eps_test() {
        let reg = Regex::parse("!*").unwrap();
        let reg2 = Regex::parse("avc(!*)").unwrap();
        println!("regex:\n{:#?}", reg);
        let sfa = reg.to_sym_fa();
        let sfa2 = reg2.to_sym_fa();
        println!("sfa:\n{:#?}", sfa);

        {
            assert!(sfa.member(&"".chars().collect::<Vec<char>>()[..]));
            assert!(sfa2.member(&"avc".chars().collect::<Vec<char>>()[..]));
        }

        {
            assert!(!sfa.member(&"ab".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa2.member(&"av".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"avcs".chars().collect::<Vec<char>>()[..]));
        }
    }

    #[test]
    fn reg_sfa_concat_test() {
        let reg = Regex::parse("abc_e").unwrap();
        println!("regex:\n{:#?}", reg);
        let sfa = reg.to_sym_fa();
        println!("sfa:\n{:#?}", sfa);

        {
            assert!(sfa.member(&"abcde".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"abcke".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"abcxe".chars().collect::<Vec<char>>()[..]));
        }

        {
            assert!(!sfa.member(&"abce".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"abc".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
        }
    }

    #[test]
    fn reg_sfa_or_test() {
        let reg = Regex::parse("(abc)|(kkk)|_").unwrap();
        println!("regex:\n{:#?}", reg);
        let sfa = reg.to_sym_fa();
        println!("sfa:\n{:#?}", sfa);

        {
            assert!(sfa.member(&"abc".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"kkk".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"d".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"x".chars().collect::<Vec<char>>()[..]));
        }

        {
            assert!(!sfa.member(&"ab".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"kk".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"abcd".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"kkx".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
        }
    }

    #[test]
    fn reg_sfa_star_test() {
        let reg = Regex::parse("(a*)(b*)(c*)").unwrap();
        println!("regex:\n{:#?}", reg);
        let sfa = reg.to_sym_fa();
        println!("sfa:\n{:#?}", sfa);

        {
            assert!(sfa.member(&"aaabcccc".chars().collect::<Vec<char>>()[..]));

            assert!(sfa.member(&"aaacccc".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"bcccc".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"aaab".chars().collect::<Vec<char>>()[..]));

            assert!(sfa.member(&"aaa".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"b".chars().collect::<Vec<char>>()[..]));
            assert!(sfa.member(&"cccc".chars().collect::<Vec<char>>()[..]));

            assert!(sfa.member(&"".chars().collect::<Vec<char>>()[..]));
        }

        {
            assert!(!sfa.member(&"kcd".chars().collect::<Vec<char>>()[..]));
            assert!(!sfa.member(&"abca".chars().collect::<Vec<char>>()[..]));
        }
    }

    #[test]
    fn reg_to_sfa_test() {
        let reg = Regex::parse("a*b(c|d)a").unwrap();
        println!("regex:\n{:#?}", reg);
        let sfa = reg.to_sym_fa();
        println!("sfa:\n{:#?}", sfa);

        assert!(sfa.member(&"aaabca".chars().collect::<Vec<char>>()[..]));
        assert!(sfa.member(&"bca".chars().collect::<Vec<char>>()[..]));
        assert!(sfa.member(&"aaabda".chars().collect::<Vec<char>>()[..]));
        assert!(!sfa.member(&"aaa".chars().collect::<Vec<char>>()[..]));
        assert!(!sfa.member(&"zzz".chars().collect::<Vec<char>>()[..]));
        assert!(!sfa.member(&"axda".chars().collect::<Vec<char>>()[..]));
    }
}
