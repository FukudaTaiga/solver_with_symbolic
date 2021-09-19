/**
 * express effective Boolean Algebra A, tuple of (D, Phi, [], top, bot, and, or, not) \
 * D: a set of domain elements \
 * Phi: a set of predicates closed under boolean connectives and checkable to its satisfiability in a polynomial time \
 * []: denotational function, Phi -> 2^D (implemented as Phi -> D -> bool, need to check in class P) \
 * top: [top] -> D \
 * bot: [bot] -> {} \
 * and: [p and q] -> [p] ++ [q] \
 * or: [p or q] -> [p] || [q] \
 * not: [not p] -> D \ [p] \
 * 
 * WIP
 */
pub trait Predicate {
  fn and(self, other: Self) -> Self;
  fn or(self, other: Self) -> Self;
  fn not(self, other: Self) -> Self;
  fn top() -> Self;
  fn bot() -> Self;

  fn denotate(&self, arg: Self) -> bool;
}
