#![allow(dead_code)]
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

//static mut INTERNAL: u64 = 0;

#[derive(Debug, Hash, Eq, Clone)]
pub struct State {
  //value: u64,
}
impl State {
  pub fn new() -> State {
    unsafe {
      //INTERNAL += 1;
      //State { value: INTERNAL }
    }
    State {}
  }
}
impl PartialEq for State {
  fn eq(&self, other: &Self) -> bool {
    std::ptr::eq(self, other)
    //self.value == other.value
  }
}

//trait for state machine
// pub trait StateMachine {
//   type Phi;
//   type Dest;

//   fn states(&self) -> &HashSet<Rc<State>>;
//   fn states_mut(&mut self) -> &mut HashSet<Rc<State>>;

//   fn initial_state(&self) -> &Rc<State>;
//   fn initial_state_mut(&self) -> &mut Rc<State>;

//   fn final_states(&self) -> &HashSet<Rc<State>>;
//   fn final_states_mut(&mut self) -> &mut HashSet<Rc<State>>;

//   fn transition(&self) ->  &HashMap<(Rc<State>, Self::Phi), Self::Dest>;
//   fn transition_mut(&self) ->  &mut HashMap<(Rc<State>, Self::Phi), Self::Dest>;

//   fn phi<P>(p: &Self::Phi) -> 
//   fn dest(d: &Self::Dest) -> &Rc<State>;
//   fn dest_clone<D>(d: &Self::Dest, ) -> D;

//   fn minimize(&mut self) {
//     let mut stack = vec![Rc::clone(&self.initial_state())];
//     let mut reachables = vec![];

//     while let Some(state) = stack.pop() {
//       reachables.push(Rc::clone(&state));

//       for ((p, _), q) in self.transition_mut() {
//         if *p == state && !reachables.contains(StateMachine::dest(q)) {
//           stack.push(Rc::clone(StateMachine::dest(q)));
//         }
//       }
//     }

//     *self.states_mut() = reachables.into_iter().collect();
//     *self.transition_mut() = self
//       .transition()
//       .iter()
//       .filter_map(|((state, phi), next)| {
//         if self.states().contains(state) && self.states().contains(StateMachine::dest(next)) {
//           Some(((Rc::clone(state), Rc::clone(phi)), Rc::clone(next)))
//         } else {
//           None
//         }
//       })
//       .collect();
//     *self.final_states_mut() = self
//       .final_states()
//       .intersection(&self.states())
//       .map(|final_state| Rc::clone(final_state))
//       .collect();
//   }
// }