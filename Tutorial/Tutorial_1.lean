import ModalLogicProject.Syntax
import ModalLogicProject.Semantics

namespace ML

--I try to formalize tutorial 1 to practice Lean.

inductive W
  | s
  | t
  | u
  | v
  | w

inductive V
  | p
  | q

def toy_model : Model W V:= {
  frame := {
    rel := fun w1 w2 =>
      match w1, w2 with
      | W.s, W.s => True
      | W.s, W.t => True
      | W.s, W.u => True
      | W.t, W.t => True
      | W.t, W.w => True
      | W.u, W.v => True
      | W.v, W.w => True
      | _, _ => False
  },

  val := fun var world =>
    match var, world with
    | V.p, W.s => True
    | V.p, W.t => True
    | V.p, W.w => True
    | V.q, W.t => True
    | _, _ => False
}

--Exercise 1. Consider the model defined above.
--(1a) Show that (toy_model, s) ⊩ ◇(q ∧ ◇q)
example  : (toy_model, W.s) ⊩ ◇(Formula.var V.q ∧ ◇(Formula.var V.q)) := by
  rw[satisfies]
  exists W.t
  constructor
  ·
    simp [toy_model]
  ·
    simp[and]
    simp[satisfies]
    constructor
    ·
      trivial
    ·
      exists W.t
