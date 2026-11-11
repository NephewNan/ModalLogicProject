-- This module serves as the root of the ModalLogicProject library.
-- Import modules here that should be built as part of the library.
import ModalLogicProject.Syntax
import ModalLogicProject.Semantics
import ModalLogicProject.Bisimulations

namespace ML

example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

example (a b : Nat) : a + b = b + a := by
  omega

example (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
  rw[Nat.add_zero]
  rw[Nat.zero_add]

  | succ n ih =>
  rw[Nat.add_comm]

example: 2 = Nat.succ (Nat.succ 0) := by
  rfl
