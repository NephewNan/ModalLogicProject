import ModalLogicProject.Syntax

namespace ML

-- W: Type
-- W is some type. think of it as a set
-- w: W means, w is of type W, or w ∈ W

structure Frame (W : Type) where
  rel : W → W → Prop

structure Model (W : Type) (V: Type) where
  frame : Frame W
  val : V → W → Prop

--Definition 1.20 from Modal Logic book.
-- Given a model M, and a world w, satisfies receives a formula V, and checks whether M, w ⊩ V
def satisfies {W : Type} (M : Model W V) (w : W) : Formula V → Prop
  | Formula.var p => M.val p w
  | Formula.bot => False
  | Formula.neg φ => ¬(satisfies M w φ)
  | Formula.or φ ψ => (satisfies M w φ) ∨ (satisfies M w ψ)
  | Formula.diamond φ => ∃ v, M.frame.rel w v ∧ satisfies M v φ

notation "(" M "," w  ")" "⊩ " φ => satisfies M w φ

--A formula is globally true in a model if it is satisfied at all points.
def true_globally {W : Type} (M : Model W V) (φ : Formula V) : Prop :=
  ∀ w, (M, w) ⊩ φ

notation M " ⊩ᵐ " φ => true_globally M φ
-- We dont need to investigate the structure of φ
-- Can also be:
-- def true_globally {W : Type} (M : Model W V) : Formula V → Prop :=
--    fun φ => ∀ w, (M, w) ⊩ φ
-- same thing

--A formula is satisfiable in a model if there is some point in which it is true.
def satisfiable {W : Type} (M : Model W V) (φ : Formula V) : Prop :=
  ∃ w, (M, w) ⊩ φ

--A formula is falsifiable in a model if its negation is satisfiable.
def falsifiable {W : Type} (M : Model W V) (φ : Formula V) : Prop :=
  satisfiable M (¬φ)

--A formula φ is valid at a state w in a frame F if
--φ is true at w in every model (F,V) based on F.
def valid_at_state_in_frame {W : Type} (F: Frame W) (w: W) (φ : Formula V): Prop :=
  ∀ (V: V → W → Prop), ((Model.mk F V), w) ⊩ φ

notation "(" F "," w ")" " ⊩ᶠ " φ => valid_at_state_in_frame F w φ

--φ is valid in a frame F if it is valide at every state in F.
def valid_in_frame {W: Type} (F: Frame W) (φ: Formula V): Prop:=
  ∀ (w: W), (F, w) ⊩ᶠ φ

notation F "⊩ᶠ" φ => valid_in_frame F φ

--φ is valid if it is valid on the class of all frames.
def valid (φ : Formula V) : Prop :=
  ∀ (W : Type) (F : Frame W), valid_in_frame F φ

notation "⊩ " φ => valid φ

end ML
