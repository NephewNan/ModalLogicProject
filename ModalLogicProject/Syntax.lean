namespace ML
-- The project will be under namespace ML.
-- We first define modal formulas inductively. We follow the definition in Modal Logic book.
-- The basic modal language includes: variable, bottom, negation, disjunction, and diamond.

inductive Formula (V: Type)
  | var (p : V)
  | bot
  | neg (φ: Formula V)
  | or (φ ψ : Formula V)
  | diamond (φ : Formula V)
  deriving Repr, DecidableEq

-- We then extend the language so it includes: top, conjunction, implication, bidirectional, and box.

def top : Formula V := Formula.neg Formula.bot

def and (φ ψ : Formula V) : Formula V := Formula.neg (Formula.or (Formula.neg φ)  (Formula.neg ψ))

def imp (φ ψ: Formula V) : Formula V := Formula.or (Formula.neg φ) ψ

def iff (φ ψ: Formula V) : Formula V := and (imp φ ψ) (imp ψ φ)

def box (φ: Formula V): Formula V := Formula.neg (Formula.diamond (Formula.neg φ))

-- infixr, right associative
-- numbers shows precedence. Higher number means higher priority.
-- Neg, Box, and Diamond should have highest binding priority.
-- And > Or > Implies > IFF

notation "⊥" => Formula.bot
notation "⊤" => top
prefix:70 "¬" => Formula.neg
infixr:55 " ⟶ " => imp
infixr:50 " ↔ " => iff
infixr:60 " ∨ " => Formula.or
infixr:65 " ∧ " => and
prefix:70 "□" => box
prefix:70 "◇" => Formula.diamond

end ML
