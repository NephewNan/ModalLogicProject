import ModalLogicProject.Semantics
import Mathlib
open Classical

namespace ML

/-- We define bisimulation here. Let M = (W,R,V) and M' - (W',R',V') be two models. A non-empty binary relation Z ⊆ W × W' is called a bisimulation between M and M' if the following conditions are satisfied.

  1: If w Z w', then w and w' satisfy the same proposition letters.
  2: If w Z w' and R w v, then ∃ v', v Z v' and R'w'v'.
  3: If w Z w' and R' w' v', then ∃ v, v Z v' and R w v.

  Non-emptyness is not guaranteed in definition!
-/

structure Bisimulation {W W' V : Type} (M : Model W V) (M' : Model W' V) where
  -- The binary relation Z
  Z : W → W' → Prop

  -- Condition 1: If w Z w', then w and w' satisfy the same proposition letters.
  atoms_match : ∀ (w : W) (w' : W'), Z w w' →
    ∀ (p : V), M.val p w ↔ M'.val p w'

  -- Condition 2: If w Z w' and R w v, then ∃ v', v Z v' and R'w'v'.
  forth : ∀ (w : W) (w' : W'), Z w w' →
    ∀ (v : W), M.frame.rel w v →
    ∃ (v' : W'), M'.frame.rel w' v' ∧ Z v v'

  -- Condition 3: If w Z w' and R' w' v', then ∃ v, v Z v' and R w v.
  back : ∀ (w : W) (w' : W'), Z w w' →
    ∀ (v' : W'), M'.frame.rel w' v' →
    ∃ (v : W), M.frame.rel w v ∧ Z v v'


-- Theorem 2.20 from Modal Logic book.
/-- Modal formulas are invariant under bisimulation. -/
theorem modal_invariance {W W' V : Type}
    (M : Model W V) (M' : Model W' V)
    (B : Bisimulation M M')
    (φ : Formula V)
    (w : W) (w' : W') (hZ : B.Z w w') :
    ((M, w) ⊩ φ) ↔ ((M', w') ⊩ φ) := by

  -- We do structural induction on the formula φ.
  -- by generalizing w and w', the induction hypothesis becomes "∀ .......".
  -- otherwise it only talks about the specific w and w'
  induction φ generalizing w w'


  -- then we solve each case

  case var p =>
    -- Base case: Variables. The Bisimulation 'atoms_match' condition guarantees this.
    unfold satisfies
    exact B.atoms_match w w' hZ p

  case bot =>
    -- Base case: Contradiction. False ↔ False is trivial.
    unfold satisfies
    rfl

  case neg ψ ih =>
    -- Inductive step: Negation. Use the inductive hypothesis (ih) for ψ.
    unfold satisfies
    rw [ih w w' hZ]

  case or ψ1 ψ2 ih1 ih2 =>
    -- Inductive step: Disjunction. Use both inductive hypotheses.
    unfold satisfies
    rw [ih1 w w' hZ, ih2 w w' hZ]

  case diamond ψ ih =>
    -- Inductive step: Diamond. We prove the iff (↔) in both directions.
    unfold satisfies
    -- constructor splits ↔ into left to right and right to left
    constructor
    · -- Left-to-Right.
      intro ⟨v, hw_v, hv_sat⟩
      have ⟨v', hw'_v', hz_vv'⟩ := B.forth w w' hZ v hw_v
      have hv'_sat : (M', v') ⊩ ψ := (ih v v' hz_vv').mp hv_sat
      exact ⟨v', hw'_v', hv'_sat⟩
    · -- Right-to-Left.
      intro ⟨v', hw'_v', hv'_sat⟩
      have ⟨v, hw_v, hz_vv'⟩ := B.back w w' hZ v' hw'_v'
      have hv_sat : (M, v) ⊩ ψ := (ih v v' hz_vv').mpr hv'_sat
      exact ⟨v, hw_v, hv_sat⟩

/-- A model is image-finite if every world has only finitely many successors. -/
def ImageFinite {W V : Type} (M : Model W V) : Prop :=
  ∀ (w : W), Set.Finite { v : W | M.frame.rel w v }

/-- The Hennessy-Milner Theorem:
    Let M and M' be two image-finite models, then model equivlance implies M and M' are bisimilar. -/

-- We define Modal Equivalence.
def modal_equiv {W W' V : Type} (M : Model W V) (M' : Model W' V) (w : W) (w' : W') : Prop :=
  ∀ (φ : Formula V), ((M, w) ⊩ φ) ↔ (M', w') ⊩ φ

/-- Recursively joins a list of formulas with conjunction.
    An empty list evaluates to True (¬⊥). -/
def big_and {V : Type} : List (Formula V) → Formula V
  | [] => Formula.neg Formula.bot
  | ψ :: ψs =>  ψ ∧ (big_and ψs)

/-- A world satisfies a big_and formula iff it satisfies every formula in the list. -/
lemma satisfies_big_and {W V : Type} (M : Model W V) (w : W) (L : List (Formula V)) :
    ((M, w) ⊩ big_and L) ↔ ∀ ψ ∈ L, (M, w) ⊩ ψ := by
  induction L with
  | nil =>
    simp [big_and, satisfies]

  | cons head tail ih =>
    simp [big_and, and , satisfies]
    rw [ih]
    tauto

/-- If two worlds are not modally equivalent, there is a formula true in v but false in v'. -/
lemma dist_formula {W W' V : Type} (M : Model W V) (M' : Model W' V) (v : W) (v' : W')
    (h_not : ¬ modal_equiv M M' v v') :
    ∃ (ψ : Formula V), ((M, v) ⊩ ψ) ∧ ¬(M', v') ⊩ ψ := by
  unfold modal_equiv at h_not
  rw [not_forall] at h_not
  rcases h_not with ⟨φ, hφ⟩

  -- The formula φ might be true in v and false in v', or vice versa.
  -- We use Classical logic to check which case it is.
  by_cases h1 : (M, v) ⊩ φ
  · -- Case 1: φ is true in v, so it is our distinguishing formula.
    use φ
    tauto
  · -- Case 2: φ is false in v, so its negation is true in v.
    use Formula.neg φ
    simp [satisfies]
    tauto

theorem hennessy_milner {W W' V : Type}
    (M : Model W V) (M' : Model W' V)
    (hFin : ImageFinite M)
    (hFin' : ImageFinite M')
    (w : W) (w' : W'):
    (∃ (B : Bisimulation M M'), B.Z w w') ↔ (modal_equiv M M' w w') := by

  constructor
  ·
    intro ⟨B, hZ⟩
    unfold modal_equiv
    intro φ
    exact (modal_invariance M M' B φ w w' hZ)

  ·
    intro hEq
    let B_equiv : Bisimulation M M' := {
        Z := modal_equiv M M'

        atoms_match := by
          intro x y h_equiv p
          exact h_equiv (Formula.var p)

        -- proof by contradiction. suppose v and v' are not bisimilar.
        -- then there has to be a formula that v and v' do not agree
        -- to find this formula, use distinguishing_formula.
        -- use big_and to join them all
        forth := by
          intro x y h_equiv v hx_v
          by_contra h_no_match
          simp only [not_exists, not_and] at h_no_match

          -- if then, dite. classical, choose
          -- get_ψ receives a world and give back a distinguishing formula
          let get_ψ : W' → Formula V := fun v' =>
            if h : M'.frame.rel y v' then
              Classical.choose (dist_formula M M' v v' (h_no_match v' h))
            else
              Formula.bot

          have h_ψ : ∀ v', (h : M'.frame.rel y v') →
              ((M, v) ⊩ get_ψ v') ∧ ¬(M', v') ⊩ get_ψ v' := by
            intro v' h
            have h_eq : get_ψ v' = Classical.choose (dist_formula M M' v v' (h_no_match v' h)) := dite_eq_left h
            rw [h_eq]
            exact Classical.choose_spec (dist_formula M M' v v' (h_no_match v' h))

          -- for each succ of v, get its dist_formula and join them together
          let succ_list := (hFin' y).toFinset.toList
          let L := succ_list.map get_ψ
          let Ψ := big_and L

          have h_v_Ψ : (M, v) ⊩ Ψ := by
            rw [satisfies_big_and]
            intro φ h_in
            simp only [L, succ_list, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset] at h_in
            rcases h_in with ⟨v', h_rel, h_eq⟩
            rw [←h_eq]
            exact (h_ψ v' h_rel).left

          -- M, x ⊩ ◇Ψ
          have h_x_dia : (M, x) ⊩ ◇Ψ := ⟨v, hx_v, h_v_Ψ⟩

          -- M', y ⊩ ◇Ψ
          have h_y_dia : (M', y) ⊩ ◇Ψ := (h_equiv (◇Ψ)).mp h_x_dia

          rcases h_y_dia with ⟨v', hy_v', hv'_Ψ⟩

          have hv'_fails_its_ψ : ¬(M', v') ⊩ get_ψ v' := (h_ψ v' hy_v').right

          have hv'_satisfies_its_ψ : (M', v') ⊩ get_ψ v' := by
            rw [satisfies_big_and] at hv'_Ψ
            apply hv'_Ψ
            simp only [L, succ_list, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset]
            exact ⟨v', hy_v', rfl⟩

          exact hv'_fails_its_ψ hv'_satisfies_its_ψ

        back := by
          intro x y h_equiv v' hy_v'
          by_contra h_no_match
          simp only [not_exists, not_and] at h_no_match

          -- if then, dite. classical, choose
          -- get_ψ receives a world and give back a distinguishing formula
          -- 1. Create a function that picks a distinguishing formula by FLIPPING the arguments
          let get_ψ : W → Formula V := fun v =>
            if h : M.frame.rel x v then
              have h_no_match_symm : ¬modal_equiv M' M v' v := by
                intro h_eq
                apply h_no_match (v) (h)
                intro φ
                exact (h_eq φ).symm
              Classical.choose (dist_formula M' M v' v h_no_match_symm)
            else
              Formula.bot

          have h_ψ : ∀ v, (h : M.frame.rel x v) →
              ((M', v') ⊩ get_ψ v) ∧ ¬(M, v) ⊩ get_ψ v := by
            intro v h
            have h_no_match_symm : ¬modal_equiv M' M v' v := by
              intro h_eq
              apply h_no_match (v) (h)
              intro φ
              exact (h_eq φ).symm

            have h_eq : get_ψ v = Classical.choose (dist_formula M' M v' v h_no_match_symm) := dite_eq_left h
            rw [h_eq]
            exact Classical.choose_spec (dist_formula M' M v' v h_no_match_symm)

          let succ_list := (hFin x).toFinset.toList
          let L := succ_list.map get_ψ
          let Ψ := big_and L

          have h_v'_Ψ : (M', v') ⊩ Ψ := by
            rw [satisfies_big_and]
            intro φ h_in
            simp only [L, succ_list, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset] at h_in
            rcases h_in with ⟨v', h_rel, h_eq⟩
            rw [←h_eq]
            exact (h_ψ v' h_rel).left

          -- M, x ⊩ ◇Ψ
          have h_y_dia : (M', y) ⊩ ◇Ψ := ⟨v', hy_v', h_v'_Ψ⟩

          -- M', y ⊩ ◇Ψ
          have h_x_dia : (M, x) ⊩ ◇Ψ := (h_equiv (◇Ψ)).mpr h_y_dia

          rcases h_x_dia with ⟨v, hy_v', hv_Ψ⟩

          have hv_fails_its_ψ : ¬(M, v) ⊩ get_ψ v := (h_ψ v hy_v').right

          have hv_satisfies_its_ψ : (M, v) ⊩ get_ψ v := by
            rw [satisfies_big_and] at hv_Ψ
            apply hv_Ψ
            simp only [L, succ_list, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset]
            exact ⟨v, hy_v', rfl⟩

          exact hv_fails_its_ψ hv_satisfies_its_ψ
    }

    exact ⟨B_equiv, hEq⟩

end ML
