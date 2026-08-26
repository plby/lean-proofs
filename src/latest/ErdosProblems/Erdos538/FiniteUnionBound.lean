import ErdosProblems.Erdos538.FiniteFieldCounts

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

open scoped BigOperators

/-- Functions whose value at one fixed coordinate lies in a prescribed set are
parametrized by that value and the function on the remaining coordinates. -/
noncomputable def evalEventEquiv
    {I L : Type*} [DecidableEq I] (B : Set L) (i : I) :
    {f : I → L // f i ∈ B} ≃ B × ({j : I // j ≠ i} → L) where
  toFun f := (⟨f.1 i, f.2⟩, fun j => f.1 j.1)
  invFun p := ⟨fun j => if h : j = i then p.1.1 else p.2 ⟨j, h⟩, by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · funext j
      simp [j.2]

/-- Removing one point from a finite type lowers its natural cardinality by
one. -/
theorem natCard_ne_point {I : Type*} [Finite I] [DecidableEq I] (i : I) :
    Nat.card {j : I // j ≠ i} = Nat.card I - 1 := by
  change Nat.card (Set.Elem {j : I | j ≠ i}) = Nat.card I - 1
  rw [Nat.card_coe_set_eq]
  have h := Set.ncard_diff_singleton_of_mem
    (s := (Set.univ : Set I)) (a := i) (Set.mem_univ i)
  have heq : (Set.univ : Set I) \ {i} = {j : I | j ≠ i} := by
    ext j
    simp
  rw [heq, Set.ncard_univ] at h
  exact h

/-- Exact cardinality of one coordinate event. -/
theorem natCard_evalEvent
    {I L : Type*} [Finite I] [DecidableEq I] [Finite L]
    (B : Set L) (i : I) :
    Nat.card {f : I → L // f i ∈ B} =
      Nat.card B * Nat.card L ^ (Nat.card I - 1) := by
  rw [Nat.card_congr (evalEventEquiv B i), Nat.card_prod, Nat.card_fun,
    natCard_ne_point]

/-- Finite union bound for coordinatewise bad labels. -/
theorem ncard_exists_bad_le
    {I L : Type*} [Fintype I] [DecidableEq I] [Finite L]
    (B : Set L) :
    {f : I → L | ∃ i, f i ∈ B}.ncard ≤
      Nat.card I * Nat.card B * Nat.card L ^ (Nat.card I - 1) := by
  let E : I → Set (I → L) := fun i => {f | f i ∈ B}
  have hU : {f : I → L | ∃ i, f i ∈ B} = ⋃ i, E i := by
    ext f
    simp [E]
  rw [hU]
  calc
    (⋃ i, E i).ncard ≤ ∑ i, (E i).ncard := Set.ncard_iUnion_le_of_fintype E
    _ = ∑ _i : I, (Nat.card B * Nat.card L ^ (Nat.card I - 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Nat.card_coe_set_eq]
      exact natCard_evalEvent B i
    _ = Nat.card I * Nat.card B * Nat.card L ^ (Nat.card I - 1) := by
      simp [Nat.card_eq_fintype_card, Nat.mul_assoc]

end Erdos538.IsotropicKernel
