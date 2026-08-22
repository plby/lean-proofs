/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllSixExactCoordinateProductClosure

/-!
# A finite-product union bound over coordinate windows

The source-balance screen is the event that at least one represented domino
has an exceptional insertion total.  This file proves the corresponding
union bound directly for the normalized heterogeneous finite product law.
No path-space probability estimate is an input.
-/

open scoped BigOperators

namespace Erdos1165.HLOZFiniteProductCoordinateUnion

open FiniteDominoProductLaw

noncomputable section

/-- A normalized joint mass is nonnegative when every raw point mass is
nonnegative. -/
lemma normalizedJointMass_nonneg_of_pointMass_nonneg
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (ell : TruncatedTotals upper) :
    0 ≤ normalizedJointMass pointMass upper ell := by
  unfold normalizedJointMass jointMass
  exact div_nonneg
    (Finset.prod_nonneg fun b _ ↦ hpoint b (ell b))
    (Finset.sum_nonneg fun z _ ↦
      Finset.prod_nonneg fun b _ ↦ hpoint b (z b))

/-- The mass of a finite union of coordinate events is at most the sum of
their individual screen masses. -/
theorem screenMass_exists_coordinate_le_sum_single
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (hpoint : ∀ b v, 0 ≤ pointMass b v) :
    screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) ≤
      ∑ b, screenMass pointMass upper (fun ell ↦ bad b (ell b)) := by
  classical
  unfold screenMass
  calc
    (∑ ell : TruncatedTotals upper,
        if ∃ b, bad b (ell b) then
          normalizedJointMass pointMass upper ell else 0) ≤
      ∑ ell : TruncatedTotals upper, ∑ b,
        if bad b (ell b) then
          normalizedJointMass pointMass upper ell else 0 := by
        apply Finset.sum_le_sum
        intro ell _
        by_cases hbad : ∃ b, bad b (ell b)
        · rw [if_pos hbad]
          obtain ⟨b, hb⟩ := hbad
          have hsingle := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun c ↦ if bad c (ell c) then
              normalizedJointMass pointMass upper ell else 0)
            (fun c _ ↦ by
              split
              · exact normalizedJointMass_nonneg_of_pointMass_nonneg
                  pointMass upper hpoint ell
              · exact le_rfl)
            (Finset.mem_univ b)
          simpa only [if_pos hb] using hsingle
        · rw [if_neg hbad]
          exact Finset.sum_nonneg fun b _ ↦ by
            split
            · exact normalizedJointMass_nonneg_of_pointMass_nonneg
                pointMass upper hpoint ell
            · exact le_rfl
    _ = ∑ b, ∑ ell : TruncatedTotals upper,
        if bad b (ell b) then
          normalizedJointMass pointMass upper ell else 0 :=
      Finset.sum_comm

/-- If every normalized coordinate has total mass one, a screen depending
on one coordinate has exactly that coordinate's accepted mass. -/
theorem screenMass_single_coordinate_eq
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1)
    (chosen : Domino) :
    screenMass pointMass upper (fun ell ↦ bad chosen (ell chosen)) =
      ∑ v : Fin (upper chosen),
        if bad chosen v then coordinateMass pointMass upper chosen v else 0 := by
  classical
  rw [screenMass_eq_product]
  let weight := fun (b : Domino) (v : Fin (upper b)) ↦
    if bad b v then coordinateMass pointMass upper b v else 0
  calc
    (∑ ell : TruncatedTotals upper,
        if bad chosen (ell chosen) then
          ∏ b, coordinateMass pointMass upper b (ell b) else 0) =
      ∑ ell : TruncatedTotals upper,
        ∏ b, if b = chosen then weight b (ell b)
          else coordinateMass pointMass upper b (ell b) := by
        apply Finset.sum_congr rfl
        intro ell _
        by_cases hbad : bad chosen (ell chosen)
        · rw [if_pos hbad]
          apply Finset.prod_congr rfl
          intro b _
          by_cases hb : b = chosen
          · subst b
            simp [weight, hbad]
          · simp only [if_neg hb]
        · rw [if_neg hbad]
          symm
          apply Finset.prod_eq_zero (Finset.mem_univ chosen)
          simp [weight, hbad]
    _ = ∏ b, ∑ v : Fin (upper b),
        if b = chosen then weight b v
          else coordinateMass pointMass upper b v :=
      (Fintype.prod_sum fun b (v : Fin (upper b)) ↦
        if b = chosen then weight b v
          else coordinateMass pointMass upper b v).symm
    _ = ∑ v : Fin (upper chosen),
        if bad chosen v then coordinateMass pointMass upper chosen v else 0 := by
      rw [Finset.prod_eq_single chosen]
      · simp [weight]
      · intro b _ hb
        simp only [if_neg hb, hsum b]
      · simp

/-- Literal coordinate union bound for a normalized finite product.  This is
the form used by the oriented source-balance acceptor. -/
theorem screenMass_exists_coordinate_le
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1) :
    screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) ≤
      ∑ b, ∑ v : Fin (upper b),
        if bad b v then coordinateMass pointMass upper b v else 0 := by
  calc
    screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) ≤
        ∑ b, screenMass pointMass upper (fun ell ↦ bad b (ell b)) :=
      screenMass_exists_coordinate_le_sum_single pointMass upper bad hpoint
    _ = ∑ b, ∑ v : Fin (upper b),
          if bad b v then coordinateMass pointMass upper b v else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      exact screenMass_single_coordinate_eq pointMass upper bad hsum b

/-- A literal raw one-coordinate estimate survives finite truncation with
only a factor two once the retained part of that coordinate law has mass at
least one half.  This is the normalization step used by the all-creation
Theta screen; the hypotheses concern the explicit point masses, not a
path-space probability. -/
theorem sum_bad_coordinateMass_le_two_mul
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (cost : Domino → ℝ)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hden : ∀ b, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper b), pointMass b v)
    (hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b)
    (b : Domino) :
    (∑ v : Fin (upper b),
      if bad b v then coordinateMass pointMass upper b v else 0) ≤
        2 * cost b := by
  classical
  let den : ℝ := ∑ v : Fin (upper b), pointMass b v
  have hden_pos : 0 < den := by
    dsimp only [den]
    linarith [hden b]
  have hbad_nonneg : 0 ≤ ∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0 := by
    exact Finset.sum_nonneg fun v _ ↦ by
      split_ifs
      · exact hpoint b v
      · exact le_rfl
  calc
    (∑ v : Fin (upper b),
        if bad b v then coordinateMass pointMass upper b v else 0) =
        (∑ v : Fin (upper b),
          if bad b v then pointMass b v else 0) / den := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      rw [coordinateMass, if_pos v.isLt]
      by_cases hv : bad b v <;> simp [hv, den]
    _ ≤ cost b / den :=
      div_le_div_of_nonneg_right (hbad b) hden_pos.le
    _ ≤ 2 * cost b := by
      have hcost : 0 ≤ cost b := hbad_nonneg.trans (hbad b)
      rw [div_le_iff₀ hden_pos]
      nlinarith [hden b]

/-- Finite-product union bound stated entirely in terms of literal raw point
masses.  The normalization loss is explicit and uniform. -/
theorem screenMass_exists_coordinate_le_two_mul_sum
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (cost : Domino → ℝ)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1)
    (hden : ∀ b, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper b), pointMass b v)
    (hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b) :
    screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) ≤
      2 * ∑ b, cost b := by
  calc
    screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) ≤
        ∑ b, ∑ v : Fin (upper b),
          if bad b v then coordinateMass pointMass upper b v else 0 :=
      screenMass_exists_coordinate_le pointMass upper bad hpoint hsum
    _ ≤ ∑ b, 2 * cost b := by
      gcongr with b
      exact sum_bad_coordinateMass_le_two_mul pointMass upper bad cost
        hpoint hden hbad b
    _ = 2 * ∑ b, cost b := by rw [Finset.mul_sum]

/-- Boolean front-end for the literal coordinate union bound.  This is the
form consumed by stopped-coordinate packages, whose finite acceptors are
stored as computable Boolean functions. -/
theorem screenMass_bool_iff_exists_coordinate_le_two_mul_sum
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (bad : ∀ b, Fin (upper b) → Prop)
    [∀ b, DecidablePred (bad b)]
    (accepts : TruncatedTotals upper → Bool)
    (haccepts : ∀ ell, accepts ell = true ↔ ∃ b, bad b (ell b))
    (cost : Domino → ℝ)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsum : ∀ b, (∑ v : Fin (upper b),
      coordinateMass pointMass upper b v) = 1)
    (hden : ∀ b, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper b), pointMass b v)
    (hbad : ∀ b, (∑ v : Fin (upper b),
      if bad b v then pointMass b v else 0) ≤ cost b) :
    screenMass pointMass upper (fun ell ↦ accepts ell = true) ≤
      2 * ∑ b, cost b := by
  have heq : screenMass pointMass upper (fun ell ↦ accepts ell = true) =
      screenMass pointMass upper (fun ell ↦ ∃ b, bad b (ell b)) := by
    unfold screenMass
    apply Finset.sum_congr rfl
    intro ell _
    rw [if_congr (haccepts ell) rfl rfl]
  rw [heq]
  exact screenMass_exists_coordinate_le_two_mul_sum pointMass upper bad cost
    hpoint hsum hden hbad

end

end Erdos1165.HLOZFiniteProductCoordinateUnion
