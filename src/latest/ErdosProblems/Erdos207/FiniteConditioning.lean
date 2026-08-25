/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributed

/-!
# Conditioning a finite law

KSSS condition on the high-probability event IG2--IG4 before proving their
master iteration lemma.  These lemmas give that reduction exactly and record
the precise reciprocal loss in every event probability.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Normalize a finite law on a positive-probability event. -/
def conditionOn (L : FiniteLaw Ω) (P : Ω → Prop)
    (hP : 0 < L.probability P) : FiniteLaw Ω := by
  classical
  refine {
    mass := fun ω ↦ if P ω then L.mass ω / L.probability P else 0
    sum_mass := ?_ }
  ·
    calc
      ∑ ω, (if P ω then L.mass ω / L.probability P else 0) =
          (∑ ω, if P ω then L.mass ω else 0) / L.probability P := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            apply sum_congr rfl
            intro ω _hω
            by_cases h : P ω <;> simp [h, div_eq_mul_inv]
      _ = L.probability P / L.probability P := rfl
      _ = 1 := div_self hP.ne'

/-- Conditional probability is the probability of the intersection divided
by the probability of the conditioning event. -/
theorem conditionOn_probability (L : FiniteLaw Ω) (P Q : Ω → Prop)
    (hP : 0 < L.probability P) :
    (L.conditionOn P hP).probability Q =
      L.probability (fun ω ↦ P ω ∧ Q ω) / L.probability P := by
  classical
  unfold probability
  simp only [conditionOn]
  calc
    ∑ ω, (if Q ω then
          (if P ω then L.mass ω / L.probability P else 0) else 0) =
        ∑ ω, (if P ω ∧ Q ω then
          L.mass ω / L.probability P else 0) := by
            apply sum_congr rfl
            intro ω _hω
            by_cases hPω : P ω <;> by_cases hQω : Q ω <;>
              simp [hPω, hQω]
    _ = (∑ ω, if P ω ∧ Q ω then L.mass ω else 0) /
          L.probability P := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            apply sum_congr rfl
            intro ω _hω
            by_cases h : P ω ∧ Q ω <;> simp [h, div_eq_mul_inv]
    _ = L.probability (fun ω ↦ P ω ∧ Q ω) /
          L.probability P := by
            unfold probability
            congr 1
            apply sum_congr rfl
            intro ω _hω
            by_cases h : P ω ∧ Q ω <;> simp [h]

/-- A conditioned law is supported on its conditioning event. -/
theorem conditionOn_supported (L : FiniteLaw Ω) (P : Ω → Prop)
    (hP : 0 < L.probability P) :
    (L.conditionOn P hP).SupportedOn P := by
  classical
  intro ω hω
  by_contra hnot
  simp [conditionOn, hnot] at hω

/-- Conditioning can inflate any event probability by at most the reciprocal
of the conditioning probability. -/
theorem conditionOn_probability_le (L : FiniteLaw Ω) (P Q : Ω → Prop)
    (hP : 0 < L.probability P) :
    (L.conditionOn P hP).probability Q ≤
      L.probability Q / L.probability P := by
  rw [L.conditionOn_probability P Q hP]
  gcongr
  exact L.probability_mono fun _ h ↦ h.2

/-- A predicate which held throughout the old support still holds after
conditioning. -/
theorem SupportedOn.conditionOn
    {L : FiniteLaw Ω} {P Q : Ω → Prop}
    (hQ : L.SupportedOn Q) (hP : 0 < L.probability P) :
    (L.conditionOn P hP).SupportedOn Q := by
  classical
  intro ω hω
  have hmass : 0 < L.mass ω := by
    by_contra hzero
    have : L.mass ω = 0 := le_antisymm (not_lt.mp hzero) zero_le
    have hmassEq : (L.conditionOn P hP).mass ω =
        if P ω then L.mass ω / L.probability P else 0 := by
      rfl
    rw [hmassEq] at hω
    simp [this] at hω
  exact hQ ω hmass

end FiniteLaw

/-- Conditioning strong well-distributedness on a positive event only
inflates its multiplicative constant by the reciprocal event probability.
The empty prescribed pattern is handled directly by probability at most
one; every nonempty pattern absorbs the reciprocal into the positive power
of the constant. -/
theorem IsStronglyWellDistributed.conditionOn
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0} (h : IsStronglyWellDistributed L W k initial later p C b)
    (P : Ω → Prop) (hP : 0 < L.probability P) :
    IsStronglyWellDistributed (L.conditionOn P hP) W k initial later
      p (C / L.probability P) b := by
  intro Ifix Dfix Efix hdisj
  let m := Ifix.card + Dfix.card + Efix.card
  let X := p ^ Efix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
    laterTriangleScale W k p Dfix + b
  by_cases hm : m = 0
  · have hI : Ifix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hD : Dfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hE : Efix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    subst Ifix
    subst Dfix
    subst Efix
    exact ((L.conditionOn P hP).probability_le_one
      (StrongDistributionEvent initial later ∅ ∅ ∅)).trans (by
        simp)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hzle : L.probability P ≤ 1 := L.probability_le_one P
    have hzpow : (L.probability P) ^ m ≤ L.probability P :=
      pow_le_of_le_one zero_le hzle hm
    have hscale : C ^ m / L.probability P ≤
        (C / L.probability P) ^ m := by
      rw [div_pow]
      gcongr
    have horiginal := h Ifix Dfix Efix hdisj
    calc
      (L.conditionOn P hP).probability
          (StrongDistributionEvent initial later Ifix Dfix Efix) ≤
        L.probability
            (StrongDistributionEvent initial later Ifix Dfix Efix) /
          L.probability P :=
        L.conditionOn_probability_le P
          (StrongDistributionEvent initial later Ifix Dfix Efix) hP
      _ ≤ (C ^ m * X) / L.probability P := by
        gcongr
      _ = (C ^ m / L.probability P) * X := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (C / L.probability P) ^ m * X := by
        gcongr
      _ = (C / L.probability P) ^
            (Ifix.card + Dfix.card + Efix.card) *
          (p ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b) := by
        rfl

end

end Erdos207
