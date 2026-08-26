/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceNormalizationIdentity

/-!
# Literal source residue probabilities

These are the original doubled Selberg square weights with a common
finite divisor cutoff. Their denominator is exactly the physical sum
whose uniform asymptotic has already been proved.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourceResidueRawWeight {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) (a : Fin q) : ℝ :=
  largeGapResidueRawWeight (preSievedShifts K w)
    (cutoffDivisorTupleSupport (preSievedShifts K w) P)
    (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
    (sourceAnalyticSelbergCoefficient S
      (fun j i ↦ F j ((preSievedShiftEquiv K w).symm i)) G LD LE) U w m q a

def sourceResidueNormalization {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) : ℝ :=
  sourceAnalyticPreSievedWeightSum (preSievedShifts K w) P S
    (fun j i ↦ F j ((preSievedShiftEquiv K w).symm i)) G LD LE w m q (U / m)

def sourceResidueMass {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) (a : Fin q) : ℝ :=
  normalizeFiniteWeight (sourceResidueRawWeight S F G P LD LE U w m q) a

theorem sourceResidueRawWeight_nonneg {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) (a : Fin q) :
    0 ≤ sourceResidueRawWeight S F G P LD LE U w m q a :=
  largeGapResidueRawWeight_nonneg _ _ _ _ U w m q a

theorem sum_sourceResidueRawWeight {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m : ℕ) :
    (∑ a : Fin q, sourceResidueRawWeight S F G P LD LE U w m q a) =
      sourceResidueNormalization S F G P LD LE U w m q :=
  sum_largeGapResidueRawWeight hq _ _ _ _ U w m

theorem sourceResidueNormalization_nonneg {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) :
    0 ≤ sourceResidueNormalization S F G P LD LE U w m q := by
  classical
  unfold sourceResidueNormalization sourceAnalyticPreSievedWeightSum
  exact Finset.sum_nonneg fun n _ ↦ by
    split_ifs
    · exact doubledSelbergWeight_nonneg _ _ _ _ m q n
    · exact le_rfl

theorem sourceResidueMass_eq_div {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m : ℕ) (a : Fin q) :
    sourceResidueMass S F G P LD LE U w m q a =
      sourceResidueRawWeight S F G P LD LE U w m q a /
        sourceResidueNormalization S F G P LD LE U w m q := by
  unfold sourceResidueMass normalizeFiniteWeight
  rw [sum_sourceResidueRawWeight hq]

theorem sourceResidueMass_nonneg {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m q : ℕ) (a : Fin q) :
    0 ≤ sourceResidueMass S F G P LD LE U w m q a :=
  normalizeFiniteWeight_nonneg _ (sourceResidueRawWeight_nonneg S F G P LD LE U w m q) a

theorem sum_sourceResidueMass_eq_one {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m : ℕ)
    (hpos : 0 < sourceResidueNormalization S F G P LD LE U w m q) :
    ∑ a : Fin q, sourceResidueMass S F G P LD LE U w m q a = 1 := by
  apply sum_normalizeFiniteWeight_eq_one
  rwa [sum_sourceResidueRawWeight hq]

/-- A raw lower bound can be divided by any upper bound for the positive
actual normalization. -/
theorem sourceResidueMass_lower_of_raw_lower {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m : ℕ) (a : Fin q) {c B : ℝ}
    (hc : 0 ≤ c) (hraw : c ≤ sourceResidueRawWeight S F G P LD LE U w m q a)
    (hpos : 0 < sourceResidueNormalization S F G P LD LE U w m q)
    (hupper : sourceResidueNormalization S F G P LD LE U w m q ≤ B) :
    c / B ≤ sourceResidueMass S F G P LD LE U w m q a := by
  rw [sourceResidueMass_eq_div hq]
  exact (div_le_div_of_nonneg_left hc hpos hupper).trans
    (div_le_div_of_nonneg_right hraw hpos.le)

/-- A normalized value within half a positive main term gives a positive
denominator and a convenient factor-two upper bound. -/
theorem normalization_pos_and_upper_of_abs_sub_lt
    {Z scale denominator main : ℝ} (hscale : 0 < scale) (hden : 0 < denominator)
    (hmain : 0 < main) (hclose : |scale * Z / denominator - main| < main / 2) :
    0 < Z ∧ Z ≤ 2 * main * denominator / scale := by
  have hlo : 0 < scale * Z / denominator := by
    have := (abs_lt.mp hclose).1
    linarith
  have hprod : 0 < scale * Z := (div_pos_iff_of_pos_right hden).mp hlo
  have hZ : 0 < Z := (mul_pos_iff_of_pos_left hscale).mp hprod
  refine ⟨hZ, (le_div_iff₀ hscale).mpr ?_⟩
  have hup : scale * Z / denominator ≤ 2 * main := by
    have := (abs_lt.mp hclose).2
    linarith
  have hmul := (div_le_iff₀ hden).mp hup
  nlinarith

end

end Erdos4b
