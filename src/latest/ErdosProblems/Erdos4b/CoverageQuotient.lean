/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.VariableFiber

/-!
# Erdős Problem 4: normalization-to-coverage quotients

This file isolates the order-theoretic step converting upper bounds for the
exact Selberg normalization into lower bounds for the normalized residue mass.
The statements are finite and do not hide an analytic hypothesis.
-/

open Filter Real Asymptotics
open scoped BigOperators Asymptotics

namespace Erdos4b

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A nonnegative numerator divided by an upper bound for a positive
denominator is no larger than the corresponding exact quotient. -/
theorem div_normalization_upper_le {x M B : ℝ}
    (hx : 0 ≤ x) (hM : 0 < M) (hMB : M ≤ B) :
    x / B ≤ x / M := by
  have hB : 0 < B := hM.trans_le hMB
  exact (div_le_div_iff₀ hB hM).2 (by nlinarith)

/-- Unfold the normalized scaled residue mass using its exact normalization
denominator. -/
theorem scaledTrivialResidueMass_eq_raw_div_mass
    (K : ℕ) (A alpha : ℝ) (m N q : ℕ) (a : Fin q) (hq : 0 < q) :
    scaledTrivialResidueMass K A alpha m N q a =
      scaledTrivialResidueRawWeight K A alpha m N q a /
        scaledTrivialCompanionNormalizationMass K A alpha
          (fun _ => m) (fun _ => q) N := by
  unfold scaledTrivialResidueMass normalizeFiniteWeight
  rw [sum_scaledTrivialResidueRawWeight_eq_mass K A alpha
    (fun _ => m) (fun _ => q) N hq]

/-- One pinned target receives at least its retained raw shifted weight divided
by any common upper bound for the exact normalization. -/
theorem shiftedPointWeights_div_normalizationUpper_le_residueMass
    {K m N q p : ℕ} {A alpha B : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hpN : p ≤ N)
    (hpre : largeGapPreSieved
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m p)
    (hmargin : ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) < p)
    (hmass : 0 < scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N)
    (hmassB : scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N ≤ B) :
    (∑ h : ↑(primorialShifts K),
        scaledTrivialPointWeight K A alpha m N q
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) / B ≤
      scaledTrivialResidueMass K A alpha m N q
        ⟨p % q, Nat.mod_lt p hq⟩ := by
  let raw := scaledTrivialResidueRawWeight K A alpha m N q
    ⟨p % q, Nat.mod_lt p hq⟩
  let numerator := ∑ h : ↑(primorialShifts K),
    scaledTrivialPointWeight K A alpha m N q
      (p - h.1 *
        (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))
  have hnum : 0 ≤ numerator := Finset.sum_nonneg fun h _ =>
    scaledTrivialPointWeight_nonneg K A alpha m N q _
  have hnumraw : numerator ≤ raw := by
    simpa [numerator, raw] using
      (sum_shift_pointWeights_le_residueRawWeight
        (K := K) (A := A) (alpha := alpha) hm hq hpN hpre hmargin)
  have hB : 0 < B := hmass.trans_le hmassB
  calc
    numerator / B ≤ raw / B := div_le_div_of_nonneg_right hnumraw hB.le
    _ ≤ raw /
        scaledTrivialCompanionNormalizationMass K A alpha
          (fun _ => m) (fun _ => q) N :=
      div_normalization_upper_le
        (scaledTrivialResidueRawWeight_nonneg K A alpha m N q _) hmass hmassB
    _ = scaledTrivialResidueMass K A alpha m N q
        ⟨p % q, Nat.mod_lt p hq⟩ := by
      symm
      exact scaledTrivialResidueMass_eq_raw_div_mass K A alpha m N q _ hq

/-- Sum the preceding pointwise quotient bound over a finite family of
auxiliary moduli. -/
theorem sum_shiftedPointWeights_div_normalizationUpper_le_residueMass
    {K m N p : ℕ} {A alpha B : ℝ} (Q : Finset ℕ)
    (hm : 0 < m) (hpN : p ≤ N)
    (hpre : largeGapPreSieved
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m p)
    (hq : ∀ q ∈ Q, 0 < q)
    (hmargin : ∀ q ∈ Q, ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) < p)
    (hmass : ∀ q ∈ Q, 0 < scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N)
    (hmassB : ∀ q ∈ Q, scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N ≤ B) :
    (∑ q : ↥Q, ∑ h : ↑(primorialShifts K),
        scaledTrivialPointWeight K A alpha m N q.1
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q.1))) / B ≤
      ∑ q : ↥Q, scaledTrivialResidueMass K A alpha m N q.1
        ⟨p % q.1, Nat.mod_lt p (hq q.1 q.2)⟩ := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro q hqQ
  exact shiftedPointWeights_div_normalizationUpper_le_residueMass
    hm (hq q.1 q.2) hpN hpre (hmargin q.1 q.2)
      (hmass q.1 q.2) (hmassB q.1 q.2)

end Erdos4b
