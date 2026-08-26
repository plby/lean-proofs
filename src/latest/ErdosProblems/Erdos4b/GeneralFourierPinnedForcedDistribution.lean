/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedRange

/-!
# Aggregate endpoint discrepancy for all forced primes through the companion cutoff

Only nonzero coefficient pairs enter the modulus range. Grouping the
forced prime together with the four reduced divisor tuples gives a
single weighted prime-level estimate, with no dependence on the size
of the arbitrarily enlarged Fourier cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def activePinnedForcedSourceTuples {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (Y : ℕ) (LD LE : ℝ) :
    Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)) :=
  (Nat.primesLE Y) ×ˢ activePinnedSourceDivisorTuples S F G h P LD LE

def pinnedSourceForcedEndpointErrorBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (Y x : ℕ) (LD LE : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y, ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
    ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)‖ *
      BoundedGaps.Maynard.maxProgressionDiscrepancy x (pinnedForcedDivisorModulus h (p, d))

theorem pinnedSourceForcedEndpointErrorBound_eq_active_sum
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (Y x : ℕ) (LD LE : ℝ) :
    pinnedSourceForcedEndpointErrorBound S F G h P Y x LD LE =
      ∑ v ∈ activePinnedForcedSourceTuples S F G h P Y LD LE,
        ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ v.2 i false) *
          pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ v.2 i true)‖ *
          BoundedGaps.Maynard.maxProgressionDiscrepancy x (pinnedForcedDivisorModulus h v) := by
  classical
  unfold pinnedSourceForcedEndpointErrorBound activePinnedForcedSourceTuples
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  unfold activePinnedSourceDivisorTuples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hn
  · rfl
  · rw [not_ne_iff] at hn
    simp only [hn, norm_zero, zero_mul]

theorem activePinnedForcedSourceTuples_data
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (Y : ℕ) (LD LE : ℝ) :
    ∀ v ∈ activePinnedForcedSourceTuples S F G h P Y LD LE,
      v.1.Prime ∧ v.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P := by
  intro v hv
  obtain ⟨hp, hd⟩ := Finset.mem_product.mp hv
  exact ⟨(Nat.mem_primesLE.mp hp).2, (Finset.mem_filter.mp hd).1⟩

theorem activePinnedForcedSourceModuli_subset_range
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {V : ℝ} {Y : ℕ} (hV : 0 < V) (hY : 1 < Y)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) :
    (activePinnedForcedSourceTuples S F G h P Y V (Real.log Y)).image
      (pinnedForcedDivisorModulus h) ⊆ Finset.Icc 1 (pinnedSourceForcedProductRadius K V Y) := by
  classical
  intro M hM
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hM
  obtain ⟨hp, hd⟩ := Finset.mem_product.mp hv
  obtain ⟨hraw, hne⟩ := Finset.mem_filter.mp hd
  have hp' := Nat.mem_primesLE.mp hp
  exact Finset.mem_Icc.mpr
    ⟨(pinnedForcedDivisorModulus_squarefree h P hP v hp'.2 hraw).ne_zero.bot_lt,
      pinnedForcedDivisorModulus_le_source_radius S F G h P hP hV hY hp'.2 hp'.1
        hFsupport hGsupport v.2 hraw hne⟩

theorem primeLevelWitness_pinnedSourceForcedEndpointErrorBound_le
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {V C₀ exponent C : ℝ} {Y X₀ x : ℕ} (hV : 160 ≤ V) (hY : 1 < Y)
    (hsmall : (K : ℝ) * Real.log Y ≤ V / 40) (hxpos : 0 < x)
    (hlog : 3 * V / 4 ≤ Real.log x)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hC₀ : 0 ≤ C₀)
    (hcoef : ∀ v, ‖pinnedSourceFlatCoefficient S F G h V (Real.log Y) v‖ ≤ C₀)
    (hw : BoundedGaps.Maynard.PrimeLevelWitness (2 / 5) exponent C X₀) (hx : X₀ ≤ x) :
    pinnedSourceForcedEndpointErrorBound S F G h P Y x V (Real.log Y) ≤
      C₀ ^ 2 * pinnedFlatTauDiscrepancyBound (K + 1) C exponent x
        (pinnedSourceForcedProductRadius K V Y) := by
  classical
  rw [pinnedSourceForcedEndpointErrorBound_eq_active_sum]
  have hSQ := activePinnedForcedSourceModuli_subset_range S F G h P hP
    (by linarith : 0 < V) hY
    hFsupport hGsupport
  apply primeLevelWitness_pinnedForcedWeightedDiscrepancy_le h P hP
    (activePinnedForcedSourceTuples S F G h P Y V (Real.log Y))
    (activePinnedForcedSourceTuples_data S F G h P Y V (Real.log Y)) _
    (sq_nonneg C₀) _ hw hx hSQ
    ((pinnedSourceForcedProductRadius_le_endpoint h.pos hV (by omega) hsmall hxpos hlog).trans
      (Nat.le_succ x))
  · intro M hM
    obtain ⟨hM1, hMR⟩ := Finset.mem_Icc.mp (hSQ hM)
    exact Finset.mem_Icc.mpr ⟨hM1, hMR.trans
      (pinnedSourceForcedProductRadius_le_twoFifthsCutoff h.pos hV (by omega) hsmall hxpos hlog)⟩
  · intro v hv
    rw [norm_mul, pow_two]
    exact mul_le_mul (hcoef _) (hcoef _) (norm_nonneg _) hC₀

end

end Erdos4b
