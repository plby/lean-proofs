/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedModulusFibers
import ErdosProblems.Erdos4b.GeneralFourierPinnedProductSupport

/-!
# Weighted prime distribution for the active pinned source support

Zero coefficients are removed before the modulus range is bounded.
The cutoff itself may be arbitrarily large. Only the source's product
support determines the moduli entering the prime-level estimate.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

open Classical in
def activePinnedSourceDivisorTuples {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (LD LE : ℝ) : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) :=
  (rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P).filter fun d ↦
    pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true) ≠ 0

def pinnedSourceEndpointErrorBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (x : ℕ) (LD LE : ℝ) : ℝ :=
  ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
    ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)‖ *
      BoundedGaps.Maynard.maxProgressionDiscrepancy x (pinnedFlatDivisorModulus h d)

theorem pinnedSourceProgressionErrorBound_eq_endpoints
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (A B : ℕ) (LD LE : ℝ) :
    pinnedSourceProgressionErrorBound S F G h P A B LD LE =
      pinnedSourceEndpointErrorBound S F G h P (B - 1) LD LE +
        pinnedSourceEndpointErrorBound S F G h P (A - 1) LD LE := by
  simp only [pinnedSourceProgressionErrorBound, pinnedSourceEndpointErrorBound,
    mul_add, Finset.sum_add_distrib]

theorem pinnedSourceEndpointErrorBound_eq_active_sum
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (x : ℕ) (LD LE : ℝ) :
    pinnedSourceEndpointErrorBound S F G h P x LD LE =
      ∑ d ∈ activePinnedSourceDivisorTuples S F G h P LD LE,
        ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
          pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)‖ *
          BoundedGaps.Maynard.maxProgressionDiscrepancy x (pinnedFlatDivisorModulus h d) := by
  classical
  unfold pinnedSourceEndpointErrorBound activePinnedSourceDivisorTuples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hn
  · rfl
  · rw [not_ne_iff] at hn
    simp only [hn, norm_zero, zero_mul]

theorem activePinnedSourceModuli_subset_product_range
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {LD LE A : ℝ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) :
    (activePinnedSourceDivisorTuples S F G h P LD LE).image (pinnedFlatDivisorModulus h) ⊆
      Finset.Icc 1 ((⌈Real.exp (A * LD)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2) := by
  classical
  intro M hM
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hM
  obtain ⟨hraw, hne⟩ := Finset.mem_filter.mp hd
  have hpos := (pinnedFlatDivisorModulus_squarefree h P hP d
    ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hraw)).ne_zero.bot_lt
  exact Finset.mem_Icc.mpr ⟨hpos, pinnedFlatDivisorModulus_le_source_product_radii S F G h
    hLD hLE hFsupport hGsupport d hne⟩

theorem primeLevelWitness_pinnedSourceEndpointErrorBound_le
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {LD LE A C₀ θ exponent C : ℝ} {X₀ x : ℕ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hC₀ : 0 ≤ C₀)
    (hcoef : ∀ v, ‖pinnedSourceFlatCoefficient S F G h LD LE v‖ ≤ C₀)
    (hw : BoundedGaps.Maynard.PrimeLevelWitness θ exponent C X₀) (hx : X₀ ≤ x)
    (hRx : (⌈Real.exp (A * LD)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2 ≤ x + 1)
    (hcut : (⌈Real.exp (A * LD)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2 ≤
      BoundedGaps.Maynard.modulusCutoff θ x) :
    pinnedSourceEndpointErrorBound S F G h P x LD LE ≤
      C₀ ^ 2 * pinnedFlatTauDiscrepancyBound K C exponent x
        ((⌈Real.exp (A * LD)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2) := by
  classical
  rw [pinnedSourceEndpointErrorBound_eq_active_sum]
  have hSQ := activePinnedSourceModuli_subset_product_range S F G h P hP hLD hLE
    hFsupport hGsupport
  apply primeLevelWitness_pinnedFlatWeightedDiscrepancy_le h P hP
    (activePinnedSourceDivisorTuples S F G h P LD LE) (Finset.filter_subset _ _) _
    (sq_nonneg C₀) _ hw hx hSQ hRx
  · intro M hM
    obtain ⟨hM1, hMR⟩ := Finset.mem_Icc.mp (hSQ hM)
    exact Finset.mem_Icc.mpr ⟨hM1, hMR.trans hcut⟩
  · intro d hd
    rw [norm_mul, pow_two]
    exact mul_le_mul (hcoef _) (hcoef _) (norm_nonneg _) hC₀

end

end Erdos4b
