/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientCoefficientSquare

/-!
# Explicit amplitudes in the totient tensor-square kernel

Pinning produces a fixed scalar amplitude for each profile. Bilinearity
retains both amplitudes in every cross term, at one graph-independent
coordinate cutoff. This includes an empty reduced coordinate type.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem cutoffTotientSelbergBilinearSum_const_mul
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) (c d : ℂ) :
    cutoffTotientSelbergBilinearSum P edges companion (fun v ↦ c * a v) (fun v ↦ d * b v) =
      (c * d) * cutoffTotientSelbergBilinearSum P edges companion a b := by
  classical
  unfold cutoffTotientSelbergBilinearSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : DoubledDivisorPrimeCompatible P edges companion v
  · simp only [if_pos hc]
    ring
  · simp only [if_neg hc, mul_zero]

theorem cutoffTotientSelbergBilinearSum_weighted_tensors
    {ι J : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffTotientSelbergBilinearSum P edges companion
        (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v)
        (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v) =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * cutoffTotientSelbergProfileTensorSum P edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [cutoffTotientSelbergBilinearSum_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [cutoffTotientSelbergBilinearSum_const_mul, cutoffTotientSelbergBilinearSum_tensors]

def compactWeightedTotientSelbergTensorSquareSum {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) : ℂ :=
  cutoffTotientSelbergBilinearSum
    (selectedFourierPrimeCutoff select
      (boundedFourierPrimes (selbergTensorFamilyCommonBound S F L))) edges companion
    (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v)
    (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v)

theorem compactWeightedTotientSelbergTensorSquareSum_eq_pair_sum
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) :
    compactWeightedTotientSelbergTensorSquareSum select edges companion S c F L =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * compactTotientSelbergProfileSum select edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [compactWeightedTotientSelbergTensorSquareSum,
    cutoffTotientSelbergBilinearSum_weighted_tensors]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [compactTotientSelbergProfileSum_eq_cutoff_of_le select edges companion _
    (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk))
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
    (compactProfileTensorCommonBound_le_family S F L hj hk)]

def weightedSelbergTensorSquareMainConstant {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ) : ℂ :=
  ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * ∏ i,
    ∫ t : ℝ in Set.Ioi 0, deriv (F j i) t * deriv (F k i) t

theorem compactWeightedTotientSelbergTensorSquareSum_eq_cutoff_of_common_le
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    {B : ℕ} (hB : selbergTensorFamilyCommonBound S F L ≤ B) :
    compactWeightedTotientSelbergTensorSquareSum select edges companion S c F L =
      cutoffTotientSelbergBilinearSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v)
          (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v) := by
  rw [compactWeightedTotientSelbergTensorSquareSum_eq_pair_sum select edges companion S c F hF L hL,
    cutoffTotientSelbergBilinearSum_weighted_tensors]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [compactTotientSelbergProfileSum_eq_cutoff_of_le select edges companion _
    (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk))
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
    ((compactProfileTensorCommonBound_le_family S F L hj hk).trans hB)]

theorem tendsto_compactWeightedTotientSelbergTensorSquareSum_normalized
    {α ι J : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (Real.sqrt (V a)) (σ a))
    (hcoherent : ∀ᶠ a in l, ∀ p : Nat.Primes, ∀ ij ∈ edges a p, companion a p = true)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ᶠ a in l, Real.log (M a) ≤ B * V a)
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
      compactWeightedTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (edges a) (companion a) S c F (L a)) l
      (𝓝 (weightedSelbergTensorSquareMainConstant S c F)) := by
  have hpair (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :=
    (tendsto_compactTotientSelbergProfileSum_normalized
      M w edges companion L σ V hdata hcoherent hw hV hσ hlog hcutoff hB hsize hupper
      (pairedSelbergProfiles (F j) (F k))
      (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hcompact j hj) (hcompact k hk))
      (contDiff_pairedSelbergProfiles (F j) (F k) (hsmooth j hj) (hsmooth k hk))).const_mul
        (c j * c k)
  have hlim := tendsto_finsetSum S fun j hj ↦ tendsto_finsetSum S fun k hk ↦ hpair j hj k hk
  change Tendsto _ l (𝓝 (weightedSelbergTensorSquareMainConstant S c F)) at hlim
  apply hlim.congr'
  filter_upwards [hdata] with a ha
  rw [compactWeightedTotientSelbergTensorSquareSum_eq_pair_sum _ _ _ S c F hcompact (L a)
    ha.scale_pos]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

end Erdos4b
