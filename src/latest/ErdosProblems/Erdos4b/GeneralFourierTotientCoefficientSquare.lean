/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonFamilyCutoff
import ErdosProblems.Erdos4b.GeneralFourierTotientProfileAsymptotic

/-!
# Totient kernel for the square of a finite tensor combination

All cross terms are retained. A single coordinate-capturing cutoff
works for every pair of profiles, independently of the varying graph.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance totientSquareDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

def cutoffTotientSelbergBilinearSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d then
      a (fun i ↦ d i false) * b (fun i ↦ d i true) /
        (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
          (fun ib ↦ d ib.1 ib.2)) : ℂ)
    else 0

theorem cutoffTotientSelbergBilinearSum_tensors
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F G : (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffTotientSelbergBilinearSum P edges companion
        (selbergTensorCoefficient F L) (selbergTensorCoefficient G L) =
      cutoffTotientSelbergProfileTensorSum P edges companion
        (pairedSelbergProfiles F G) (fun i _ ↦ L i) := by
  unfold cutoffTotientSelbergBilinearSum cutoffTotientSelbergProfileTensorSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [doubledSelbergProfileTensor_eq_coefficient_mul]

theorem cutoffTotientSelbergBilinearSum_sum
    {ι J J' : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (T : Finset J')
    (a : J → ((ι ⊕ ι) → ℕ) → ℂ) (b : J' → ((ι ⊕ ι) → ℕ) → ℂ) :
    cutoffTotientSelbergBilinearSum P edges companion
        (fun d ↦ ∑ j ∈ S, a j d) (fun d ↦ ∑ j ∈ T, b j d) =
      ∑ j ∈ S, ∑ k ∈ T, cutoffTotientSelbergBilinearSum P edges companion (a j) (b k) := by
  unfold cutoffTotientSelbergBilinearSum
  have hpoint (d : (ι ⊕ ι) → Bool → ℕ) :
      (if DoubledDivisorPrimeCompatible P edges companion d then
        (∑ j ∈ S, a j (fun i ↦ d i false)) * (∑ k ∈ T, b k (fun i ↦ d i true)) /
          (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
            (fun ib ↦ d ib.1 ib.2)) : ℂ)
      else 0) =
      ∑ j ∈ S, ∑ k ∈ T,
        if DoubledDivisorPrimeCompatible P edges companion d then
          a j (fun i ↦ d i false) * b k (fun i ↦ d i true) /
            (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
              (fun ib ↦ d ib.1 ib.2)) : ℂ)
        else 0 := by
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
    · simp only [if_pos hc, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_comm
    · simp only [if_neg hc, Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

theorem cutoffTotientSelbergBilinearSum_tensor_sum_square
    {ι J : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffTotientSelbergBilinearSum P edges companion
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) =
      ∑ j ∈ S, ∑ k ∈ S, cutoffTotientSelbergProfileTensorSum P edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [cutoffTotientSelbergBilinearSum_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact cutoffTotientSelbergBilinearSum_tensors P edges companion (F j) (F k) L

def compactTotientSelbergTensorSquareSum {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) : ℂ :=
  cutoffTotientSelbergBilinearSum
    (selectedFourierPrimeCutoff select
      (boundedFourierPrimes (selbergTensorFamilyCommonBound S F L)))
    edges companion
    (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
    (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)

theorem compactTotientSelbergTensorSquareSum_eq_pair_sum
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) :
    compactTotientSelbergTensorSquareSum select edges companion S F L =
      ∑ j ∈ S, ∑ k ∈ S, compactTotientSelbergProfileSum select edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [compactTotientSelbergTensorSquareSum, cutoffTotientSelbergBilinearSum_tensor_sum_square]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact (compactTotientSelbergProfileSum_eq_cutoff_of_le select edges companion
    (pairedSelbergProfiles (F j) (F k))
    (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk))
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
    (compactProfileTensorCommonBound_le_family S F L hj hk)).symm

theorem compactTotientSelbergTensorSquareSum_eq_cutoff_of_common_le
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    {B : ℕ} (hB : selbergTensorFamilyCommonBound S F L ≤ B) :
    compactTotientSelbergTensorSquareSum select edges companion S F L =
      cutoffTotientSelbergBilinearSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
          (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) := by
  rw [compactTotientSelbergTensorSquareSum_eq_pair_sum select edges companion S F hF L hL,
    cutoffTotientSelbergBilinearSum_tensor_sum_square]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact compactTotientSelbergProfileSum_eq_cutoff_of_le select edges companion _
    (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk))
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
    ((compactProfileTensorCommonBound_le_family S F L hj hk).trans hB)

theorem tendsto_compactTotientSelbergTensorSquareSum_normalized
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
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
      compactTotientSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (edges a) (companion a) S F (L a)) l (𝓝 (selbergTensorSquareMainConstant S F)) := by
  have hpair (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :=
    tendsto_compactTotientSelbergProfileSum_normalized
      M w edges companion L σ V hdata hcoherent hw hV hσ hlog hcutoff hB hsize hupper
      (pairedSelbergProfiles (F j) (F k))
      (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hcompact j hj) (hcompact k hk))
      (contDiff_pairedSelbergProfiles (F j) (F k) (hsmooth j hj) (hsmooth k hk))
  have hlim := tendsto_finsetSum S fun j hj ↦ tendsto_finsetSum S fun k hk ↦ hpair j hj k hk
  change Tendsto _ l (𝓝 (selbergTensorSquareMainConstant S F)) at hlim
  apply hlim.congr'
  filter_upwards [hdata] with a ha
  rw [compactTotientSelbergTensorSquareSum_eq_pair_sum _ _ _ S F hcompact (L a) ha.scale_pos]
  simp only [Finset.mul_sum]

end

end Erdos4b
