/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCoefficientSquare
import ErdosProblems.Erdos4b.GeneralFourierCanonicalAsymptotic

/-!
# Affine asymptotics for the square of a finite tensor combination

Every profile cross term uses one common finite divisor cutoff. This
cutoff depends only on the fixed profile family and its scales, so it
does not introduce an auxiliary-prime dependence into the coefficient.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem hasCompactSupport_pairedSelbergProfiles {ι : Type*}
    (F G : (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ i, HasCompactSupport (F i)) (hG : ∀ i, HasCompactSupport (G i)) :
    ∀ ib, HasCompactSupport (pairedSelbergProfiles F G ib) := by
  rintro ⟨i, b⟩
  cases b
  · exact hF i
  · exact hG i

theorem contDiff_pairedSelbergProfiles {ι : Type*}
    (F G : (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hG : ∀ i, ContDiff ℝ ∞ (G i)) :
    ∀ ib, ContDiff ℝ ∞ (pairedSelbergProfiles F G ib) := by
  rintro ⟨i, b⟩
  cases b
  · exact hF i
  · exact hG i

def selbergTensorFamilyPrimeBound {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) : ℕ :=
  ∑ j ∈ S, ∑ k ∈ S, compactSelbergPrimeBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i)

theorem compactSelbergPrimeBound_le_family {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ)
    {j k : J} (hj : j ∈ S) (hk : k ∈ S) :
    compactSelbergPrimeBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) ≤
      selbergTensorFamilyPrimeBound S F L := by
  apply (Finset.single_le_sum
    (f := fun k ↦ compactSelbergPrimeBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i))
    (fun k hk ↦ Nat.zero_le _) hk).trans
  exact Finset.single_le_sum
    (f := fun j ↦ ∑ k ∈ S,
      compactSelbergPrimeBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i))
    (fun j hj ↦ Nat.zero_le _) hj

def compactSelbergTensorSquareSum {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) : ℂ :=
  cutoffSelbergBilinearSum
    (selectedFourierPrimeCutoff select (boundedFourierPrimes (selbergTensorFamilyPrimeBound S F L)))
    edges companion
    (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
    (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)

theorem compactSelbergTensorSquareSum_eq_pair_sum
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) :
    compactSelbergTensorSquareSum select edges companion S F L =
      ∑ j ∈ S, ∑ k ∈ S, compactSelbergProfileSum select edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [compactSelbergTensorSquareSum, cutoffSelbergBilinearSum_tensor_sum_square]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact (compactSelbergProfileSum_eq_cutoff_of_le select edges companion
    (pairedSelbergProfiles (F j) (F k))
    (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk))
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
    (compactSelbergPrimeBound_le_family S F L hj hk)).symm

def selbergTensorSquareMainConstant {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) : ℂ :=
  ∑ j ∈ S, ∑ k ∈ S, ∏ i,
    ∫ t : ℝ in Set.Ioi 0, deriv (F j i) t * deriv (F k i) t

theorem tendsto_compactAffineTensorSquareSum_actual_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (w m q : α → ℕ) (V : α → ℝ) (L : α → (Fin K ⊕ Fin K) → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hq : ∀ᶠ a in l, (q a).Prime)
    (hwq : ∀ᶠ a in l, w a < q a)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hqV : ∀ᶠ a in l, Real.log (q a) ≤ V a)
    (hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i)
    (hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (S : Finset J) (F : J → (Fin K ⊕ Fin K) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    Tendsto (fun a ↦ actualAffineFourierNormalization K (w a) (m a) (q a) (L a) *
      compactSelbergTensorSquareSum (fun p ↦ decide (w a < p))
        (indexedPreSievedFourierEdges K (w a) (m a) (q a))
        (affineFourierCompanionSwitch (m a)) S F (L a)) l
      (𝓝 (selbergTensorSquareMainConstant S F)) := by
  have hpair (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :=
    tendsto_compactAffineProfileSum_actual_normalized
      K w m q V L hw hV hm hq hwq hcutoff hmV hqV hLlower hLupper
      (pairedSelbergProfiles (F j) (F k))
      (hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hcompact j hj) (hcompact k hk))
      (contDiff_pairedSelbergProfiles (F j) (F k) (hsmooth j hj) (hsmooth k hk))
  have hlim := tendsto_finsetSum S fun j hj ↦ tendsto_finsetSum S fun k hk ↦ hpair j hj k hk
  change Tendsto _ l (𝓝 (selbergTensorSquareMainConstant S F)) at hlim
  apply hlim.congr'
  filter_upwards [hLlower, hV.eventually_ge_atTop 1] with a hLa hVa
  rw [compactSelbergTensorSquareSum_eq_pair_sum _ _ _ S F hcompact (L a)
    (fun i ↦ fourierScale_pos_of_threeQuarter_bound hVa (hLa i))]
  simp only [Finset.mul_sum]

end

end Erdos4b
