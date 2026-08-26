/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonSourceIdentity
import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientFace
import ErdosProblems.Erdos4b.GeneralFourierWeightedTotientSquare

/-!
# One source cutoff for normalization and every pinned coordinate

The cutoff depends only on the profiles and logarithmic scales. Explicit
pinning amplitudes are retained; no inference from a weighted sum to a
nonzero unweighted sum is used.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators ContDiff

theorem selbergTensorFamilyCommonBound_capture_weighted_coefficient
    {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (d : (ι ⊕ ι) → ℕ) (hd : ∀ i, 0 < d i)
    (hne : (∑ j ∈ S, c j * selbergTensorCoefficient (F j) L d) ≠ 0) :
    ∀ i, d i ≤ selbergTensorFamilyCommonBound S F L := by
  obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ht := (mul_ne_zero_iff.mp hjne).2
  have hpair : doubledSelbergProfileTensor (pairedSelbergProfiles (F j) (F j))
      (fun i _ ↦ L i) (fun i _ ↦ d i) ≠ 0 := by
    rw [doubledSelbergProfileTensor_eq_coefficient_mul]
    exact mul_ne_zero ht ht
  have hcap := compactProfileTensorCommonBound_capture
    (pairedSelbergProfiles (F j) (F j))
    (hasCompactSupport_pairedSelbergProfiles (F j) (F j) (hF j hj) (hF j hj))
    (fun i _ ↦ L i) (fun i _ ↦ hL i) (fun i _ ↦ d i) (fun i _ ↦ hd i) hpair
  exact fun i ↦ (hcap i false).trans (compactProfileTensorCommonBound_le_family S F L hj hj)

theorem hasCompactSupport_pinnedSourceProfileFamily
    {K : ℕ} {J : Type*} (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (j : J) (hF : ∀ i, HasCompactSupport (F j i))
    (hG : HasCompactSupport G) :
    ∀ i, HasCompactSupport (pinnedSourceProfileFamily F G h j i) :=
  hasCompactSupport_twoFamilySelbergProfiles (fun i : PinnedShiftIndex h ↦ F j i.val) G
    (fun i ↦ hF i.val) hG

theorem contDiff_pinnedSourceProfileFamily
    {K : ℕ} {J : Type*} (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (j : J) (hF : ∀ i, ContDiff ℝ ∞ (F j i)) (hG : ContDiff ℝ ∞ G) :
    ∀ i, ContDiff ℝ ∞ (pinnedSourceProfileFamily F G h j i) :=
  contDiff_twoFamilySelbergProfiles (fun i : PinnedShiftIndex h ↦ F j i.val) G
    (fun i ↦ hF i.val) hG

def pinnedSourceCommonPrimeBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (LD LE : ℝ) : ℕ :=
  selbergTensorFamilyCommonBound S (pinnedSourceProfileFamily F G h)
    (twoFamilySelbergScales LD LE)

def jointSourceCommonPrimeBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ) : ℕ :=
  sourceAnalyticCommonPrimeBound S F G LD LE +
    ∑ h : Fin K, pinnedSourceCommonPrimeBound S F G h LD LE

theorem sourceAnalyticCommonPrimeBound_le_joint {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ) :
    sourceAnalyticCommonPrimeBound S F G LD LE ≤ jointSourceCommonPrimeBound S F G LD LE :=
  Nat.le_add_right _ _

theorem pinnedSourceCommonPrimeBound_le_joint {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (LD LE : ℝ) :
    pinnedSourceCommonPrimeBound S F G h LD LE ≤ jointSourceCommonPrimeBound S F G LD LE := by
  apply (Finset.single_le_sum (f := fun h ↦ pinnedSourceCommonPrimeBound S F G h LD LE)
    (fun i hi ↦ Nat.zero_le _) (Finset.mem_univ h)).trans
  exact Nat.le_add_left _ _

theorem pinnedSourceSelbergCoefficient_capture
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (hLD : 0 < LD) (hLE : 0 < LE)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i)) (hG : HasCompactSupport G)
    (d e : PinnedShiftIndex h → ℕ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hne : pinnedSourceSelbergCoefficient S F G h LD LE d e ≠ 0) :
    (∀ i, d i ≤ jointSourceCommonPrimeBound S F G LD LE) ∧
      (∀ i, e i ≤ jointSourceCommonPrimeBound S F G LD LE) := by
  have hscale : ∀ i : PinnedShiftIndex h ⊕ PinnedShiftIndex h,
      0 < twoFamilySelbergScales LD LE i := by
    intro i
    cases i
    · exact hLD
    · exact hLE
  have hpos : ∀ i : PinnedShiftIndex h ⊕ PinnedShiftIndex h, 0 < Sum.elim d e i := by
    intro i
    cases i
    · exact hd _
    · exact he _
  have hc := selbergTensorFamilyCommonBound_capture_weighted_coefficient
    S (pinnedSourceProfileAmplitude F G h) (pinnedSourceProfileFamily F G h)
    (fun j hj ↦ hasCompactSupport_pinnedSourceProfileFamily F G h j (hF j hj) hG)
    (twoFamilySelbergScales LD LE) hscale (Sum.elim d e) hpos hne
  exact ⟨fun i ↦ (hc (Sum.inl i)).trans (pinnedSourceCommonPrimeBound_le_joint S F G h LD LE),
    fun i ↦ (hc (Sum.inr i)).trans (pinnedSourceCommonPrimeBound_le_joint S F G h LD LE)⟩

end

end Erdos4b
