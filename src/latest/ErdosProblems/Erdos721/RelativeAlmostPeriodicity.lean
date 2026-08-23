/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.BoostedAlmostPeriodicity
import ErdosProblems.Erdos721.Regularity

/-!
# Relative cyclic almost-periodicity

This file supplies the local small-sumset input needed to run the checked
Croot--Sisask--Chang smoothing package inside a regular cyclic Bohr set.
-/

namespace Erdos721

open Finset
open scoped Pointwise Combinatorics.Additive BigOperators ENNReal Indicator mu NNReal

namespace CyclicRelativeAlmostPeriodicity

variable {N : ℕ} [NeZero N]

open CyclicBohr
open CyclicBoostedAlmostPeriodicity

/-- If `A` lies in an inner Bohr dilate, then adding the perturbation dilate
keeps it inside the corresponding outer dilate. -/
lemma add_inner_subset_outer (B : CyclicBohr.Set N) (A : Finset (ZMod N))
    {t δ : ℝ} (hδ : 0 ≤ δ) (hδt : δ ≤ t)
    (hA : A ⊆ (B.dilate (t - δ)).carrier) :
    A + (B.dilate δ).carrier ⊆ (B.dilate t).carrier := by
  rw [Finset.add_subset_iff]
  intro x hx y hy
  have hinner : 0 ≤ t - δ := sub_nonneg.mpr hδt
  have hsum := CyclicBohr.Set.add_mem_dilate hinner hδ (hA hx) hy
  change x + y ∈ B.dilate t
  simpa only [sub_add_cancel] using hsum

/-- A dense subset of the inner member of a controlled Bohr triple has the
addition constant required by Croot--Sisask. -/
theorem addConst_inner_le (B : CyclicBohr.Set N) (A : Finset (ZMod N))
    {t δ α : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ) (hδt : δ ≤ t)
    (hA : A ⊆ (B.dilate (t - δ)).carrier)
    (hdense : α * (B.dilate (t - δ)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card) :
    (A.addConst (B.dilate δ).carrier : ℝ) ≤ 11 / (10 * α) := by
  have hsum :
      A + (B.dilate δ).carrier ⊆ (B.dilate (t + δ)).carrier := by
    exact (add_inner_subset_outer B A hδ hδt hA).trans
      (CyclicBohr.Set.dilate_mono B (hδ.trans hδt) (le_add_of_nonneg_right hδ))
  have hcard := Finset.card_le_card hsum
  rw [Finset.cast_addConst]
  have hApos : (0 : ℝ) < A.card := by
    have hinnerpos : (0 : ℝ) < (B.dilate (t - δ)).carrier.card := by
      exact_mod_cast CyclicBohr.Set.card_pos (B.dilate (t - δ))
    have : 0 < α * (B.dilate (t - δ)).carrier.card := mul_pos hα hinnerpos
    exact this.trans_le hdense
  rw [div_le_iff₀ hApos]
  have hcardR :
      ((A + (B.dilate δ).carrier).card : ℝ) ≤
        (B.dilate (t + δ)).carrier.card := by exact_mod_cast hcard
  have hregularR :
      (10 : ℝ) * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card := by exact_mod_cast hregular
  have hden : 0 < 10 * α := mul_pos (by norm_num) hα
  calc
    ((A + (B.dilate δ).carrier).card : ℝ) ≤
        11 * A.card / (10 * α) := by
      rw [le_div_iff₀ hden]
      nlinarith
    _ = 11 / (10 * α) * A.card := by ring

/-- Reflected-translate form of the controlled addition-constant estimate.
If `A ⊆ x - B_{t-δ}`, then `-A + B_δ` is contained in a translate of
`B_{t+δ}` and hence has the same quantitative bound. -/
theorem addConst_neg_reflectedTranslate_inner_le
    (B : CyclicBohr.Set N) (A : Finset (ZMod N)) (x : ZMod N)
    {t δ α : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ) (hδt : δ ≤ t)
    (hA : A ⊆ x +ᵥ -(B.dilate (t - δ)).carrier)
    (hdense : α * (B.dilate (t - δ)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card) :
    ((-A).addConst (B.dilate δ).carrier : ℝ) ≤
      11 / (10 * α) := by
  have hsum :
      (-A) + (B.dilate δ).carrier ⊆
        (-x) +ᵥ (B.dilate (t + δ)).carrier := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [Finset.mem_neg] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have haRef := hA ha₀
    rw [Finset.mem_vadd_finset] at haRef
    obtain ⟨c, hc, hac⟩ := haRef
    rw [Finset.mem_neg] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rw [Finset.mem_vadd_finset]
    refine ⟨d + b, ?_, ?_⟩
    · have hinner : 0 ≤ t - δ := sub_nonneg.mpr hδt
      have hadd := CyclicBohr.Set.add_mem_dilate hinner hδ hd hb
      exact (CyclicBohr.Set.dilate_mono B
        (add_nonneg hinner hδ) (by linarith)) hadd
    · rw [vadd_eq_add] at hac ⊢
      rw [← hac]
      abel
  have hcard := Finset.card_le_card hsum
  rw [Finset.card_vadd_finset] at hcard
  rw [Finset.cast_addConst]
  have hApos : (0 : ℝ) < A.card := by
    have hinnerpos : (0 : ℝ) <
        (B.dilate (t - δ)).carrier.card := by
      exact_mod_cast CyclicBohr.Set.card_pos (B.dilate (t - δ))
    exact (mul_pos hα hinnerpos).trans_le hdense
  have hnegcard : (-A).card = A.card := Finset.card_neg A
  rw [hnegcard, div_le_iff₀ hApos]
  have hcardR :
      (((-A) + (B.dilate δ).carrier).card : ℝ) ≤
        (B.dilate (t + δ)).carrier.card := by exact_mod_cast hcard
  have hregularR :
      (10 : ℝ) * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card := by
    exact_mod_cast hregular
  have hden : 0 < 10 * α := mul_pos (by norm_num) hα
  calc
    (((-A) + (B.dilate δ).carrier).card : ℝ) ≤
        11 * A.card / (10 * α) := by
      rw [le_div_iff₀ hden]
      nlinarith
    _ = 11 / (10 * α) * A.card := by ring

/-- The explicit Croot--Sisask--Chang smoothing package, localized to the
inner member of a controlled Bohr triple. -/
theorem exists_local_bohr_smoothing
    (B : CyclicBohr.Set N) (A P Q : Finset (ZMod N))
    {t δ α epsilon eta rho : ℝ} (k : ℕ)
    (hα0 : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hδ : 0 ≤ δ) (hδt : δ ≤ t)
    (hAinner : A ⊆ (B.dilate (t - δ)).carrier)
    (hAdense : α * (B.dilate (t - δ)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * α)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate δ).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate δ).carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  have hK2 : 2 ≤ 11 / (10 * α) := by
    have hden : 0 < 10 * α := mul_pos (by norm_num) hα0
    rw [le_div_iff₀ hden]
    nlinarith
  simpa only [CyclicBohr.Set.rank_dilate] using
    (CyclicBoostedAlmostPeriodicity.exists_large_set_and_refined_bohr_smoothing_explicit
      (B.dilate δ) A (B.dilate δ).carrier P Q k
      hepsilon0 hepsilon1 hk hK2
      (addConst_inner_le B A hα0 hδ hδt hAinner hAdense hregular)
      hA (CyclicBohr.Set.carrier_nonempty _) hP hQ heta hrho)

/-- Adaptive-radius version of local smoothing.  The spectral radius may
depend on the Croot--Sisask shift set, and the exact radius and inherited
rank of the refined Bohr set are retained. -/
theorem exists_local_bohr_smoothing_adaptive
    (B : CyclicBohr.Set N) (A P Q : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  simpa only [CyclicBohr.Set.rank_dilate] using
    (CyclicBoostedAlmostPeriodicity.exists_large_set_and_refined_bohr_smoothing_explicit_adaptive
        (B.dilate delta) A (B.dilate delta).carrier P Q rho k
        hepsilon0 hepsilon1 hk hK2
        (addConst_inner_le B A halpha0 hdelta hdeltat hAinner hAdense hregular)
        hA (CyclicBohr.Set.carrier_nonempty _) hP hQ heta hrho)

/-- Adaptive local smoothing whose averaging carrier has already been put on
a fine regular scale.  The output `C_t` is therefore ready to carry the next
normalized slice in the density-increment iteration. -/
theorem exists_local_regular_bohr_smoothing_adaptive
    (B : CyclicBohr.Set N) (A P Q : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k m : ℕ)
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank) (hm : 0 < m)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 < delta) (hdeltat : delta ≤ t)
    (hAinner : A ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N) (u zeta : ℝ),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      0 < C.radius ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      1 / 2 ≤ u ∧ u ≤ 1 ∧
      zeta = (400 * (m : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < zeta ∧ zeta < u ∧
      (10 * m) * (C.dilate (u + zeta)).carrier.card ≤
        (10 * m + 1) * (C.dilate (u - zeta)).carrier.card ∧
      (C.dilate u).carrier ⊆ (B.dilate delta).carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight
              (C.dilate u).carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  have hK2 : 2 ≤ 11 / (10 * alpha) := by
    have hden : 0 < 10 * alpha := mul_pos (by norm_num) halpha0
    rw [le_div_iff₀ hden]
    nlinarith
  have hRradius : 0 < (B.dilate delta).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hdelta]
    positivity
  have hRrank : 0 < (B.dilate delta).rank := by simpa using hBrank
  simpa only [CyclicBohr.Set.rank_dilate] using
    (CyclicBoostedAlmostPeriodicity.exists_large_set_and_regular_refined_bohr_smoothing_explicit_adaptive
        (B.dilate delta) A (B.dilate delta).carrier P Q rho k m
        hRradius hRrank hm hepsilon0 hepsilon1 hk hK2
        (addConst_inner_le B A halpha0 hdelta.le hdeltat hAinner hAdense hregular)
        hA (CyclicBohr.Set.carrier_nonempty _) hP hQ heta hrho)

end CyclicRelativeAlmostPeriodicity
end Erdos721
