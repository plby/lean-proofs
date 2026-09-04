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

import ErdosProblems.Erdos721.Regularity

/-!
# Translation stability from fixed-scale Bohr regularity

The nested inner, center, and outer dilates supplied by the fixed-scale
regularization lemma make the normalized center Bohr measure approximately
translation invariant under the small perturbation dilate.  This is the
elementary combinatorial core needed by the subsequent almost-periodicity
argument.
-/

namespace Erdos721

open Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

/-- Translation of a finite subset of the cyclic group. -/
def translateFinset (S : Finset (ZMod N)) (z : ZMod N) : Finset (ZMod N) :=
  S.map (Equiv.addRight z).toEmbedding

@[simp] lemma card_translateFinset (S : Finset (ZMod N)) (z : ZMod N) :
    (translateFinset S z).card = S.card := by
  simp [translateFinset]

lemma mem_translateFinset {S : Finset (ZMod N)} {z y : ZMod N} :
    y ∈ translateFinset S z ↔ y - z ∈ S := by
  constructor
  · intro hy
    rw [translateFinset, Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  · intro hy
    rw [translateFinset, Finset.mem_map]
    refine ⟨y - z, hy, ?_⟩
    change (y - z) + z = y
    abel

/-- Cardinality of the symmetric difference with a translate. -/
def translationDiscrepancy (S : Finset (ZMod N)) (z : ZMod N) : ℕ :=
  (S \ translateFinset S z).card + (translateFinset S z \ S).card

/-- The symmetric-difference finset underlying `translationDiscrepancy`. -/
def translationSymmDiff (S : Finset (ZMod N)) (z : ZMod N) : Finset (ZMod N) :=
  (S \ translateFinset S z) ∪ (translateFinset S z \ S)

lemma card_translationSymmDiff (S : Finset (ZMod N)) (z : ZMod N) :
    (translationSymmDiff S z).card = translationDiscrepancy S z := by
  unfold translationSymmDiff translationDiscrepancy
  rw [Finset.card_union_of_disjoint]
  exact disjoint_sdiff_sdiff

/-- Density-one normalization of the indicator of a nonempty finite set. -/
noncomputable def uniformWeight (S : Finset (ZMod N)) (x : ZMod N) : ℝ :=
  if x ∈ S then (N : ℝ) / S.card else 0

lemma average_uniformWeight {S : Finset (ZMod N)} (hS : S.Nonempty) :
    (𝔼 x : ZMod N, uniformWeight S x) = 1 := by
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : ∑ x : ZMod N, uniformWeight S x =
      S.card * ((N : ℝ) / S.card) := by
    unfold uniformWeight
    rw [← Finset.sum_filter]
    simp
  rw [hsum, ZMod.card]
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  field_simp

/-- Exact normalized `L¹` translation discrepancy of a uniform finite-set
weight. -/
lemma expect_abs_uniformWeight_sub_translate
    {S : Finset (ZMod N)} (hS : S.Nonempty) (z : ZMod N) :
    (𝔼 x : ZMod N, |uniformWeight S (x - z) - uniformWeight S x|) =
      (translationDiscrepancy S z : ℝ) / S.card := by
  let D := translationSymmDiff S z
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hpoint (x : ZMod N) :
      |uniformWeight S (x - z) - uniformWeight S x| =
        if x ∈ D then (N : ℝ) / S.card else 0 := by
    have htrans : x ∈ translateFinset S z ↔ x - z ∈ S := mem_translateFinset
    have hmass : 0 ≤ (N : ℝ) / S.card := div_nonneg hN.le hcard.le
    by_cases hx : x ∈ S
    · by_cases hxt : x ∈ translateFinset S z
      · have hxz : x - z ∈ S := htrans.mp hxt
        simp [uniformWeight, D, translationSymmDiff, hx, hxt, hxz]
      · have hxz : x - z ∉ S := fun hxz ↦ hxt (htrans.mpr hxz)
        simp [uniformWeight, D, translationSymmDiff, hx, hxt, hxz,
          abs_of_nonpos (neg_nonpos.mpr hmass)]
    · by_cases hxt : x ∈ translateFinset S z
      · have hxz : x - z ∈ S := htrans.mp hxt
        simp [uniformWeight, D, translationSymmDiff, hx, hxt, hxz,
          abs_of_nonneg hmass]
      · have hxz : x - z ∉ S := fun hxz ↦ hxt (htrans.mpr hxz)
        simp [uniformWeight, D, translationSymmDiff, hx, hxt, hxz]
  rw [Fintype.expect_eq_sum_div_card]
  calc
    (∑ x : ZMod N, |uniformWeight S (x - z) - uniformWeight S x|) /
        Fintype.card (ZMod N) =
        (∑ x : ZMod N, if x ∈ D then (N : ℝ) / S.card else 0) / N := by
      simp only [hpoint, ZMod.card]
    _ = (D.card : ℝ) * ((N : ℝ) / S.card) / N := by
      rw [← Finset.sum_filter]
      simp
    _ = (translationDiscrepancy S z : ℝ) / S.card := by
      rw [card_translationSymmDiff]
      field_simp

/-- A controlled inner/outer cardinality ratio gives quantitative
translation stability of the center Bohr set. -/
theorem five_mul_translationDiscrepancy_le_card
    (B : Set N) {t δ : ℝ} (hδ : 0 ≤ δ) (hinner : 0 ≤ t - δ)
    (hregular :
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card)
    {z : ZMod N} (hz : z ∈ B.dilate δ) :
    5 * translationDiscrepancy (B.dilate t).carrier z ≤
      (B.dilate t).carrier.card := by
  let I := (B.dilate (t - δ)).carrier
  let C := (B.dilate t).carrier
  let O := (B.dilate (t + δ)).carrier
  let Iz := translateFinset I z
  let Cz := translateFinset C z
  have ht : 0 ≤ t := by linarith
  have hIC : I ⊆ C := by
    dsimp only [I, C]
    exact Set.dilate_mono B hinner (by linarith)
  have hCO : C ⊆ O := by
    dsimp only [C, O]
    exact Set.dilate_mono B ht (by linarith)
  have hIzC : Iz ⊆ C := by
    intro y hy
    rw [mem_translateFinset] at hy
    have hsum := Set.add_mem_dilate hinner hδ hy hz
    change y ∈ B.dilate t
    simpa only [sub_add_cancel] using hsum
  have hCzO : Cz ⊆ O := by
    intro y hy
    rw [mem_translateFinset] at hy
    have hsum := Set.add_mem_dilate ht hδ hy hz
    change y ∈ B.dilate (t + δ)
    simpa only [sub_add_cancel] using hsum
  have hIzCz : Iz ⊆ Cz := by
    intro y hy
    rw [mem_translateFinset] at hy ⊢
    exact hIC hy
  have hleft : C \ Cz ⊆ O \ Iz := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hCO hy.1, fun hyIz ↦ hy.2 (hIzCz hyIz)⟩
  have hright : Cz \ C ⊆ O \ Iz := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hCzO hy.1, fun hyIz ↦ hy.2 (hIzC hyIz)⟩
  have hIzO : Iz ⊆ O := hIzC.trans hCO
  have hdiff : (O \ Iz).card = O.card - I.card := by
    rw [Finset.card_sdiff_of_subset hIzO, card_translateFinset]
  have hdisc : translationDiscrepancy C z ≤ 2 * (O.card - I.card) := by
    unfold translationDiscrepancy
    change (C \ Cz).card + (Cz \ C).card ≤ 2 * (O.card - I.card)
    rw [← hdiff]
    have hl := Finset.card_le_card hleft
    have hr := Finset.card_le_card hright
    omega
  have hIO : I ⊆ O := hIC.trans hCO
  have hgap : 10 * (O.card - I.card) ≤ I.card := by
    have hcardIO := Finset.card_le_card hIO
    dsimp only [I, O] at hregular ⊢
    omega
  have hIcardC : I.card ≤ C.card := Finset.card_le_card hIC
  calc
    5 * translationDiscrepancy (B.dilate t).carrier z =
        5 * translationDiscrepancy C z := by rfl
    _ ≤ 5 * (2 * (O.card - I.card)) := Nat.mul_le_mul_left 5 hdisc
    _ = 10 * (O.card - I.card) := by ring
    _ ≤ I.card := hgap
    _ ≤ (B.dilate t).carrier.card := hIcardC

/-- Fine version of the translation-discrepancy estimate. -/
theorem five_mul_m_translationDiscrepancy_le_card
    (B : Set N) (m : ℕ) {t δ : ℝ} (hm : 0 < m)
    (hδ : 0 ≤ δ) (hinner : 0 ≤ t - δ)
    (hregular :
      (10 * m) * (B.dilate (t + δ)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - δ)).carrier.card)
    {z : ZMod N} (hz : z ∈ B.dilate δ) :
    (5 * m) * translationDiscrepancy (B.dilate t).carrier z ≤
      (B.dilate t).carrier.card := by
  let I := (B.dilate (t - δ)).carrier
  let C := (B.dilate t).carrier
  let O := (B.dilate (t + δ)).carrier
  let Iz := translateFinset I z
  let Cz := translateFinset C z
  have ht : 0 ≤ t := by linarith
  have hIC : I ⊆ C := by
    dsimp only [I, C]
    exact Set.dilate_mono B hinner (by linarith)
  have hCO : C ⊆ O := by
    dsimp only [C, O]
    exact Set.dilate_mono B ht (by linarith)
  have hIzC : Iz ⊆ C := by
    intro y hy
    rw [mem_translateFinset] at hy
    have hsum := Set.add_mem_dilate hinner hδ hy hz
    change y ∈ B.dilate t
    simpa only [sub_add_cancel] using hsum
  have hCzO : Cz ⊆ O := by
    intro y hy
    rw [mem_translateFinset] at hy
    have hsum := Set.add_mem_dilate ht hδ hy hz
    change y ∈ B.dilate (t + δ)
    simpa only [sub_add_cancel] using hsum
  have hIzCz : Iz ⊆ Cz := by
    intro y hy
    rw [mem_translateFinset] at hy ⊢
    exact hIC hy
  have hleft : C \ Cz ⊆ O \ Iz := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hCO hy.1, fun hyIz ↦ hy.2 (hIzCz hyIz)⟩
  have hright : Cz \ C ⊆ O \ Iz := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hCzO hy.1, fun hyIz ↦ hy.2 (hIzC hyIz)⟩
  have hIzO : Iz ⊆ O := hIzC.trans hCO
  have hdiff : (O \ Iz).card = O.card - I.card := by
    rw [Finset.card_sdiff_of_subset hIzO, card_translateFinset]
  have hdisc : translationDiscrepancy C z ≤ 2 * (O.card - I.card) := by
    unfold translationDiscrepancy
    change (C \ Cz).card + (Cz \ C).card ≤ 2 * (O.card - I.card)
    rw [← hdiff]
    have hl := Finset.card_le_card hleft
    have hr := Finset.card_le_card hright
    omega
  have hIO : I ⊆ O := hIC.trans hCO
  have hgap : (10 * m) * (O.card - I.card) ≤ I.card := by
    have hcardIO := Finset.card_le_card hIO
    dsimp only [I, O] at hregular ⊢
    simp only [Nat.add_mul, one_mul, Nat.mul_sub_left_distrib] at hregular ⊢
    omega
  have hIcardC : I.card ≤ C.card := Finset.card_le_card hIC
  calc
    (5 * m) * translationDiscrepancy (B.dilate t).carrier z =
        (5 * m) * translationDiscrepancy C z := by rfl
    _ ≤ (5 * m) * (2 * (O.card - I.card)) :=
      Nat.mul_le_mul_left (5 * m) hdisc
    _ = (10 * m) * (O.card - I.card) := by ring
    _ ≤ I.card := hgap
    _ ≤ (B.dilate t).carrier.card := hIcardC

/-- Arbitrarily accurate translation stability obtained from the fine
regularity grid. -/
theorem exists_uniformWeight_translation_stable_dilate_fine
    (B : Set N) (m : ℕ) (hB : 0 < B.radius) (hrank : 0 < B.rank)
    (hm : 0 < m) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      δ = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹ ∧
      0 < δ ∧ δ < t ∧
      ∀ z ∈ B.dilate δ,
        (𝔼 x : ZMod N,
          |uniformWeight (B.dilate t).carrier (x - z) -
            uniformWeight (B.dilate t).carrier x|) ≤ 1 / (5 * m) := by
  obtain ⟨t, δ, htlow, hthigh, hδformula, hδ, hδt, hregular⟩ :=
    exists_fixed_regular_scale_fine B m hB hrank hm
  refine ⟨t, δ, htlow, hthigh, hδformula, hδ, hδt, ?_⟩
  intro z hz
  rw [expect_abs_uniformWeight_sub_translate (Set.carrier_nonempty _) z]
  have hdisc := five_mul_m_translationDiscrepancy_le_card B m hm hδ.le
    (sub_nonneg.mpr hδt.le) hregular hz
  have hcard : (0 : ℝ) < (B.dilate t).carrier.card := by
    exact_mod_cast Set.card_pos _
  have hdiscReal :
      ((5 * m : ℕ) : ℝ) * translationDiscrepancy (B.dilate t).carrier z ≤
        (B.dilate t).carrier.card := by exact_mod_cast hdisc
  have hmR : (0 : ℝ) < 5 * m := by positivity
  rw [div_le_iff₀ hcard]
  field_simp
  norm_num [Nat.cast_mul] at hdiscReal ⊢
  nlinarith

/-- Every positive-rank positive-radius Bohr set has a comparable dilate whose
uniform measure is stable under all translations from one smaller dilate. -/
theorem exists_translation_stable_dilate
    (B : Set N) (hB : 0 < B.radius) (hrank : 0 < B.rank) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧ 0 < δ ∧ δ < t ∧
      ∀ z ∈ B.dilate δ,
        5 * translationDiscrepancy (B.dilate t).carrier z ≤
          (B.dilate t).carrier.card := by
  obtain ⟨t, δ, htlow, hthigh, hδ, hδt, hregular⟩ :=
    exists_fixed_regular_scale B hB hrank
  refine ⟨t, δ, htlow, hthigh, hδ, hδt, ?_⟩
  intro z hz
  exact five_mul_translationDiscrepancy_le_card B hδ.le (sub_nonneg.mpr hδt.le)
    hregular hz

/-- Analytic form of the fixed-scale translation stability estimate. -/
theorem exists_uniformWeight_translation_stable_dilate
    (B : Set N) (hB : 0 < B.radius) (hrank : 0 < B.rank) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧ 0 < δ ∧ δ < t ∧
      ∀ z ∈ B.dilate δ,
        (𝔼 x : ZMod N,
          |uniformWeight (B.dilate t).carrier (x - z) -
            uniformWeight (B.dilate t).carrier x|) ≤ 1 / 5 := by
  obtain ⟨t, δ, htlow, hthigh, hδ, hδt, hstable⟩ :=
    exists_translation_stable_dilate B hB hrank
  refine ⟨t, δ, htlow, hthigh, hδ, hδt, ?_⟩
  intro z hz
  rw [expect_abs_uniformWeight_sub_translate (Set.carrier_nonempty _) z]
  have hdisc := hstable z hz
  have hcard : (0 : ℝ) < (B.dilate t).carrier.card := by
    exact_mod_cast Set.card_pos _
  have hdiscReal :
      (5 : ℝ) * translationDiscrepancy (B.dilate t).carrier z ≤
        (B.dilate t).carrier.card := by
    exact_mod_cast hdisc
  calc
    (translationDiscrepancy (B.dilate t).carrier z : ℝ) /
        (B.dilate t).carrier.card ≤ 1 / 5 := by
      rw [div_le_iff₀ hcard]
      nlinarith

/-! ## Translation stability of smoothed averages -/

/-- Real normalized cyclic convolution.  This is the real-valued companion
of `CyclicFourier.convolution`, convenient for density increments. -/
noncomputable def realConvolution
    (f g : ZMod N → ℝ) (x : ZMod N) : ℝ :=
  𝔼 y : ZMod N, f y * g (x - y)

/-- A normalized real average is invariant under the involution
`y ↦ x - y`. -/
lemma expect_sub_left (f : ZMod N → ℝ) (x : ZMod N) :
    (𝔼 y : ZMod N, f (x - y)) = 𝔼 y : ZMod N, f y := by
  simp only [Fintype.expect_eq_sum_div_card]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ fun _ ↦ rfl

/-- Convolution by a bounded function is Lipschitz in the normalized
`L¹` distance between the two translates of the smoothing kernel. -/
lemma abs_realConvolution_sub_le
    (f μ : ZMod N → ℝ) (M ε : ℝ)
    (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    {x z : ZMod N}
    (hμ : (𝔼 u : ZMod N, |μ (u - (-z)) - μ u|) ≤ ε) :
    |realConvolution f μ (x + z) - realConvolution f μ x| ≤ M * ε := by
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by
    rw [ZMod.card]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hrewrite (y : ZMod N) :
      f y * μ (x + z - y) - f y * μ (x - y) =
        f y * (μ ((x - y) - (-z)) - μ (x - y)) := by
    rw [show x + z - y = (x - y) - (-z) by abel]
    ring
  have hkernel :
      (𝔼 y : ZMod N, |μ (x + z - y) - μ (x - y)|) ≤ ε := by
    calc
      (𝔼 y : ZMod N, |μ (x + z - y) - μ (x - y)|) =
          𝔼 y : ZMod N, |μ ((x - y) - (-z)) - μ (x - y)| := by
            congr 1
            funext y
            congr 2 <;> abel_nf
      _ = 𝔼 u : ZMod N, |μ (u - (-z)) - μ u| :=
        expect_sub_left (fun u ↦ |μ (u - (-z)) - μ u|) x
      _ ≤ ε := hμ
  unfold realConvolution
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  calc
    |(∑ y : ZMod N, (f y * μ (x + z - y) - f y * μ (x - y))) /
        Fintype.card (ZMod N)| =
        |∑ y : ZMod N, (f y * μ (x + z - y) - f y * μ (x - y))| /
          Fintype.card (ZMod N) := by
            rw [abs_div, abs_of_pos hN]
    _ ≤ (∑ y : ZMod N,
          |f y * μ (x + z - y) - f y * μ (x - y)|) /
          Fintype.card (ZMod N) := by
            gcongr
            exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ y : ZMod N, M * |μ (x + z - y) - μ (x - y)|) /
          Fintype.card (ZMod N) := by
            gcongr with y
            rw [hrewrite, abs_mul]
            rw [show x + z - y = (x - y) - (-z) by abel]
            exact mul_le_mul (hf y) le_rfl (abs_nonneg _) hM
    _ = M * (𝔼 y : ZMod N, |μ (x + z - y) - μ (x - y)|) := by
          simp only [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
          ring
    _ ≤ M * ε := mul_le_mul_of_nonneg_left hkernel hM

/-- At the regular scale, every `[0,1]`-valued function has a Bohr-smoothed
average which changes by at most `1/5` on the smaller Bohr dilate. -/
theorem exists_realConvolution_uniformWeight_translation_stable_dilate
    (B : Set N) (hB : 0 < B.radius) (hrank : 0 < B.rank)
    (f : ZMod N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧ 0 < δ ∧ δ < t ∧
      ∀ x, ∀ z ∈ B.dilate δ,
        |realConvolution f (uniformWeight (B.dilate t).carrier) (x + z) -
          realConvolution f (uniformWeight (B.dilate t).carrier) x| ≤ 1 / 5 := by
  obtain ⟨t, δ, htlow, hthigh, hδ, hδt, hstable⟩ :=
    exists_uniformWeight_translation_stable_dilate B hB hrank
  refine ⟨t, δ, htlow, hthigh, hδ, hδt, ?_⟩
  intro x z hz
  have hzneg : -z ∈ B.dilate δ := (B.dilate δ).neg_mem_iff z |>.2 hz
  simpa using (abs_realConvolution_sub_le f _ 1 (1 / 5) (by norm_num) hf
    (x := x) (z := z) (hstable (-z) hzneg))

/-- Fine-grid version of the smoothed-average stability estimate. -/
theorem exists_realConvolution_uniformWeight_translation_stable_dilate_fine
    (B : Set N) (m : ℕ) (hB : 0 < B.radius) (hrank : 0 < B.rank)
    (hm : 0 < m) (f : ZMod N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      δ = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹ ∧
      0 < δ ∧ δ < t ∧
      ∀ x, ∀ z ∈ B.dilate δ,
        |realConvolution f (uniformWeight (B.dilate t).carrier) (x + z) -
          realConvolution f (uniformWeight (B.dilate t).carrier) x| ≤
            1 / (5 * m) := by
  obtain ⟨t, δ, htlow, hthigh, hδformula, hδ, hδt, hstable⟩ :=
    exists_uniformWeight_translation_stable_dilate_fine B m hB hrank hm
  refine ⟨t, δ, htlow, hthigh, hδformula, hδ, hδt, ?_⟩
  intro x z hz
  have hzneg : -z ∈ B.dilate δ := (B.dilate δ).neg_mem_iff z |>.2 hz
  simpa using
    (abs_realConvolution_sub_le f _ 1 (1 / (5 * m)) (by norm_num) hf
      (x := x) (z := z) (hstable (-z) hzneg))

/-- The average of a real cyclic convolution is the product of the two
averages. -/
lemma expect_realConvolution (f g : ZMod N → ℝ) :
    (𝔼 x : ZMod N, realConvolution f g x) =
      (𝔼 x : ZMod N, f x) * (𝔼 x : ZMod N, g x) := by
  have htranslate (y : ZMod N) :
      ∑ x : ZMod N, g (x - y) = ∑ x : ZMod N, g x := by
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun _ ↦ rfl
  have hdouble :
      ∑ x : ZMod N, ∑ y : ZMod N, f y * g (x - y) =
        (∑ y : ZMod N, f y) * ∑ x : ZMod N, g x := by
    rw [Finset.sum_comm]
    calc
      ∑ y : ZMod N, ∑ x : ZMod N, f y * g (x - y) =
          ∑ y : ZMod N, f y * ∑ x : ZMod N, g (x - y) := by
            congr 1 with y
            rw [Finset.mul_sum]
      _ = ∑ y : ZMod N, f y * ∑ x : ZMod N, g x := by
            congr 1 with y
            rw [htranslate]
      _ = (∑ y : ZMod N, f y) * ∑ x : ZMod N, g x := by
            rw [Finset.sum_mul]
  have hcard : (Fintype.card (ZMod N) : ℝ) ≠ 0 := by
    rw [ZMod.card]
    exact_mod_cast NeZero.ne N
  unfold realConvolution
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, hdouble]
  field_simp

/-- Some translate of a smoothing kernel of average one attains at least the
global average of the function. -/
lemma exists_expect_le_realConvolution
    (f g : ZMod N → ℝ) (hg : (𝔼 x : ZMod N, g x) = 1) :
    ∃ x : ZMod N, (𝔼 y : ZMod N, f y) ≤ realConvolution f g x := by
  have havg :
      (𝔼 x : ZMod N, realConvolution f g x) = 𝔼 y : ZMod N, f y := by
    rw [expect_realConvolution, hg, mul_one]
  obtain ⟨x, _hx, hx⟩ := Finset.exists_le_of_le_expect
    (s := (Finset.univ : Finset (ZMod N))) Finset.univ_nonempty
    (le_of_eq havg.symm)
  exact ⟨x, hx⟩

/-- Real indicator of a finite subset of the cyclic group. -/
def realIndicator (A : Finset (ZMod N)) (x : ZMod N) : ℝ :=
  if x ∈ A then 1 else 0

/-- The points of `A` lying in the reflected translate `x - S`. -/
def translatedSlice (A S : Finset (ZMod N)) (x : ZMod N) : Finset (ZMod N) :=
  A.filter fun y ↦ x - y ∈ S

/-- Smoothing an indicator by the uniform weight is exactly relative
cardinality on a translated slice. -/
lemma realConvolution_indicator_uniformWeight
    (A S : Finset (ZMod N)) (hS : S.Nonempty) (x : ZMod N) :
    realConvolution (realIndicator A) (uniformWeight S) x =
      (translatedSlice A S x).card / (S.card : ℝ) := by
  let T := translatedSlice A S x
  have hpoint (y : ZMod N) :
      realIndicator A y * uniformWeight S (x - y) =
        if y ∈ T then (N : ℝ) / S.card else 0 := by
    by_cases hyA : y ∈ A <;> by_cases hyS : x - y ∈ S <;>
      simp [realIndicator, uniformWeight, T, translatedSlice, hyA, hyS]
  have hsum :
      ∑ y : ZMod N, realIndicator A y * uniformWeight S (x - y) =
        T.card * ((N : ℝ) / S.card) := by
    simp_rw [hpoint]
    rw [← Finset.sum_filter]
    simp
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  unfold realConvolution
  rw [Fintype.expect_eq_sum_div_card, hsum, ZMod.card]
  dsimp only [T]
  field_simp

/-- In particular, some translate of a nonempty smoothing set sees at least
the global density of `A`. -/
theorem exists_dense_translatedSlice
    (A S : Finset (ZMod N)) (hS : S.Nonempty) :
    ∃ x : ZMod N,
      (A.card : ℝ) / N ≤
        (translatedSlice A S x).card / (S.card : ℝ) := by
  have hweight : (𝔼 x : ZMod N, uniformWeight S x) = 1 :=
    average_uniformWeight hS
  obtain ⟨x, hx⟩ :=
    exists_expect_le_realConvolution (realIndicator A) (uniformWeight S) hweight
  refine ⟨x, ?_⟩
  rw [realConvolution_indicator_uniformWeight A S hS] at hx
  have hindicator : (𝔼 y : ZMod N, realIndicator A y) = (A.card : ℝ) / N := by
    rw [Fintype.expect_eq_sum_div_card]
    have hsum : ∑ y : ZMod N, realIndicator A y = A.card := by
      unfold realIndicator
      rw [← Finset.sum_filter]
      simp
    rw [hsum, ZMod.card]
  rwa [hindicator] at hx

end CyclicBohr
end Erdos721
