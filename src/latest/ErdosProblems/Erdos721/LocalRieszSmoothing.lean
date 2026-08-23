/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.LocalChang

/-!
# Smoothed local Riesz products

This file supplies the Fourier-algebra half of the Chang--Sanders local
spectral lemma.  The key point is that the Fourier transform of a Riesz
product is supported on signed sums of its frequencies and has bounded
Fourier `L¹` norm.  Convolution powers of a much narrower Bohr probability
then suppress every signed sum outside its large spectrum.
-/

namespace Erdos721

open AddChar Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalRieszSmoothing

variable {N : ℕ} [NeZero N]

open CyclicFourier CyclicLocalChang CyclicSpectralSmoothing

lemma fourier_add (f g : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (fun x ↦ f x + g x) r =
      CyclicFourier.fourier f r + CyclicFourier.fourier g r := by
  unfold CyclicFourier.fourier
  rw [← CyclicFourier.average_add]
  apply congrArg CyclicFourier.average
  funext x
  ring

lemma fourier_character (a r : ZMod N) :
    CyclicFourier.fourier (fun x ↦ CyclicBohr.character a x) r =
      if r = a then 1 else 0 := by
  unfold CyclicFourier.fourier
  have hpoint (x : ZMod N) :
      (starRingEnd ℂ) (CyclicBohr.character r x) *
          CyclicBohr.character a x =
        CyclicBohr.character (a - r) x := by
    rw [← CyclicBohr.Set.character_neg_index, mul_comm,
      ← CyclicBohr.character_add_index]
    congr 1
    abel
  simp_rw [hpoint]
  rw [show (fun x : ZMod N ↦ CyclicBohr.character (a - r) x) =
      (fun x : ZMod N ↦ CyclicBohr.character x (a - r)) by
    funext x
    exact CyclicBohr.character_comm _ _]
  rw [CyclicFourier.average_character]
  simp only [sub_eq_zero, eq_comm]

lemma fourier_pointwise_mul (f g : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (fun x ↦ f x * g x) r =
      ∑ s : ZMod N,
        CyclicFourier.fourier f s * CyclicFourier.fourier g (r - s) := by
  simp_rw [← CyclicFourier.fourier_inversion f]
  have hpoint (x s : ZMod N) :
      (starRingEnd ℂ) (CyclicBohr.character r x) *
          (CyclicFourier.fourier f s * CyclicBohr.character s x * g x) =
        CyclicFourier.fourier f s *
          ((starRingEnd ℂ) (CyclicBohr.character (r - s) x) * g x) := by
    have hchar :
        (starRingEnd ℂ) (CyclicBohr.character (r - s) x) =
          (starRingEnd ℂ) (CyclicBohr.character r x) *
            CyclicBohr.character s x := by
      rw [show r - s = r + -s by abel, CyclicBohr.character_add_index,
        map_mul, CyclicBohr.Set.character_neg_index]
      simp
    rw [hchar]
    ring
  change CyclicFourier.average (fun x : ZMod N ↦
      (starRingEnd ℂ) (CyclicBohr.character r x) *
        ((∑ s : ZMod N,
            CyclicFourier.fourier f s * CyclicBohr.character s x) * g x)) = _
  rw [show (fun x : ZMod N ↦
      (starRingEnd ℂ) (CyclicBohr.character r x) *
        ((∑ s : ZMod N,
            CyclicFourier.fourier f s * CyclicBohr.character s x) * g x)) =
      (fun x : ZMod N ↦ ∑ s : ZMod N,
        CyclicFourier.fourier f s *
          ((starRingEnd ℂ) (CyclicBohr.character (r - s) x) * g x)) by
    funext x
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact hpoint x s]
  rw [CyclicFourier.average_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [CyclicFourier.average_const_mul]
  rfl

/-- The complex-valued version of the real Riesz product. -/
noncomputable def complexRieszProduct (Delta : Finset (ZMod N))
    (omega : ZMod N → ℂ) (x : ZMod N) : ℂ :=
  (rieszProduct Delta omega x : ℂ)

lemma complexRieszProduct_empty (omega : ZMod N → ℂ) :
    complexRieszProduct (∅ : Finset (ZMod N)) omega = 1 := by
  funext x
  simp [complexRieszProduct, rieszProduct]

lemma complexRieszProduct_insert {r : ZMod N} {Delta : Finset (ZMod N)}
    (hr : r ∉ Delta) (omega : ZMod N → ℂ) :
    complexRieszProduct (insert r Delta) omega = fun x ↦
      complexRieszProduct Delta omega x *
        (1 + (omega r * CyclicBohr.character r x).re) := by
  funext x
  simp [complexRieszProduct, rieszProduct, hr, mul_comm]

private noncomputable def rieszFactor (r : ZMod N) (w : ℂ)
    (x : ZMod N) : ℂ :=
  1 + (w * CyclicBohr.character r x).re

lemma complexRieszProduct_insert_rieszFactor
    {r : ZMod N} {Delta : Finset (ZMod N)}
    (hr : r ∉ Delta) (omega : ZMod N → ℂ) :
    complexRieszProduct (insert r Delta) omega = fun x ↦
      complexRieszProduct Delta omega x * rieszFactor r (omega r) x := by
  rw [complexRieszProduct_insert hr]
  rfl

lemma rieszFactor_eq (r : ZMod N) (w : ℂ) :
    rieszFactor r w = fun x ↦
      1 + (w / 2) * CyclicBohr.character r x +
        ((starRingEnd ℂ) w / 2) * CyclicBohr.character (-r) x := by
  funext x
  unfold rieszFactor
  rw [CyclicBohr.Set.character_neg_index]
  have hz (z : ℂ) : (z.re : ℂ) = (z + (starRingEnd ℂ) z) / 2 := by
    apply Complex.ext <;> simp
  rw [hz]
  rw [map_mul]
  ring

lemma fourier_rieszFactor (r s : ZMod N) (w : ℂ) :
    CyclicFourier.fourier (rieszFactor r w) s =
      (if s = 0 then 1 else 0) +
        (if s = r then w / 2 else 0) +
          (if s = -r then (starRingEnd ℂ) w / 2 else 0) := by
  rw [rieszFactor_eq]
  rw [fourier_add, fourier_add]
  rw [CyclicSpectralSmoothing.fourier_const_mul,
    CyclicSpectralSmoothing.fourier_const_mul]
  have hone : (fun _x : ZMod N ↦ (1 : ℂ)) =
      fun x ↦ CyclicBohr.character 0 x := by
    funext x
    simp
  rw [hone, fourier_character, fourier_character, fourier_character]
  simp only [mul_ite, mul_one, mul_zero]

lemma fourier_rieszFactor_eq_zero_of
    {r s : ZMod N} {w : ℂ} (hs0 : s ≠ 0) (hsr : s ≠ r)
    (hsnr : s ≠ -r) :
    CyclicFourier.fourier (rieszFactor r w) s = 0 := by
  simp [fourier_rieszFactor, hs0, hsr, hsnr]

private lemma sum_norm_ite_eq (a : ZMod N) (z : ℂ) :
    ∑ s : ZMod N, ‖if s = a then z else 0‖ = ‖z‖ := by
  calc
    ∑ s : ZMod N, ‖if s = a then z else 0‖ =
        ∑ s : ZMod N, if s = a then ‖z‖ else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsa : s = a <;> simp [hsa]
    _ = ‖z‖ := by simp

lemma sum_norm_fourier_rieszFactor_le (r : ZMod N) (w : ℂ)
    (hw : ‖w‖ ≤ 1) :
    ∑ s : ZMod N, ‖CyclicFourier.fourier (rieszFactor r w) s‖ ≤ 2 := by
  calc
    ∑ s : ZMod N, ‖CyclicFourier.fourier (rieszFactor r w) s‖ ≤
        ∑ s : ZMod N,
          (‖if s = 0 then (1 : ℂ) else 0‖ +
            ‖if s = r then w / 2 else 0‖ +
              ‖if s = -r then (starRingEnd ℂ) w / 2 else 0‖) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [fourier_rieszFactor]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ = 1 + ‖w‖ / 2 + ‖w‖ / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [sum_norm_ite_eq, sum_norm_ite_eq, sum_norm_ite_eq]
      simp [norm_div, RCLike.norm_conj]
    _ ≤ 2 := by linarith

lemma sum_norm_fourier_pointwise_mul_le (f g : ZMod N → ℂ) :
    (∑ r : ZMod N,
      ‖CyclicFourier.fourier (fun x ↦ f x * g x) r‖) ≤
      (∑ r : ZMod N, ‖CyclicFourier.fourier f r‖) *
        ∑ r : ZMod N, ‖CyclicFourier.fourier g r‖ := by
  calc
    (∑ r : ZMod N,
        ‖CyclicFourier.fourier (fun x ↦ f x * g x) r‖) =
        ∑ r : ZMod N,
          ‖∑ s : ZMod N,
            CyclicFourier.fourier f s * CyclicFourier.fourier g (r - s)‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [fourier_pointwise_mul]
    _ ≤ ∑ r : ZMod N,
        ∑ s : ZMod N,
          ‖CyclicFourier.fourier f s‖ *
            ‖CyclicFourier.fourier g (r - s)‖ := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        ‖∑ s : ZMod N,
            CyclicFourier.fourier f s * CyclicFourier.fourier g (r - s)‖ ≤
            ∑ s : ZMod N,
              ‖CyclicFourier.fourier f s *
                CyclicFourier.fourier g (r - s)‖ :=
          norm_sum_le _ _
        _ = _ := by simp only [norm_mul]
    _ = (∑ r : ZMod N, ‖CyclicFourier.fourier f r‖) *
        ∑ r : ZMod N, ‖CyclicFourier.fourier g r‖ := by
      rw [Finset.sum_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      have hshift :
          (∑ r : ZMod N, ‖CyclicFourier.fourier g (r - s)‖) =
            ∑ r : ZMod N, ‖CyclicFourier.fourier g r‖ :=
        Fintype.sum_equiv (Equiv.subRight s)
          (fun r : ZMod N ↦ ‖CyclicFourier.fourier g (r - s)‖)
          (fun r : ZMod N ↦ ‖CyclicFourier.fourier g r‖) (fun _ ↦ rfl)
      calc
        (∑ r : ZMod N,
            ‖CyclicFourier.fourier f s‖ *
              ‖CyclicFourier.fourier g (r - s)‖) =
            ‖CyclicFourier.fourier f s‖ *
              ∑ r : ZMod N, ‖CyclicFourier.fourier g (r - s)‖ := by
          rw [Finset.mul_sum]
        _ = _ := by rw [hshift]

/-- The Fourier `L¹` norm of a Riesz product is at most `2^|Delta|`. -/
lemma sum_norm_fourier_complexRieszProduct_le
    (Delta : Finset (ZMod N)) (omega : ZMod N → ℂ)
    (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1) :
    ∑ s : ZMod N,
      ‖CyclicFourier.fourier (complexRieszProduct Delta omega) s‖ ≤
      2 ^ Delta.card := by
  induction Delta using Finset.induction_on with
  | empty =>
      rw [complexRieszProduct_empty]
      have hfour (s : ZMod N) :
          CyclicFourier.fourier (fun _x : ZMod N ↦ (1 : ℂ)) s =
            if s = 0 then 1 else 0 := by
        simpa only [CyclicBohr.character_zero_index] using
          fourier_character (N := N) 0 s
      calc
        ∑ s : ZMod N,
            ‖CyclicFourier.fourier (fun _x : ZMod N ↦ (1 : ℂ)) s‖ =
            ∑ s : ZMod N, ‖if s = 0 then (1 : ℂ) else 0‖ := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hfour]
        _ = 1 := by rw [sum_norm_ite_eq]; norm_num
        _ ≤ 2 ^ (∅ : Finset (ZMod N)).card := by simp
  | @insert r Delta hr ih =>
      rw [complexRieszProduct_insert hr]
      calc
        ∑ s : ZMod N,
            ‖CyclicFourier.fourier
              (fun x ↦ complexRieszProduct Delta omega x *
                rieszFactor r (omega r) x) s‖ ≤
            (∑ s : ZMod N,
                ‖CyclicFourier.fourier
                  (complexRieszProduct Delta omega) s‖) *
              ∑ s : ZMod N,
                ‖CyclicFourier.fourier (rieszFactor r (omega r)) s‖ :=
          sum_norm_fourier_pointwise_mul_le _ _
        _ ≤ 2 ^ Delta.card * 2 := by
          gcongr
          · exact ih (fun s hs ↦ homega s (by simp [hs]))
          · exact sum_norm_fourier_rieszFactor_le r (omega r)
              (homega r (by simp))
        _ = 2 ^ (insert r Delta).card := by simp [hr, pow_succ]

/-! ## Fourier support -/

lemma addSpan_mono {A B : Finset (ZMod N)} (hAB : A ⊆ B) :
    A.addSpan ⊆ B.addSpan := by
  intro x hx
  rw [Finset.mem_addSpan] at hx ⊢
  obtain ⟨epsilon, hepsilon, heq⟩ := hx
  let epsilon' : ZMod N → ℤ := fun a ↦ if a ∈ A then epsilon a else 0
  refine ⟨epsilon', ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ A
    · simpa [epsilon', ha] using hepsilon a
    · simp [epsilon', ha]
  · calc
      (∑ a ∈ B, epsilon' a • a) = ∑ a ∈ A, epsilon' a • a := by
        symm
        apply Finset.sum_subset hAB
        intro a haB haA
        simp [epsilon', haA]
      _ = ∑ a ∈ A, epsilon a • a := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [epsilon', ha]
      _ = x := heq

lemma add_mem_addSpan_insert {Delta : Finset (ZMod N)} {r s : ZMod N}
    (hr : r ∉ Delta) (hs : s ∈ Delta.addSpan) :
    s + r ∈ (insert r Delta).addSpan := by
  rw [Finset.mem_addSpan] at hs ⊢
  obtain ⟨epsilon, hepsilon, heq⟩ := hs
  let epsilon' : ZMod N → ℤ := fun a ↦ if a = r then 1 else epsilon a
  refine ⟨epsilon', ?_, ?_⟩
  · intro a
    by_cases ha : a = r
    · simp [epsilon', ha]
    · simpa [epsilon', ha] using hepsilon a
  · rw [Finset.sum_insert hr]
    simp only [epsilon', if_pos, one_zsmul]
    have hrest :
        (∑ a ∈ Delta, (if a = r then (1 : ℤ) else epsilon a) • a) =
          ∑ a ∈ Delta, epsilon a • a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [show a ≠ r by exact fun har ↦ hr (har ▸ ha)]
    rw [hrest, heq]
    abel

lemma sub_mem_addSpan_insert {Delta : Finset (ZMod N)} {r s : ZMod N}
    (hr : r ∉ Delta) (hs : s ∈ Delta.addSpan) :
    s - r ∈ (insert r Delta).addSpan := by
  rw [Finset.mem_addSpan] at hs ⊢
  obtain ⟨epsilon, hepsilon, heq⟩ := hs
  let epsilon' : ZMod N → ℤ := fun a ↦ if a = r then -1 else epsilon a
  refine ⟨epsilon', ?_, ?_⟩
  · intro a
    by_cases ha : a = r
    · simp [epsilon', ha]
    · simpa [epsilon', ha] using hepsilon a
  · rw [Finset.sum_insert hr]
    simp only [epsilon', if_pos, neg_one_zsmul]
    have hrest :
        (∑ a ∈ Delta, (if a = r then (-1 : ℤ) else epsilon a) • a) =
          ∑ a ∈ Delta, epsilon a • a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [show a ≠ r by exact fun har ↦ hr (har ▸ ha)]
    rw [hrest, heq]
    abel

lemma fourier_rieszFactor_ne_zero_imp {r s : ZMod N} {w : ℂ}
    (h : CyclicFourier.fourier (rieszFactor r w) s ≠ 0) :
    s = 0 ∨ s = r ∨ s = -r := by
  by_contra hcases
  push Not at hcases
  exact h (fourier_rieszFactor_eq_zero_of hcases.1 hcases.2.1 hcases.2.2)

/-- Every Fourier frequency of a Riesz product lies in the signed span of
its defining frequencies. -/
lemma fourier_complexRieszProduct_eq_zero_of_not_mem_addSpan
    (Delta : Finset (ZMod N)) (omega : ZMod N → ℂ) {a : ZMod N}
    (ha : a ∉ Delta.addSpan) :
    CyclicFourier.fourier (complexRieszProduct Delta omega) a = 0 := by
  induction Delta using Finset.induction_on generalizing a with
  | empty =>
      rw [complexRieszProduct_empty]
      change CyclicFourier.fourier (fun _x : ZMod N ↦ (1 : ℂ)) a = 0
      have hfour :
          CyclicFourier.fourier (fun _x : ZMod N ↦ (1 : ℂ)) a =
            if a = 0 then 1 else 0 := by
        simpa only [CyclicBohr.character_zero_index] using
          fourier_character (N := N) 0 a
      rw [hfour]
      have ha0 : a ≠ 0 := by
        intro ha0
        subst a
        apply ha
        rw [Finset.mem_addSpan]
        exact ⟨fun _ ↦ 0, by simp, by simp⟩
      simp [ha0]
  | @insert r Delta hr ih =>
      rw [complexRieszProduct_insert_rieszFactor hr,
        fourier_pointwise_mul]
      apply Finset.sum_eq_zero
      intro s hs
      by_cases hsSpan : s ∈ Delta.addSpan
      · by_cases hfactor :
            CyclicFourier.fourier (rieszFactor r (omega r)) (a - s) = 0
        · simp [hfactor]
        · rcases fourier_rieszFactor_ne_zero_imp hfactor with
            hzero | hpos | hneg
          · have has : a = s := sub_eq_zero.mp hzero
            exfalso
            apply ha
            rw [has]
            exact addSpan_mono (Finset.subset_insert r Delta) hsSpan
          · have has : a = s + r := eq_add_of_sub_eq' hpos
            exfalso
            exact ha (has ▸ add_mem_addSpan_insert hr hsSpan)
          · have has : a = s - r := by
              simpa [sub_eq_add_neg] using eq_add_of_sub_eq' hneg
            exfalso
            exact ha (has ▸ sub_mem_addSpan_insert hr hsSpan)
      · rw [ih hsSpan]
        simp

/-! ## The constant Fourier coefficient -/

/-- A globally dissociated Riesz product has normalized average one.  Zero
coefficients are removed before applying Mathlib's randomisation identity,
whose statement asks that every retained coefficient be nonzero. -/
lemma average_complexRieszProduct_eq_one
    (Delta : Finset (ZMod N))
    (hDelta : AddDissociated (Delta : Set (ZMod N)))
    (omega : ZMod N → ℂ) :
    CyclicFourier.average (complexRieszProduct Delta omega) = 1 := by
  let Delta0 : Finset (ZMod N) := Delta.filter fun r ↦ omega r ≠ 0
  let imageDelta : Finset (AddChar (ZMod N) ℂ) :=
    CyclicRudin.cyclicCharacterImage Delta0
  let b : AddChar (ZMod N) ℂ → ℂ := fun psi ↦
    omega (AddChar.zmodAddEquiv.symm psi)
  have hDelta0 : AddDissociated (Delta0 : Set (ZMod N)) := by
    apply AddDissociated.subset _ hDelta
    intro r hr
    exact (Finset.mem_filter.mp hr).1
  have himage : AddDissociated (imageDelta : Set (AddChar (ZMod N) ℂ)) := by
    simpa [imageDelta] using
      CyclicRudin.addDissociated_cyclicCharacterImage hDelta0
  have hb : ∀ psi ∈ imageDelta, b psi ≠ 0 := by
    intro psi hpsi
    change psi ∈ CyclicRudin.cyclicCharacterImage Delta0 at hpsi
    rw [CyclicRudin.cyclicCharacterImage, Finset.mem_map] at hpsi
    obtain ⟨r, hr, rfl⟩ := hpsi
    simpa only [b, CyclicRudin.cyclicCharacterEmbedding_apply,
      CyclicBohr.character, AddEquiv.symm_apply_apply] using
        (Finset.mem_filter.mp hr).2
  have hrand := CyclicRudin.randomisation_finset imageDelta himage
    (fun _psi ↦ (1 : ℝ)) b hb
  have hprod (x : ZMod N) :
      (∏ psi ∈ imageDelta, (1 + (b psi * psi x).re)) =
        rieszProduct Delta omega x := by
    calc
      (∏ psi ∈ imageDelta, (1 + (b psi * psi x).re)) =
          ∏ r ∈ Delta0,
            (1 + (omega r * CyclicBohr.character r x).re) := by
        unfold imageDelta CyclicRudin.cyclicCharacterImage
        rw [Finset.prod_map]
        apply Finset.prod_congr rfl
        intro r hr
        simp only [b, CyclicRudin.cyclicCharacterEmbedding_apply,
          CyclicBohr.character, AddEquiv.symm_apply_apply]
      _ = ∏ r ∈ Delta,
            (1 + (omega r * CyclicBohr.character r x).re) := by
        apply Finset.prod_subset (Finset.filter_subset _ _)
        intro r hrDelta hrnot
        have hzero : omega r = 0 := by
          by_contra hne
          exact hrnot (Finset.mem_filter.mpr ⟨hrDelta, hne⟩)
        simp [hzero]
      _ = rieszProduct Delta omega x := rfl
  have hrand' :
      Finset.expect Finset.univ
        (fun x : ZMod N ↦ rieszProduct Delta omega x) = 1 := by
    calc
      Finset.expect Finset.univ
          (fun x : ZMod N ↦ rieszProduct Delta omega x) =
          Finset.expect Finset.univ (fun x : ZMod N ↦
            ∏ psi ∈ imageDelta, (1 + (b psi * psi x).re)) := by
        apply Finset.expect_congr rfl
        intro x _hx
        exact (hprod x).symm
      _ = 1 := by simpa only [Finset.prod_const_one] using hrand
  rw [Fintype.expect_eq_sum_div_card] at hrand'
  have hreal :
      (N : ℝ)⁻¹ * ∑ x : ZMod N, rieszProduct Delta omega x = 1 := by
    simpa only [ZMod.card, div_eq_mul_inv, mul_comm] using hrand'
  unfold CyclicFourier.average complexRieszProduct
  simpa using congrArg Complex.ofReal hreal

lemma fourier_complexRieszProduct_zero_eq_one
    (Delta : Finset (ZMod N))
    (hDelta : AddDissociated (Delta : Set (ZMod N)))
    (omega : ZMod N → ℂ) :
    CyclicFourier.fourier (complexRieszProduct Delta omega) 0 = 1 := by
  rw [CyclicFourier.fourier_zero]
  exact average_complexRieszProduct_eq_one Delta hDelta omega

/-! ## Spectral dissociativity and an abstract smoothed bound -/

/-- `Delta` is dissociated relative to `Q` when it is globally dissociated
and its signed span meets `Q` only at zero.  In the application `Q` is the
large spectrum of a very narrow Bohr probability. -/
def SpectrallyDissociated (Q Delta : Finset (ZMod N)) : Prop :=
  AddDissociated (Delta : Set (ZMod N)) ∧
    ∀ r ∈ Delta.addSpan, r ∈ Q → r = 0

lemma spectrallyDissociated_empty (Q : Finset (ZMod N)) :
    SpectrallyDissociated Q (∅ : Finset (ZMod N)) := by
  constructor
  · simp
  · intro r hr
    rw [Finset.mem_addSpan] at hr
    obtain ⟨epsilon, hepsilon, rfl⟩ := hr
    simp

/-- A Fourier multiplier whose non-`Q` coefficients are small gives a
smoothed Riesz-product average close to one.  The signed-support theorem is
what turns relative dissociativity into the required tail condition. -/
theorem norm_smoothed_riesz_average_sub_one_le
    (Q Delta : Finset (ZMod N))
    (hDelta : SpectrallyDissociated Q Delta)
    (omega : ZMod N → ℂ) (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1)
    (mu : ZMod N → ℂ) {theta : ℝ} (htheta : 0 ≤ theta)
    (hmuZero : CyclicFourier.fourier mu 0 = 1)
    (hmuTail : ∀ r ∉ Q, ‖CyclicFourier.fourier mu r‖ ≤ theta) :
    ‖CyclicFourier.average (fun x ↦
        (starRingEnd ℂ) (mu x) * complexRieszProduct Delta omega x) - 1‖ ≤
      theta * 2 ^ Delta.card := by
  let term : ZMod N → ℂ := fun r ↦
    (starRingEnd ℂ) (CyclicFourier.fourier mu r) *
      CyclicFourier.fourier (complexRieszProduct Delta omega) r
  have htermZero : term 0 = 1 := by
    simp only [term, hmuZero, map_one, one_mul,
      fourier_complexRieszProduct_zero_eq_one Delta hDelta.1 omega]
  have htail (r : ZMod N) (hr0 : r ≠ 0) :
      ‖term r‖ ≤
        theta *
          ‖CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ := by
    by_cases hq :
        CyclicFourier.fourier (complexRieszProduct Delta omega) r = 0
    · simp [term, hq, htheta]
    · have hrSpan : r ∈ Delta.addSpan := by
        by_contra hrSpan
        exact hq (fourier_complexRieszProduct_eq_zero_of_not_mem_addSpan
          Delta omega hrSpan)
      have hrQ : r ∉ Q := by
        intro hrQ
        exact hr0 (hDelta.2 r hrSpan hrQ)
      simp only [term, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_right (hmuTail r hrQ) (norm_nonneg _)
  rw [CyclicFourier.parseval]
  change ‖(∑ r : ZMod N, term r) - 1‖ ≤ theta * 2 ^ Delta.card
  have hzeroMem : (0 : ZMod N) ∈ (Finset.univ : Finset (ZMod N)) :=
    Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hzeroMem, htermZero]
  simp only [term]
  rw [add_sub_cancel_right]
  calc
    ‖∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        (starRingEnd ℂ) (CyclicFourier.fourier mu r) *
          CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ ≤
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
          ‖(starRingEnd ℂ) (CyclicFourier.fourier mu r) *
            CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        theta *
          ‖CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact htail r (Finset.mem_erase.mp hr).1
    _ ≤ theta * ∑ r : ZMod N,
        ‖CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun r _hr _ ↦ mul_nonneg htheta (norm_nonneg _))
    _ ≤ theta * 2 ^ Delta.card := by
      gcongr
      exact sum_norm_fourier_complexRieszProduct_le Delta omega homega

lemma rieszProduct_le_two_pow
    (Delta : Finset (ZMod N)) (omega : ZMod N → ℂ)
    (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1) (x : ZMod N) :
    rieszProduct Delta omega x ≤ 2 ^ Delta.card := by
  unfold rieszProduct
  calc
    (∏ r ∈ Delta,
        (1 + (omega r * CyclicBohr.character r x).re)) ≤
        ∏ _r ∈ Delta, (2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro r hr
        have hre : -(1 : ℝ) ≤
            (omega r * CyclicBohr.character r x).re := by
          calc
            -(1 : ℝ) ≤ -‖omega r‖ := neg_le_neg (homega r hr)
            _ = -‖omega r * CyclicBohr.character r x‖ := by
              rw [norm_mul, CyclicBohr.norm_character, mul_one]
            _ ≤ (omega r * CyclicBohr.character r x).re :=
              neg_le_of_abs_le (Complex.abs_re_le_norm _)
        linarith
      · intro r hr
        have hre : (omega r * CyclicBohr.character r x).re ≤ 1 := by
          calc
            (omega r * CyclicBohr.character r x).re ≤
                ‖omega r * CyclicBohr.character r x‖ :=
              Complex.re_le_norm _
            _ = ‖omega r‖ := by
              rw [norm_mul, CyclicBohr.norm_character, mul_one]
            _ ≤ 1 := homega r hr
        linarith
    _ = 2 ^ Delta.card := by simp

lemma average_probabilityWeight_mul_complexRieszProduct
    (S Delta : Finset (ZMod N)) (hS : S.Nonempty)
    (omega : ZMod N → ℂ) :
    CyclicFourier.average (fun x ↦
        (starRingEnd ℂ) (probabilityWeight S x) *
          complexRieszProduct Delta omega x) =
      (finsetMean S (rieszProduct Delta omega) : ℂ) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hScard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  unfold CyclicFourier.average probabilityWeight complexRieszProduct
    finsetMean
  have hstar (x : ZMod N) :
      (starRingEnd ℂ) (if x ∈ S then (N : ℂ) / S.card else 0) =
        if x ∈ S then (N : ℂ) / S.card else 0 := by
    by_cases hx : x ∈ S <;> simp [hx]
  calc
    (N : ℂ)⁻¹ * ∑ x : ZMod N,
        (starRingEnd ℂ) (if x ∈ S then (N : ℂ) / S.card else 0) *
          (rieszProduct Delta omega x : ℂ) =
        (N : ℂ)⁻¹ * ∑ x ∈ S,
          ((N : ℂ) / S.card) * (rieszProduct Delta omega x : ℂ) := by
      congr 1
      simp_rw [hstar, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = (S.card : ℂ)⁻¹ *
          ∑ x ∈ S, (rieszProduct Delta omega x : ℂ) := by
      rw [← Finset.mul_sum]
      field_simp
    _ = (((S.card : ℝ)⁻¹ *
          ∑ x ∈ S, rieszProduct Delta omega x : ℝ) : ℂ) := by
      have hsum :
          (∑ x ∈ S, (rieszProduct Delta omega x : ℂ)) =
            ((∑ x ∈ S, rieszProduct Delta omega x : ℝ) : ℂ) := by
        exact (Complex.ofReal_sum _ _).symm
      rw [Complex.ofReal_mul, Complex.ofReal_inv]
      exact congrArg (fun z : ℂ ↦ (S.card : ℂ)⁻¹ * z) hsum

lemma norm_average_star_sub_mul_complexRieszProduct_le
    (mu nu : ZMod N → ℂ) (Delta : Finset (ZMod N))
    (omega : ZMod N → ℂ) (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1) :
    ‖CyclicFourier.average (fun x ↦
        ((starRingEnd ℂ) (mu x) - (starRingEnd ℂ) (nu x)) *
          complexRieszProduct Delta omega x)‖ ≤
      (N : ℝ)⁻¹ * 2 ^ Delta.card * ∑ x : ZMod N, ‖mu x - nu x‖ := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold CyclicFourier.average
  calc
    ‖(N : ℂ)⁻¹ * ∑ x : ZMod N,
        ((starRingEnd ℂ) (mu x) - (starRingEnd ℂ) (nu x)) *
          complexRieszProduct Delta omega x‖ ≤
        ‖(N : ℂ)⁻¹‖ * ∑ x : ZMod N,
          ‖((starRingEnd ℂ) (mu x) - (starRingEnd ℂ) (nu x)) *
            complexRieszProduct Delta omega x‖ := by
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ x : ZMod N,
          (‖mu x - nu x‖ * 2 ^ Delta.card) := by
      have hNnorm : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
        simp [norm_inv, abs_of_pos hN]
      rw [hNnorm]
      gcongr with x
      rw [norm_mul, ← map_sub, RCLike.norm_conj]
      have hnonneg := rieszProduct_nonneg Delta omega homega x
      have hupper := rieszProduct_le_two_pow Delta omega homega x
      simpa only [complexRieszProduct, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg] using
          mul_le_mul_of_nonneg_left hupper (norm_nonneg (mu x - nu x))
    _ = (N : ℝ)⁻¹ * 2 ^ Delta.card *
        ∑ x : ZMod N, ‖mu x - nu x‖ := by
      rw [← Finset.sum_mul]
      ring

/-! ## The narrow-set convolution kernel -/

/-- Smooth the probability weight of `S` by `k` independent samples from
the uniform probability on `V`. -/
noncomputable def smoothedProbabilityWeight
    (V S : Finset (ZMod N)) (k : ℕ) : ZMod N → ℂ :=
  μ_[ℂ] V ∗ᵈ^ k ∗ᵈ probabilityWeight S

lemma fourier_smoothedProbabilityWeight
    {V : Finset (ZMod N)} (hV : V.Nonempty)
    (S : Finset (ZMod N)) (k : ℕ) (r : ZMod N) :
    CyclicFourier.fourier (smoothedProbabilityWeight V S k) r =
      CyclicFourier.fourier (probabilityWeight V) r ^ k *
        CyclicFourier.fourier (probabilityWeight S) r := by
  exact CyclicBoostedAlmostPeriodicity.fourier_mu_iterConv_ddconv
    hV (probabilityWeight S) k r

lemma fourier_smoothedProbabilityWeight_zero
    {V S : Finset (ZMod N)} (hV : V.Nonempty) (hS : S.Nonempty)
    (k : ℕ) :
    CyclicFourier.fourier (smoothedProbabilityWeight V S k) 0 = 1 := by
  rw [fourier_smoothedProbabilityWeight hV S k 0,
    CyclicFourier.fourier_zero, CyclicFourier.fourier_zero,
    average_probabilityWeight hV, average_probabilityWeight hS]
  simp

lemma probabilityWeight_eq_ofReal_uniformWeight
    (S : Finset (ZMod N)) (x : ZMod N) :
    probabilityWeight S x = (CyclicBohr.uniformWeight S x : ℂ) := by
  by_cases hx : x ∈ S <;>
    simp [probabilityWeight, CyclicBohr.uniformWeight, hx]

lemma smoothedProbabilityWeight_eq_ofReal
    (V S : Finset (ZMod N)) (k : ℕ) (x : ZMod N) :
    smoothedProbabilityWeight V S k x =
      (((μ_[ℝ] V ∗ᵈ^ k ∗ᵈ CyclicBohr.uniformWeight S) x : ℝ) : ℂ) := by
  have hiter : μ_[ℂ] V ∗ᵈ^ k =
      Complex.ofReal ∘ (μ_[ℝ] V ∗ᵈ^ k) := by
    funext y
    rw [← Complex.ofReal_comp_mu]
    exact (Complex.ofReal_iterConv (μ_[ℝ] V) k y).symm
  have hweight : probabilityWeight S =
      Complex.ofReal ∘ CyclicBohr.uniformWeight S := by
    funext y
    exact probabilityWeight_eq_ofReal_uniformWeight S y
  unfold smoothedProbabilityWeight
  rw [hiter, hweight, ← Complex.ofReal_comp_ddconv]
  rfl

/-- Averaging a uniform weight against an arbitrary probability kernel
preserves any uniform `L¹` translation estimate on the kernel support. -/
lemma expect_abs_probabilityKernel_ddconv_sub_le
    (K u : ZMod N → ℝ) {epsilon : ℝ}
    (hKnonneg : 0 ≤ K) (hKsum : ∑ z : ZMod N, K z = 1)
    (htranslate : ∀ z ∈ Function.support K,
      (Finset.expect Finset.univ fun x : ZMod N ↦ |u (x - z) - u x|) ≤
        epsilon) :
    (Finset.expect Finset.univ fun x : ZMod N ↦
      |(K ∗ᵈ u) x - u x|) ≤ epsilon := by
  have hcard : (0 : ℝ) < Fintype.card (ZMod N) := by
    rw [ZMod.card]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpoint (x : ZMod N) :
      |(K ∗ᵈ u) x - u x| ≤
        ∑ z : ZMod N, K z * |u (x - z) - u x| := by
    rw [ddconv_eq_sum_sub']
    have heq :
        (∑ z : ZMod N, K z * u (x - z)) - u x =
          ∑ z : ZMod N, K z * (u (x - z) - u x) := by
      calc
        (∑ z : ZMod N, K z * u (x - z)) - u x =
            (∑ z : ZMod N, K z * u (x - z)) -
              (∑ z : ZMod N, K z) * u x := by rw [hKsum, one_mul]
        _ = ∑ z : ZMod N,
            (K z * u (x - z) - K z * u x) := by
          rw [Finset.sum_mul, Finset.sum_sub_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
    rw [heq]
    calc
      |∑ z : ZMod N, K z * (u (x - z) - u x)| ≤
          ∑ z : ZMod N, |K z * (u (x - z) - u x)| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ z : ZMod N, K z * |u (x - z) - u x| := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [abs_mul, abs_of_nonneg (hKnonneg z)]
  rw [Fintype.expect_eq_sum_div_card]
  calc
    (∑ x : ZMod N, |(K ∗ᵈ u) x - u x|) /
        Fintype.card (ZMod N) ≤
        (∑ x : ZMod N,
          ∑ z : ZMod N, K z * |u (x - z) - u x|) /
            Fintype.card (ZMod N) := by
      gcongr with x
      exact hpoint x
    _ = ∑ z : ZMod N, K z *
        (Finset.expect Finset.univ fun x : ZMod N ↦
          |u (x - z) - u x|) := by
      simp only [Fintype.expect_eq_sum_div_card]
      rw [Finset.sum_comm]
      calc
        (∑ z : ZMod N,
            ∑ x : ZMod N, K z * |u (x - z) - u x|) /
              Fintype.card (ZMod N) =
            (∑ z : ZMod N, K z *
              ∑ x : ZMod N, |u (x - z) - u x|) /
                Fintype.card (ZMod N) := by
          congr 1
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.mul_sum]
        _ = ∑ z : ZMod N, K z *
            ((∑ x : ZMod N, |u (x - z) - u x|) /
              Fintype.card (ZMod N)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro z hz
          ring
    _ ≤ ∑ z : ZMod N, K z * epsilon := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hKz : K z = 0
      · simp [hKz]
      · exact mul_le_mul_of_nonneg_left
          (htranslate z hKz) (hKnonneg z)
    _ = epsilon := by
      rw [← Finset.sum_mul, hKsum, one_mul]

lemma expect_abs_smoothedProbabilityWeight_sub_le
    (V S : Finset (ZMod N)) (hV : V.Nonempty) (k : ℕ)
    {epsilon : ℝ}
    (htranslate : ∀ z ∈ Function.support (μ_[ℝ] V ∗ᵈ^ k),
      (Finset.expect Finset.univ fun x : ZMod N ↦
        |CyclicBohr.uniformWeight S (x - z) -
          CyclicBohr.uniformWeight S x|) ≤ epsilon) :
    (N : ℝ)⁻¹ *
        ∑ x : ZMod N,
          ‖smoothedProbabilityWeight V S k x - probabilityWeight S x‖ ≤
      epsilon := by
  have hKnonneg : 0 ≤ μ_[ℝ] V ∗ᵈ^ k := iterConv_nonneg mu_nonneg
  have hKsum : ∑ z : ZMod N, (μ_[ℝ] V ∗ᵈ^ k) z = 1 := by
    rw [sum_iterConv, sum_mu ℝ hV, one_pow]
  have hbound := expect_abs_probabilityKernel_ddconv_sub_le
    (μ_[ℝ] V ∗ᵈ^ k) (CyclicBohr.uniformWeight S)
      hKnonneg hKsum htranslate
  rw [Fintype.expect_eq_sum_div_card, ZMod.card] at hbound
  simpa only [smoothedProbabilityWeight_eq_ofReal,
    probabilityWeight_eq_ofReal_uniformWeight, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, div_eq_inv_mul] using hbound

lemma nsmul_dilate_subset (B : CyclicBohr.Set N) {rho : ℝ}
    (hrho : 0 ≤ rho) : ∀ k : ℕ,
    k • ((B.dilate rho).carrier : Set (ZMod N)) ⊆
      ((B.dilate ((k : ℝ) * rho)).carrier : Set (ZMod N))
  | 0 => by
      intro z hz
      simp only [zero_nsmul, Set.mem_singleton_iff] at hz
      subst z
      have hzero := (B.dilate ((0 : ℝ) * rho)).zero_mem
      change (0 : ZMod N) ∈ (B.dilate ((0 : ℝ) * rho)).carrier at hzero
      norm_num at hzero ⊢
  | k + 1 => by
      rw [succ_nsmul]
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
      have hx' := nsmul_dilate_subset B hrho k hx
      have hsum := CyclicBohr.Set.add_mem_dilate
        (mul_nonneg (Nat.cast_nonneg k) hrho) hrho hx' hy
      have hscale : (((k + 1 : ℕ) : ℝ) * rho) =
          (k : ℝ) * rho + rho := by
        push_cast
        ring
      rw [hscale]
      change x + y ∈
        (B.dilate ((k : ℝ) * rho + rho)).carrier at hsum
      simpa only [Finset.mem_coe] using hsum

lemma support_iterConv_mu_subset_dilate
    (B : CyclicBohr.Set N) (V : Finset (ZMod N)) {rho : ℝ}
    (hrho : 0 ≤ rho) (hV : V ⊆ (B.dilate rho).carrier) (k : ℕ) :
    Function.support (μ_[ℝ] V ∗ᵈ^ k) ⊆
      ((B.dilate ((k : ℝ) * rho)).carrier : Set (ZMod N)) := by
  have hsupport : Function.support (μ_[ℝ] V) ⊆
      ((B.dilate rho).carrier : Set (ZMod N)) := by
    intro z hz
    rw [support_mu, Finset.mem_coe] at hz
    exact hV hz
  exact (support_iterConv_subset (μ_[ℝ] V) k).trans
    ((Set.nsmul_subset_nsmul_left hsupport).trans
      (nsmul_dilate_subset B hrho k))

lemma expect_abs_smoothedProbabilityWeight_sub_le_of_dilate
    (B : CyclicBohr.Set N) (V S : Finset (ZMod N)) (hVnonempty : V.Nonempty)
    (k : ℕ) {rho delta epsilon : ℝ}
    (hrho : 0 ≤ rho) (hscale : (k : ℝ) * rho ≤ delta)
    (hV : V ⊆ (B.dilate rho).carrier)
    (hstable : ∀ z ∈ B.dilate delta,
      (Finset.expect Finset.univ fun x : ZMod N ↦
        |CyclicBohr.uniformWeight S (x - z) -
          CyclicBohr.uniformWeight S x|) ≤ epsilon) :
    (N : ℝ)⁻¹ *
        ∑ x : ZMod N,
          ‖smoothedProbabilityWeight V S k x - probabilityWeight S x‖ ≤
      epsilon := by
  apply expect_abs_smoothedProbabilityWeight_sub_le V S hVnonempty k
  intro z hz
  apply hstable z
  exact CyclicBohr.Set.dilate_mono B
    (mul_nonneg (Nat.cast_nonneg k) hrho) hscale
      (support_iterConv_mu_subset_dilate B V hrho hV k hz)

lemma norm_fourier_smoothedProbabilityWeight_le_pow_of_not_mem
    {V S : Finset (ZMod N)} (hV : V.Nonempty) (hS : S.Nonempty)
    (k : ℕ) {eta : ℝ} (heta : 0 ≤ eta) {r : ZMod N}
    (hr : r ∉ CyclicChang.relativeLargeSpectrum V eta) :
    ‖CyclicFourier.fourier (smoothedProbabilityWeight V S k) r‖ ≤
      eta ^ k := by
  have hrLarge :
      r ∉ CyclicFourier.largeSpectrum (probabilityWeight V) eta := by
    rwa [largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum hV]
  have hVcoeff :
      ‖CyclicFourier.fourier (probabilityWeight V) r‖ ≤ eta :=
    le_of_lt (by
      simpa only [CyclicFourier.mem_largeSpectrum, not_le] using hrLarge)
  rw [fourier_smoothedProbabilityWeight hV S k r, norm_mul, norm_pow]
  calc
    ‖CyclicFourier.fourier (probabilityWeight V) r‖ ^ k *
        ‖CyclicFourier.fourier (probabilityWeight S) r‖ ≤
        eta ^ k * 1 := by
      exact mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hVcoeff k)
        (norm_fourier_probabilityWeight_le_one hS r)
        (norm_nonneg _) (pow_nonneg heta k)
    _ = eta ^ k := mul_one _

/-- The abstract local dissociation conclusion.  The `L¹` hypothesis is the
finite regularity estimate; the spectral hypothesis is supplied by a
convolution power of a narrower Bohr probability. -/
theorem locallyDissociated_of_spectral_smoothing
    (S Q Delta : Finset (ZMod N)) (hS : S.Nonempty)
    (hDelta : SpectrallyDissociated Q Delta)
    (mu : ZMod N → ℂ) {theta : ℝ} (htheta : 0 ≤ theta)
    (hmuZero : CyclicFourier.fourier mu 0 = 1)
    (hmuTail : ∀ r ∉ Q, ‖CyclicFourier.fourier mu r‖ ≤ theta)
    (hthetaCard : theta * 2 ^ Delta.card ≤ 1)
    (hL1 : (N : ℝ)⁻¹ * 2 ^ Delta.card *
      (∑ x : ZMod N, ‖mu x - probabilityWeight S x‖) ≤ 1) :
    LocallyDissociated S Delta (Real.log 4) := by
  intro omega homega
  let z : ℂ := CyclicFourier.average (fun x ↦
    (starRingEnd ℂ) (mu x) * complexRieszProduct Delta omega x)
  have hz : ‖z - 1‖ ≤ 1 :=
    (norm_smoothed_riesz_average_sub_one_le Q Delta hDelta omega homega mu
      htheta hmuZero hmuTail).trans hthetaCard
  have hdiff :
      ‖z - (finsetMean S (rieszProduct Delta omega) : ℂ)‖ ≤ 1 := by
    have havg := norm_average_star_sub_mul_complexRieszProduct_le
      mu (probabilityWeight S) Delta omega homega
    have heq :
        z - (finsetMean S (rieszProduct Delta omega) : ℂ) =
          CyclicFourier.average (fun x ↦
            ((starRingEnd ℂ) (mu x) -
              (starRingEnd ℂ) (probabilityWeight S x)) *
                complexRieszProduct Delta omega x) := by
      rw [← average_probabilityWeight_mul_complexRieszProduct S Delta hS omega]
      unfold z
      unfold CyclicFourier.average
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [heq]
    exact havg.trans hL1
  have hzre : z.re ≤ 2 := by
    have hre : z.re - 1 ≤ ‖z - 1‖ := by
      calc
        z.re - 1 = (z - 1).re := by simp
        _ ≤ ‖z - 1‖ := Complex.re_le_norm _
    linarith
  have hmean : finsetMean S (rieszProduct Delta omega) ≤ 3 := by
    have hre : finsetMean S (rieszProduct Delta omega) - z.re ≤
        ‖z - (finsetMean S (rieszProduct Delta omega) : ℂ)‖ := by
      calc
        finsetMean S (rieszProduct Delta omega) - z.re =
            (-(z - (finsetMean S (rieszProduct Delta omega) : ℂ))).re := by
          simp
        _ ≤ ‖-(z - (finsetMean S (rieszProduct Delta omega) : ℂ))‖ :=
          Complex.re_le_norm _
        _ = _ := norm_neg _
    linarith
  calc
    finsetMean S (rieszProduct Delta omega) ≤ 3 := hmean
    _ ≤ 4 := by norm_num
    _ = Real.exp (Real.log 4) := by
      rw [Real.exp_log]
      norm_num

/-- Ready-to-use specialization of the abstract smoothing lemma to a
convolution power of a narrow finite set. -/
theorem locallyDissociated_of_narrow_convolution
    (S V Delta : Finset (ZMod N)) (hS : S.Nonempty) (hV : V.Nonempty)
    (k : ℕ) {eta : ℝ} (heta : 0 ≤ eta)
    (hDelta : SpectrallyDissociated
      (CyclicChang.relativeLargeSpectrum V eta) Delta)
    (hthetaCard : eta ^ k * 2 ^ Delta.card ≤ 1)
    (hL1 : (N : ℝ)⁻¹ * 2 ^ Delta.card *
      (∑ x : ZMod N,
        ‖smoothedProbabilityWeight V S k x - probabilityWeight S x‖) ≤ 1) :
    LocallyDissociated S Delta (Real.log 4) := by
  apply locallyDissociated_of_spectral_smoothing S
    (CyclicChang.relativeLargeSpectrum V eta) Delta hS hDelta
    (smoothedProbabilityWeight V S k) (pow_nonneg heta k)
  · exact fourier_smoothedProbabilityWeight_zero hV hS k
  · intro r hr
    exact norm_fourier_smoothedProbabilityWeight_le_pow_of_not_mem
      hV hS k heta hr
  · exact hthetaCard
  · exact hL1

theorem locallyDissociated_of_narrow_dilate
    (B : CyclicBohr.Set N) (S V Delta : Finset (ZMod N))
    (hS : S.Nonempty) (hVnonempty : V.Nonempty)
    {rho delta epsilon eta : ℝ} (hrho : 0 ≤ rho)
    (heta : 0 ≤ eta)
    (hscale : (Delta.card : ℝ) * rho ≤ delta)
    (hV : V ⊆ (B.dilate rho).carrier)
    (hstable : ∀ z ∈ B.dilate delta,
      (Finset.expect Finset.univ fun x : ZMod N ↦
        |CyclicBohr.uniformWeight S (x - z) -
          CyclicBohr.uniformWeight S x|) ≤ epsilon)
    (hDelta : SpectrallyDissociated
      (CyclicChang.relativeLargeSpectrum V eta) Delta)
    (hetaCard : eta ^ Delta.card * 2 ^ Delta.card ≤ 1)
    (hepsilonCard : 2 ^ Delta.card * epsilon ≤ 1) :
    LocallyDissociated S Delta (Real.log 4) := by
  apply locallyDissociated_of_narrow_convolution S V Delta hS hVnonempty
    Delta.card heta hDelta hetaCard
  have hnormalized :=
    expect_abs_smoothedProbabilityWeight_sub_le_of_dilate
      B V S hVnonempty Delta.card hrho hscale hV hstable
  calc
    (N : ℝ)⁻¹ * 2 ^ Delta.card *
        ∑ x : ZMod N,
          ‖smoothedProbabilityWeight V S Delta.card x -
            probabilityWeight S x‖ =
        2 ^ Delta.card *
          ((N : ℝ)⁻¹ *
            ∑ x : ZMod N,
              ‖smoothedProbabilityWeight V S Delta.card x -
                probabilityWeight S x‖) := by ring
    _ ≤ 2 ^ Delta.card * epsilon := by
      exact mul_le_mul_of_nonneg_left hnormalized (by positivity)
    _ ≤ 1 := hepsilonCard

lemma one_third_pow_mul_two_pow_le_one (d : ℕ) :
    (1 / 3 : ℝ) ^ d * 2 ^ d ≤ 1 := by
  rw [← mul_pow]
  norm_num
  exact pow_le_one₀ (by norm_num) (by norm_num)

end CyclicLocalRieszSmoothing
end Erdos721
