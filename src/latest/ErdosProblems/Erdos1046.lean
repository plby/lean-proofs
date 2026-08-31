/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1046.
https://www.erdosproblems.com/forum/thread/1046

Informal authors:
- Christian Pommerenke

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1046.md
-/
/-
Copyright (c) 2026 The LeanProofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The LeanProofs contributors
-/
import ErdosProblems.Erdos1046.Erdos1046Jensen

/-!
# Erdős Problem 1046

Pommerenke's theorem that the connected open lemniscate of a monic complex
polynomial is contained in a disk of radius `2`.
-/

open Filter MeasureTheory Metric Polynomial Real Set Topology
open scoped BigOperators ComplexConjugate

namespace Erdos1046

/-- The open unit lemniscate of a complex polynomial. -/
def lemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ < 1}

/-- The corresponding closed unit lemniscate. -/
def closedLemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ ≤ 1}

/-- The centroid of the roots, counted with multiplicity. -/
noncomputable def rootCentroid (f : ℂ[X]) : ℂ :=
  f.roots.sum / (f.natDegree : ℂ)

lemma isOpen_lemniscate (f : ℂ[X]) : IsOpen (lemniscate f) := by
  exact isOpen_lt (continuous_norm.comp f.continuous) continuous_const

lemma open_subset_ball_of_subset_closedBall {s : Set ℂ} {c : ℂ}
    (hs : IsOpen s) (hsub : s ⊆ Metric.closedBall c 2) :
    s ⊆ Metric.ball c 2 := by
  rw [← interior_closedBall c (by norm_num : (2 : ℝ) ≠ 0)]
  exact interior_maximal hsub hs

lemma natDegree_pos_of_isConnected_lemniscate (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) : 0 < f.natDegree := by
  rw [Nat.pos_iff_ne_zero]
  intro hdeg
  have hone : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hdeg
  have hempty : lemniscate f = ∅ := by
    ext z
    simp [lemniscate, hone]
  rw [hempty] at hE
  exact Set.not_nonempty_empty hE.nonempty

lemma card_roots_eq_natDegree (f : ℂ[X]) : f.roots.card = f.natDegree := by
  exact (IsAlgClosed.splits f).natDegree_eq_card_roots.symm

lemma eval_eq_prod_roots_of_monic (f : ℂ[X]) (hf : f.Monic) (z : ℂ) :
    f.eval z = (f.roots.map fun a => z - a).prod := by
  exact (IsAlgClosed.splits f).eval_eq_prod_roots_of_monic hf z

lemma rootCentroid_eq_neg_nextCoeff_div_natDegree (f : ℂ[X]) (hf : f.Monic) :
    rootCentroid f = -f.nextCoeff / (f.natDegree : ℂ) := by
  rw [rootCentroid, (IsAlgClosed.splits f).nextCoeff_eq_neg_sum_roots_of_monic hf]
  simp

lemma sum_projected_roots (f : ℂ[X]) (u : ℂ) :
    (f.roots.map fun z => (z * star u).re).sum = (f.roots.sum * star u).re := by
  let p : ℂ →+ ℝ :=
    { toFun := fun z => (z * star u).re
      map_zero' := by simp
      map_add' := by intro x y; simp [add_mul] }
  exact (map_multiset_sum p f.roots).symm

lemma projected_roots_average_eq (f : ℂ[X]) (u : ℂ) :
    (f.roots.map fun z => (z * star u).re).sum / (f.natDegree : ℝ) =
      (rootCentroid f * star u).re := by
  rw [sum_projected_roots, rootCentroid, div_mul_eq_mul_div]
  rw [show (f.natDegree : ℂ) = ((f.natDegree : ℝ) : ℂ) by norm_cast]
  rw [Complex.div_ofReal_re]

lemma projected_roots_average_eq_card (f : ℂ[X]) (u : ℂ) :
    (f.roots.map fun z => (z * star u).re).sum / (f.roots.card : ℝ) =
      (rootCentroid f * star u).re := by
  rw [card_roots_eq_natDegree]
  exact projected_roots_average_eq f u

/-- Orthogonal projection onto the real axis in the unit direction `u`. -/
def projection (u z : ℂ) : ℝ := (conj u * z).re

lemma continuous_projection (u : ℂ) : Continuous (projection u) := by
  exact Complex.continuous_re.comp (continuous_const.mul continuous_id)

lemma root_mem_lemniscate {f : ℂ[X]} (hf : f.Monic) {r : ℂ} (hr : r ∈ f.roots) :
    r ∈ lemniscate f := by
  have hr0 : f.eval r = 0 := (Polynomial.mem_roots hf.ne_zero).mp hr
  simp [lemniscate, hr0]

lemma isConnected_projection_image {f : ℂ[X]} (hE : IsConnected (lemniscate f)) (u : ℂ) :
    IsConnected (projection u '' lemniscate f) := by
  exact hE.image _ (continuous_projection u).continuousOn

lemma projection_sub_le_norm (u w r : ℂ) (hu : ‖u‖ = 1) :
    |projection u w - projection u r| ≤ ‖w - r‖ := by
  calc
    |projection u w - projection u r| = |(conj u * (w - r)).re| := by
      simp only [projection, mul_sub, Complex.sub_re]
    _ ≤ ‖conj u * (w - r)‖ := Complex.abs_re_le_norm _
    _ = ‖w - r‖ := by simp [hu]

lemma projected_roots_product_le {f : ℂ[X]} (hf : f.Monic) (u w : ℂ) (hu : ‖u‖ = 1) :
    ‖∏ r ∈ f.roots.toFinset,
        (projection u w - projection u r) ^ (f.roots.count r)‖ ≤ ‖f.eval w‖ := by
  have hfactor :
      f.eval w = ∏ r ∈ f.roots.toFinset, (w - r) ^ (f.roots.count r) := by
    have hp : f = ∏ r ∈ f.roots.toFinset,
        (Polynomial.X - Polynomial.C r) ^ (f.roots.count r) := by
      convert (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
      simp [Finset.prod_multiset_map_count]
    simpa [Polynomial.eval_prod] using congr_arg (Polynomial.eval w) hp
  rw [hfactor]
  simp only [norm_prod, norm_pow, Real.norm_eq_abs]
  exact Finset.prod_le_prod (fun _ _ => pow_nonneg (abs_nonneg _) _) fun r hr =>
    pow_le_pow_left₀ (abs_nonneg _) (projection_sub_le_norm u w r hu) _

lemma projected_roots_product_lt_one_of_mem_image {f : ℂ[X]} (hf : f.Monic)
    (u : ℂ) (hu : ‖u‖ = 1) {t : ℝ} (ht : t ∈ projection u '' lemniscate f) :
    ‖∏ r ∈ f.roots.toFinset,
        (t - projection u r) ^ (f.roots.count r)‖ < 1 := by
  obtain ⟨w, hw, rfl⟩ := ht
  exact (projected_roots_product_le hf u w hu).trans_lt hw

lemma exists_projection_bracket {f : ℂ[X]} (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) {z : ℂ} (hz : z ∈ lemniscate f)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ A B : ℝ,
      A < B ∧
      A ∈ projection u '' lemniscate f ∧
      B ∈ projection u '' lemniscate f ∧
      Set.Icc A B ⊆ projection u '' lemniscate f ∧
      A < projection u z ∧ projection u z < B ∧
      ∀ r ∈ f.roots, A < projection u r ∧ projection u r < B := by
  let T : Finset ℝ := insert (projection u z) (f.roots.toFinset.image (projection u))
  have hT : T.Nonempty := ⟨projection u z, Finset.mem_insert_self _ _⟩
  have hT_image : ∀ t ∈ T, t ∈ projection u '' lemniscate f := by
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact ⟨z, hz, rfl⟩
    · rw [Finset.mem_image] at ht
      obtain ⟨r, hr, rfl⟩ := ht
      exact ⟨r, root_mem_lemniscate hf (Multiset.mem_toFinset.mp hr), rfl⟩
  let a : ℝ := T.min' hT
  let b : ℝ := T.max' hT
  have haT : a ∈ T := Finset.min'_mem T hT
  have hbT : b ∈ T := Finset.max'_mem T hT
  obtain ⟨wa, hwaE, hwa_proj⟩ := hT_image a haT
  obtain ⟨wb, hwbE, hwb_proj⟩ := hT_image b hbT
  have hopen : IsOpen (lemniscate f) := isOpen_lemniscate f
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hopen wa hwaE
  obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hopen wb hwbE
  let A : ℝ := a - εa / 2
  let B : ℝ := b + εb / 2
  let wa' : ℂ := wa - u * (εa / 2 : ℝ)
  let wb' : ℂ := wb + u * (εb / 2 : ℝ)
  have hwa'E : wa' ∈ lemniscate f := by
    apply hballa
    calc
      dist wa' wa = εa / 2 := by simp [wa', hu, abs_of_pos hεa]
      _ < εa := half_lt_self hεa
  have hwb'E : wb' ∈ lemniscate f := by
    apply hballb
    calc
      dist wb' wb = εb / 2 := by simp [wb', hu, abs_of_pos hεb]
      _ < εb := half_lt_self hεb
  have hproj_wa' : projection u wa' = A := by
    dsimp [A]
    rw [← hwa_proj]
    simp [wa', projection, mul_sub, ← mul_assoc, Complex.conj_mul', hu]
  have hproj_wb' : projection u wb' = B := by
    dsimp [B]
    rw [← hwb_proj]
    simp [wb', projection, mul_add, ← mul_assoc, Complex.conj_mul', hu]
  have hA_image : A ∈ projection u '' lemniscate f := ⟨wa', hwa'E, hproj_wa'⟩
  have hB_image : B ∈ projection u '' lemniscate f := ⟨wb', hwb'E, hproj_wb'⟩
  have hA_lt_all : ∀ t ∈ T, A < t := by
    intro t ht
    have hat : a ≤ t := Finset.min'_le T t ht
    dsimp [A]
    exact (sub_lt_self a (half_pos hεa)).trans_le hat
  have hall_lt_B : ∀ t ∈ T, t < B := by
    intro t ht
    have htb : t ≤ b := Finset.le_max' T t ht
    dsimp [B]
    exact htb.trans_lt (lt_add_of_pos_right b (half_pos hεb))
  have hzT : projection u z ∈ T := Finset.mem_insert_self _ _
  have hAz : A < projection u z := hA_lt_all _ hzT
  have hzB : projection u z < B := hall_lt_B _ hzT
  refine ⟨A, B, hAz.trans hzB, hA_image, hB_image,
    (isConnected_projection_image hE u).Icc_subset hA_image hB_image,
    hAz, hzB, ?_⟩
  intro r hr
  have hrT : projection u r ∈ T := by
    rw [Finset.mem_insert]
    right
    exact Finset.mem_image.mpr ⟨r, Multiset.mem_toFinset.mpr hr, rfl⟩
  exact ⟨hA_lt_all _ hrT, hall_lt_B _ hrT⟩

lemma fin_prod_multiset_occurrences {α β : Type*} [DecidableEq α] [CommMonoid β]
    (m : Multiset α) (g : α → β) :
    (∏ i : Fin (Fintype.card m), g (((Fintype.equivFin m).symm i : m) : α)) =
      (m.map g).prod := by
  calc
    _ = ∏ j : m, g (j : α) :=
      Fintype.prod_equiv (Fintype.equivFin m).symm _ _ (fun _ => rfl)
    _ = _ := by
      change ((Finset.univ : Finset m).val.map (fun j : m => g (j : α))).prod = _
      exact congrArg Multiset.prod (Multiset.map_univ m g)

lemma fin_sum_multiset_occurrences {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (m : Multiset α) (g : α → β) :
    (∑ i : Fin (Fintype.card m), g (((Fintype.equivFin m).symm i : m) : α)) =
      (m.map g).sum := by
  calc
    _ = ∑ j : m, g (j : α) :=
      Fintype.sum_equiv (Fintype.equivFin m).symm _ _ (fun _ => rfl)
    _ = _ := by
      change ((Finset.univ : Finset m).val.map (fun j : m => g (j : α))).sum = _
      exact congrArg Multiset.sum (Multiset.map_univ m g)

/-- The one-dimensional estimate after projecting the connected lemniscate in a unit
direction.  Roots are enumerated with multiplicity by the type associated to `f.roots`. -/
lemma projection_sub_centroid_le_two (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) {z : ℂ} (hz : z ∈ lemniscate f)
    (u : ℂ) (hu : ‖u‖ = 1) :
    projection u z - projection u (rootCentroid f) ≤ 2 := by
  obtain ⟨A, B, hAB, hA, hB, hIcc, hAz, hzB, hroots⟩ :=
    exists_projection_bracket hf hE hz u hu
  let e : Fin (Fintype.card f.roots) ≃ f.roots := (Fintype.equivFin f.roots).symm
  let x : Fin (Fintype.card f.roots) → ℝ := fun i ↦ projection u (e i : ℂ)
  have hn : 0 < Fintype.card f.roots := by
    simpa using (show 0 < f.roots.card by
      rw [card_roots_eq_natDegree]
      exact natDegree_pos_of_isConnected_lemniscate f hf hE)
  have hx : ∀ i, x i ∈ Icc A B := by
    intro i
    have hi := hroots (e i : ℂ) (Multiset.coe_mem (x := e i))
    exact ⟨hi.1.le, hi.2.le⟩
  have hbound : ∀ y ∈ Icc A B, ∏ i, |y - x i| ≤ 1 := by
    intro y hy
    have hlt := projected_roots_product_lt_one_of_mem_image hf u hu (hIcc hy)
    apply le_of_lt
    calc
      (∏ i, |y - x i|) =
          (f.roots.map fun r ↦ |y - projection u r|).prod := by
            simpa [x, e] using
              fin_prod_multiset_occurrences f.roots (fun r ↦ |y - projection u r|)
      _ = ∏ r ∈ f.roots.toFinset,
          |y - projection u r| ^ f.roots.count r :=
            Finset.prod_multiset_map_count f.roots _
      _ = ‖∏ r ∈ f.roots.toFinset,
          (y - projection u r) ^ f.roots.count r‖ := by
            simp only [norm_prod, norm_pow, Real.norm_eq_abs]
      _ < 1 := hlt
  have hend := JensenWeight.right_endpoint_sub_average_le_two hn hAB x hx hbound
  have hsum : (∑ i, x i) =
      (f.roots.map fun r ↦ projection u r).sum := by
    simpa [x, e] using
      fin_sum_multiset_occurrences f.roots (fun r ↦ projection u r)
  have hmean : (∑ i, x i) / (Fintype.card f.roots : ℝ) =
      projection u (rootCentroid f) := by
    rw [hsum]
    simpa [projection, mul_comm] using projected_roots_average_eq_card f u
  rw [hmean] at hend
  linarith

/-- Pommerenke's stronger conclusion with the center fixed to be the centroid of the roots. -/
theorem pommerenke_centroid_closed_bound (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) :
    lemniscate f ⊆ Metric.closedBall (rootCentroid f) 2 := by
  intro z hz
  by_cases hzc : z = rootCentroid f
  · simp [hzc]
  · let d : ℂ := z - rootCentroid f
    have hd : d ≠ 0 := by simpa [d, sub_ne_zero] using hzc
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
    let u : ℂ := d / (‖d‖ : ℂ)
    have hu : ‖u‖ = 1 := by
      simp [u, hdnorm.ne']
    have hproj : projection u z - projection u (rootCentroid f) = ‖d‖ := by
      rw [show projection u z - projection u (rootCentroid f) =
          (conj u * d).re by simp [projection, d, mul_sub]]
      dsimp [u]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
        sub_neg_eq_add]
      have hre : (d / (‖d‖ : ℂ)).re = d.re / ‖d‖ := by
        exact Complex.div_ofReal_re d ‖d‖
      have him : (d / (‖d‖ : ℂ)).im = d.im / ‖d‖ := by
        exact Complex.div_ofReal_im d ‖d‖
      rw [hre, him]
      have hs : d.re * d.re + d.im * d.im = ‖d‖ ^ 2 := by
        rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
      field_simp [hdnorm.ne']
      nlinarith
    have hle := projection_sub_centroid_le_two f hf hE hz u hu
    rw [hproj] at hle
    simpa [mem_closedBall, dist_eq_norm, d] using hle

/-- The open lemniscate lies in the open radius-two disk centered at the root centroid. -/
theorem pommerenke_centroid_bound (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) :
    lemniscate f ⊆ Metric.ball (rootCentroid f) 2 :=
  open_subset_ball_of_subset_closedBall (isOpen_lemniscate f)
    (pommerenke_centroid_closed_bound f hf hE)

/-- Erdős Problem 1046: every connected monic polynomial lemniscate is contained in a disk
of radius two. -/
theorem erdos_1046 (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) :
    ∃ c : ℂ, lemniscate f ⊆ Metric.ball c 2 :=
  ⟨rootCentroid f, pommerenke_centroid_bound f hf hE⟩

end Erdos1046

#print axioms Erdos1046.erdos_1046
