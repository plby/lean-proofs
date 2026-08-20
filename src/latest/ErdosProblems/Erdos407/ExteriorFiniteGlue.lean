/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.ExteriorEndpoint

/-!
# Finite glue for the exterior-power endpoint

This file contains only the finite and order-theoretic part of the last
step in the rational three-place Subspace Theorem.  Its inputs from the
analytic argument are deliberately narrow: bounded ranks, a finite family
of exterior spans, and membership of each sufficiently large point in a
recovered original subspace.

The first section constructs the actual finite logarithmic labels used for
the original approximation boxes.  The remaining sections record finite
pigeonholing, the choice of a least adjacent-ratio index, Pluecker recovery
from finitely many exterior spans, and absorption of the bounded-height
exceptional points.
-/

namespace Erdos407.PadicSubspace.ExteriorFiniteGlue

open scoped BigOperators ExteriorAlgebra

open Erdos407
open HeightBoxes
open ExteriorEndpoint

/-! ## A uniform cutoff and finite labels for the original local exponents -/

/-- One height cutoff which dominates the cutoffs of every form at all
three places.  The outer `max` keeps the cutoff at least two even in the
zero-dimensional totalization. -/
noncomputable def localFormsHeightCutoff {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : ℕ :=
  max 2 <| Finset.univ.sup fun v : Place23 ↦
    Finset.univ.sup fun i : Fin n ↦ linearFormHeightCutoff (L v i)

theorem two_le_localFormsHeightCutoff {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    2 ≤ localFormsHeightCutoff L :=
  le_max_left _ _

theorem linearFormHeightCutoff_le_localFormsHeightCutoff {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23) (i : Fin n) :
    linearFormHeightCutoff (L v i) ≤ localFormsHeightCutoff L := by
  apply le_trans _ (le_max_right 2 _)
  apply Finset.le_sup_of_le (Finset.mem_univ v)
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j : Fin n ↦ linearFormHeightCutoff (L v j))
    (Finset.mem_univ i)

/-- Above the uniform cutoff, every nonzero local form value has normalized
logarithm in the fixed interval `[-5,2]`. -/
theorem localConstant_mem_Icc_of_largeHeight {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : IntVector n) (hx : x ≠ 0)
    (hLx : ∀ v i, L v i (intCastVec x) ≠ 0)
    (hlarge : localFormsHeightCutoff L ≤ boxHeight x) :
    ∀ v i, localConstant L (boxHeight x : ℝ) (intCastVec x) v i ∈
      Set.Icc (-5 : ℝ) 2 := by
  intro v i
  have hcut : linearFormHeightCutoff (L v i) ≤ boxHeight x :=
    (linearFormHeightCutoff_le_localFormsHeightCutoff L v i).trans hlarge
  have h := localConstant_fixedForm_mem_Icc
    (L v i) x hx (hLx v i) hcut v i
  simpa [localConstant] using h

/-- The finite type of simultaneous local logarithmic-box labels. -/
abbrev LocalBoxLabel (n : ℕ) (eta : ℝ) :=
  Place23 → Fin n → BoundedLogBox eta (-5) 2

/-- The label of a point all of whose local constants lie in `[-5,2]`. -/
noncomputable def localBoxLabelOf {n : ℕ} {eta : ℝ} (heta : 0 < eta)
    {L : Place23 → Fin n → RatLinearForm n} {H : ℝ} {x : RatVector n}
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2) :
    LocalBoxLabel n eta :=
  fun v i ↦ boundedLogBoxOf heta (hrange v i)

/-- The upper endpoint of every half-open logarithmic box in a label. -/
noncomputable def upperLocalConstants {n : ℕ} {eta : ℝ}
    (b : LocalBoxLabel n eta) : LocalConstants n :=
  fun v i ↦ (((b v i).1 : ℝ) + 1) * eta

theorem localConstant_lt_upperLocalConstants {n : ℕ} {eta : ℝ}
    (heta : 0 < eta)
    {L : Place23 → Fin n → RatLinearForm n} {H : ℝ} {x : RatVector n}
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2)
    (v : Place23) (i : Fin n) :
    localConstant L H x v i <
      upperLocalConstants (localBoxLabelOf heta hrange) v i := by
  change localConstant L H x v i <
    (((logBoxIndex eta (localConstant L H x v i) : ℤ) : ℝ) + 1) * eta
  exact logBoxIndex_upper (t := localConstant L H x v i) heta

theorem upperLocalConstants_le_localConstant_add {n : ℕ} {eta : ℝ}
    (heta : 0 < eta)
    {L : Place23 → Fin n → RatLinearForm n} {H : ℝ} {x : RatVector n}
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2)
    (v : Place23) (i : Fin n) :
    upperLocalConstants (localBoxLabelOf heta hrange) v i ≤
      localConstant L H x v i + eta := by
  have hlo := logBoxIndex_lower
    (t := localConstant L H x v i) heta
  change ((((logBoxIndex eta (localConstant L H x v i) : ℤ) : ℝ) + 1) * eta) ≤
    localConstant L H x v i + eta
  rw [add_mul, one_mul]
  simpa [add_comm] using add_le_add_right hlo eta

/-- Rounding to the upper endpoints of the finite local boxes produces an
approximation box containing the point. -/
theorem mem_upperLocalConstants_approximationBox {n : ℕ} {eta H : ℝ}
    (heta : 0 < eta) (hH : 1 < H)
    (L : Place23 → Fin n → RatLinearForm n) (x : RatVector n)
    (hpos : ∀ v i, 0 < realPlaceNorm v (L v i x))
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2) :
    InApproximationBox L H
      (upperLocalConstants (localBoxLabelOf heta hrange)) x := by
  apply mem_approximationBox_of_localConstant_le (η := eta) L hH x _ hpos
  intro v i
  exact (localConstant_lt_upperLocalConstants heta hrange v i).le

/-- The total exponent of the upper-endpoint box loses at most one mesh in
each of the at most fifteen local coordinates. -/
theorem sum_upperLocalConstants_le_neg_one_add {n : ℕ} (hn : n ≤ 5)
    {eta H : ℝ} (heta : 0 < eta)
    {L : Place23 → Fin n → RatLinearForm n} {x : RatVector n}
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2)
    (hsum : (∑ v, ∑ i, localConstant L H x v i) ≤ -1) :
    (∑ v, ∑ i, upperLocalConstants (localBoxLabelOf heta hrange) v i) ≤
      -1 + 15 * eta := by
  apply sum_le_of_local_error hn heta.le hsum
  intro v i
  exact upperLocalConstants_le_localConstant_add heta hrange v i

/-- The mesh used for the original dimension-at-most-five boxing. -/
noncomputable def originalBoxingMesh : ℝ := 1 / 60

theorem originalBoxingMesh_pos : 0 < originalBoxingMesh := by
  norm_num [originalBoxingMesh]

/-- With mesh `1/60`, the rounded total exponent is at most `-3/4`. -/
theorem sum_upperLocalConstants_le_neg_three_quarters {n : ℕ}
    (hn : n ≤ 5)
    {H : ℝ} {L : Place23 → Fin n → RatLinearForm n} {x : RatVector n}
    (hrange : ∀ v i, localConstant L H x v i ∈ Set.Icc (-5 : ℝ) 2)
    (hsum : (∑ v, ∑ i, localConstant L H x v i) ≤ -1) :
    (∑ v, ∑ i,
      upperLocalConstants
        (localBoxLabelOf originalBoxingMesh_pos hrange) v i) ≤ -(3 / 4 : ℝ) := by
  have h := sum_upperLocalConstants_le_neg_one_add hn
    originalBoxingMesh_pos hrange hsum
  norm_num [originalBoxingMesh] at h ⊢
  exact h

theorem realLocalFormProduct_eq_cast_localFormProduct {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : RatVector n) :
    realLocalFormProduct L x = (localFormProduct L x : ℝ) := by
  simp [realLocalFormProduct, realPlaceNorm, localFormProduct]

/-- Every sufficiently large strong integral point with nonzero local form
values belongs to one of the fixed finite upper-endpoint boxes, and that box
retains a uniform negative exponent sum. -/
theorem exists_originalLocalBox_of_large_strongPoint {n : ℕ}
    (hn : n ≤ 5) (L : Place23 → Fin n → RatLinearForm n)
    (x : IntVector n) (hx : x ≠ 0)
    (hLx : ∀ v i, L v i (intCastVec x) ≠ 0)
    (hlarge : localFormsHeightCutoff L ≤ boxHeight x)
    (hstrong : SatisfiesStrongInequality L x) :
    ∃ b : LocalBoxLabel n originalBoxingMesh,
      InApproximationBox L (boxHeight x : ℝ) (upperLocalConstants b)
        (intCastVec x) ∧
      (∑ v, ∑ i, upperLocalConstants b v i) ≤ -(3 / 4 : ℝ) := by
  have hrange := localConstant_mem_Icc_of_largeHeight L x hx hLx hlarge
  let b : LocalBoxLabel n originalBoxingMesh :=
    localBoxLabelOf originalBoxingMesh_pos hrange
  refine ⟨b, ?_, ?_⟩
  · have hH : (1 : ℝ) < boxHeight x := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2)
        ((two_le_localFormsHeightCutoff L).trans hlarge))
    have hpos : ∀ v i,
        0 < realPlaceNorm v (L v i (intCastVec x)) := by
      intro v i
      unfold realPlaceNorm
      exact_mod_cast (placeNorm_pos_iff v (L v i (intCastVec x))).2 (hLx v i)
    exact mem_upperLocalConstants_approximationBox
      originalBoxingMesh_pos hH L (intCastVec x) hpos hrange
  · apply sum_upperLocalConstants_le_neg_three_quarters hn hrange
    have hH : (1 : ℝ) < boxHeight x := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2)
        ((two_le_localFormsHeightCutoff L).trans hlarge))
    have hpos : ∀ v i,
        0 < realPlaceNorm v (L v i (intCastVec x)) := by
      intro v i
      unfold realPlaceNorm
      exact_mod_cast (placeNorm_pos_iff v (L v i (intCastVec x))).2 (hLx v i)
    apply sum_localConstant_le_neg_one L hH (intCastVec x) hpos
    rw [realLocalFormProduct_eq_cast_localFormProduct]
    exact_mod_cast hstrong

/-- Total form of the original finite boxing: a large strong point either
lies on one of the finitely many fixed form kernels, or enters a labelled
box with exponent sum at most `-3/4`. -/
theorem zeroLocalForm_or_exists_originalLocalBox {n : ℕ}
    (hn : n ≤ 5) (L : Place23 → Fin n → RatLinearForm n)
    (x : IntVector n) (hx : x ≠ 0)
    (hlarge : localFormsHeightCutoff L ≤ boxHeight x)
    (hstrong : SatisfiesStrongInequality L x) :
    (∃ v i, L v i (intCastVec x) = 0) ∨
      ∃ b : LocalBoxLabel n originalBoxingMesh,
        InApproximationBox L (boxHeight x : ℝ) (upperLocalConstants b)
          (intCastVec x) ∧
        (∑ v, ∑ i, upperLocalConstants b v i) ≤ -(3 / 4 : ℝ) := by
  classical
  by_cases hzero : ∃ v i, L v i (intCastVec x) = 0
  · exact Or.inl hzero
  · right
    apply exists_originalLocalBox_of_large_strongPoint hn L x hx
    · push Not at hzero
      exact hzero
    · exact hlarge
    · exact hstrong

/-! ## Finite pigeonholing of exponent boxes and bounded ranks -/

/-- Simultaneously stabilize a finite box label and a natural-valued rank
bounded by `N` on an infinite set. -/
theorem exists_infinite_fiber_box_and_rank {alpha kappa : Type*} [Finite kappa]
    {X : Set alpha} (hX : X.Infinite) (box : alpha → kappa)
    (rank : alpha → ℕ) (N : ℕ) (hrank : ∀ x ∈ X, rank x ≤ N) :
    ∃ b : kappa, ∃ R : ℕ, R ≤ N ∧
      {x | x ∈ X ∧ box x = b ∧ rank x = R}.Infinite := by
  classical
  let rankLabel : X → Fin (N + 1) := fun x ↦ ⟨rank x.1, by
    have hx := hrank x.1 x.2
    omega⟩
  let label : X → kappa × Fin (N + 1) := fun x ↦ ⟨box x.1, rankLabel x⟩
  let _ : Infinite X := hX.to_subtype
  obtain ⟨p, hp⟩ := HeightBoxes.exists_infinite_fiber
    (Set.univ : Set X) Set.infinite_univ label
  refine ⟨p.1, p.2.1, Nat.le_of_lt_succ p.2.2, ?_⟩
  have hsub :
      ((fun x : X ↦ x.1) '' {x : X | x ∈ Set.univ ∧ label x = p}) ⊆
        {x | x ∈ X ∧ box x = p.1 ∧ rank x = p.2.1} := by
    rintro x ⟨y, hy, rfl⟩
    have hlabel : label y = p := hy.2
    have hbox : box y.1 = p.1 := congrArg Prod.fst hlabel
    have hr : rank y.1 = p.2.1 := by
      have := congrArg (fun z ↦ z.2.1) hlabel
      exact this
    exact ⟨y.2, hbox, hr⟩
  apply (hp.image Subtype.val_injective.injOn).mono hsub

/-! ## A least adjacent-ratio index -/

/-- A nonempty finite interval of adjacent indices has an index minimizing
any linearly ordered ratio statistic.  The use of `Fin (m+1)` matches a
successive-minima list with `m` adjacent ratios. -/
theorem exists_min_adjacentIndex {m : ℕ} (hm : 0 < m)
    (ratio : Fin m → ℝ) :
    ∃ k : Fin m, ∀ i : Fin m, ratio k ≤ ratio i := by
  classical
  obtain ⟨k, hk, hkmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin m)) ratio
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact ⟨k, fun i ↦ hkmin i (Finset.mem_univ i)⟩

/-- The preceding argmin packaged for adjacent quotients of a positive
successive-minima sequence. -/
theorem exists_min_adjacentRatio {m : ℕ} (hm : 0 < m)
    (mu : Fin (m + 1) → ℝ) :
    ∃ k : Fin m, ∀ i : Fin m,
      mu k.succ / mu k.castSucc ≤ mu i.succ / mu i.castSucc :=
  exists_min_adjacentIndex hm (fun i ↦ mu i.succ / mu i.castSucc)

/-- Argmin on a nonempty closed interval of adjacent indices.  This is the
form used after the rank `R` has stabilized and only gaps in a prescribed
tail (or subinterval) may be selected. -/
theorem exists_min_adjacentRatio_on_interval {m lo hi : ℕ}
    (hlo : lo < m) (hlohi : lo ≤ hi)
    (mu : Fin (m + 1) → ℝ) :
    ∃ k : Fin m, lo ≤ k.1 ∧ k.1 ≤ hi ∧
      ∀ i : Fin m, lo ≤ i.1 → i.1 ≤ hi →
        mu k.succ / mu k.castSucc ≤ mu i.succ / mu i.castSucc := by
  classical
  let candidates : Finset (Fin m) :=
    Finset.univ.filter fun i ↦ lo ≤ i.1 ∧ i.1 ≤ hi
  have hloMem : (⟨lo, hlo⟩ : Fin m) ∈ candidates := by
    simp [candidates, hlohi]
  obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image candidates
    (fun i ↦ mu i.succ / mu i.castSucc) ⟨_, hloMem⟩
  have hk' : lo ≤ k.1 ∧ k.1 ≤ hi :=
    Finset.mem_filter.mp hk |>.2
  refine ⟨k, hk'.1, hk'.2, ?_⟩
  intro i hili hihi
  exact hkmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hili, hihi⟩)

/-! ## Finite Pluecker recovery and bounded-height completion -/

/-- A basis-complement subspace recovered from a positive exterior degree
is proper. -/
theorem basisComplementSubspace_lt_top {n q : ℕ}
    {v : Fin n → Fin n → ℚ} (hv : LinearIndependent ℚ v)
    (hq : 0 < q) (J : Set.powersetCard (Fin n) q) :
    basisComplementSubspace v J < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hdim := finrank_basisComplementSubspace hv J
  rw [htop] at hdim
  have hqn : q ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ J.1)
    simpa [J.2] using this
  simp at hdim
  omega

/-- A finite family of exterior spans recovers only finitely many proper
original subspaces; if those subspaces cover every point above a cutoff,
the bounded-height remainder can be added without any analytic input. -/
theorem finiteCover_of_finite_exteriorSpans {n q H : ℕ}
    (hn : 2 ≤ n) (hq : 0 < q)
    {C : Set (Submodule ℚ (⋀[ℚ]^q (Fin n → ℚ)))} (hC : C.Finite)
    {X : Set (IntVector n)} (hzero : (0 : IntVector n) ∉ X)
    (hcover : ∀ x ∈ X, H < boxHeight x →
      ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
        ∃ J : Set.powersetCard (Fin n) q,
          omittedExteriorSpan v J ∈ C ∧
          intCastVec x ∈ basisComplementSubspace v J) :
    HasFiniteHyperplaneCover X := by
  let R : Set (Submodule ℚ (Fin n → ℚ)) :=
    {W | ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
      ∃ J : Set.powersetCard (Fin n) q,
        W = basisComplementSubspace v J ∧ omittedExteriorSpan v J ∈ C}
  have hR : R.Finite := by
    apply finite_basisComplementSubspaces_of_finite_exteriorSpans
      (E := Fin n → ℚ) (n := n) (q := q)
    · simp
    · exact hq
    · exact hC
  have habove : HasFiniteHyperplaneCover
      {x | x ∈ X ∧ H < boxHeight x} := by
    apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces hR
    · intro W hWR
      obtain ⟨v, hv, J, rfl, hJC⟩ := hWR
      exact basisComplementSubspace_lt_top hv hq J
    · intro x hx
      obtain ⟨v, hv, J, hJC, hxW⟩ := hcover x hx.1 hx.2
      refine ⟨basisComplementSubspace v J, ?_, hxW⟩
      exact ⟨v, hv, J, rfl, hJC⟩
  exact hasFiniteHyperplaneCover_of_above hn hzero habove

/-- Fully abstract finite-label form of the same last step.  A label may
bundle the stabilized rank, the minimizing adjacent-ratio index, an exponent
box, and a member of a finite exterior-span family. -/
theorem finiteCover_of_finite_recoveredSpace_labels {n H : ℕ}
    (hn : 2 ≤ n) {kappa : Type*} [Finite kappa]
    (recover : kappa → Submodule ℚ (Fin n → ℚ))
    (hproper : ∀ a, recover a < ⊤)
    {X : Set (IntVector n)} (hzero : (0 : IntVector n) ∉ X)
    (hcover : ∀ x ∈ X, H < boxHeight x →
      ∃ a, intCastVec x ∈ recover a) :
    HasFiniteHyperplaneCover X := by
  let C : Set (Submodule ℚ (Fin n → ℚ)) := Set.range recover
  have hC : C.Finite := Set.toFinite C
  have habove : HasFiniteHyperplaneCover
      {x | x ∈ X ∧ H < boxHeight x} := by
    apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces hC
    · rintro W ⟨a, rfl⟩
      exact hproper a
    · intro x hx
      obtain ⟨a, hxa⟩ := hcover x hx.1 hx.2
      exact ⟨recover a, ⟨a, rfl⟩, hxa⟩
  exact hasFiniteHyperplaneCover_of_above hn hzero habove

/-- Final finite-union form used after logarithmic boxing.  Vanishing local
form values are handled by the fixed finite family of form kernels; every
remaining large point is required only to belong to one recovered space
from a finite label type.  The bounded-height remainder is then automatic. -/
theorem finiteCover_of_zeroLocalForm_or_finiteRecoveredSpace_labels
    {n H : ℕ} (hn : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : ∀ v i, L v i ≠ 0)
    {kappa : Type*} [Finite kappa]
    (recover : kappa → Submodule ℚ (Fin n → ℚ))
    (hproper : ∀ a, recover a < ⊤)
    {X : Set (IntVector n)} (hzeroX : (0 : IntVector n) ∉ X)
    (hcover : ∀ x ∈ X, H < boxHeight x →
      (∃ v i, L v i (intCastVec x) = 0) ∨
        ∃ a, intCastVec x ∈ recover a) :
    HasFiniteHyperplaneCover X := by
  let Z : Set (IntVector n) :=
    {x | x ∈ X ∧ H < boxHeight x ∧
      ∃ v i, L v i (intCastVec x) = 0}
  let R : Set (IntVector n) :=
    {x | x ∈ X ∧ H < boxHeight x ∧
      ¬ ∃ v i, L v i (intCastVec x) = 0}
  have hZ : HasFiniteHyperplaneCover Z :=
    (zeroLocalForm_hasFiniteHyperplaneCover L hL).mono fun x hx ↦ hx.2.2
  have hR : HasFiniteHyperplaneCover R := by
    let C : Set (Submodule ℚ (Fin n → ℚ)) := Set.range recover
    apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces
      (Set.toFinite C)
    · rintro W ⟨a, rfl⟩
      exact hproper a
    · intro x hx
      rcases hcover x hx.1 hx.2.1 with hxform | ⟨a, hxa⟩
      · exact (hx.2.2 hxform).elim
      · exact ⟨recover a, ⟨a, rfl⟩, hxa⟩
  have habove : HasFiniteHyperplaneCover
      {x | x ∈ X ∧ H < boxHeight x} := by
    apply (hZ.union hR).mono
    intro x hx
    by_cases hxform : ∃ v i, L v i (intCastVec x) = 0
    · exact Or.inl ⟨hx.1, hx.2, hxform⟩
    · exact Or.inr ⟨hx.1, hx.2, hxform⟩
  exact hasFiniteHyperplaneCover_of_above hn hzeroX habove

#print axioms exists_originalLocalBox_of_large_strongPoint
#print axioms zeroLocalForm_or_exists_originalLocalBox
#print axioms exists_infinite_fiber_box_and_rank
#print axioms exists_min_adjacentRatio
#print axioms exists_min_adjacentRatio_on_interval
#print axioms finiteCover_of_finite_exteriorSpans
#print axioms finiteCover_of_finite_recoveredSpace_labels
#print axioms finiteCover_of_zeroLocalForm_or_finiteRecoveredSpace_labels

end Erdos407.PadicSubspace.ExteriorFiniteGlue
