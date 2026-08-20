/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos909.CuttingUpper
import ErdosProblems.Erdos909.RationalCoordinateUpper
import Mathlib.Order.Interval.Set.Infinite

/-!
# Rational grid skeletons

This file proves the dimension half of the rational-coordinate Nöbeling
construction without invoking a closed-sum theorem.  A finite union of
rational coordinate faces is represented by one `gridSkeleton Q r`: a point
belongs to it when at least `r` distinct coordinates take values in the
finite rational grids `Q i`.

At a skeleton `Q`, use boxes whose endpoints avoid every `Q i`.  A relative
frontier point has a coordinate equal to a new endpoint.  That coordinate
cannot be one of the old witnesses, so the frontier lies in the next
skeleton.  Inside the order-`k` Nöbeling set the `(k+1)`-st skeleton is empty.
Iterating the defining basis criterion for small inductive dimension gives
the desired upper bound directly.
-/

open Set Topology TopologicalSpace

namespace Erdos909.RationalSkeleton

open CuttingUpper RationalCoordinateUpper

/-- A full rational box in a finite real coordinate space. -/
def rationalBox {ι : Type*} (a b : ι → ℚ) : Set (ι → ℝ) :=
  Set.univ.pi fun i ↦ Set.Ioo (a i : ℝ) (b i : ℝ)

/-- Full rational boxes whose two endpoints in coordinate `i` avoid the
already-used finite grid `Q i`. -/
def avoidingRationalBoxBasis {ι : Type*} (Q : ι → Finset ℚ) :
    Set (Set (ι → ℝ)) :=
  {U | ∃ a b : ι → ℚ,
    (∀ i, a i < b i ∧ a i ∉ Q i ∧ b i ∉ Q i) ∧
      U = rationalBox a b}

/-- There is a rational point outside a prescribed finite set in every
nonempty real interval. -/
theorem exists_rat_not_mem_between (Q : Finset ℚ) {x y : ℝ} (hxy : x < y) :
    ∃ q : ℚ, q ∉ Q ∧ x < (q : ℝ) ∧ (q : ℝ) < y := by
  obtain ⟨q₀, hxq₀, hq₀y⟩ := exists_rat_btwn hxy
  obtain ⟨q₁, hq₀q₁, hq₁y⟩ := exists_rat_btwn hq₀y
  have hrat : q₀ < q₁ := by exact_mod_cast hq₀q₁
  obtain ⟨q, hqI, hqQ⟩ := (Set.Ioo_infinite hrat).exists_notMem_finite
    (Q.finite_toSet)
  have hq₀q : (q₀ : ℝ) < q := by exact_mod_cast hqI.1
  have hqq₁ : (q : ℝ) < q₁ := by exact_mod_cast hqI.2
  exact ⟨q, hqQ, hxq₀.trans hq₀q, hqq₁.trans hq₁y⟩

/-- Rational intervals avoiding a finite endpoint set still form a basis of
the real line. -/
def avoidingRationalIntervalBasis (Q : Finset ℚ) : Set (Set ℝ) :=
  {U | ∃ a b : ℚ, a < b ∧ a ∉ Q ∧ b ∉ Q ∧
    U = Set.Ioo (a : ℝ) (b : ℝ)}

theorem isTopologicalBasis_avoidingRationalIntervalBasis (Q : Finset ℚ) :
    IsTopologicalBasis (avoidingRationalIntervalBasis Q) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a, b, hab, haQ, hbQ, rfl⟩
    exact isOpen_Ioo
  · intro x U hxU hU
    obtain ⟨l, u, ⟨hlx, hxu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hxU)
    obtain ⟨a, haQ, hla, hax⟩ := exists_rat_not_mem_between Q hlx
    obtain ⟨b, hbQ, hxb, hbu⟩ := exists_rat_not_mem_between Q hxu
    refine ⟨Set.Ioo (a : ℝ) (b : ℝ), ?_, ⟨hax, hxb⟩, ?_⟩
    · exact ⟨a, b, (by exact_mod_cast hax.trans hxb), haQ, hbQ, rfl⟩
    · intro z hz
      exact hlu ⟨hla.trans hz.1, hz.2.trans hbu⟩

/-- In finitely many coordinates, full boxes from the endpoint-avoiding
one-dimensional bases form a basis. -/
theorem isTopologicalBasis_avoidingRationalBoxBasis
    {ι : Type*} [Finite ι] (Q : ι → Finset ℚ) :
    IsTopologicalBasis (avoidingRationalBoxBasis Q) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a, b, hab, rfl⟩
    apply isOpen_set_pi Set.finite_univ
    intro i _
    exact isOpen_Ioo
  · intro x U hxU hU
    rw [isOpen_pi_iff'] at hU
    obtain ⟨V, hV, hVU⟩ := hU x hxU
    have hchoice : ∀ i, ∃ W ∈ avoidingRationalIntervalBasis (Q i),
        x i ∈ W ∧ W ⊆ V i := by
      intro i
      exact (isTopologicalBasis_avoidingRationalIntervalBasis (Q i))
        |>.exists_subset_of_mem_open (hV i).2 (hV i).1
    choose W hWB hxW hWV using hchoice
    have hrepr : ∀ i, ∃ a b : ℚ,
        a < b ∧ a ∉ Q i ∧ b ∉ Q i ∧
          W i = Set.Ioo (a : ℝ) (b : ℝ) := by
      intro i
      exact hWB i
    choose a b hab haQ hbQ hW using hrepr
    refine ⟨rationalBox a b, ?_, ?_, ?_⟩
    · exact ⟨a, b, fun i ↦ ⟨hab i, haQ i, hbQ i⟩, rfl⟩
    · intro i _
      change x i ∈ Set.Ioo (a i : ℝ) (b i : ℝ)
      simpa only [← hW i] using hxW i
    · apply (Set.pi_mono fun i _ ↦ ?_).trans hVU
      intro z hz
      apply hWV i
      simpa only [hW i] using hz

theorem avoidingRationalBoxBasis_countable
    {ι : Type*} [Finite ι] (Q : ι → Finset ℚ) :
    (avoidingRationalBoxBasis Q).Countable := by
  classical
  let _ : Countable ι := inferInstance
  apply (Set.countable_range fun p : (ι → ℚ) × (ι → ℚ) ↦
    rationalBox p.1 p.2).mono
  rintro U ⟨a, b, hab, rfl⟩
  exact ⟨(a, b), rfl⟩

/-- Add the endpoints of a box to the coordinate grids. -/
def updateGrid {ι : Type*} (Q : ι → Finset ℚ) (a b : ι → ℚ) :
    ι → Finset ℚ :=
  fun i ↦ insert (a i) (insert (b i) (Q i))

/-- Points for which at least `r` distinct coordinates lie in the prescribed
finite rational grids. -/
def gridSkeleton {ι : Type*} (Q : ι → Finset ℚ) (r : ℕ) :
    Set (ι → ℝ) :=
  {x | ∃ I : Finset ι, I.card = r ∧
    ∀ i ∈ I, ∃ q ∈ Q i, (q : ℝ) = x i}

theorem gridSkeleton_zero {ι : Type*} (Q : ι → Finset ℚ) :
    gridSkeleton Q 0 = Set.univ := by
  ext x
  simp [gridSkeleton]

theorem gridSkeleton_subset_rationalCoordinatesAtLeast
    {ι : Type*} {Q : ι → Finset ℚ} {r : ℕ} :
    gridSkeleton Q r ⊆ rationalCoordinatesAtLeast r := by
  rintro x ⟨I, hI, hx⟩
  refine ⟨I, hI, ?_⟩
  intro i hi
  obtain ⟨q, hqQ, hq⟩ := hx i hi
  exact ⟨q, hq⟩

/-- Every frontier point of a full open box lies on one of its coordinate
faces. -/
theorem exists_coordinate_eq_endpoint_of_mem_frontier_rationalBox
    {ι : Type*} [Finite ι] {a b : ι → ℚ}
    (hab : ∀ i, a i < b i) {x : ι → ℝ}
    (hx : x ∈ frontier (rationalBox a b)) :
    ∃ i, x i = (a i : ℝ) ∨ x i = (b i : ℝ) := by
  classical
  have hopen : IsOpen (rationalBox a b) := by
    apply isOpen_set_pi Set.finite_univ
    intro i _
    exact isOpen_Ioo
  rw [frontier, hopen.interior_eq, rationalBox, closure_pi_set] at hx
  have hclosed : ∀ i, x i ∈ Set.Icc (a i : ℝ) (b i : ℝ) := by
    intro i
    have hi := hx.1 i (Set.mem_univ i)
    have hne : (a i : ℝ) ≠ (b i : ℝ) := by
      exact_mod_cast (hab i).ne
    simpa only [closure_Ioo hne] using hi
  have hout : ¬ ∀ i, x i ∈ Set.Ioo (a i : ℝ) (b i : ℝ) := by
    simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hx.2
  push Not at hout
  obtain ⟨i, hi⟩ := hout
  refine ⟨i, ?_⟩
  have hci := hclosed i
  rcases lt_trichotomy (x i) (a i : ℝ) with hlt | heq | hgt
  · exact (not_lt_of_ge hci.1) hlt |>.elim
  · exact Or.inl heq
  · rcases lt_trichotomy (x i) (b i : ℝ) with hlt | heq | hgtb
    · exact (hi ⟨hgt, hlt⟩).elim
    · exact Or.inr heq
    · exact (not_lt_of_ge hci.2) hgtb |>.elim

/-- Because the new endpoints avoid the old grids, a box frontier raises the
skeleton order by one. -/
theorem mem_gridSkeleton_update_of_mem_frontier
    {ι : Type*} [Finite ι] {Q : ι → Finset ℚ} {r : ℕ}
    {a b : ι → ℚ}
    (hab : ∀ i, a i < b i ∧ a i ∉ Q i ∧ b i ∉ Q i)
    {x : ι → ℝ} (hxQ : x ∈ gridSkeleton Q r)
    (hxfront : x ∈ frontier (rationalBox a b)) :
    x ∈ gridSkeleton (updateGrid Q a b) (r + 1) := by
  classical
  rcases hxQ with ⟨I, hIcard, hxI⟩
  obtain ⟨j, hj⟩ :=
    exists_coordinate_eq_endpoint_of_mem_frontier_rationalBox
      (fun i ↦ (hab i).1) hxfront
  have hjI : j ∉ I := by
    intro hjmem
    obtain ⟨q, hqQ, hqx⟩ := hxI j hjmem
    rcases hj with hja | hjb
    · apply (hab j).2.1
      have hqa : q = a j := Rat.cast_injective (hqx.trans hja)
      simpa only [← hqa] using hqQ
    · apply (hab j).2.2
      have hqb : q = b j := Rat.cast_injective (hqx.trans hjb)
      simpa only [← hqb] using hqQ
  refine ⟨insert j I, by simp [hjI, hIcard], ?_⟩
  intro i hi
  rw [Finset.mem_insert] at hi
  rcases hi with rfl | hi
  · rcases hj with hja | hjb
    · exact ⟨a i, by simp [updateGrid], hja.symm⟩
    · exact ⟨b i, by simp [updateGrid], hjb.symm⟩
  · obtain ⟨q, hqQ, hqx⟩ := hxI i hi
    exact ⟨q, by simp [updateGrid, hqQ], hqx⟩

/-- The order-`r` grid skeleton, viewed inside the order-`k` Nöbeling
space. -/
def skeletonInNobeling {ι : Type*} (k : ℕ) (Q : ι → Finset ℚ)
    (r : ℕ) : Set (rationalCoordinateNobeling (ι := ι) k) :=
  Subtype.val ⁻¹' gridSkeleton Q r

/-- Recursive dimension certificate for rational grid skeletons. -/
theorem skeletonInNobeling_hasSmallInductiveDimensionLT
    {ι : Type*} [Finite ι] (k r n : ℕ) (Q : ι → Finset ℚ)
    (hrn : r + n = k + 1) :
    HasSmallInductiveDimensionLT (skeletonInNobeling k Q r) n := by
  induction n generalizing r Q with
  | zero =>
      rw [hasSmallInductiveDimensionLT_zero_iff]
      refine ⟨fun x ↦ ?_⟩
      have hxN := x.1.property
      have hxS := x.property
      change (x.1.1 : ι → ℝ) ∈ gridSkeleton Q r at hxS
      apply hxN
      have hr : r = k + 1 := by omega
      simpa only [hr] using
        (gridSkeleton_subset_rationalCoordinatesAtLeast hxS)
  | succ n ih =>
      let S : Set (rationalCoordinateNobeling (ι := ι) k) :=
        skeletonInNobeling k Q r
      let bN : Set (Set (rationalCoordinateNobeling (ι := ι) k)) :=
        (fun U ↦ Subtype.val ⁻¹' U) '' avoidingRationalBoxBasis Q
      let b : Set (Set S) :=
        (fun U ↦ Subtype.val ⁻¹' U) '' bN
      have hbN : IsTopologicalBasis bN :=
        (isTopologicalBasis_avoidingRationalBoxBasis Q).isInducing
          IsInducing.subtypeVal
      have hb : IsTopologicalBasis b := hbN.isInducing IsInducing.subtypeVal
      refine .succ n b hb ?_
      intro V hV
      rcases hV with ⟨W, hW, rfl⟩
      rcases hW with ⟨U, hU, rfl⟩
      rcases hU with ⟨a, b₀, hab, rfl⟩
      let Q' : ι → Finset ℚ := updateGrid Q a b₀
      let S' : Set (rationalCoordinateNobeling (ι := ι) k) :=
        skeletonInNobeling k Q' (r + 1)
      have hrn' : (r + 1) + n = k + 1 := by omega
      have hdim : HasSmallInductiveDimensionLT S' n := ih (r + 1) Q' hrn'
      have hdimInter :
          HasSmallInductiveDimensionLT (Subtype.val ⁻¹' S : Set S') n :=
        inducing_hasSmallInductiveDimensionLT IsInducing.subtypeVal hdim
      have hdimPre :
          HasSmallInductiveDimensionLT (Subtype.val ⁻¹' S' : Set S) n :=
        inducing_hasSmallInductiveDimensionLT
          (interSwapHomeomorph S S').isInducing hdimInter
      apply inducing_hasSmallInductiveDimensionLT
        (IsEmbedding.inclusion ?_).isInducing hdimPre
      intro x hx
      have hxNFrontier : x.1 ∈
          frontier (Subtype.val ⁻¹' rationalBox a b₀ :
            Set (rationalCoordinateNobeling (ι := ι) k)) :=
        continuous_subtype_val.frontier_preimage_subset _ hx
      have hxAmbientFrontier :
          (x.1.1 : ι → ℝ) ∈ frontier (rationalBox a b₀) :=
        continuous_subtype_val.frontier_preimage_subset _ hxNFrontier
      exact mem_gridSkeleton_update_of_mem_frontier hab x.property
        hxAmbientFrontier

/-- The order-`k` rational-coordinate Nöbeling set has small inductive
dimension at most `k`. -/
theorem rationalCoordinateNobeling_hasSmallInductiveDimensionLT
    {ι : Type*} [Finite ι] (k : ℕ) :
    HasSmallInductiveDimensionLT
      (rationalCoordinateNobeling (ι := ι) k) (k + 1) := by
  let Q₀ : ι → Finset ℚ := fun _ ↦ ∅
  have hdim := skeletonInNobeling_hasSmallInductiveDimensionLT
    k 0 (k + 1) Q₀ (by omega)
  have hS : skeletonInNobeling k Q₀ 0 =
      (Set.univ : Set (rationalCoordinateNobeling (ι := ι) k)) := by
    simp [skeletonInNobeling, gridSkeleton_zero]
  let e : rationalCoordinateNobeling (ι := ι) k ≃ₜ
      skeletonInNobeling k Q₀ 0 :=
    (Homeomorph.Set.univ _).symm.trans (Homeomorph.setCongr hS.symm)
  exact inducing_hasSmallInductiveDimensionLT e.isInducing hdim

/-- The bad rational-coordinate set is an order-`m` dimension obstruction. -/
theorem rationalCoordinatesAtLeast_isSmallInductiveDimensionObstruction
    {ι : Type*} [Finite ι] (m : ℕ) (hm : 0 < m) :
    IsSmallInductiveDimensionObstruction
      (rationalCoordinatesAtLeast (ι := ι) m) m := by
  intro T hT
  have hsub : T ⊆ rationalCoordinateNobeling (ι := ι) (m - 1) := by
    intro x hxT hxBad
    exact Set.disjoint_left.1 hT hxT <| by
      simpa [rationalCoordinateNobeling, Nat.sub_add_cancel hm] using hxBad
  apply inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion hsub).isInducing
  simpa [Nat.sub_add_cancel hm] using
    (rationalCoordinateNobeling_hasSmallInductiveDimensionLT
      (ι := ι) (m - 1))

end Erdos909.RationalSkeleton
