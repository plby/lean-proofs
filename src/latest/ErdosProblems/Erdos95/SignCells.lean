/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.Partitioning
import ErdosProblems.Erdos95.SurfaceFactors
import Mathlib.Analysis.Polynomial.Order

/-!
# Sign cells met by an Elekes--Sharir line

A line not contained in the product wall meets at most `degree + 1` strict
sign cells.  The proof assigns to a realized sign pattern the number of wall
roots below a chosen parameter.  Equal ranks force equal signs by the
intermediate value theorem.
-/

open scoped BigOperators

namespace Erdos95.SignCells

open Set Erdos95.Algebraic Erdos95.ES Erdos95.Partitioning

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

private theorem linePoint_eq_base_add (a b : PlanePoint) (t : ℝ) :
    (fun i ↦ linePoint a b 0 i + t * lineDirection a b i) =
      linePoint a b t := by
  funext i
  fin_cases i <;> simp [linePoint, lineDirection] <;> ring

/-- Strict sign patterns realized along the Elekes--Sharir line indexed by
`(a,b)`. -/
noncomputable def lineSignPatterns {J : ℕ} (p : Fin J → Poly3)
    (a b : PlanePoint) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦ ∃ t : ℝ, ∀ j,
    if sign j then 0 < MvPolynomial.eval (linePoint a b t) (p j)
    else MvPolynomial.eval (linePoint a b t) (p j) < 0

theorem mem_lineSignPatterns_iff {J : ℕ} {p : Fin J → Poly3}
    {a b : PlanePoint} {sign : Fin J → Bool} :
    sign ∈ lineSignPatterns p a b ↔ ∃ t : ℝ, ∀ j,
      if sign j then 0 < MvPolynomial.eval (linePoint a b t) (p j)
      else MvPolynomial.eval (linePoint a b t) (p j) < 0 := by
  classical
  simp [lineSignPatterns]

theorem lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
    {J : ℕ} {p : Fin J → Poly3} {a b : PlanePoint}
    {sign : Fin J → Bool} (hsign : sign ∈ lineSignPatterns p a b) :
    lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0 := by
  obtain ⟨t, ht⟩ := mem_lineSignPatterns_iff.mp hsign
  intro hzero
  have hzeroEval := congrArg (fun f : Polynomial ℝ ↦ f.eval t) hzero
  have hwallzero : MvPolynomial.eval (linePoint a b t)
      (partitionPolynomial p) = 0 := by
    simpa [eval_lineRestriction, linePoint_eq_base_add] using hzeroEval
  have hwallne : MvPolynomial.eval (linePoint a b t)
      (partitionPolynomial p) ≠ 0 := by
    rw [eval_partitionPolynomial]
    exact Finset.prod_ne_zero_iff.mpr fun j _hj ↦ by
      have hj := ht j
      split at hj <;> linarith
  exact hwallne hwallzero

private theorem exists_strict_root_between
    (f : Polynomial ℝ) {s t : ℝ} (hst : s < t)
    (hs : 0 < f.eval s) (ht : f.eval t < 0) :
    ∃ u ∈ Ioo s t, f.eval u = 0 := by
  have hzero : (0 : ℝ) ∈ Icc (f.eval t) (f.eval s) := ⟨ht.le, hs.le⟩
  obtain ⟨u, huIcc, hu⟩ :=
    (intermediate_value_Icc' hst.le f.continuous.continuousOn hzero)
  refine ⟨u, ⟨?_, ?_⟩, hu⟩
  · exact lt_of_le_of_ne huIcc.1 fun hus ↦ by
      subst u
      linarith
  · exact lt_of_le_of_ne huIcc.2 fun hut ↦ by
      subst u
      linarith

private theorem exists_strict_root_between_of_opposite
    (f : Polynomial ℝ) {s t : ℝ} (hst : s < t)
    (hopposite : (0 < f.eval s ∧ f.eval t < 0) ∨
      (f.eval s < 0 ∧ 0 < f.eval t)) :
    ∃ u ∈ Ioo s t, f.eval u = 0 := by
  rcases hopposite with h | h
  · exact exists_strict_root_between f hst h.1 h.2
  · obtain ⟨u, hu, hzero⟩ :=
      exists_strict_root_between (-f) hst (by simpa using h.1) (by simpa using h.2)
    exact ⟨u, hu, by simpa using hzero⟩

private theorem card_filter_lt_filter_of_between
    (R : Finset ℝ) {s u t : ℝ} (hsu : s < u) (hut : u < t)
    (huR : u ∈ R) :
    (R.filter fun z ↦ z < s).card < (R.filter fun z ↦ z < t).card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, lt_trans hz'.2 (lt_trans hsu hut)⟩, by
    intro heq
    have huRight : u ∈ R.filter (fun z ↦ z < t) :=
      Finset.mem_filter.mpr ⟨huR, hut⟩
    have huLeft : u ∉ R.filter (fun z ↦ z < s) := by
      simp [not_lt.mpr hsu.le]
    rw [heq] at huLeft
    exact huLeft huRight⟩

private theorem sign_eq_of_equal_rootRank
    {J : ℕ} (p : Fin J → Poly3) (a b : PlanePoint)
    (hwall : lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0)
    {sign₁ sign₂ : Fin J → Bool} {s t : ℝ}
    (hsign₁ : ∀ j, if sign₁ j then
        0 < MvPolynomial.eval (linePoint a b s) (p j)
      else MvPolynomial.eval (linePoint a b s) (p j) < 0)
    (hsign₂ : ∀ j, if sign₂ j then
        0 < MvPolynomial.eval (linePoint a b t) (p j)
      else MvPolynomial.eval (linePoint a b t) (p j) < 0)
    (hrank : (((lineRestriction (partitionPolynomial p)
        (linePoint a b 0) (lineDirection a b)).roots.toFinset.filter
          fun z ↦ z < s).card) =
      (((lineRestriction (partitionPolynomial p)
        (linePoint a b 0) (lineDirection a b)).roots.toFinset.filter
          fun z ↦ z < t).card)) :
    sign₁ = sign₂ := by
  classical
  apply funext
  intro j
  by_contra hne
  have hopp :
      (0 < MvPolynomial.eval (linePoint a b s) (p j) ∧
          MvPolynomial.eval (linePoint a b t) (p j) < 0) ∨
        (MvPolynomial.eval (linePoint a b s) (p j) < 0 ∧
          0 < MvPolynomial.eval (linePoint a b t) (p j)) := by
    cases h₁ : sign₁ j <;> cases h₂ : sign₂ j
    · exact (hne (by simp [h₁, h₂])).elim
    · exact Or.inr ⟨by simpa [h₁] using hsign₁ j,
          by simpa [h₂] using hsign₂ j⟩
    · exact Or.inl ⟨by simpa [h₁] using hsign₁ j,
          by simpa [h₂] using hsign₂ j⟩
    · exact (hne (by simp [h₁, h₂])).elim
  rcases lt_trichotomy s t with hst | rfl | hts
  · let f := lineRestriction (p j) (linePoint a b 0) (lineDirection a b)
    have hsEval : f.eval s = MvPolynomial.eval (linePoint a b s) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have htEval : f.eval t = MvPolynomial.eval (linePoint a b t) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    obtain ⟨u, hu, hfu⟩ := exists_strict_root_between_of_opposite f hst (by
      simpa [hsEval, htEval] using hopp)
    let wall := lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b)
    have hwall' : wall ≠ 0 := hwall
    have hwallu : wall.eval u = 0 := by
      rw [eval_lineRestriction]
      rw [eval_partitionPolynomial]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simpa [f, eval_lineRestriction, linePoint] using hfu
    have huRoot : u ∈ wall.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hwall').mpr hwallu)
    have hlt := card_filter_lt_filter_of_between wall.roots.toFinset
      hu.1 hu.2 huRoot
    exact (ne_of_lt hlt) hrank
  · have hsame := hsign₁ j
    have hsame' := hsign₂ j
    rcases hopp with h | h <;> linarith
  · let f := lineRestriction (p j) (linePoint a b 0) (lineDirection a b)
    have hsEval : f.eval s = MvPolynomial.eval (linePoint a b s) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have htEval : f.eval t = MvPolynomial.eval (linePoint a b t) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have hopp' :
        (0 < f.eval t ∧ f.eval s < 0) ∨ (f.eval t < 0 ∧ 0 < f.eval s) := by
      rcases hopp with h | h
      · exact Or.inr ⟨by simpa [htEval] using h.2, by simpa [hsEval] using h.1⟩
      · exact Or.inl ⟨by simpa [htEval] using h.2, by simpa [hsEval] using h.1⟩
    obtain ⟨u, hu, hfu⟩ := exists_strict_root_between_of_opposite f hts hopp'
    let wall := lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b)
    have hwall' : wall ≠ 0 := hwall
    have hwallu : wall.eval u = 0 := by
      rw [eval_lineRestriction]
      rw [eval_partitionPolynomial]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simpa [f, eval_lineRestriction, linePoint] using hfu
    have huRoot : u ∈ wall.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hwall').mpr hwallu)
    have hlt := card_filter_lt_filter_of_between wall.roots.toFinset
      hu.1 hu.2 huRoot
    exact (ne_of_gt hlt) hrank

/-- A line not contained in the product wall realizes at most one more
strict sign pattern than the wall degree. -/
theorem card_lineSignPatterns_le {J : ℕ} (p : Fin J → Poly3)
    (a b : PlanePoint)
    (hwall : lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0) :
    (lineSignPatterns p a b).card ≤
      (partitionPolynomial p).totalDegree + 1 := by
  classical
  let wall := lineRestriction (partitionPolynomial p)
    (linePoint a b 0) (lineDirection a b)
  let parameter : (Fin J → Bool) → ℝ := fun sign ↦
    if h : sign ∈ lineSignPatterns p a b then
      Classical.choose (mem_lineSignPatterns_iff.mp h)
    else 0
  let rank : (Fin J → Bool) → ℕ := fun sign ↦
    (wall.roots.toFinset.filter fun z ↦ z < parameter sign).card
  have hmaps : Set.MapsTo rank (lineSignPatterns p a b)
      (Finset.range (wall.roots.toFinset.card + 1)) := by
    intro sign hsign
    change rank sign ∈ Finset.range (wall.roots.toFinset.card + 1)
    rw [Finset.mem_range]
    dsimp [rank]
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  have hinj : Set.InjOn rank (lineSignPatterns p a b) := by
    intro sign₁ hsign₁ sign₂ hsign₂ hrank
    change sign₁ ∈ lineSignPatterns p a b at hsign₁
    change sign₂ ∈ lineSignPatterns p a b at hsign₂
    have hparam₁ : parameter sign₁ =
        Classical.choose (mem_lineSignPatterns_iff.mp hsign₁) := by
      dsimp [parameter]
      rw [dif_pos hsign₁]
    have hparam₂ : parameter sign₂ =
        Classical.choose (mem_lineSignPatterns_iff.mp hsign₂) := by
      dsimp [parameter]
      rw [dif_pos hsign₂]
    have hw₁ : ∀ j, if sign₁ j then
        0 < MvPolynomial.eval (linePoint a b (parameter sign₁)) (p j)
      else MvPolynomial.eval (linePoint a b (parameter sign₁)) (p j) < 0 := by
      rw [hparam₁]
      exact Classical.choose_spec (mem_lineSignPatterns_iff.mp hsign₁)
    have hw₂ : ∀ j, if sign₂ j then
        0 < MvPolynomial.eval (linePoint a b (parameter sign₂)) (p j)
      else MvPolynomial.eval (linePoint a b (parameter sign₂)) (p j) < 0 := by
      rw [hparam₂]
      exact Classical.choose_spec (mem_lineSignPatterns_iff.mp hsign₂)
    apply sign_eq_of_equal_rootRank p a b hwall hw₁ hw₂
    simpa [rank, wall] using hrank
  calc
    (lineSignPatterns p a b).card ≤
        (Finset.range (wall.roots.toFinset.card + 1)).card :=
      Finset.card_le_card_of_injOn rank hmaps hinj
    _ = wall.roots.toFinset.card + 1 := by simp
    _ ≤ wall.natDegree + 1 := by
      gcongr
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' wall)
    _ ≤ (partitionPolynomial p).totalDegree + 1 := by
      gcongr
      exact natDegree_lineRestriction _ _ _

end Erdos95.SignCells
