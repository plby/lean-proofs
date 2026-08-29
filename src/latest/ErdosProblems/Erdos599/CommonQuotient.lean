/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientMaximal
import ErdosProblems.Erdos599.QuotientAssociativity

/-!
# Countable waves in a common quotient

This file contains the support bookkeeping for the countable up-arrow in
Aharoni--Berger Lemma 3.30.  The quotient-transport part of that lemma is
kept separate from this bookkeeping: once every stage wave has been
transported to one fixed quotient, `DWeb.omegaArrow` constructs the final
wave.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-! ## Transport to a larger quotient -/

/-- A wave in `G / X`, transported to `G / Y` when `X ⊆ Y`.

The construction first applies source Lemma 3.5 inside `G / X`, then uses
quotient associativity and `X ∪ Y = Y`.  Thus this is concrete quotient
transport, not an assumption that packages Lemma 3.30. -/
noncomputable def waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) : (G.quotient Y).Wave := by
  let Z : ((G.quotient X).quotient Y).Wave :=
    ⟨(G.quotient X).generalWaveQuotient Y W.1,
      (G.quotient X).isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : (G.quotient X).quotient Y = G.quotient Y := by
    calc
      (G.quotient X).quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  exact heq ▸ Z

theorem isWave_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    (G.quotient Y).IsWave (G.waveToLargerQuotient hNoEnter hXY W).1 :=
  (G.waveToLargerQuotient hNoEnter hXY W).2

/-- The raw union of the commitment sets in the Section 6 recursion. -/
def commonQuotientSet (X : ℕ → Set V) : Set V :=
  ⋃ i, X i

theorem subset_commonQuotientSet (X : ℕ → Set V) (i : ℕ) :
    X i ⊆ commonQuotientSet X :=
  Set.subset_iUnion X i

/-- The `i`th quotient wave transported into the one quotient by the raw
union of all commitment sets. -/
noncomputable def commonQuotientStage
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) (i : ℕ) :
    (G.quotient (commonQuotientSet X)).Wave :=
  G.waveToLargerQuotient hNoEnter (subset_commonQuotientSet X i) (W i)

/-- The final countable up-arrow of the transported quotient waves. -/
noncomputable def commonQuotientOmegaArrow
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) :
    (G.quotient (commonQuotientSet X)).Wave :=
  (G.quotient (commonQuotientSet X)).omegaArrow
    (G.commonQuotientStage hNoEnter X W)

/-- Aharoni--Berger Lemma 3.30, wave clause, with the paper's raw union
kept visible in the type. -/
theorem isWave_commonQuotientOmegaArrow
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) :
    (G.quotient (commonQuotientSet X)).IsWave
      (G.commonQuotientOmegaArrow hNoEnter X W).1 :=
  (G.commonQuotientOmegaArrow hNoEnter X W).2

/-- Every transported stage is below the final Lemma 3.30 wave in roof
order. -/
theorem roofLE_commonQuotientOmegaArrow
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) (i : ℕ) :
    (G.quotient (commonQuotientSet X)).RoofLE
      (G.commonQuotientStage hNoEnter X W i).1
      (G.commonQuotientOmegaArrow hNoEnter X W).1 :=
  (G.quotient (commonQuotientSet X)).roofLE_omegaArrow
    (G.commonQuotientStage hNoEnter X W) i

/-! ## Support of finite and countable arrows -/

/-- The arrow operation introduces no vertex outside the two input
families.  This is the path-support half of the stabilization used after
source Lemma 3.30. -/
theorem vertexSet_arrow_subset (U W : Set G.DPath) :
    G.vertexSet (G.arrow U W) ⊆ G.vertexSet U ∪ G.vertexSet W := by
  rintro x ⟨q, ⟨p, rfl⟩, hxq⟩
  rcases hp : p.1 with f | r
  · have hf : (Sum.inl f : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inl f, hf⟩ := Subtype.ext hp
    subst p
    rcases G.arrowPath_finite_cases U W f hf with h | ⟨c, h⟩
    · left
      exact ⟨.inl f, hf, by simpa [h] using hxq⟩
    · rw [h, DirectedPath.Path.support_appendAt] at hxq
      rcases hxq with hxf | hxc
      · exact Or.inl ⟨.inl f, hf, hxf⟩
      · exact Or.inr ⟨c.path, c.mem_path,
          c.path.support_suffixFrom_subset f.finish c.finish_mem hxc⟩
  · have hr : (Sum.inr r : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inr r, hr⟩ := Subtype.ext hp
    subst p
    exact Or.inl ⟨.inr r, hr, by
      simpa [G.arrowPath_ray U W r hr] using hxq⟩

/-- Every vertex of a direct-limit chain wave already occurs at a finite
member of the chain.  A limit path itself need not be a member of any
stage, which is why this is stated at vertex level. -/
theorem vertexSet_waveChainUpper_subset_iUnion
    (c : Set G.Wave) (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c) :
    G.vertexSet (G.waveChainUpper c hcne hc) ⊆
      ⋃ U : c, G.vertexSet U.1.1 := by
  rintro x ⟨q, ⟨a, rfl⟩, hxq⟩
  have hx : x ∈ ⋃ p ∈ G.waveThread c a.1, p.support := by
    simpa only [waveThreadLimit, DirectedPath.Path.support_chainLimit] using hxq
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨p, hpThread, hxp⟩ := hx
  obtain ⟨U, hUc, hpU, _⟩ := hpThread
  exact ⟨⟨U, hUc⟩, p, hpU, hxp⟩

/-- Any two vertices of one limit path occur together on a path at one
finite member of the chain.  This is the finite-support form of path
stabilization needed by the closing-up construction. -/
theorem exists_chain_path_containing_pair
    (c : Set G.Wave) (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    {q : G.DPath} (hq : q ∈ G.waveChainUpper c hcne hc)
    {x y : V} (hxq : x ∈ q.support) (hyq : y ∈ q.support) :
    ∃ U : c, ∃ p ∈ U.1.1, x ∈ p.support ∧ y ∈ p.support := by
  obtain ⟨a, rfl⟩ := hq
  have hx : x ∈ ⋃ p ∈ G.waveThread c a.1, p.support := by
    simpa only [waveThreadLimit, DirectedPath.Path.support_chainLimit] using hxq
  have hy : y ∈ ⋃ p ∈ G.waveThread c a.1, p.support := by
    simpa only [waveThreadLimit, DirectedPath.Path.support_chainLimit] using hyq
  simp only [Set.mem_iUnion] at hx hy
  obtain ⟨p, hpThread, hxp⟩ := hx
  obtain ⟨r, hrThread, hyr⟩ := hy
  by_cases hpr : p = r
  · subst r
    obtain ⟨U, hUc, hpU, _⟩ := hpThread
    exact ⟨⟨U, hUc⟩, p, hpU, hxp, hyr⟩
  · rcases G.waveThread_isChain hc a.1 hpThread hrThread hpr with h | h
    · obtain ⟨U, hUc, hrU, _⟩ := hrThread
      exact ⟨⟨U, hUc⟩, r, hrU,
        G.support_mono_of_extends h hxp, hyr⟩
    · obtain ⟨U, hUc, hpU, _⟩ := hpThread
      exact ⟨⟨U, hUc⟩, p, hpU, hxp,
        G.support_mono_of_extends h hyr⟩

/-- At finite stage `n`, every accumulated-arrow vertex comes from one of
the first `n+1` input waves. -/
theorem vertexSet_omegaArrowStage_subset (W : ℕ → G.Wave) (n : ℕ) :
    G.vertexSet (G.omegaArrowStage W n).1 ⊆
      ⋃ i ≤ n, G.vertexSet (W i).1 := by
  induction n with
  | zero =>
      simpa using (Set.subset_iUnion (fun i : ℕ ↦
        ⋃ _h : i ≤ 0, G.vertexSet (W i).1) 0 |>.trans
          (Set.subset_iUnion (fun _h : 0 ≤ 0 ↦ G.vertexSet (W 0).1) le_rfl))
  | succ n ih =>
      rw [G.omegaArrowStage_succ]
      refine (G.vertexSet_arrow_subset
        (G.omegaArrowStage W n).1 (W (n + 1)).1).trans ?_
      apply Set.union_subset
      · exact ih.trans (by
          intro x hx
          simp only [Set.mem_iUnion] at hx ⊢
          obtain ⟨i, hi, hxi⟩ := hx
          exact ⟨i, Nat.le.step hi, hxi⟩)
      · intro x hx
        exact Set.mem_iUnion_of_mem (n + 1)
          (Set.mem_iUnion_of_mem le_rfl hx)

/-- Every vertex of the countable up-arrow occurs in one of its input
waves. -/
theorem vertexSet_omegaArrow_subset_iUnion (W : ℕ → G.Wave) :
    G.vertexSet (G.omegaArrow W).1 ⊆ ⋃ i, G.vertexSet (W i).1 := by
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  refine (G.vertexSet_waveChainUpper_subset_iUnion c hcne hc).trans ?_
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨U, p, hpU, hxp⟩ := hx
  obtain ⟨n, hn⟩ := U.2
  have hpstage : p ∈ (G.omegaArrowStage W n).1 := by
    rw [hn]
    exact hpU
  have hxstage : x ∈ G.vertexSet (G.omegaArrowStage W n).1 :=
    ⟨p, hpstage, hxp⟩
  have hxinput := G.vertexSet_omegaArrowStage_subset W n hxstage
  simp only [Set.mem_iUnion] at hxinput
  obtain ⟨i, _hi, hxi⟩ := hxinput
  exact ⟨i, hxi⟩

/-- Any two vertices on one path of the countable up-arrow occur together
at one finite accumulated-arrow stage. -/
theorem exists_omegaArrowStage_path_containing_pair
    (W : ℕ → G.Wave) {q : G.DPath} (hq : q ∈ (G.omegaArrow W).1)
    {x y : V} (hxq : x ∈ q.support) (hyq : y ∈ q.support) :
    ∃ n, ∃ p ∈ (G.omegaArrowStage W n).1,
      x ∈ p.support ∧ y ∈ p.support := by
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  have hq' : q ∈ G.waveChainUpper c hcne hc := by
    simpa only [omegaArrow, waveChainUpperWave] using hq
  obtain ⟨U, p, hpU, hxp, hyp⟩ :=
    G.exists_chain_path_containing_pair c hcne hc hq' hxq hyq
  obtain ⟨n, hn⟩ := U.2
  refine ⟨n, p, ?_, hxp, hyp⟩
  rw [hn]
  exact hpU

/-- The finite stage witnessing two vertices can be chosen after any
prescribed stage. -/
theorem exists_later_omegaArrowStage_path_containing_pair
    (W : ℕ → G.Wave) (k : ℕ) {q : G.DPath}
    (hq : q ∈ (G.omegaArrow W).1) {x y : V}
    (hxq : x ∈ q.support) (hyq : y ∈ q.support) :
    ∃ m, k ≤ m ∧ ∃ p ∈ (G.omegaArrowStage W m).1,
      x ∈ p.support ∧ y ∈ p.support := by
  obtain ⟨n, p, hpStage, hxp, hyp⟩ :=
    G.exists_omegaArrowStage_path_containing_pair W hq hxq hyq
  let m := max n k
  have hnm : n ≤ m := Nat.le_max_left n k
  have hkm : k ≤ m := Nat.le_max_right n k
  obtain ⟨r, hrStage, hpr⟩ :=
    (G.omegaArrowStage_mono W hnm).1 p hpStage
  exact ⟨m, hkm, r, hrStage,
    G.support_mono_of_extends hpr hxp,
    G.support_mono_of_extends hpr hyp⟩

/-! ### Families meeting a vertex set -/

/-- The subfamily consisting of paths that meet `X`.  The distinct name
avoids coupling this foundational module to the Section 6 notation in
`SafeLink`. -/
def pathsMeetingSet (W : Set G.DPath) (X : Set V) : Set G.DPath :=
  {p | p ∈ W ∧ (p.support ∩ X).Nonempty}

/-- All vertices on members of `W` that meet `X`. -/
def verticesMeetingSet (W : Set G.DPath) (X : Set V) : Set V :=
  G.vertexSet (G.pathsMeetingSet W X)

/-- Meeting-path stabilization for the countable up-arrow: every vertex
on a final path meeting `X` already lies on a path meeting `X` at one
finite accumulated-arrow stage. -/
theorem verticesMeetingSet_omegaArrow_subset_iUnion
    (W : ℕ → G.Wave) (X : Set V) :
    G.verticesMeetingSet (G.omegaArrow W).1 X ⊆
      ⋃ n, G.verticesMeetingSet (G.omegaArrowStage W n).1 X := by
  rintro y ⟨q, ⟨hqW, hqX⟩, hyq⟩
  obtain ⟨x, hxq, hxX⟩ := hqX
  obtain ⟨n, p, hpStage, hxp, hyp⟩ :=
    G.exists_omegaArrowStage_path_containing_pair W hqW hxq hyq
  exact Set.mem_iUnion_of_mem n
    ⟨p, ⟨hpStage, ⟨x, hxp, hxX⟩⟩, hyp⟩

/-! ## Closing-up transfer from finite stages -/

/-- If every accumulated stage inserts all tree vertices on its paths
meeting the current increasing set, then the union is closed under the
same operation for the final countable up-arrow.  This is the support
content of Proposition 6.3(d). -/
theorem verticesMeetingSet_omegaArrow_subset_iUnion_of_step
    (W : ℕ → G.Wave) (X : ℕ → Set V) (hX : Monotone X)
    (hstep : ∀ n,
      G.verticesMeetingSet (G.omegaArrowStage W n).1 (X n) ⊆ X (n + 1)) :
    G.verticesMeetingSet (G.omegaArrow W).1 (⋃ n, X n) ⊆ ⋃ n, X n := by
  rintro y ⟨q, ⟨hqW, hqX⟩, hyq⟩
  obtain ⟨x, hxq, hxUnion⟩ := hqX
  obtain ⟨k, hxXk⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨m, hkm, p, hpStage, hxp, hyp⟩ :=
    G.exists_later_omegaArrowStage_path_containing_pair W k hqW hxq hyq
  have hxXm : x ∈ X m := hX hkm hxXk
  have hyNext : y ∈ X (m + 1) := hstep m
    ⟨p, ⟨hpStage, ⟨x, hxp, hxXm⟩⟩, hyp⟩
  exact Set.mem_iUnion_of_mem (m + 1) hyNext

/-- Boundary-data version of the same closing-up argument.  If stage
`n+1` inserts `F z` for every boundary vertex `z` lying on a stage-`n`
path meeting `X n`, then the final union inserts `F z` for every boundary
vertex on a final path meeting the union.  This is Proposition 6.3(b)'s
stage-domination argument. -/
theorem boundary_subset_iUnion_of_omegaArrow_step
    (W : ℕ → G.Wave) (X : ℕ → Set V) (hX : Monotone X)
    (Y : Set V) (F : V → Set V)
    (hstep : ∀ n ⦃z⦄,
      z ∈ Y ∩ G.verticesMeetingSet (G.omegaArrowStage W n).1 (X n) →
        F z ⊆ X (n + 1))
    ⦃z : V⦄
    (hz : z ∈ Y ∩
      G.verticesMeetingSet (G.omegaArrow W).1 (⋃ n, X n)) :
    F z ⊆ ⋃ n, X n := by
  rintro y hyF
  rcases hz with ⟨hzY, q, ⟨hqW, hqX⟩, hzq⟩
  obtain ⟨x, hxq, hxUnion⟩ := hqX
  obtain ⟨k, hxXk⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨m, hkm, p, hpStage, hxp, hzp⟩ :=
    G.exists_later_omegaArrowStage_path_containing_pair W k hqW hxq hzq
  have hxXm : x ∈ X m := hX hkm hxXk
  have hzStage : z ∈
      G.verticesMeetingSet (G.omegaArrowStage W m).1 (X m) :=
    ⟨p, ⟨hpStage, ⟨x, hxp, hxXm⟩⟩, hzp⟩
  exact Set.mem_iUnion_of_mem (m + 1)
    (hstep m ⟨hzY, hzStage⟩ hyF)

/-- Witness form of `vertexSet_omegaArrow_subset_iUnion`. -/
theorem exists_stage_of_mem_vertexSet_omegaArrow
    (W : ℕ → G.Wave) {x : V} (hx : x ∈ G.vertexSet (G.omegaArrow W).1) :
    ∃ i, x ∈ G.vertexSet (W i).1 := by
  simpa only [Set.mem_iUnion] using G.vertexSet_omegaArrow_subset_iUnion W hx

/-! ## Fixed-web Lemma 3.30 assembly -/

/-- Once quotient transport has placed every stage wave in a single web,
the countable up-arrow is a wave, roofs every stage, and contains no new
vertices. -/
theorem exists_omegaArrow_roofing_with_support (W : ℕ → G.Wave) :
    ∃ M : G.Wave,
      (∀ i, G.RoofLE (W i).1 M.1) ∧
      G.vertexSet M.1 ⊆ ⋃ i, G.vertexSet (W i).1 := by
  exact ⟨G.omegaArrow W, G.roofLE_omegaArrow W,
    G.vertexSet_omegaArrow_subset_iUnion W⟩

end DWeb

end Erdos599
