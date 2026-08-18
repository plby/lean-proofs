/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Finite hypergraphs for Erdős Problem 136

This file supplies the finite combinatorial language used by the
conflict-free matching part of the Joos--Mubayi construction.  A hypergraph
is represented directly as a `Finset` of finite vertex sets.  In particular,
all degree, codegree, matching, conflict, and test-function notions below are
finite and executable.
-/

namespace Erdos136

open Finset

variable {V : Type*} [DecidableEq V]

/-- A finite hypergraph on `V`, represented by its finite edge set. -/
abbrev Hypergraph (V : Type*) [DecidableEq V] := Finset (Finset V)

/-- The finite set of vertices which occur in at least one edge of `H`.
This is the correct vertex set for degree hypotheses: an ambient finite type
may contain additional labels of degree zero. -/
def vertexFinset (H : Hypergraph V) : Finset V :=
  H.biUnion id

/-- Every edge of `H` has cardinality `r`. -/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- The number of hyperedges containing a vertex. -/
def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter fun e => v ∈ e).card

/-- The number of hyperedges containing every vertex in `s`. -/
def codegree (H : Hypergraph V) (s : Finset V) : ℕ :=
  (H.filter fun e => s ⊆ e).card

/-- Every vertex degree is at most `D`. -/
def MaxDegreeLE (H : Hypergraph V) (D : ℕ) : Prop :=
  ∀ v, degree H v ≤ D

/-- Every vertex degree is at least `D`. -/
def MinDegreeGE (H : Hypergraph V) (D : ℕ) : Prop :=
  ∀ v, D ≤ degree H v

/-- Every `j`-set has codegree at most `D`. -/
def MaxCodegreeLE (H : Hypergraph V) (j D : ℕ) : Prop :=
  ∀ s, s.card = j → codegree H s ≤ D

/-- Distinct members of `M` are disjoint as vertex sets. -/
def PairwiseDisjoint (M : Hypergraph V) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → Disjoint e f

/-- A matching in `H` is a pairwise-disjoint subfamily of its edges. -/
def IsMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ PairwiseDisjoint M

/-- A conflict system for a hypergraph on `V` is a finite hypergraph whose
vertices are themselves hyperedges on `V`. -/
abbrev ConflictSystem (V : Type*) [DecidableEq V] := Hypergraph (Finset V)

/-- Every member of `C` consists only of edges of `H`. -/
def IsConflictSystem (H : Hypergraph V) (C : ConflictSystem V) : Prop :=
  ∀ c ∈ C, c ⊆ H

/-- The conflicts having exactly `j` members. -/
def conflictLayer (C : ConflictSystem V) (j : ℕ) : ConflictSystem V :=
  C.filter fun c => c.card = j

/-- The link of `e` in a conflict system: erase `e` from every conflict
which contains it. -/
def conflictLink (C : ConflictSystem V) (e : Finset V) : ConflictSystem V :=
  (C.filter fun c => e ∈ c).image fun c => c.erase e

/-- The `j`-uniform layer of the link of `e`. -/
def conflictLinkLayer (C : ConflictSystem V) (e : Finset V) (j : ℕ) :
    ConflictSystem V :=
  conflictLayer (conflictLink C e) j

/-- `M` contains no whole conflict from `C`. -/
def ConflictFree (C : ConflictSystem V) (M : Hypergraph V) : Prop :=
  ∀ c ∈ C, ¬c ⊆ M

/-- The literal `(d, ell, eta)` boundedness conditions (C1)--(C3) from the
conflict-free matching theorem.  Cardinalities are cast to reals because
(C3) has a nonintegral exponent. -/
def IsBounded (C : ConflictSystem V) (d : ℝ) (ell : ℕ) (eta : ℝ) : Prop :=
  (∀ c ∈ C, 3 ≤ c.card ∧ c.card ≤ ell) ∧
  (∀ j, 3 ≤ j → j ≤ ell → ∀ e,
    (degree (conflictLayer C j) e : ℝ) ≤
      (ell : ℝ) * Real.rpow d ((j : ℝ) - 1)) ∧
  (∀ j, 3 ≤ j → j ≤ ell → ∀ j', 2 ≤ j' → j' < j → ∀ s,
    s.card = j' →
      (codegree (conflictLayer C j) s : ℝ) ≤
        Real.rpow d ((j : ℝ) - (j' : ℝ) - eta))

/-- A real-valued weight on finite families of hyperedges. -/
abbrev TestWeight (V : Type*) [DecidableEq V] := Hypergraph V → ℝ

/-- A `j`-uniform test function with values in `[0, ell]`, vanishing away
from matchings in `H`.  We use a total function and require it to vanish
outside its intended finite domain; this makes later sums convenient. -/
def IsTestFunction (H : Hypergraph V) (j ell : ℕ) (w : TestWeight V) : Prop :=
  (∀ S, 0 ≤ w S) ∧
  (∀ S, w S ≤ (ell : ℝ)) ∧
  (∀ S, S.card ≠ j → w S = 0) ∧
  (∀ S, ¬IsMatching H S → w S = 0)

/-- Extend a test weight to a finite family by summing over its `j`-sets. -/
def testTotal (w : TestWeight V) (A : Hypergraph V) (j : ℕ) : ℝ :=
  ∑ S ∈ A.powersetCard j, w S

/-- Weight of the `j`-sets in `A` which extend a fixed subfamily `root`. -/
def testExtension (w : TestWeight V) (A : Hypergraph V) (j : ℕ)
    (root : Hypergraph V) : ℝ :=
  ∑ S ∈ (A.powersetCard j).filter (root ⊆ ·), w S

/-- The literal trackability conditions (W1)--(W4). -/
def IsTrackable (H : Hypergraph V) (C : ConflictSystem V) (j ell : ℕ)
    (d eta : ℝ) (w : TestWeight V) : Prop :=
  IsTestFunction H j ell w ∧
  Real.rpow d ((j : ℝ) + eta) ≤ testTotal w H j ∧
  (∀ j', 1 ≤ j' → j' < j → ∀ root, root ⊆ H → root.card = j' →
    testExtension w H j root ≤
      testTotal w H j / Real.rpow d ((j' : ℝ) + eta)) ∧
  (∀ S ∈ H.powersetCard j, 0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
    ∀ j', 1 ≤ j' → j' < ell →
      (((conflictLinkLayer C e j') ∩
        (conflictLinkLayer C f j')).card : ℝ) ≤
          Real.rpow d ((j' : ℝ) - eta)) ∧
  (∀ S ∈ H.powersetCard j, (∃ c ∈ C, c ⊆ S) → w S = 0)

/-! ## Uniformity, degree, and codegree lemmas -/

@[simp] theorem mem_vertexFinset {H : Hypergraph V} {v : V} :
    v ∈ vertexFinset H ↔ ∃ e ∈ H, v ∈ e := by
  simp [vertexFinset]

@[simp] theorem vertexFinset_empty :
    vertexFinset (∅ : Hypergraph V) = ∅ := by
  simp [vertexFinset]

@[simp] theorem vertexFinset_singleton (e : Finset V) :
    vertexFinset ({e} : Hypergraph V) = e := by
  simp [vertexFinset]

theorem edge_subset_vertexFinset {H : Hypergraph V} {e : Finset V}
    (he : e ∈ H) : e ⊆ vertexFinset H := by
  intro v hv
  exact mem_vertexFinset.mpr ⟨e, he, hv⟩

theorem vertexFinset_mono {H K : Hypergraph V} (hHK : H ⊆ K) :
    vertexFinset H ⊆ vertexFinset K := by
  intro v hv
  obtain ⟨e, heH, hve⟩ := mem_vertexFinset.mp hv
  exact mem_vertexFinset.mpr ⟨e, hHK heH, hve⟩

@[simp] theorem isUniform_empty (r : ℕ) :
    IsUniform (∅ : Hypergraph V) r := by
  simp [IsUniform]

theorem IsUniform.mono {H K : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) (hKH : K ⊆ H) : IsUniform K r := by
  intro e he
  exact hH e (hKH he)

@[simp] theorem isUniform_singleton (e : Finset V) :
    IsUniform ({e} : Hypergraph V) e.card := by
  simp [IsUniform]

@[simp] theorem degree_empty (v : V) : degree (∅ : Hypergraph V) v = 0 := by
  simp [degree]

@[simp] theorem degree_singleton (e : Finset V) (v : V) :
    degree ({e} : Hypergraph V) v = if v ∈ e then 1 else 0 := by
  rw [degree, Finset.filter_singleton]
  by_cases hv : v ∈ e <;> simp [hv]

theorem degree_le_card (H : Hypergraph V) (v : V) : degree H v ≤ H.card := by
  exact Finset.card_filter_le _ _

theorem degree_pos_iff_mem_vertexFinset {H : Hypergraph V} {v : V} :
    0 < degree H v ↔ v ∈ vertexFinset H := by
  rw [degree, Finset.card_pos]
  constructor
  · rintro ⟨e, he⟩
    exact mem_vertexFinset.mpr ⟨e, (Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2⟩
  · intro hv
    obtain ⟨e, heH, hve⟩ := mem_vertexFinset.mp hv
    exact ⟨e, Finset.mem_filter.mpr ⟨heH, hve⟩⟩

theorem degree_eq_zero_iff_not_mem_vertexFinset {H : Hypergraph V} {v : V} :
    degree H v = 0 ↔ v ∉ vertexFinset H := by
  constructor
  · intro hzero hv
    have hpos := degree_pos_iff_mem_vertexFinset.mpr hv
    omega
  · intro hv
    exact Nat.eq_zero_of_not_pos fun hpos =>
      hv (degree_pos_iff_mem_vertexFinset.mp hpos)

theorem degree_eq_zero_of_not_mem_vertexFinset {H : Hypergraph V} {v : V}
    (hv : v ∉ vertexFinset H) : degree H v = 0 :=
  degree_eq_zero_iff_not_mem_vertexFinset.mpr hv

theorem degree_mono {H K : Hypergraph V} (hHK : H ⊆ K) (v : V) :
    degree H v ≤ degree K v := by
  exact Finset.card_le_card (fun e he => by
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨hHK he.1, he.2⟩)

@[simp] theorem codegree_empty_family (s : Finset V) :
    codegree (∅ : Hypergraph V) s = 0 := by
  simp [codegree]

@[simp] theorem codegree_empty (H : Hypergraph V) : codegree H ∅ = H.card := by
  simp [codegree]

@[simp] theorem codegree_singleton (H : Hypergraph V) (v : V) :
    codegree H {v} = degree H v := by
  simp [codegree, degree]

theorem codegree_le_card (H : Hypergraph V) (s : Finset V) :
    codegree H s ≤ H.card := by
  exact Finset.card_filter_le _ _

theorem codegree_mono_hypergraph {H K : Hypergraph V} (hHK : H ⊆ K)
    (s : Finset V) : codegree H s ≤ codegree K s := by
  exact Finset.card_le_card (fun e he => by
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨hHK he.1, he.2⟩)

theorem codegree_antitone {H : Hypergraph V} {s t : Finset V} (hst : s ⊆ t) :
    codegree H t ≤ codegree H s := by
  exact Finset.card_le_card (fun e he => by
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨he.1, hst.trans he.2⟩)

theorem codegree_eq_zero_of_uniform_of_card_lt {H : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) {s : Finset V} (hrs : r < s.card) :
    codegree H s = 0 := by
  rw [codegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e heH hse
  have := Finset.card_le_card hse
  rw [hH e heH] at this
  exact (Nat.not_le_of_lt hrs) this

theorem MaxCodegreeLE.mono_index {H : Hypergraph V} {i j D : ℕ}
    (h : MaxCodegreeLE H i D) (hij : i ≤ j) : MaxCodegreeLE H j D := by
  intro s hs
  obtain ⟨root, hroot, hrootcard⟩ :=
    Finset.exists_subset_card_eq (by omega : i ≤ s.card)
  exact (codegree_antitone hroot).trans (h root hrootcard)

/-- Double-count incidences between the actual vertices and the edges. -/
theorem sum_degree_vertexFinset (H : Hypergraph V) :
    ∑ v ∈ vertexFinset H, degree H v = ∑ e ∈ H, e.card := by
  simp only [degree, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e heH
  rw [← Finset.card_filter]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun hv => hv.2
  · intro hv
    exact ⟨edge_subset_vertexFinset heH hv, hv⟩

theorem sum_degree_vertexFinset_of_uniform {H : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) :
    ∑ v ∈ vertexFinset H, degree H v = r * H.card := by
  rw [sum_degree_vertexFinset]
  calc
    ∑ e ∈ H, e.card = ∑ _e ∈ H, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hH e he
    _ = r * H.card := by simp [Nat.mul_comm]

/-- The union of a finite edge family has at most the sum of its edge
cardinalities. -/
theorem card_vertexFinset_le_sum_card (H : Hypergraph V) :
    (vertexFinset H).card ≤ ∑ e ∈ H, e.card := by
  unfold vertexFinset
  exact Finset.card_biUnion_le

theorem card_vertexFinset_le_of_uniform {H : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) : (vertexFinset H).card ≤ r * H.card := by
  calc
    (vertexFinset H).card ≤ ∑ e ∈ H, e.card :=
      card_vertexFinset_le_sum_card H
    _ = ∑ _e ∈ H, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hH e he
    _ = r * H.card := by simp [Nat.mul_comm]

/-! ## Matching and conflict lemmas -/

@[simp] theorem pairwiseDisjoint_empty :
    PairwiseDisjoint (∅ : Hypergraph V) := by
  simp [PairwiseDisjoint]

@[simp] theorem pairwiseDisjoint_singleton (e : Finset V) :
    PairwiseDisjoint ({e} : Hypergraph V) := by
  simp [PairwiseDisjoint]

theorem PairwiseDisjoint.mono {M N : Hypergraph V}
    (hM : PairwiseDisjoint M) (hNM : N ⊆ M) : PairwiseDisjoint N := by
  intro e he f hf hne
  exact hM (hNM he) (hNM hf) hne

theorem pairwiseDisjoint_insert_iff {e : Finset V} {M : Hypergraph V} :
    PairwiseDisjoint (insert e M) ↔
      PairwiseDisjoint M ∧ ∀ f ∈ M, f ≠ e → Disjoint e f := by
  constructor
  · intro h
    refine ⟨h.mono (Finset.subset_insert _ _), ?_⟩
    intro f hf hfe
    exact h (Finset.mem_insert_self e M) (Finset.mem_insert_of_mem hf) hfe.symm
  · rintro ⟨hM, heM⟩ a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact heM b hb hab.symm
    · rcases hb with rfl | hb
      · exact (heM a ha hab).symm
      · exact hM ha hb hab

theorem card_vertexFinset_eq_sum_card_of_pairwiseDisjoint
    {M : Hypergraph V} (hM : PairwiseDisjoint M) :
    (vertexFinset M).card = ∑ e ∈ M, e.card := by
  unfold vertexFinset
  apply Finset.card_biUnion
  intro e he f hf hef
  exact hM he hf hef

theorem card_vertexFinset_eq_of_pairwiseDisjoint_uniform
    {M : Hypergraph V} {r : ℕ} (hdisj : PairwiseDisjoint M)
    (hunif : IsUniform M r) : (vertexFinset M).card = r * M.card := by
  rw [card_vertexFinset_eq_sum_card_of_pairwiseDisjoint hdisj]
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e he
    _ = r * M.card := by simp [Nat.mul_comm]

@[simp] theorem isMatching_empty (H : Hypergraph V) :
    IsMatching H ∅ := by
  simp [IsMatching]

theorem IsMatching.mono {H M N : Hypergraph V} (hM : IsMatching H M)
    (hNM : N ⊆ M) : IsMatching H N := by
  exact ⟨hNM.trans hM.1, hM.2.mono hNM⟩

theorem isMatching_singleton_iff {H : Hypergraph V} {e : Finset V} :
    IsMatching H {e} ↔ e ∈ H := by
  simp [IsMatching]

theorem isMatching_insert_iff {H M : Hypergraph V} {e : Finset V} :
    IsMatching H (insert e M) ↔
      e ∈ H ∧ IsMatching H M ∧ ∀ f ∈ M, f ≠ e → Disjoint e f := by
  simp only [IsMatching, Finset.insert_subset_iff, pairwiseDisjoint_insert_iff]
  aesop

theorem IsMatching.edge_mem {H M : Hypergraph V} (hM : IsMatching H M)
    {e : Finset V} (he : e ∈ M) : e ∈ H :=
  hM.1 he

@[simp] theorem conflictLayer_zero (C : ConflictSystem V) :
    conflictLayer C 0 = C.filter (fun c => c.card = 0) := rfl

theorem conflictLayer_subset (C : ConflictSystem V) (j : ℕ) :
    conflictLayer C j ⊆ C :=
  Finset.filter_subset _ _

@[simp] theorem mem_conflictLayer {C : ConflictSystem V} {j : ℕ}
    {c : Hypergraph V} : c ∈ conflictLayer C j ↔ c ∈ C ∧ c.card = j := by
  simp [conflictLayer]

theorem conflictLayer_uniform (C : ConflictSystem V) (j : ℕ) :
    IsUniform (conflictLayer C j) j := by
  intro c hc
  exact (mem_conflictLayer.mp hc).2

theorem IsConflictSystem.layer {H : Hypergraph V} {C : ConflictSystem V}
    (hC : IsConflictSystem H C) (j : ℕ) :
    IsConflictSystem H (conflictLayer C j) := by
  intro c hc
  exact hC c (conflictLayer_subset C j hc)

@[simp] theorem conflictFree_empty {C : ConflictSystem V} (hC : ∅ ∉ C) :
    ConflictFree C ∅ := by
  intro c hc hsub
  have : c = ∅ := Finset.subset_empty.mp hsub
  exact hC (this ▸ hc)

theorem ConflictFree.mono_family {C : ConflictSystem V} {M N : Hypergraph V}
    (hM : ConflictFree C M) (hNM : N ⊆ M) : ConflictFree C N := by
  intro c hc hcn
  exact hM c hc (hcn.trans hNM)

theorem ConflictFree.mono_conflicts {C D : ConflictSystem V} {M : Hypergraph V}
    (hC : ConflictFree C M) (hDC : D ⊆ C) : ConflictFree D M := by
  intro c hc
  exact hC c (hDC hc)

theorem not_conflictFree_iff {C : ConflictSystem V} {M : Hypergraph V} :
    ¬ConflictFree C M ↔ ∃ c ∈ C, c ⊆ M := by
  simp [ConflictFree]

theorem conflictFree_iff_filter_eq_empty {C : ConflictSystem V}
    {M : Hypergraph V} :
    ConflictFree C M ↔ C.filter (· ⊆ M) = ∅ := by
  simp [ConflictFree, Finset.filter_eq_empty_iff]

theorem mem_conflictLink {C : ConflictSystem V} {e : Finset V}
    {s : Hypergraph V} :
    s ∈ conflictLink C e ↔ ∃ c ∈ C, e ∈ c ∧ c.erase e = s := by
  constructor
  · intro hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, rfl⟩
  · rintro ⟨c, hcC, hec, rfl⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hcC, hec⟩, rfl⟩

theorem mem_conflictLinkLayer {C : ConflictSystem V} {e : Finset V}
    {j : ℕ} {s : Hypergraph V} :
    s ∈ conflictLinkLayer C e j ↔
      (∃ c ∈ C, e ∈ c ∧ c.erase e = s) ∧ s.card = j := by
  simp [conflictLinkLayer, mem_conflictLink]

theorem IsBounded.conflict_card {C : ConflictSystem V} {d eta : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell eta) {c : Hypergraph V} (hc : c ∈ C) :
    3 ≤ c.card ∧ c.card ≤ ell :=
  hC.1 c hc

theorem IsBounded.empty_not_mem {C : ConflictSystem V} {d eta : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell eta) : ∅ ∉ C := by
  intro hzero
  have := (hC.conflict_card hzero).1
  simp at this

theorem IsBounded.conflictFree_empty {C : ConflictSystem V} {d eta : ℝ}
    {ell : ℕ} (hC : IsBounded C d ell eta) : ConflictFree C ∅ :=
  Erdos136.conflictFree_empty hC.empty_not_mem

theorem IsBounded.layer_degree {C : ConflictSystem V} {d eta : ℝ} {ell j : ℕ}
    (hC : IsBounded C d ell eta) (hj3 : 3 ≤ j) (hjell : j ≤ ell)
    (e : Finset V) :
    (degree (conflictLayer C j) e : ℝ) ≤
      (ell : ℝ) * Real.rpow d ((j : ℝ) - 1) :=
  hC.2.1 j hj3 hjell e

theorem IsBounded.layer_codegree {C : ConflictSystem V} {d eta : ℝ}
    {ell j j' : ℕ} (hC : IsBounded C d ell eta) (hj3 : 3 ≤ j)
    (hjell : j ≤ ell) (hj'2 : 2 ≤ j') (hj'j : j' < j)
    (s : Hypergraph V) (hs : s.card = j') :
    (codegree (conflictLayer C j) s : ℝ) ≤
      Real.rpow d ((j : ℝ) - (j' : ℝ) - eta) :=
  hC.2.2 j hj3 hjell j' hj'2 hj'j s hs

/-! ## Test-function lemmas -/

theorem IsTestFunction.nonneg {H : Hypergraph V} {j ell : ℕ}
    {w : TestWeight V} (hw : IsTestFunction H j ell w) (S : Hypergraph V) :
    0 ≤ w S :=
  hw.1 S

theorem IsTestFunction.le {H : Hypergraph V} {j ell : ℕ}
    {w : TestWeight V} (hw : IsTestFunction H j ell w) (S : Hypergraph V) :
    w S ≤ (ell : ℝ) :=
  hw.2.1 S

theorem IsTestFunction.eq_zero_of_card_ne {H : Hypergraph V} {j ell : ℕ}
    {w : TestWeight V} (hw : IsTestFunction H j ell w) {S : Hypergraph V}
    (hS : S.card ≠ j) : w S = 0 :=
  hw.2.2.1 S hS

theorem IsTestFunction.eq_zero_of_not_matching {H : Hypergraph V} {j ell : ℕ}
    {w : TestWeight V} (hw : IsTestFunction H j ell w) {S : Hypergraph V}
    (hS : ¬IsMatching H S) : w S = 0 :=
  hw.2.2.2 S hS

@[simp] theorem testTotal_empty_of_pos (w : TestWeight V) {j : ℕ} (hj : 0 < j) :
    testTotal w ∅ j = 0 := by
  rw [testTotal, Finset.powersetCard_eq_empty.mpr (by simpa using hj)]
  simp

@[simp] theorem testTotal_zero (w : TestWeight V) (A : Hypergraph V) :
    testTotal w A 0 = w ∅ := by
  simp [testTotal]

theorem testTotal_nonneg {w : TestWeight V} (hw : ∀ S, 0 ≤ w S)
    (A : Hypergraph V) (j : ℕ) : 0 ≤ testTotal w A j := by
  exact Finset.sum_nonneg fun S _ => hw S

theorem testTotal_mono {w : TestWeight V} (hw : ∀ S, 0 ≤ w S)
    {A B : Hypergraph V} (hAB : A ⊆ B) (j : ℕ) :
    testTotal w A j ≤ testTotal w B j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.powersetCard_mono hAB)
  intro S hSB hSA
  exact hw S

theorem testExtension_nonneg {w : TestWeight V} (hw : ∀ S, 0 ≤ w S)
    (A : Hypergraph V) (j : ℕ) (root : Hypergraph V) :
    0 ≤ testExtension w A j root := by
  exact Finset.sum_nonneg fun S _ => hw S

theorem testExtension_le_total {w : TestWeight V} (hw : ∀ S, 0 ≤ w S)
    (A : Hypergraph V) (j : ℕ) (root : Hypergraph V) :
    testExtension w A j root ≤ testTotal w A j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro S hS hnot
  exact hw S

@[simp] theorem testExtension_empty_root (w : TestWeight V)
    (A : Hypergraph V) (j : ℕ) :
    testExtension w A j ∅ = testTotal w A j := by
  simp [testExtension, testTotal]

theorem IsTrackable.isTestFunction {H : Hypergraph V} {C : ConflictSystem V}
    {j ell : ℕ} {d eta : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) : IsTestFunction H j ell w :=
  hw.1

theorem IsTrackable.total_lower {H : Hypergraph V} {C : ConflictSystem V}
    {j ell : ℕ} {d eta : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) :
    Real.rpow d ((j : ℝ) + eta) ≤ testTotal w H j :=
  hw.2.1

theorem IsTrackable.extension_upper {H : Hypergraph V} {C : ConflictSystem V}
    {j ell j' : ℕ} {d eta : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) (hj'1 : 1 ≤ j') (hj'j : j' < j)
    (root : Hypergraph V) (hroot : root ⊆ H) (hrootcard : root.card = j') :
    testExtension w H j root ≤
      testTotal w H j / Real.rpow d ((j' : ℝ) + eta) :=
  hw.2.2.1 j' hj'1 hj'j root hroot hrootcard

theorem IsTrackable.link_intersection_upper
    {H : Hypergraph V} {C : ConflictSystem V} {j ell j' : ℕ}
    {d eta : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) {S : Hypergraph V}
    (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S)
    {e f : Finset V} (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f)
    (hj'1 : 1 ≤ j') (hj'ell : j' < ell) :
    (((conflictLinkLayer C e j') ∩ conflictLinkLayer C f j').card : ℝ) ≤
      Real.rpow d ((j' : ℝ) - eta) :=
  hw.2.2.2.1 S hSH hwS e he f hf hef j' hj'1 hj'ell

theorem IsTrackable.eq_zero_of_contains_conflict
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d eta : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) {S : Hypergraph V}
    (hSH : S ∈ H.powersetCard j) (hconflict : ∃ c ∈ C, c ⊆ S) : w S = 0 :=
  hw.2.2.2.2 S hSH hconflict

end Erdos136
