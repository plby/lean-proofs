/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Hypergraph

/-!
# Weight bookkeeping for the finite container algorithm

This file contains the quantitative, but still purely finite, part of the
Campos--Samotij container algorithm.  It is deliberately independent of the
recursive implementation of the algorithm: the latter can instantiate the
lemmas below with its successive antichains.
-/

open scoped BigOperators

namespace Erdos565
namespace ContainerWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

open Hypergraph

/-- Deleting a fixed subset is injective on the sets which contain it. -/
theorem sdiff_injective_on_supersets (L : Finset V) :
    Set.InjOn (fun E : Finset V => E \ L) {E | L ⊆ E} := by
  intro A hLA B hLB h
  rw [Set.mem_setOf_eq] at hLA hLB
  change A \ L = B \ L at h
  calc
    A = L ∪ (A \ L) := (Finset.union_sdiff_of_subset hLA).symm
    _ = L ∪ (B \ L) := congrArg (fun X => L ∪ X) h
    _ = B := Finset.union_sdiff_of_subset hLB

/-- Taking a link does not identify two edges containing the seed. -/
theorem card_link_eq_degree (H : Hypergraph V) (L : Finset V) :
    (H.link L).card = H.degree L := by
  rw [link, degree]
  exact Finset.card_image_iff.mpr fun A hA B hB h =>
    sdiff_injective_on_supersets L (Finset.mem_filter.mp hA).2
      (Finset.mem_filter.mp hB).2 h

/-- A link of an `a`-uniform layer is `(a-|L|)`-uniform. -/
theorem link_layer_edge_card {H : Hypergraph V} {a : ℕ} {L F : Finset V}
    (hF : F ∈ (H.layer a).link L) : F.card = a - L.card := by
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.card_sdiff_of_subset hLE, (mem_layer.mp hE).2]

/-- If the seed is smaller than the uniformity, the link has no empty edge. -/
theorem empty_not_mem_link_layer_of_card_lt {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) : ∅ ∉ (H.layer a).link L := by
  intro h
  have hc : (0 : ℕ) = a - L.card := by
    simpa using link_layer_edge_card h
  omega

/-- On a uniform layer and below the top rank, strict and ordinary links agree. -/
theorem strictLink_layer_eq_link_of_card_lt {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) :
    (H.layer a).strictLink L = (H.layer a).link L := by
  simp [strictLink, empty_not_mem_link_layer_of_card_lt hLa]

/-- Exact `p`-weight of a strict link in a uniform layer. -/
theorem pWeight_strictLink_layer {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) (p : ℝ) :
    ((H.layer a).strictLink L).pWeight p =
      (H.layer a).degree L * p ^ (a - L.card) := by
  rw [strictLink_layer_eq_link_of_card_lt hLa, pWeight, weight]
  calc
    ∑ F ∈ (H.layer a).link L, p ^ F.card =
        ∑ _F ∈ (H.layer a).link L, p ^ (a - L.card) := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [link_layer_edge_card hF]
    _ = ((H.layer a).link L).card * p ^ (a - L.card) := by simp
    _ = (H.layer a).degree L * p ^ (a - L.card) := by
      rw [card_link_eq_degree]

/-- The strict-link weight, restored by the weight of the seed, equals the
weight of all layer edges containing the seed. -/
theorem seed_mul_pWeight_strictLink_layer {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) (p : ℝ) :
    p ^ L.card * ((H.layer a).strictLink L).pWeight p =
      (H.layer a).degree L * p ^ a := by
  rw [pWeight_strictLink_layer hLa]
  calc
    p ^ L.card * ((H.layer a).degree L * p ^ (a - L.card)) =
        (H.layer a).degree L * (p ^ L.card * p ^ (a - L.card)) := by ring
    _ = (H.layer a).degree L * p ^ (L.card + (a - L.card)) := by rw [pow_add]
    _ = (H.layer a).degree L * p ^ a := by congr 2 <;> omega

/-- Incidence double counting for one uniform layer. -/
theorem sum_singleton_degree_layer (H : Hypergraph V) (a : ℕ) :
    ∑ v : V, (H.layer a).degree {v} = a * (H.layer a).card := by
  classical
  calc
    ∑ v : V, (H.layer a).degree {v} =
        ∑ v : V, ∑ E ∈ H.layer a, if v ∈ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1
      ext E
      simp
    _ = ∑ E ∈ H.layer a, ∑ v : V, if v ∈ E then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ E ∈ H.layer a, E.card := by
      apply Finset.sum_congr rfl
      intro E _
      simp
    _ = ∑ _E ∈ H.layer a, a := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [(mem_layer.mp hE).2]
    _ = a * (H.layer a).card := by simp [mul_comm]

/-- Weighted incidence double counting for one uniform layer.  This is the
identity used to find a seed when the stopping test fails. -/
theorem sum_singleton_strictLink_pWeight_layer (H : Hypergraph V) (a : ℕ)
    (ha : 2 ≤ a) (p : ℝ) :
    ∑ v : V, p * ((H.layer a).strictLink {v}).pWeight p =
      (a : ℝ) * (H.layer a).pWeight p := by
  calc
    ∑ v : V, p * ((H.layer a).strictLink {v}).pWeight p =
        ∑ v : V, ((H.layer a).degree {v} : ℝ) * p ^ a := by
      apply Finset.sum_congr rfl
      intro v _
      simpa using seed_mul_pWeight_strictLink_layer
        (H := H) (L := {v}) (a := a) (by simp; omega) p
    _ = ((∑ v : V, (H.layer a).degree {v} : ℕ) : ℝ) * p ^ a := by
      simp [Finset.sum_mul]
    _ = ((a * (H.layer a).card : ℕ) : ℝ) * p ^ a := by
      rw [sum_singleton_degree_layer]
    _ = (a : ℝ) * (H.layer a).pWeight p := by
      rw [pWeight_layer]
      push_cast
      ring

/-- The old edges which strictly contain a fixed seed. -/
def strictSupersets (H : Hypergraph V) (L : Finset V) : Hypergraph V :=
  H.filter fun E => L ⊂ E

@[simp] theorem mem_strictSupersets {H : Hypergraph V} {L E : Finset V} :
    E ∈ strictSupersets H L ↔ E ∈ H ∧ L ⊂ E := by
  simp [strictSupersets]

theorem union_seed_mem_strictSupersets_of_mem_strictLink
    {H : Hypergraph V} {L F : Finset V} (hF : F ∈ H.strictLink L) :
    L ∪ F ∈ strictSupersets H L := by
  obtain ⟨hne, E, hEH, hLE, hdiff⟩ := mem_strictLink.mp hF
  have hEq : L ∪ F = E := by
    rw [← hdiff]
    exact Finset.union_sdiff_of_subset hLE
  rw [hEq, mem_strictSupersets]
  refine ⟨hEH, Finset.ssubset_iff_subset_ne.mpr ⟨hLE, ?_⟩⟩
  intro hEqLE
  have : E \ L = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr
    (hEqLE ▸ Finset.Subset.rfl)
  exact hne (hdiff ▸ this)

theorem union_seed_injective_on_strictLink (H : Hypergraph V) (L : Finset V) :
    Set.InjOn (fun F : Finset V => L ∪ F) {F | F ∈ H.strictLink L} := by
  intro F hF G hG hEq
  have hFd : Disjoint F L :=
    link_edge_disjoint (H := H) (S := L) (strictLink_subset_link H L hF)
  have hGd : Disjoint G L :=
    link_edge_disjoint (H := H) (S := L) (strictLink_subset_link H L hG)
  have h := congrArg (fun X : Finset V => X \ L) hEq
  have hdiff : F \ L = G \ L := by simpa [Finset.union_sdiff_left] using h
  calc
    F = F \ L := (Finset.sdiff_eq_self_of_disjoint hFd).symm
    _ = G \ L := hdiff
    _ = G := Finset.sdiff_eq_self_of_disjoint hGd

theorem exists_strictLink_union_seed_eq_of_mem_strictSupersets
    {H : Hypergraph V} {L E : Finset V} (hE : E ∈ strictSupersets H L) :
    ∃ F ∈ H.strictLink L, L ∪ F = E := by
  obtain ⟨hEH, hLE⟩ := mem_strictSupersets.mp hE
  refine ⟨E \ L, ?_, Finset.union_sdiff_of_subset hLE.1⟩
  rw [mem_strictLink]
  refine ⟨Finset.nonempty_iff_ne_empty.mp
      (Finset.sdiff_nonempty.mpr (fun hEL => hLE.2 hEL)),
    E, hEH, hLE.1, rfl⟩

/-- Restoring the seed restores exactly the original edge weight.  This is
the basic identity behind all charging estimates in the algorithm. -/
theorem seed_mul_pWeight_strictLink (H : Hypergraph V) (L : Finset V) (p : ℝ) :
    p ^ L.card * (H.strictLink L).pWeight p =
      (strictSupersets H L).pWeight p := by
  rw [pWeight, pWeight, weight, weight, Finset.mul_sum]
  refine Finset.sum_bij (fun F _ => L ∪ F) ?_ ?_ ?_ ?_
  · intro F hF
    exact union_seed_mem_strictSupersets_of_mem_strictLink hF
  · intro F hF G hG hEq
    exact union_seed_injective_on_strictLink H L hF hG hEq
  · intro E hE
    obtain ⟨F, hF, hEq⟩ :=
      exists_strictLink_union_seed_eq_of_mem_strictSupersets hE
    exact ⟨F, hF, hEq⟩
  · intro F hF
    have hdis : Disjoint L F :=
      (link_edge_disjoint (H := H) (S := L)
        (strictLink_subset_link H L hF)).symm
    rw [Finset.card_union_of_disjoint hdis, pow_add]

/-- The fixed-layer identity above is also an immediate upper bound whenever
one has a numerical degree estimate. -/
theorem pWeight_strictLink_layer_le {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hLa : L.card < a) {p R : ℝ}
    (hdegree : ((H.layer a).degree L : ℝ) * p ^ (a - L.card) ≤ R) :
    ((H.layer a).strictLink L).pWeight p ≤ R := by
  rwa [pWeight_strictLink_layer hLa]

/-- Edges of rank strictly below `s`. -/
def belowRank (H : Hypergraph V) (s : ℕ) : Hypergraph V :=
  H.filter fun E => E.card < s

@[simp] theorem mem_belowRank {H : Hypergraph V} {s : ℕ} {E : Finset V} :
    E ∈ belowRank H s ↔ E ∈ H ∧ E.card < s := by
  simp [belowRank]

/-- Edges with at least two vertices. -/
def aboveOne (H : Hypergraph V) : Hypergraph V :=
  H.filter fun E => 2 ≤ E.card

@[simp] theorem mem_aboveOne {H : Hypergraph V} {E : Finset V} :
    E ∈ aboveOne H ↔ E ∈ H ∧ 2 ≤ E.card := by
  simp [aboveOne]

/-- Vertices which are not forbidden by a singleton edge. -/
def availableVertices (H : Hypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∉ H

@[simp] theorem mem_availableVertices {H : Hypergraph V} {v : V} :
    v ∈ availableVertices H ↔ ({v} : Finset V) ∉ H := by
  simp [availableVertices]

/-- `p`-weight is subadditive under union. -/
theorem pWeight_union_le (H K : Hypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    (H ∪ K).pWeight p ≤ H.pWeight p + K.pWeight p := by
  have hEq : H ∪ K = H ∪ (K \ H) := by
    ext E
    simp [or_and_right]
  have hdis : Disjoint H (K \ H) := by
    rw [Finset.disjoint_left]
    intro E hEH hEK
    exact (Finset.mem_sdiff.mp hEK).2 hEH
  rw [hEq, pWeight, weight_union hdis]
  exact add_le_add_right
    (pWeight_mono (H := K \ H) (K := K) Finset.sdiff_subset (p := p) hp) _

/-- Union bound for a finite union of hypergraphs. -/
theorem pWeight_biUnion_le {A : Type*} [DecidableEq A]
    (S : Finset A) (K : A → Hypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    Hypergraph.pWeight (S.biUnion K) p ≤ ∑ a ∈ S, (K a).pWeight p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (pWeight_union_le (K a) (S.biUnion K) hp).trans
        (add_le_add le_rfl ih)

/-- Every strict link in the below-rank family occurs in the strict link of
one of its uniform layers. -/
theorem strictLink_belowRank_subset_biUnion_layers (H : Hypergraph V)
    (L : Finset V) (s : ℕ) :
    (belowRank H s).strictLink L ⊆
      (Finset.range s).biUnion (fun a => (H.layer a).strictLink L) := by
  intro F hF
  obtain ⟨hne, E, hE, hLE, hdiff⟩ := mem_strictLink.mp hF
  obtain ⟨hEH, hEs⟩ := mem_belowRank.mp hE
  rw [Finset.mem_biUnion]
  refine ⟨E.card, Finset.mem_range.mpr hEs, ?_⟩
  exact mem_strictLink.mpr
    ⟨hne, E, mem_layer.mpr ⟨hEH, rfl⟩, hLE, hdiff⟩

/-- Low link bounds on the uniform layers sum to a low link bound on all
edges below the top rank. -/
theorem pWeight_strictLink_belowRank_le_sum_layers
    (H : Hypergraph V) (L : Finset V) (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((belowRank H s).strictLink L).pWeight p ≤
      ∑ a ∈ Finset.range s, ((H.layer a).strictLink L).pWeight p := by
  calc
    ((belowRank H s).strictLink L).pWeight p ≤
        Hypergraph.pWeight ((Finset.range s).biUnion
          (fun a => (H.layer a).strictLink L)) p :=
      pWeight_mono (strictLink_belowRank_subset_biUnion_layers H L s) hp
    _ ≤ ∑ a ∈ Finset.range s, ((H.layer a).strictLink L).pWeight p :=
      pWeight_biUnion_le _ _ hp

/-- Summing `s` bounds of size `1/(2s)` gives `1/2`. -/
theorem sum_range_le_half {s : ℕ} (hs : 0 < s) {f : ℕ → ℝ}
    (hf : ∀ a ∈ Finset.range s, f a ≤ 1 / (2 * (s : ℝ))) :
    ∑ a ∈ Finset.range s, f a ≤ 1 / 2 := by
  calc
    ∑ a ∈ Finset.range s, f a ≤
        ∑ _a ∈ Finset.range s, 1 / (2 * (s : ℝ)) :=
      Finset.sum_le_sum hf
    _ = (s : ℝ) * (1 / (2 * (s : ℝ))) := by simp
    _ = 1 / 2 := by
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
      have hden : (2 : ℝ) * s ≠ 0 := mul_ne_zero (by norm_num) hs0
      rw [mul_one_div]
      rw [div_eq_iff hden]
      ring

/-- The form of the low-link invariant consumed by the charging argument. -/
theorem pWeight_strictLink_belowRank_le_half
    (H : Hypergraph V) (L : Finset V) {s : ℕ} (hs : 0 < s)
    {p : ℝ} (hp : 0 ≤ p)
    (hlayer : ∀ a ∈ Finset.range s,
      ((H.layer a).strictLink L).pWeight p ≤ 1 / (2 * (s : ℝ))) :
    ((belowRank H s).strictLink L).pWeight p ≤ 1 / 2 := by
  exact (pWeight_strictLink_belowRank_le_sum_layers H L s hp).trans
    (sum_range_le_half hs hlayer)

/-- Old edges removed by inserting one of the replacement edges. -/
def removedBy (H C : Hypergraph V) : Hypergraph V :=
  H.filter fun E => ∃ F ∈ C, F ⊆ E

@[simp] theorem mem_removedBy {H C : Hypergraph V} {E : Finset V} :
    E ∈ removedBy H C ↔ E ∈ H ∧ ∃ F ∈ C, F ⊆ E := by
  simp [removedBy]

/-- Removed edges are covered by the strict supersets of replacement edges,
provided no replacement edge was already old. -/
theorem removedBy_subset_biUnion_strictSupersets {H C : Hypergraph V}
    (hout : ∀ F ∈ C, F ∉ H) :
    removedBy H C ⊆ C.biUnion (strictSupersets H) := by
  intro E hE
  obtain ⟨hEH, F, hFC, hFE⟩ := mem_removedBy.mp hE
  rw [Finset.mem_biUnion]
  refine ⟨F, hFC, mem_strictSupersets.mpr ⟨hEH, ?_⟩⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hFE, fun h => hout F hFC (h ▸ hEH)⟩

/-- Charging inequality: charge each removed old edge to a replacement edge
which it contains. -/
theorem pWeight_removedBy_le_sum_seed_links {H C : Hypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hout : ∀ F ∈ C, F ∉ H) :
    (removedBy H C).pWeight p ≤
      ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p := by
  calc
    (removedBy H C).pWeight p ≤
        Hypergraph.pWeight (C.biUnion (strictSupersets H)) p :=
      pWeight_mono (removedBy_subset_biUnion_strictSupersets hout) hp
    _ ≤ ∑ F ∈ C, (strictSupersets H F).pWeight p :=
      pWeight_biUnion_le _ _ hp
    _ = ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p := by
      apply Finset.sum_congr rfl
      intro F _
      rw [seed_mul_pWeight_strictLink]

/-- If every replacement edge has a low old link, at most half of the
replacement weight is lost by deletion. -/
theorem pWeight_removedBy_le_half_mul {H C : Hypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hout : ∀ F ∈ C, F ∉ H)
    (hlow : ∀ F ∈ C, (H.strictLink F).pWeight p ≤ 1 / 2) :
    (removedBy H C).pWeight p ≤ (1 / 2 : ℝ) * C.pWeight p := by
  calc
    (removedBy H C).pWeight p ≤
        ∑ F ∈ C, p ^ F.card * (H.strictLink F).pWeight p :=
      pWeight_removedBy_le_sum_seed_links hp hout
    _ ≤ ∑ F ∈ C, p ^ F.card * (1 / 2 : ℝ) := by
      exact Finset.sum_le_sum fun F hF =>
        mul_le_mul_of_nonneg_left (hlow F hF) (pow_nonneg hp _)
    _ = (1 / 2 : ℝ) * C.pWeight p := by
      rw [pWeight, weight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      ring

/-- Weight decomposition after deleting a subfamily. -/
theorem pWeight_sdiff_add {H D : Hypergraph V} (hDH : D ⊆ H) (p : ℝ) :
    (H \ D).pWeight p + D.pWeight p = H.pWeight p := by
  have hinter : H ∩ D = D := by
    exact Finset.inter_eq_right.mpr hDH
  simpa [pWeight, hinter] using
    (weight_sdiff_add_weight_inter H D (fun E : Finset V => p ^ E.card))

/-- Abstract gain inequality: all retained old edges and all inserted edges
are present in the next family. -/
theorem pWeight_retained_inserted_le {H D C K : Hypergraph V}
    {p : ℝ} (hp : 0 ≤ p) (hDH : D ⊆ H)
    (hkeep : H \ D ⊆ K) (hinsert : C ⊆ K)
    (hdis : Disjoint (H \ D) C) :
    H.pWeight p + C.pWeight p - D.pWeight p ≤ K.pWeight p := by
  have hunion : (H \ D) ∪ C ⊆ K := by
    intro E hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact hkeep hE
    · exact hinsert hE
  have hmono := pWeight_mono hunion hp
  rw [pWeight, weight_union hdis] at hmono
  change (H \ D).pWeight p + C.pWeight p ≤ K.pWeight p at hmono
  have hdecomp := pWeight_sdiff_add hDH p
  nlinarith

/-- One accepting step gains at least `1/(8s)` in below-rank weight once
the replacement has weight at least `1/(4s)` and at most half of it is
charged to deleted edges. -/
theorem accepting_step_gain {H D C K : Hypergraph V} {s : ℕ}
    (hs : 0 < s) {p : ℝ} (hp : 0 ≤ p) (hDH : D ⊆ H)
    (hkeep : H \ D ⊆ K) (hinsert : C ⊆ K)
    (hdis : Disjoint (H \ D) C)
    (hremoved : D.pWeight p ≤ (1 / 2 : ℝ) * C.pWeight p)
    (hreplacement : 1 / (4 * (s : ℝ)) ≤ C.pWeight p) :
    H.pWeight p + 1 / (8 * (s : ℝ)) ≤ K.pWeight p := by
  have hbase := pWeight_retained_inserted_le hp hDH hkeep hinsert hdis
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hfour : (0 : ℝ) < 4 * s := mul_pos (by norm_num) hsR
  have height : (0 : ℝ) < 8 * s := mul_pos (by norm_num) hsR
  have hhalf : (1 / 2 : ℝ) * (1 / (4 * (s : ℝ))) =
      1 / (8 * (s : ℝ)) := by
    rw [one_div_mul_one_div]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_left hreplacement (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Telescoping a finite list of one-step gain inequalities. -/
theorem telescope_step_gains {w gain : ℕ → ℝ} {k : ℕ}
    (hstep : ∀ j < k, w j + gain j ≤ w (j + 1)) :
    w 0 + ∑ j ∈ Finset.range k, gain j ≤ w k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hih : w 0 + ∑ j ∈ Finset.range k, gain j ≤ w k :=
        ih (fun j hj => hstep j (hj.trans (Nat.lt_succ_self k)))
      have hk := hstep k (Nat.lt_succ_self k)
      have : w 0 + (∑ j ∈ Finset.range k, gain j) + gain k ≤ w (k + 1) := by
        nlinarith
      simpa [Nat.succ_eq_add_one, add_assoc] using this

/-- A convenient accepted-step form of telescoping. -/
theorem telescope_accepting_steps {w : ℕ → ℝ} {accepted : Finset ℕ}
    {k : ℕ} {d : ℝ} (hacc : accepted ⊆ Finset.range k)
    (hstep : ∀ j < k, w j + (if j ∈ accepted then d else 0) ≤ w (j + 1)) :
    w 0 + (accepted.card : ℝ) * d ≤ w k := by
  have htel := telescope_step_gains hstep
  calc
    w 0 + (accepted.card : ℝ) * d =
        w 0 + ∑ j ∈ Finset.range k, if j ∈ accepted then d else 0 := by
      congr 1
      rw [← Finset.sum_filter]
      have heq : (Finset.range k).filter (fun j => j ∈ accepted) = accepted := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => h.2
        · intro hj
          exact ⟨Finset.mem_range.mp (hacc hj), hj⟩
      rw [heq]
      simp
    _ ≤ w k := htel

/-- Numerical consequence of telescoping accepting gains. -/
theorem accepting_count_bound {w : ℕ → ℝ} {accepted : Finset ℕ}
    {k s : ℕ} {M : ℝ} (hs : 0 < s) (hacc : accepted ⊆ Finset.range k)
    (hstep : ∀ j < k,
      w j + (if j ∈ accepted then 1 / (8 * (s : ℝ)) else 0) ≤ w (j + 1))
    (hw0 : 0 ≤ w 0) (hwk : w k ≤ M) :
    (accepted.card : ℝ) ≤ 8 * (s : ℝ) * M := by
  have htel := telescope_accepting_steps hacc hstep
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hden : (0 : ℝ) < 8 * s := mul_pos (by norm_num) hsR
  rw [div_eq_mul_inv] at htel
  have : (accepted.card : ℝ) * (8 * (s : ℝ))⁻¹ ≤ M := by nlinarith
  calc
    (accepted.card : ℝ) =
        ((accepted.card : ℝ) * (8 * (s : ℝ))⁻¹) *
          (8 * (s : ℝ)) := by
      rw [mul_assoc, inv_mul_cancel₀ hden.ne']
      ring
    _ ≤ M * (8 * (s : ℝ)) := mul_le_mul_of_nonneg_right this hden.le
    _ = 8 * (s : ℝ) * M := by ring

/-- If every accepting seed has at most `s` vertices, the union fingerprint
has the advertised `8s²M` bound. -/
theorem fingerprint_card_bound {S : Finset V} {accepted : Finset ℕ}
    {s : ℕ} {M : ℝ}
    (hScard : (S.card : ℝ) ≤ (s : ℝ) * accepted.card)
    (haccept : (accepted.card : ℝ) ≤ 8 * (s : ℝ) * M)
    (hM : 0 ≤ M) :
    (S.card : ℝ) ≤ 8 * (s : ℝ) ^ 2 * M := by
  have hs0 : (0 : ℝ) ≤ s := by positivity
  calc
    (S.card : ℝ) ≤ (s : ℝ) * accepted.card := hScard
    _ ≤ (s : ℝ) * (8 * (s : ℝ) * M) :=
      mul_le_mul_of_nonneg_left haccept hs0
    _ = 8 * (s : ℝ) ^ 2 * M := by ring

/-- Vertices which do occur as singleton edges. -/
def forbiddenVertices (H : Hypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∈ H

@[simp] theorem mem_forbiddenVertices {H : Hypergraph V} {v : V} :
    v ∈ forbiddenVertices H ↔ ({v} : Finset V) ∈ H := by
  simp [forbiddenVertices]

/-- The singleton layer is the image of the forbidden vertices. -/
theorem layer_one_eq_image_forbiddenVertices (H : Hypergraph V) :
    H.layer 1 = (forbiddenVertices H).image fun v => ({v} : Finset V) := by
  ext E
  constructor
  · intro hE
    obtain ⟨hEH, hcard⟩ := mem_layer.mp hE
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Finset.mem_image]
    exact ⟨v, mem_forbiddenVertices.mpr hEH, rfl⟩
  · intro hE
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    exact mem_layer.mpr ⟨mem_forbiddenVertices.mp hv, by simp⟩

theorem card_layer_one_eq_forbiddenVertices (H : Hypergraph V) :
    (H.layer 1).card = (forbiddenVertices H).card := by
  rw [layer_one_eq_image_forbiddenVertices]
  apply Finset.card_image_iff.mpr
  intro v _ w _ h
  simpa using h

/-- Available and forbidden vertices partition the ambient finite type. -/
theorem card_forbidden_add_available (H : Hypergraph V) :
    (forbiddenVertices H).card + (availableVertices H).card = Fintype.card V := by
  simpa [forbiddenVertices, availableVertices] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (p := fun v => ({v} : Finset V) ∈ H))

/-- Exact weight of the terminal singleton layer. -/
theorem pWeight_layer_one (H : Hypergraph V) (p : ℝ) :
    (H.layer 1).pWeight p = p * (forbiddenVertices H).card := by
  rw [pWeight_layer, card_layer_one_eq_forbiddenVertices]
  simp
  ring

/-- Equivalent terminal singleton formula in terms of the available
container vertices. -/
theorem pWeight_layer_one_eq_complement (H : Hypergraph V) (p : ℝ) :
    (H.layer 1).pWeight p =
      p * ((Fintype.card V - (availableVertices H).card : ℕ) : ℝ) := by
  have hcard := card_forbidden_add_available H
  have heq : (forbiddenVertices H).card =
      Fintype.card V - (availableVertices H).card := by omega
  rw [pWeight_layer_one, heq]

/-- A hypergraph with no empty edge is the disjoint union of its singleton
layer and its edges of size at least two. -/
theorem layer_one_union_aboveOne {H : Hypergraph V}
    (hne : ∀ E ∈ H, E.Nonempty) :
    H.layer 1 ∪ aboveOne H = H := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact (mem_layer.mp hE).1
    · exact (mem_aboveOne.mp hE).1
  · intro hEH
    have hpos : 0 < E.card := Finset.card_pos.mpr (hne E hEH)
    by_cases hcard : E.card = 1
    · exact Finset.mem_union_left _ (mem_layer.mpr ⟨hEH, hcard⟩)
    · exact Finset.mem_union_right _ (mem_aboveOne.mpr ⟨hEH, by omega⟩)

theorem disjoint_layer_one_aboveOne (H : Hypergraph V) :
    Disjoint (H.layer 1) (aboveOne H) := by
  rw [Finset.disjoint_left]
  intro E hE1 hE2
  have hcard1 := (mem_layer.mp hE1).2
  have hcard2 := (mem_aboveOne.mp hE2).2
  omega

/-- Terminal total-weight estimate.  The singleton layer contributes exactly
`p` times the number of forbidden vertices, while the stopping inequality
bounds all remaining edges by `p` times the number of available vertices. -/
theorem terminal_pWeight_le (H : Hypergraph V) {p : ℝ} (hp : 0 ≤ p)
    (hne : ∀ E ∈ H, E.Nonempty)
    (hstop : (aboveOne H).pWeight p ≤
      p * (availableVertices H).card) :
    H.pWeight p ≤ p * Fintype.card V := by
  have hdecomp : H.pWeight p =
      (H.layer 1).pWeight p + (aboveOne H).pWeight p := by
    calc
      H.pWeight p = (H.layer 1 ∪ aboveOne H).pWeight p := by
        rw [layer_one_union_aboveOne hne]
      _ = (H.layer 1).pWeight p + (aboveOne H).pWeight p := by
        simpa only [pWeight] using
          (weight_union (disjoint_layer_one_aboveOne H)
            (fun E : Finset V => p ^ E.card))
  have hsingle := pWeight_layer_one H p
  have hcard := card_forbidden_add_available H
  norm_num at hsingle
  have hcardR : ((forbiddenVertices H).card : ℝ) +
      (availableVertices H).card = Fintype.card V := by exact_mod_cast hcard
  rw [hdecomp, hsingle]
  nlinarith

end ContainerWeight
end Erdos565
