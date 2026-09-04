/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.CarrierOdd
import ErdosProblems.Erdos223.FourLowerConstruction
import ErdosProblems.Erdos223.CenteredArcConstruction

/-!
# A shifted three-circle counterexample in dimension seven

For every odd `m ≥ 3`, this module constructs three `m`-point circle blocks
in mutually orthogonal two-planes of `ℝ⁷`.  The two outer circles have
opposite offsets along the remaining axis, while the middle circle is
centered on that axis.  Every cross-block pair is a diameter, the outer
blocks each contribute at least `m` internal diameters, and the middle block
contributes one.  Consequently

`3 * m ^ 2 + 2 * m + 1 ≤ f 7 (3 * m)`.

This exceeds the previously proposed odd-dimensional exact value on these
cardinalities.  The construction records the rank-two-plus-rank-two-plus-rank-two
branch omitted by the published common-center argument.
-/

open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph
open Fintype

namespace Erdos223.SevenCounterexample

noncomputable section

open CarrierOdd

def embedCircle (i : Fin 3) (z : ℝ) (x : Point 2) : Point 7 :=
  EuclideanSpace.single (planeFirst 3 i) (x 0) +
    EuclideanSpace.single (planeSecond 3 i) (x 1) +
      EuclideanSpace.single (axisIndex 3) z

lemma inner_embedCircle (i j : Fin 3) (z w : ℝ) (x y : Point 2) :
    inner ℝ (embedCircle i z x) (embedCircle j w y) =
      (if i = j then inner ℝ x y else 0) + z * w := by
  fin_cases i <;> fin_cases j <;>
    simp [embedCircle, planeFirst, planeSecond, axisIndex,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ] <;>
    ring

lemma norm_embedCircle_sq (i : Fin 3) (z : ℝ) (x : Point 2) :
    ‖embedCircle i z x‖ ^ 2 = ‖x‖ ^ 2 + z ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_embedCircle, if_pos rfl,
    real_inner_self_eq_norm_sq]
  ring

lemma dist_embedCircle_same (i : Fin 3) (z : ℝ) (x y : Point 2) :
    dist (embedCircle i z x) (embedCircle i z y) = dist x y := by
  have hsq : dist (embedCircle i z x) (embedCircle i z y) ^ 2 =
      dist x y ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [inner_embedCircle, inner_embedCircle, inner_embedCircle,
      inner_embedCircle]
    simp only [if_pos]
    rw [real_inner_comm y x]
    ring
  nlinarith [dist_nonneg (x := embedCircle i z x) (y := embedCircle i z y),
    dist_nonneg (x := x) (y := y)]

lemma dist_embedCircle_cross_sq {i j : Fin 3} (hij : i ≠ j)
    (z w : ℝ) (x y : Point 2) :
    dist (embedCircle i z x) (embedCircle j w y) ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 + (z - w) ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_embedCircle, inner_embedCircle, inner_embedCircle,
    inner_embedCircle, if_pos rfl, if_pos rfl, if_neg hij, if_neg hij.symm,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

lemma embedCircle_injective (i : Fin 3) (z : ℝ) :
    Function.Injective (embedCircle i z) := by
  intro x y h
  apply dist_eq_zero.mp
  rw [← dist_embedCircle_same i z x y, h]
  simp

section Count

variable {m : ℕ} {B : Finset (Point 2)}

abbrev D7V (m : ℕ) := Fin 3 × Fin m

def leftEmbedding (e : {x // x ∈ B} ≃ Fin m) : {x // x ∈ B} ↪ D7V m where
  toFun x := (0, e x)
  inj' x y h := e.injective (congrArg Prod.snd h)

def rightEmbedding (e : {x // x ∈ B} ≃ Fin m) : {x // x ∈ B} ↪ D7V m where
  toFun x := (2, e x)
  inj' x y h := e.injective (congrArg Prod.snd h)

def leftLocalGraph (e : {x // x ∈ B} ≃ Fin m) : SimpleGraph (D7V m) :=
  (diameterGraph B).map (leftEmbedding e)

def rightLocalGraph (e : {x // x ∈ B} ≃ Fin m) : SimpleGraph (D7V m) :=
  (diameterGraph B).map (rightEmbedding e)

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) :
    Fintype (leftLocalGraph e).edgeSet := by
  rw [leftLocalGraph]
  infer_instance

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) :
    Fintype (rightLocalGraph e).edgeSet := by
  rw [rightLocalGraph]
  infer_instance

lemma card_edgeFinset_leftLocalGraph (e : {x // x ∈ B} ≃ Fin m) :
    (leftLocalGraph e).edgeFinset.card = diameterPairCount B := by
  exact SimpleGraph.card_edgeFinset_map (leftEmbedding e) (diameterGraph B)

lemma card_edgeFinset_rightLocalGraph (e : {x // x ∈ B} ≃ Fin m) :
    (rightLocalGraph e).edgeFinset.card = diameterPairCount B := by
  exact SimpleGraph.card_edgeFinset_map (rightEmbedding e) (diameterGraph B)

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) :
    DecidableRel (leftLocalGraph e).Adj := Classical.decRel _

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) :
    DecidableRel (rightLocalGraph e).Adj := Classical.decRel _

lemma cross_disjoint_left (e : {x // x ∈ B} ≃ Fin m) :
    Disjoint (SimpleGraph.completeEquipartiteGraph 3 m) (leftLocalGraph e) := by
  classical
  rw [disjoint_iff_inf_le]
  intro v w h
  rcases h with ⟨hcross, hlocal⟩
  rw [leftLocalGraph, SimpleGraph.map_adj] at hlocal
  obtain ⟨x, y, _hxy, hx, hy⟩ := hlocal
  have hv := congrArg Prod.fst hx
  have hw := congrArg Prod.fst hy
  simp only [SimpleGraph.emptyGraph_eq_bot, SimpleGraph.bot_adj] at hv hw
  exact (SimpleGraph.completeEquipartiteGraph_adj.mp hcross) (hv.symm.trans hw)

lemma cross_disjoint_right (e : {x // x ∈ B} ≃ Fin m) :
    Disjoint (SimpleGraph.completeEquipartiteGraph 3 m) (rightLocalGraph e) := by
  classical
  rw [disjoint_iff_inf_le]
  intro v w h
  rcases h with ⟨hcross, hlocal⟩
  rw [rightLocalGraph, SimpleGraph.map_adj] at hlocal
  obtain ⟨x, y, _hxy, hx, hy⟩ := hlocal
  have hv := congrArg Prod.fst hx
  have hw := congrArg Prod.fst hy
  simp only [SimpleGraph.emptyGraph_eq_bot, SimpleGraph.bot_adj] at hv hw
  exact (SimpleGraph.completeEquipartiteGraph_adj.mp hcross) (hv.symm.trans hw)

lemma left_disjoint_right (e : {x // x ∈ B} ≃ Fin m) :
    Disjoint (leftLocalGraph e) (rightLocalGraph e) := by
  classical
  rw [disjoint_iff_inf_le]
  intro v w h
  rcases h with ⟨hl, hr⟩
  rw [leftLocalGraph, SimpleGraph.map_adj] at hl
  rw [rightLocalGraph, SimpleGraph.map_adj] at hr
  obtain ⟨x, y, _hxy, hx, _hy⟩ := hl
  obtain ⟨x', y', _hxy', hx', _hy'⟩ := hr
  have hv := congrArg Prod.fst (hx.trans hx'.symm)
  change (0 : Fin 3) = 2 at hv
  omega

def baseGraph (e : {x // x ∈ B} ≃ Fin m) : SimpleGraph (D7V m) :=
  SimpleGraph.completeEquipartiteGraph 3 m ⊔ leftLocalGraph e ⊔ rightLocalGraph e

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) :
    DecidableRel (baseGraph e).Adj := Classical.decRel _

lemma edgeFinset_baseGraph (e : {x // x ∈ B} ≃ Fin m) :
    (baseGraph e).edgeFinset =
      ((SimpleGraph.completeEquipartiteGraph 3 m).edgeFinset ∪
        (leftLocalGraph e).edgeFinset) ∪ (rightLocalGraph e).edgeFinset := by
  classical
  ext q
  simp only [SimpleGraph.mem_edgeFinset]
  simp [baseGraph]
  tauto

lemma card_edgeFinset_baseGraph (e : {x // x ∈ B} ≃ Fin m) :
    (baseGraph e).edgeFinset.card = 3 * m ^ 2 + 2 * diameterPairCount B := by
  classical
  have hcrossleft : Disjoint
      (SimpleGraph.completeEquipartiteGraph 3 m).edgeFinset (leftLocalGraph e).edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr (cross_disjoint_left e)
  have hcrossright : Disjoint
      (SimpleGraph.completeEquipartiteGraph 3 m).edgeFinset (rightLocalGraph e).edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr (cross_disjoint_right e)
  have hleftright : Disjoint
      (leftLocalGraph e).edgeFinset (rightLocalGraph e).edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr (left_disjoint_right e)
  have hunionright : Disjoint
      ((SimpleGraph.completeEquipartiteGraph 3 m).edgeFinset ∪
        (leftLocalGraph e).edgeFinset) (rightLocalGraph e).edgeFinset :=
    (Finset.disjoint_union_left).2 ⟨hcrossright, hleftright⟩
  rw [edgeFinset_baseGraph]
  rw [Finset.card_union_of_disjoint hunionright,
    Finset.card_union_of_disjoint hcrossleft,
    SimpleGraph.card_edgeFinset_completeEquipartiteGraph,
    card_edgeFinset_leftLocalGraph, card_edgeFinset_rightLocalGraph]
  simp [diameterPairCount]
  ring

def d7SourceGraph (e : {x // x ∈ B} ≃ Fin m) (hm : 2 ≤ m) :
    SimpleGraph (D7V m) :=
  baseGraph e ⊔ SimpleGraph.edge (1, ⟨0, by omega⟩) (1, ⟨m - 1, by omega⟩)

noncomputable instance (e : {x // x ∈ B} ≃ Fin m) (hm : 2 ≤ m) :
    DecidableRel (d7SourceGraph e hm).Adj := Classical.decRel _

lemma baseGraph_not_adj_middle (e : {x // x ∈ B} ≃ Fin m) (hm : 2 ≤ m) :
    ¬(baseGraph e).Adj (1, ⟨0, by omega⟩) (1, ⟨m - 1, by omega⟩) := by
  classical
  intro h
  rcases h with (hcross | hleft) | hright
  · exact (SimpleGraph.completeEquipartiteGraph_adj.mp hcross) rfl
  · rw [leftLocalGraph, SimpleGraph.map_adj] at hleft
    obtain ⟨x, y, _hxy, hx, _hy⟩ := hleft
    have := congrArg Prod.fst hx
    change (0 : Fin 3) = 1 at this
    omega
  · rw [rightLocalGraph, SimpleGraph.map_adj] at hright
    obtain ⟨x, y, _hxy, hx, _hy⟩ := hright
    have := congrArg Prod.fst hx
    change (2 : Fin 3) = 1 at this
    omega

lemma card_edgeFinset_d7SourceGraph (e : {x // x ∈ B} ≃ Fin m) (hm : 2 ≤ m) :
    (d7SourceGraph e hm).edgeFinset.card =
      3 * m ^ 2 + 2 * diameterPairCount B + 1 := by
  classical
  let u : D7V m := ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
  let v : D7V m := ((1 : Fin 3), (⟨m - 1, by omega⟩ : Fin m))
  have hne : u ≠ v := by
    intro h
    have hfin : (⟨0, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ :=
      congrArg Prod.snd h
    have := congrArg Fin.val hfin
    simp at this
    omega
  have hnot : s(u, v) ∉ (baseGraph e).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [u, v] using baseGraph_not_adj_middle e hm
  have hE : (d7SourceGraph e hm).edgeFinset =
      (baseGraph e).edgeFinset ∪ {s(u, v)} := by
    ext q
    simp only [SimpleGraph.mem_edgeFinset]
    simp only [Finset.union_singleton, Finset.mem_insert, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro (hbase | ⟨hq, _⟩)
      · exact Or.inr hbase
      · exact Or.inl hq
    · rintro (hq | hbase)
      · refine Or.inr ⟨hq, ?_⟩
        subst q
        rw [Sym2.mk_isDiag_iff]
        exact hne
      · exact Or.inl hbase
  rw [hE, Finset.card_union_of_disjoint]
  · rw [card_edgeFinset_baseGraph]
    simp
  · rw [Finset.disjoint_singleton_right]
    exact hnot

end Count

/-! The concrete shifted three-circle configuration. -/

section Configuration

variable {m : ℕ} {B : Finset (Point 2)}

def axisHeight (t : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then -t else if i = 1 then 0 else t

def planePoint (e : {x // x ∈ B} ≃ Fin m) (r : ℝ) (hm : 2 ≤ m)
    (i : Fin 3) (k : Fin m) : Point 2 :=
  if i = 1 then GenericArc.arcPoint r hm k else (e.symm k).1

def d7Point (e : {x // x ∈ B} ≃ Fin m) (r t : ℝ) (hm : 2 ≤ m)
    (v : D7V m) : Point 7 :=
  embedCircle v.1 (axisHeight t v.1) (planePoint e r hm v.1 v.2)

lemma norm_planePoint_sq (e : {x // x ∈ B} ≃ Fin m) (r a : ℝ)
    (hm : 2 ≤ m) (hr : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a) (i : Fin 3) (k : Fin m) :
    ‖planePoint e r hm i k‖ ^ 2 = if i = 1 then r ^ 2 else a := by
  fin_cases i
  · simpa [planePoint] using hBnorm (e.symm k).1 (e.symm k).2
  · simpa [planePoint] using GenericArc.norm_arcPoint_sq hr hm k
  · simpa [planePoint] using hBnorm (e.symm k).1 (e.symm k).2

lemma d7Point_cross_dist_eq_one
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 0 < r) (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1)
    {i j : Fin 3} (hij : i ≠ j) (k l : Fin m) :
    dist (d7Point e r t hm (i, k)) (d7Point e r t hm (j, l)) = 1 := by
  let D := dist (d7Point e r t hm (i, k)) (d7Point e r t hm (j, l))
  have hsq := dist_embedCircle_cross_sq hij (axisHeight t i) (axisHeight t j)
    (planePoint e r hm i k) (planePoint e r hm j l)
  change D ^ 2 = _ at hsq
  rw [norm_planePoint_sq e r a hm hr hBnorm i k,
    norm_planePoint_sq e r a hm hr hBnorm j l] at hsq
  have hd : 0 ≤ D := dist_nonneg
  change D = 1
  fin_cases i <;> fin_cases j <;>
    simp [axisHeight] at hsq ⊢ <;> try contradiction
  all_goals
    have hDsq : D ^ 2 = 1 := by nlinarith [houter, hmixed]
    rcases sq_eq_one_iff.mp hDsq with hD | hD
    · exact hD
    · nlinarith

lemma d7Point_same_dist_le_one
    (e : {x // x ∈ B} ≃ Fin m) (r t : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hB : IsDiameterOne B)
    (i : Fin 3) (k l : Fin m) :
    dist (d7Point e r t hm (i, k)) (d7Point e r t hm (i, l)) ≤ 1 := by
  rw [d7Point, d7Point, dist_embedCircle_same]
  fin_cases i
  · simpa [planePoint] using hB.dist_le (e.symm k).2 (e.symm l).2
  · simpa [planePoint] using GenericArc.dist_arcPoint_le_one hr hm k l
  · simpa [planePoint] using hB.dist_le (e.symm k).2 (e.symm l).2

lemma d7Point_injective
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    Function.Injective (d7Point e r t hm) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hij : i = j := by
    by_contra hij
    have hd := d7Point_cross_dist_eq_one e r t a hm hrpos hBnorm
      houter hmixed hij k l
    rw [h] at hd
    simp at hd
  subst j
  have hp : planePoint e r hm i k = planePoint e r hm i l :=
    embedCircle_injective i (axisHeight t i) h
  have hkl : k = l := by
    fin_cases i
    · apply e.symm.injective
      apply Subtype.ext
      simpa [planePoint] using hp
    · exact GenericArc.arcPoint_injective hr hm (by simpa [planePoint] using hp)
    · apply e.symm.injective
      apply Subtype.ext
      simpa [planePoint] using hp
  exact Prod.ext rfl hkl

def d7Configuration (e : {x // x ∈ B} ≃ Fin m) (r t : ℝ) (hm : 2 ≤ m) :
    Finset (Point 7) := Finset.univ.image (d7Point e r t hm)

lemma mem_d7Configuration (e : {x // x ∈ B} ≃ Fin m) (r t : ℝ)
    (hm : 2 ≤ m) (v : D7V m) :
    d7Point e r t hm v ∈ d7Configuration e r t hm := by
  simp [d7Configuration]

lemma card_d7Configuration
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    (d7Configuration e r t hm).card = 3 * m := by
  rw [d7Configuration, Finset.card_image_iff.mpr
    (d7Point_injective e r t a hm hr hrpos hBnorm houter hmixed).injOn]
  simp

lemma isDiameterOne_d7Configuration
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (hB : IsDiameterOne B)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    IsDiameterOne (d7Configuration e r t hm) := by
  rw [isDiameterOne_iff]
  constructor
  · simp only [d7Configuration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨⟨i, k⟩, rfl⟩ _ ⟨⟨j, l⟩, rfl⟩
    by_cases hij : i = j
    · subst j
      exact d7Point_same_dist_le_one e r t hm hr hB i k l
    · exact (d7Point_cross_dist_eq_one e r t a hm hrpos hBnorm
        houter hmixed hij k l).le
  · let u : D7V m := (0, ⟨0, by omega⟩)
    let v : D7V m := (1, ⟨0, by omega⟩)
    exact ⟨d7Point e r t hm u, mem_d7Configuration e r t hm u,
      d7Point e r t hm v, mem_d7Configuration e r t hm v,
      d7Point_cross_dist_eq_one e r t a hm hrpos hBnorm houter hmixed
        (by norm_num [u, v]) _ _⟩

def d7VertexEmbedding
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    D7V m ↪ {x // x ∈ d7Configuration e r t hm} where
  toFun v := ⟨d7Point e r t hm v, mem_d7Configuration e r t hm v⟩
  inj' v w h := d7Point_injective e r t a hm hr hrpos hBnorm houter hmixed
    (congrArg Subtype.val h)

lemma d7SourceGraph_adj_maps_to_diameter
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1)
    {v w : D7V m} (hvw : (d7SourceGraph e hm).Adj v w) :
    (diameterGraph (d7Configuration e r t hm)).Adj
      (d7VertexEmbedding e r t a hm hr hrpos hBnorm houter hmixed v)
      (d7VertexEmbedding e r t a hm hr hrpos hBnorm houter hmixed w) := by
  change dist (d7Point e r t hm v) (d7Point e r t hm w) = 1
  rcases hvw with ((hcross | hleft) | hright) | hmiddle
  · exact d7Point_cross_dist_eq_one e r t a hm hrpos hBnorm houter hmixed
      (SimpleGraph.completeEquipartiteGraph_adj.mp hcross) v.2 w.2
  · rw [leftLocalGraph, SimpleGraph.map_adj] at hleft
    obtain ⟨x, y, hxy, hx, hy⟩ := hleft
    rw [← hx, ← hy]
    change dist (d7Point e r t hm (0, e x)) (d7Point e r t hm (0, e y)) = 1
    rw [d7Point, d7Point, dist_embedCircle_same]
    simpa [planePoint] using hxy
  · rw [rightLocalGraph, SimpleGraph.map_adj] at hright
    obtain ⟨x, y, hxy, hx, hy⟩ := hright
    rw [← hx, ← hy]
    change dist (d7Point e r t hm (2, e x)) (d7Point e r t hm (2, e y)) = 1
    rw [d7Point, d7Point, dist_embedCircle_same]
    simpa [planePoint] using hxy
  · rw [SimpleGraph.edge_adj] at hmiddle
    rcases hmiddle.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [d7Point, d7Point, dist_embedCircle_same]
      simpa [planePoint] using GenericArc.dist_arc_endpoints_eq_one hr hm
    · rw [dist_comm, d7Point, d7Point, dist_embedCircle_same]
      simpa [planePoint] using GenericArc.dist_arc_endpoints_eq_one hr hm

def d7SourceCopy
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    SimpleGraph.Copy (d7SourceGraph e hm)
      (diameterGraph (d7Configuration e r t hm)) where
  toHom := {
    toFun := d7VertexEmbedding e r t a hm hr hrpos hBnorm houter hmixed
    map_rel' := fun h ↦ d7SourceGraph_adj_maps_to_diameter e r t a hm hr hrpos
      hBnorm houter hmixed h }
  injective' := (d7VertexEmbedding e r t a hm hr hrpos hBnorm houter hmixed).injective

lemma d7SourceGraph_card_le_diameterPairCount
    (e : {x // x ∈ B} ≃ Fin m) (r t a : ℝ) (hm : 2 ≤ m)
    (hr : 1 / Real.sqrt 2 ≤ r) (hrpos : 0 < r)
    (hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a)
    (houter : 2 * a + 4 * t ^ 2 = 1)
    (hmixed : a + r ^ 2 + t ^ 2 = 1) :
    (d7SourceGraph e hm).edgeFinset.card ≤
      diameterPairCount (d7Configuration e r t hm) := by
  let K := d7SourceCopy e r t a hm hr hrpos hBnorm houter hmixed
  rw [diameterPairCount, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_le_of_injective K.mapEdgeSet K.mapEdgeSet.injective

end Configuration

/-! Instantiation with the odd active regular-star circle. -/

theorem exists_shifted_three_circle_counterexample
    {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    ∃ A : Finset (Point 7),
      A.card = 3 * m ∧ IsDiameterOne A ∧
        3 * m ^ 2 + 2 * m + 1 ≤ diameterPairCount A := by
  obtain ⟨B, s, hBcard, hBon, hs, hsle, hBdiam, hBcount⟩ :=
    exists_activeCircleConfiguration m hm
  let a : ℝ := s ^ 2
  let t : ℝ := Real.sqrt ((1 - 2 * a) / 4)
  let r : ℝ := Real.sqrt (3 / 4 - a / 2)
  have ha0 : 0 ≤ a := by positivity
  have hale : a ≤ 1 / 2 := by simpa [a] using hsle
  have htarg : 0 ≤ (1 - 2 * a) / 4 := by nlinarith
  have htsq : t ^ 2 = (1 - 2 * a) / 4 := by
    exact Real.sq_sqrt htarg
  have hrarg : 1 / 2 ≤ 3 / 4 - a / 2 := by nlinarith
  have hrarg0 : 0 ≤ 3 / 4 - a / 2 := by linarith
  have hrsq : r ^ 2 = 3 / 4 - a / 2 := Real.sq_sqrt hrarg0
  have hsqrt2sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hinvsqrt2sq : (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, hsqrt2sq]
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hinvnonneg : 0 ≤ (1 / Real.sqrt (2 : ℝ)) := by positivity
  have hr : 1 / Real.sqrt 2 ≤ r := by
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have houter : 2 * a + 4 * t ^ 2 = 1 := by nlinarith
  have hmixed : a + r ^ 2 + t ^ 2 = 1 := by nlinarith
  have hBnorm : ∀ x ∈ B, ‖x‖ ^ 2 = a := by
    intro x hx
    have hxnorm : ‖x‖ = s := by
      simpa [dist_zero_right] using hBon x hx
    rw [hxnorm]
  let e : {x // x ∈ B} ≃ Fin m := Finset.equivFinOfCardEq hBcard
  let A := d7Configuration e r t (by omega : 2 ≤ m)
  have hAcard : A.card = 3 * m := by
    exact card_d7Configuration e r t a (by omega) hr hrpos hBnorm houter hmixed
  have hAdiam : IsDiameterOne A := by
    exact isDiameterOne_d7Configuration e r t a (by omega) hr hrpos hBnorm
      hBdiam houter hmixed
  have hactive : m ≤ diameterPairCount B := by
    simpa [cyclicDiameterAllowance, hodd] using hBcount
  have hsource := d7SourceGraph_card_le_diameterPairCount e r t a (by omega)
    hr hrpos hBnorm houter hmixed
  rw [card_edgeFinset_d7SourceGraph] at hsource
  refine ⟨A, hAcard, hAdiam, ?_⟩
  calc
    3 * m ^ 2 + 2 * m + 1 ≤
        3 * m ^ 2 + 2 * diameterPairCount B + 1 := by omega
    _ ≤ diameterPairCount A := by simpa [A] using hsource

theorem seven_shifted_three_circle_lower
    {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    3 * m ^ 2 + 2 * m + 1 ≤ f 7 (3 * m) := by
  obtain ⟨A, hAcard, hAdiam, hcount⟩ :=
    exists_shifted_three_circle_counterexample hm hodd
  exact hcount.trans (diameterPairCount_le_f hAcard hAdiam)

end

end Erdos223.SevenCounterexample

namespace Erdos223

export SevenCounterexample
  (exists_shifted_three_circle_counterexample seven_shifted_three_circle_lower)

end Erdos223
