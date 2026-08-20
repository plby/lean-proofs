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

import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Generic charts and finite line orders for projective arrangements

This file selects an affine chart avoiding a finite family of projective
vertices, chooses a coordinate separating their normalized representatives,
and develops the finite consecutive-edge facts used to extract a line
arrangement from projective incidence data.
-/

open scoped LinearAlgebra.Projectivization

namespace Erdos735.ChartOrder

noncomputable section

section GenericChart

variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

/-- A finite family of projective points admits a hyperplane at infinity
which contains none of them. -/
theorem exists_chart_avoiding (S : Finset (ℙ K V)) :
    ∃ f : Module.Dual K V, ∀ p ∈ S, f p.rep ≠ 0 := by
  let I := {p // p ∈ S}
  let v : I → V := fun p ↦ p.1.rep
  have hv : ∀ i, v i ≠ 0 := fun i ↦ i.1.rep_nonzero
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) v hv
  exact ⟨f, fun p hp ↦ hf ⟨p, hp⟩⟩

/-- For a nonempty vertex family, the avoiding functional is itself nonzero,
so its kernel is a genuine projective hyperplane at infinity. -/
theorem exists_nonzero_chart_avoiding (S : Finset (ℙ K V)) (hS : S.Nonempty) :
    ∃ f : Module.Dual K V, f ≠ 0 ∧ ∀ p ∈ S, f p.rep ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_chart_avoiding S
  obtain ⟨p, hp⟩ := hS
  refine ⟨f, ?_, hf⟩
  intro hzero
  have := hf p hp
  simp [hzero] at this

/-- The representative of a projective point normalized to have chart
functional equal to one. -/
def chartRep (f : Module.Dual K V) (p : ℙ K V) : V :=
  (f p.rep)⁻¹ • p.rep

/-- A scalar coordinate on the affine chart. -/
def chartCoord (f g : Module.Dual K V) (p : ℙ K V) : K :=
  g (chartRep f p)

/-- Applying a linear form to the library's chosen representative of a
projective point created from `x` vanishes exactly when it vanishes on `x`.
This is the representative-independent incidence bridge used by concrete
arrangement extraction. -/
lemma apply_rep_mk_eq_zero_iff (g : Module.Dual K V) (x : V) (hx : x ≠ 0) :
    g (Projectivization.mk K x hx).rep = 0 ↔ g x = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  have ha' : (a : K) • x = (Projectivization.mk K x hx).rep := ha
  rw [← ha', map_smul]
  simp

lemma chartRep_nonzero (f : Module.Dual K V) (p : ℙ K V) (hp : f p.rep ≠ 0) :
    chartRep f p ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero hp) p.rep_nonzero

@[simp] lemma apply_chartRep (f : Module.Dual K V) (p : ℙ K V) (hp : f p.rep ≠ 0) :
    f (chartRep f p) = 1 := by
  simp [chartRep, hp]

/-- Normalization into an affine chart preserves incidence with every
projective hyperplane. -/
lemma apply_chartRep_eq_zero_iff (f g : Module.Dual K V) (p : ℙ K V)
    (hp : f p.rep ≠ 0) : g (chartRep f p) = 0 ↔ g p.rep = 0 := by
  simp [chartRep, hp]

lemma mk_chartRep (f : Module.Dual K V) (p : ℙ K V) (hp : f p.rep ≠ 0) :
    Projectivization.mk K (chartRep f p) (chartRep_nonzero f p hp) = p := by
  calc
    Projectivization.mk K (chartRep f p) (chartRep_nonzero f p hp) =
        Projectivization.mk K p.rep p.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨(f p.rep)⁻¹, rfl⟩
    _ = p := p.mk_rep

lemma chartRep_injOn (f : Module.Dual K V) (S : Finset (ℙ K V))
    (hf : ∀ p ∈ S, f p.rep ≠ 0) : Set.InjOn (chartRep f) (S : Set (ℙ K V)) := by
  intro p hp q hq heq
  have hp' := mk_chartRep f p (hf p hp)
  have hq' := mk_chartRep f q (hf q hq)
  rw [← hp', ← hq']
  congr

/-- In addition to a generic affine chart, a finite family admits a linear
coordinate which separates all its normalized representatives. -/
theorem exists_chart_and_separating_coordinate (S : Finset (ℙ K V)) :
    ∃ f g : Module.Dual K V,
      (∀ p ∈ S, f p.rep ≠ 0) ∧
      Set.InjOn (chartCoord f g) (S : Set (ℙ K V)) := by
  obtain ⟨f, hf⟩ := exists_chart_avoiding S
  let PS := {z : ({p // p ∈ S} × {p // p ∈ S}) // z.1 ≠ z.2}
  let d : PS → V := fun z ↦ chartRep f z.1.1.1 - chartRep f z.1.2.1
  have hd : ∀ z, d z ≠ 0 := by
    intro z
    change chartRep f z.1.1.1 - chartRep f z.1.2.1 ≠ 0
    rw [sub_ne_zero]
    intro heq
    apply z.2
    apply Subtype.ext
    exact chartRep_injOn f S hf z.1.1.2 z.1.2.2 heq
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) d hd
  refine ⟨f, g, hf, ?_⟩
  intro p hp q hq heq
  by_contra hpq
  let z : PS := ⟨(⟨p, hp⟩, ⟨q, hq⟩), by
    intro h
    apply hpq
    exact congrArg Subtype.val h⟩
  have hgz := hg z
  apply hgz
  change g (chartRep f p - chartRep f q) = 0
  rw [map_sub, sub_eq_zero]
  exact heq

end GenericChart

section SortedIntersections

variable {V L : Type*} [DecidableEq V]

/-- The increasing list of coordinate values of a finite vertex set.  If the
coordinate separates the vertices, this list parametrizes them bijectively. -/
def sortedCoordinates (coord : V → ℝ) (S : Finset V) : List ℝ :=
  (S.image coord).sort

@[simp] lemma mem_sortedCoordinates {coord : V → ℝ} {S : Finset V} {t : ℝ} :
    t ∈ sortedCoordinates coord S ↔ ∃ v ∈ S, coord v = t := by
  simp [sortedCoordinates]

lemma sortedCoordinates_nodup (coord : V → ℝ) (S : Finset V) :
    (sortedCoordinates coord S).Nodup := by
  exact Finset.sort_nodup _ _

lemma sortedCoordinates_strict (coord : V → ℝ) (S : Finset V) :
    (sortedCoordinates coord S).SortedLT := by
  exact Finset.sortedLT_sort _

lemma length_sortedCoordinates (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) :
    (sortedCoordinates coord S).length = S.card := by
  rw [sortedCoordinates, Finset.length_sort, Finset.card_image_of_injOn hinj]

/-- Two vertices are consecutive in the increasing coordinate order on `S`. -/
def Consecutive (coord : V → ℝ) (S : Finset V) (a b : V) : Prop :=
  a ∈ S ∧ b ∈ S ∧ coord a < coord b ∧
    ∀ x ∈ S, ¬(coord a < coord x ∧ coord x < coord b)

lemma Consecutive.left_mem {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : Consecutive coord S a b) : a ∈ S := h.1

lemma Consecutive.right_mem {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : Consecutive coord S a b) : b ∈ S := h.2.1

lemma Consecutive.lt {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : Consecutive coord S a b) : coord a < coord b := h.2.2.1

lemma Consecutive.ne {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : Consecutive coord S a b) : a ≠ b := by
  intro hab
  simpa [hab] using h.lt

lemma Consecutive.no_between {coord : V → ℝ} {S : Finset V} {a b x : V}
    (h : Consecutive coord S a b) (hx : x ∈ S) :
    ¬(coord a < coord x ∧ coord x < coord b) := h.2.2.2 x hx

/-- Every nonterminal vertex of a finite coordinate-ordered set has a
consecutive successor. -/
theorem exists_consecutive_successor (coord : V → ℝ) (S : Finset V) (a : V)
    (ha : a ∈ S) (hnext : ∃ b ∈ S, coord a < coord b) :
    ∃ b, Consecutive coord S a b := by
  let T := S.filter fun b ↦ coord a < coord b
  have hT : T.Nonempty := by
    obtain ⟨b, hb, hab⟩ := hnext
    exact ⟨b, by simp [T, hb, hab]⟩
  obtain ⟨b, hbT, hbmin⟩ := T.exists_min_image coord hT
  have hb : b ∈ S := (Finset.mem_filter.mp hbT).1
  have hab : coord a < coord b := (Finset.mem_filter.mp hbT).2
  refine ⟨b, ha, hb, hab, ?_⟩
  intro x hx hbetween
  have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hbetween.1⟩
  exact (not_lt_of_ge (hbmin x hxT)) hbetween.2

/-- Consecutive successors are unique when the coordinate separates `S`. -/
theorem consecutive_right_unique (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) {a b c : V}
    (hab : Consecutive coord S a b) (hac : Consecutive coord S a c) : b = c := by
  apply hinj hab.right_mem hac.right_mem
  rcases lt_trichotomy (coord b) (coord c) with hbc | hbc | hcb
  · exact (hac.no_between hab.right_mem ⟨hab.lt, hbc⟩).elim
  · exact hbc
  · exact (hab.no_between hac.right_mem ⟨hac.lt, hcb⟩).elim

/-- Consecutivity on the circle obtained by adjoining the point at infinity:
ordinary consecutive pairs are retained, and the maximum vertex is followed
by the minimum vertex. -/
def CyclicConsecutive (coord : V → ℝ) (S : Finset V) (a b : V) : Prop :=
  Consecutive coord S a b ∨
    a ∈ S ∧ b ∈ S ∧
      (∀ x ∈ S, coord x ≤ coord a) ∧
      ∀ x ∈ S, coord b ≤ coord x

lemma CyclicConsecutive.left_mem {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : CyclicConsecutive coord S a b) : a ∈ S := by
  rcases h with h | h
  · exact h.left_mem
  · exact h.1

lemma CyclicConsecutive.right_mem {coord : V → ℝ} {S : Finset V} {a b : V}
    (h : CyclicConsecutive coord S a b) : b ∈ S := by
  rcases h with h | h
  · exact h.right_mem
  · exact h.2.1

lemma CyclicConsecutive.no_between {coord : V → ℝ} {S : Finset V} {a b x : V}
    (h : CyclicConsecutive coord S a b) (hx : x ∈ S) :
    ¬(coord a < coord x ∧ coord x < coord b) := by
  rcases h with h | h
  · exact h.no_between hx
  · intro hbetween
    exact (not_lt_of_ge (h.2.2.1 x hx)) hbetween.1

/-- Every vertex of a nonempty finite coordinate-ordered set has a cyclic
successor, with the maximum wrapping to the minimum. -/
theorem exists_cyclicConsecutive_successor (coord : V → ℝ) (S : Finset V) (a : V)
    (ha : a ∈ S) : ∃ b, CyclicConsecutive coord S a b := by
  by_cases hnext : ∃ b ∈ S, coord a < coord b
  · obtain ⟨b, hab⟩ := exists_consecutive_successor coord S a ha hnext
    exact ⟨b, Or.inl hab⟩
  · obtain ⟨b, hb, hbmin⟩ := S.exists_min_image coord ⟨a, ha⟩
    refine ⟨b, Or.inr ⟨ha, hb, ?_, hbmin⟩⟩
    intro x hx
    exact le_of_not_gt fun hax ↦ hnext ⟨x, hx, hax⟩

/-- Cyclic successors are unique when the coordinate separates the set. -/
theorem cyclicConsecutive_right_unique (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) {a b c : V}
    (hab : CyclicConsecutive coord S a b) (hac : CyclicConsecutive coord S a c) : b = c := by
  rcases hab with hab | ⟨ha, hb, hamax, hbmin⟩
  · rcases hac with hac | ⟨_, hc, hamax, _⟩
    · exact consecutive_right_unique coord S hinj hab hac
    · exact ((not_lt_of_ge (hamax b hab.right_mem)) hab.lt).elim
  · rcases hac with hac | ⟨_, hc, _, hcmin⟩
    · exact ((not_lt_of_ge (hamax c hac.right_mem)) hac.lt).elim
    · apply hinj hb hc
      exact le_antisymm (hbmin c hc) (hcmin b hb)

/-- Every vertex of a nonempty finite coordinate-ordered set has a cyclic
predecessor. -/
theorem exists_cyclicConsecutive_predecessor (coord : V → ℝ) (S : Finset V) (a : V)
    (ha : a ∈ S) : ∃ b, CyclicConsecutive coord S b a := by
  by_cases hprev : ∃ b ∈ S, coord b < coord a
  · let T := S.filter fun b ↦ coord b < coord a
    have hT : T.Nonempty := by
      obtain ⟨b, hb, hba⟩ := hprev
      exact ⟨b, by simp [T, hb, hba]⟩
    obtain ⟨b, hbT, hbmax⟩ := T.exists_max_image coord hT
    have hb : b ∈ S := (Finset.mem_filter.mp hbT).1
    have hba : coord b < coord a := (Finset.mem_filter.mp hbT).2
    refine ⟨b, Or.inl ⟨hb, ha, hba, ?_⟩⟩
    intro x hx hbetween
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hbetween.2⟩
    exact (not_lt_of_ge (hbmax x hxT)) hbetween.1
  · obtain ⟨b, hb, hbmax⟩ := S.exists_max_image coord ⟨a, ha⟩
    refine ⟨b, Or.inr ⟨hb, ha, hbmax, ?_⟩⟩
    intro x hx
    exact le_of_not_gt fun hxa ↦ hprev ⟨x, hx, hxa⟩

/-- Ordinary consecutive predecessors are unique under a separating
coordinate. -/
theorem consecutive_left_unique (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) {a b c : V}
    (hba : Consecutive coord S b a) (hca : Consecutive coord S c a) : b = c := by
  apply hinj hba.left_mem hca.left_mem
  rcases lt_trichotomy (coord b) (coord c) with hbc | hbc | hcb
  · exact (hba.no_between hca.left_mem ⟨hbc, hca.lt⟩).elim
  · exact hbc
  · exact (hca.no_between hba.left_mem ⟨hcb, hba.lt⟩).elim

/-- Cyclic predecessors are unique when the coordinate separates the set. -/
theorem cyclicConsecutive_left_unique (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) {a b c : V}
    (hba : CyclicConsecutive coord S b a) (hca : CyclicConsecutive coord S c a) : b = c := by
  rcases hba with hba | ⟨hb, ha, hbmax, hamin⟩
  · rcases hca with hca | ⟨hc, _, _, hamin⟩
    · exact consecutive_left_unique coord S hinj hba hca
    · exact ((not_lt_of_ge (hamin b hba.left_mem)) hba.lt).elim
  · rcases hca with hca | ⟨hc, _, hcmax, _⟩
    · exact ((not_lt_of_ge (hamin c hca.left_mem)) hca.lt).elim
    · apply hinj hb hc
      exact le_antisymm (hcmax b hb) (hbmax c hc)

/-- A cyclic consecutive pair has distinct endpoints as soon as the finite
set has at least two vertices and the coordinate separates it. -/
theorem cyclicConsecutive_ne_of_two_le_card (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) (hcard : 2 ≤ S.card) {a b : V}
    (hab : CyclicConsecutive coord S a b) : a ≠ b := by
  rcases hab with hab | ⟨ha, hb, hamax, hbmin⟩
  · exact hab.ne
  · intro hab
    subst b
    have hsub : S ⊆ {a} := by
      intro x hx
      simp only [Finset.mem_singleton]
      apply hinj hx ha
      exact le_antisymm (hamax x hx) (hbmin x hx)
    have hsmall := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hsmall
    omega

/-- The canonical cyclic successor of a vertex in a finite ordered set. -/
noncomputable def cyclicSuccessor (coord : V → ℝ) (S : Finset V) (a : {x // x ∈ S}) :
    {x // x ∈ S} :=
  ⟨Classical.choose (exists_cyclicConsecutive_successor coord S a.1 a.2),
    (Classical.choose_spec (exists_cyclicConsecutive_successor coord S a.1 a.2)).right_mem⟩

lemma cyclicSuccessor_spec (coord : V → ℝ) (S : Finset V) (a : {x // x ∈ S}) :
    CyclicConsecutive coord S a.1 (cyclicSuccessor coord S a).1 :=
  Classical.choose_spec (exists_cyclicConsecutive_successor coord S a.1 a.2)

/-- The canonical cyclic predecessor of a vertex in a finite ordered set. -/
noncomputable def cyclicPredecessor (coord : V → ℝ) (S : Finset V) (a : {x // x ∈ S}) :
    {x // x ∈ S} :=
  ⟨Classical.choose (exists_cyclicConsecutive_predecessor coord S a.1 a.2),
    (Classical.choose_spec (exists_cyclicConsecutive_predecessor coord S a.1 a.2)).left_mem⟩

lemma cyclicPredecessor_spec (coord : V → ℝ) (S : Finset V) (a : {x // x ∈ S}) :
    CyclicConsecutive coord S (cyclicPredecessor coord S a).1 a.1 :=
  Classical.choose_spec (exists_cyclicConsecutive_predecessor coord S a.1 a.2)

lemma cyclicSuccessor_predecessor (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) (a : {x // x ∈ S}) :
    cyclicSuccessor coord S (cyclicPredecessor coord S a) = a := by
  apply Subtype.ext
  exact cyclicConsecutive_right_unique coord S hinj
    (cyclicSuccessor_spec coord S (cyclicPredecessor coord S a))
    (cyclicPredecessor_spec coord S a)

lemma cyclicPredecessor_successor (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V)) (a : {x // x ∈ S}) :
    cyclicPredecessor coord S (cyclicSuccessor coord S a) = a := by
  apply Subtype.ext
  exact cyclicConsecutive_left_unique coord S hinj
    (cyclicPredecessor_spec coord S (cyclicSuccessor coord S a))
    (cyclicSuccessor_spec coord S a)

/-- Vertices of an arrangement incident with a fixed line. -/
def verticesOn (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (l : L) : Finset V :=
  vertices.filter fun v ↦ onLine v l

lemma mem_verticesOn (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] {v : V} {l : L} :
    v ∈ verticesOn vertices onLine l ↔ v ∈ vertices ∧ onLine v l := by
  simp [verticesOn]

/-- A bounded edge of a charted arrangement is a pair of consecutive
intersection vertices on one arrangement line. -/
def IsArrangementEdge (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ) (l : L) (a b : V) : Prop :=
  Consecutive coord (verticesOn vertices onLine l) a b

/-- A first-class bounded edge together with the arrangement line carrying
it. -/
structure LabeledArrangementEdge (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ) where
  line : L
  left : V
  right : V
  edge : IsArrangementEdge vertices onLine coord line left right

lemma IsArrangementEdge.left_incident (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ) {l : L} {a b : V}
    (h : IsArrangementEdge vertices onLine coord l a b) : onLine a l := by
  exact (mem_verticesOn vertices onLine).mp h.left_mem |>.2

lemma IsArrangementEdge.right_incident (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ) {l : L} {a b : V}
    (h : IsArrangementEdge vertices onLine coord l a b) : onLine b l := by
  exact (mem_verticesOn vertices onLine).mp h.right_mem |>.2

lemma IsArrangementEdge.endpoints_mem (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ) {l : L} {a b : V}
    (h : IsArrangementEdge vertices onLine coord l a b) : a ∈ vertices ∧ b ∈ vertices := by
  exact ⟨(mem_verticesOn vertices onLine).mp h.left_mem |>.1,
    (mem_verticesOn vertices onLine).mp h.right_mem |>.1⟩

lemma IsArrangementEdge.no_incident_vertex_between
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) {l : L} {a b x : V}
    (h : IsArrangementEdge vertices onLine coord l a b)
    (hxv : x ∈ vertices) (hxl : onLine x l) :
    ¬(coord a < coord x ∧ coord x < coord b) := by
  exact h.no_between ((mem_verticesOn vertices onLine).mpr ⟨hxv, hxl⟩)

lemma LabeledArrangementEdge.left_incident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (e : LabeledArrangementEdge vertices onLine coord) :
    onLine e.left e.line :=
  IsArrangementEdge.left_incident vertices onLine coord e.edge

lemma LabeledArrangementEdge.right_incident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (e : LabeledArrangementEdge vertices onLine coord) :
    onLine e.right e.line :=
  IsArrangementEdge.right_incident vertices onLine coord e.edge

/-- A line-labelled cyclic edge, including the wrap-around edge from the
maximum intersection to the minimum intersection. -/
structure LabeledCyclicArrangementEdge
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) where
  line : L
  left : V
  right : V
  edge : CyclicConsecutive coord (verticesOn vertices onLine line) left right

lemma LabeledCyclicArrangementEdge.left_incident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (e : LabeledCyclicArrangementEdge vertices onLine coord) :
    onLine e.left e.line := by
  exact (mem_verticesOn vertices onLine).mp e.edge.left_mem |>.2

lemma LabeledCyclicArrangementEdge.right_incident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (e : LabeledCyclicArrangementEdge vertices onLine coord) :
    onLine e.right e.line := by
  exact (mem_verticesOn vertices onLine).mp e.edge.right_mem |>.2

/-- On a line with a separating coordinate, the bounded arrangement edge
starting at a given vertex is unique. -/
theorem arrangementEdge_right_unique
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    {l : L} {a b c : V}
    (hab : IsArrangementEdge vertices onLine coord l a b)
    (hac : IsArrangementEdge vertices onLine coord l a c) : b = c := by
  apply consecutive_right_unique coord (verticesOn vertices onLine l)
  · exact hinj.mono (Finset.filter_subset _ _)
  · exact hab
  · exact hac

end SortedIntersections

end

end Erdos735.ChartOrder
