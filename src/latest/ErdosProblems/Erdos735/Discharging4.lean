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

import ErdosProblems.Erdos735.Discharging3
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite

/-!
# The fourth ABKPR discharging step for Erdős Problem 735

This file formalizes the helping-pair/evil-pair bipartite graph, its
degree-two component count, Hall matching, and the final charge
contradiction in integer quarter-units.
-/

namespace Erdos735

open scoped BigOperators

universe uO uH uE

namespace ABKPR

/-- The finite bipartite graph between helping pairs and evil pairs. -/
structure HelpingGraph (Help : Type uH) (Evil : Type uE)
    [Fintype Help] [Fintype Evil] [DecidableEq Help] [DecidableEq Evil] where
  Adj : Evil → Help → Prop
  adjDecidable : DecidableRel Adj
  evilDegree_one_le : ∀ e,
    1 ≤ (Finset.univ.filter fun h => Adj e h).card
  evilDegree_le_two : ∀ e,
    (Finset.univ.filter fun h => Adj e h).card ≤ 2
  helpingDegree_le_two : ∀ h,
    (Finset.univ.filter fun e => Adj e h).card ≤ 2

namespace HelpingGraph

variable {Help : Type uH} {Evil : Type uE}
variable [Fintype Help] [Fintype Evil] [DecidableEq Help] [DecidableEq Evil]
variable (G : HelpingGraph Help Evil)

local instance : DecidableRel G.Adj := G.adjDecidable

def evilNeighbors (e : Evil) : Finset Help :=
  Finset.univ.filter fun h => G.Adj e h

def helpingNeighbors (h : Help) : Finset Evil :=
  Finset.univ.filter fun e => G.Adj e h

theorem evil_degree_one_le (e : Evil) : 1 ≤ (G.evilNeighbors e).card :=
  G.evilDegree_one_le e

theorem evil_degree_le_two (e : Evil) : (G.evilNeighbors e).card ≤ 2 :=
  G.evilDegree_le_two e

theorem helping_degree_le_two (h : Help) : (G.helpingNeighbors h).card ≤ 2 :=
  G.helpingDegree_le_two h

/-- The precise finite counting consequence supplied by the no-evil--evil
path/Levi argument.  For maximum-degree-two bipartite components, a failure
of this Hall inequality is exactly a path component whose two endpoints are
evil. -/
def NoEvilEvilPath : Prop :=
  ∀ S : Finset Evil,
    S.card ≤ (Finset.univ.filter fun h => ∃ e ∈ S, G.Adj e h).card

/-- The elementary component count behind `NoEvilEvilPath`.  In a finite
connected maximum-degree-two bipartite component, incidence counting gives
the displayed degree balance; the component is a cycle or a path, hence has
zero or two degree-one endpoints.  Excluding two evil endpoints forces at
least as many helpers as evils. -/
theorem component_help_count_ge_evil_count
    (helpDegreeOne helpDegreeTwo evilDegreeOne evilDegreeTwo : ℕ)
    (hincidence : evilDegreeOne + 2 * evilDegreeTwo =
      helpDegreeOne + 2 * helpDegreeTwo)
    (hendpoints : helpDegreeOne + evilDegreeOne = 0 ∨
      helpDegreeOne + evilDegreeOne = 2)
    (hnoEvilEndpoints : evilDegreeOne ≤ 1) :
    evilDegreeOne + evilDegreeTwo ≤ helpDegreeOne + helpDegreeTwo := by
  rcases hendpoints with hendpoints | hendpoints <;> omega

/-- Hall's theorem turns the no-evil--evil-path count into an adjacent
injective matching of every evil pair to a helping pair. -/
theorem exists_adjacent_matching (hpath : G.NoEvilEvilPath) :
    ∃ matchHelper : Evil → Help, Function.Injective matchHelper ∧
      ∀ e, G.Adj e (matchHelper e) := by
  let neighborSet (e : Evil) : Finset Help :=
    Finset.univ.filter fun h => G.Adj e h
  have hneighbors (S : Finset Evil) :
      (Finset.univ.filter fun h => ∃ e ∈ S, G.Adj e h) =
        S.biUnion neighborSet := by
    ext h
    simp [neighborSet]
  have hHall : ∀ S : Finset Evil, S.card ≤ (S.biUnion neighborSet).card := by
    intro S
    rw [← hneighbors S]
    exact hpath S
  obtain ⟨matchHelper, hinjective, hadjacent⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neighborSet).mp hHall
  exact ⟨matchHelper, hinjective, fun e => by
    simpa [neighborSet] using hadjacent e⟩

end HelpingGraph

/-- Abstract charge data for the last discharging step.  An object may own
several helping pairs, but its Stage-3 charge covers all of them.  Evil pairs
enumerate all negative objects injectively and each such object has charge
exactly `-1` in quarter-units. -/
structure FinalChargeData
    (Object : Type uO) (Help : Type uH) (Evil : Type uE)
    [Fintype Object] [Fintype Help] [Fintype Evil]
    [DecidableEq Object] [DecidableEq Help] [DecidableEq Evil]
    (G : HelpingGraph Help Evil) where
  baseCharge : Object → ℤ
  helpOwner : Help → Object
  evilOwner : Evil → Object
  evilOwner_injective : Function.Injective evilOwner
  helperCapacity : ∀ o, 0 ≤ baseCharge o →
    ((Finset.univ.filter fun h => helpOwner h = o).card : ℤ) ≤ baseCharge o
  helperOwner_ne_evilOwner : ∀ h e, helpOwner h ≠ evilOwner e
  evilCharge : ∀ e, baseCharge (evilOwner e) = -1
  negative_is_evil : ∀ o, baseCharge o < 0 → ∃ e, evilOwner e = o
  totalBaseCharge : (∑ o, baseCharge o) = -24

namespace FinalChargeData

variable {Object : Type uO} {Help : Type uH} {Evil : Type uE}
variable [Fintype Object] [Fintype Help] [Fintype Evil]
variable [DecidableEq Object] [DecidableEq Help] [DecidableEq Evil]
variable {G : HelpingGraph Help Evil}
variable (D : FinalChargeData Object Help Evil G)

def helperFiber (o : Object) : Finset Help :=
  Finset.univ.filter fun h => D.helpOwner h = o

def evilFiber (o : Object) : Finset Evil :=
  Finset.univ.filter fun e => D.evilOwner e = o

def selectedEvils (matchHelper : Evil → Help) (o : Object) : Finset Evil :=
  Finset.univ.filter fun e => D.helpOwner (matchHelper e) = o

/-- Final charge after each matched helper gives one quarter-unit to its
matched evil object. -/
def finalCharge (matchHelper : Evil → Help) (o : Object) : ℤ :=
  D.baseCharge o - (D.selectedEvils matchHelper o).card + (D.evilFiber o).card

lemma selectedEvils_card_le_helperFiber_card
    {matchHelper : Evil → Help} (hm : Function.Injective matchHelper) (o : Object) :
    (D.selectedEvils matchHelper o).card ≤ (D.helperFiber o).card := by
  rw [← Finset.card_image_of_injective (D.selectedEvils matchHelper o) hm]
  apply Finset.card_le_card
  intro h hh
  rcases Finset.mem_image.mp hh with ⟨e, he, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩

lemma evilFiber_owner (e : Evil) : D.evilFiber (D.evilOwner e) = {e} := by
  ext e'
  simp only [evilFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact D.evilOwner_injective.eq_iff

lemma finalCharge_nonnegative
    {matchHelper : Evil → Help} (hm : Function.Injective matchHelper) (o : Object) :
    0 ≤ D.finalCharge matchHelper o := by
  have hselected := D.selectedEvils_card_le_helperFiber_card hm o
  by_cases hnegative : D.baseCharge o < 0
  · obtain ⟨e, he⟩ := D.negative_is_evil o hnegative
    have hbase : D.baseCharge o = -1 := by
      rw [← he]
      exact D.evilCharge e
    have hselectedZero : D.selectedEvils matchHelper o = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨e', he'⟩
      have howner : D.helpOwner (matchHelper e') = o := (Finset.mem_filter.mp he').2
      exact D.helperOwner_ne_evilOwner (matchHelper e') e (howner.trans he.symm)
    have hevils : (D.evilFiber o).card = 1 := by
      rw [← he, D.evilFiber_owner e]
      simp
    simp [finalCharge, hbase, hselectedZero, hevils]
  · have hbase : 0 ≤ D.baseCharge o := by omega
    have hcapacity : ((D.helperFiber o).card : ℤ) ≤ D.baseCharge o := by
      simpa [helperFiber] using D.helperCapacity o hbase
    simp only [finalCharge]
    omega

private lemma sum_card_incidence
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (row : α → Finset β) (column : β → Finset α)
    (h : ∀ a b, b ∈ row a ↔ a ∈ column b) :
    (∑ a, (row a).card) = ∑ b, (column b).card := by
  classical
  calc
    (∑ a, (row a).card) = ∑ a, ∑ b, if b ∈ row a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if b ∈ row a then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, if a ∈ column b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      simp only [h a b]
    _ = ∑ b, (column b).card := by
      apply Finset.sum_congr rfl
      intro b _
      simp

private lemma sum_fiber_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (owner : β → α) :
    (∑ a, (Finset.univ.filter fun b => owner b = a).card) = Fintype.card β := by
  calc
    (∑ a, (Finset.univ.filter fun b => owner b = a).card) =
        ∑ b, ({owner b} : Finset α).card := by
      apply sum_card_incidence
      intro a b
      simp [eq_comm]
    _ = Fintype.card β := by simp

lemma sum_finalCharge (matchHelper : Evil → Help) :
    (∑ o, D.finalCharge matchHelper o) = -24 := by
  have hselectedNat := sum_fiber_card (fun e => D.helpOwner (matchHelper e))
  have hevilsNat := sum_fiber_card D.evilOwner
  have hselected :
      (∑ o, ((D.selectedEvils matchHelper o).card : ℤ)) = (Fintype.card Evil : ℤ) := by
    exact_mod_cast hselectedNat
  have hevils :
      (∑ o, ((D.evilFiber o).card : ℤ)) = (Fintype.card Evil : ℤ) := by
    exact_mod_cast hevilsNat
  simp only [finalCharge, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hselected, hevils, D.totalBaseCharge]
  ring

/-- The final contradiction: Hall matching makes every final charge
nonnegative, while redistribution preserves the total `-24`. -/
theorem contradiction
    (D : FinalChargeData Object Help Evil G) (hpath : G.NoEvilEvilPath) : False := by
  obtain ⟨matchHelper, hm, hadj⟩ := G.exists_adjacent_matching hpath
  have hnonnegative : 0 ≤ ∑ o, D.finalCharge matchHelper o :=
    Finset.sum_nonneg fun o _ => D.finalCharge_nonnegative hm o
  rw [D.sum_finalCharge matchHelper] at hnonnegative
  norm_num at hnonnegative

end FinalChargeData

namespace Data

universe uV uEd uF

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

/-- The exact Stage-4 data which has to be extracted from the projective
arrangement.  Helping pairs are owned by nonnegative Stage-3 faces; evil
pairs enumerate the evil triangles.  The graph fields contain precisely the
local degree bounds, while `NoEvilEvilPath` is supplied separately by the
Levi-geometry argument. -/
structure Stage4Geometry (Help : Type uH) (Evil : Type uE)
    [Fintype Help] [Fintype Evil] [DecidableEq Help] [DecidableEq Evil] where
  graph : HelpingGraph Help Evil
  helpFace : Help → Face
  evilFace : Evil → Face
  evilFace_injective : Function.Injective evilFace
  evilFace_isEvil : ∀ e, A.IsEvilTriangle (evilFace e)
  everyEvilFace : ∀ f, A.IsEvilTriangle f → ∃ e, evilFace e = f
  helpFace_ne_evilFace : ∀ h e, helpFace h ≠ evilFace e
  /-- A face has enough quarter-units to fund all helping pairs that it owns.
  This is deliberately required only for a nonnegative face, so evil faces
  are not made impossible by the capacity hypothesis. -/
  helpFace_capacity : ∀ f, 0 ≤ A.step3FaceCharge4 f →
    ((Finset.univ.filter fun h => helpFace h = f).card : ℤ) ≤
      A.step3FaceCharge4 f

/-- Evil objects need not be postulated: they are canonically the subtype of
faces proved evil after Stage 3. -/
abbrev EvilFace := {f : Face // A.IsEvilTriangle f}

/-- A version of the remaining geometry in which evil pairs are the actual
evil faces.  Thus injectivity, exhaustiveness, and charge `-1` are supplied
by Stage 3 itself rather than by extra geometric hypotheses. -/
structure Stage4FaceGeometry (Help : Type uH)
    [Fintype Help] [DecidableEq Help] where
  graph : HelpingGraph Help A.EvilFace
  helpFace : Help → Face
  helpFace_ne_evilFace : ∀ (h : Help) (e : A.EvilFace), helpFace h ≠ e.1
  helpFace_capacity : ∀ f, 0 ≤ A.step3FaceCharge4 f →
    ((Finset.univ.filter fun h => helpFace h = f).card : ℤ) ≤
      A.step3FaceCharge4 f

namespace Stage4Geometry

variable {A : ABKPR.Data C}
variable {Help : Type uH} {Evil : Type uE}
variable [Fintype Help] [Fintype Evil] [DecidableEq Help] [DecidableEq Evil]
variable (S : A.Stage4Geometry Help Evil)

/-- The disjoint union of blue vertices and faces is the set carrying charge
after Stage 3. -/
noncomputable def objectCharge (_S : A.Stage4Geometry Help Evil) : Vertex ⊕ Face → ℤ
  | Sum.inl v => A.step1VertexCharge4 v
  | Sum.inr f => A.step3FaceCharge4 f

def helpOwner (h : Help) : Vertex ⊕ Face := Sum.inr (S.helpFace h)

def evilOwner (e : Evil) : Vertex ⊕ Face := Sum.inr (S.evilFace e)

lemma evilOwner_injective : Function.Injective S.evilOwner := by
  intro e e' he
  apply S.evilFace_injective
  exact Sum.inr.inj he

lemma helperOwner_ne_evilOwner (h : Help) (e : Evil) :
    S.helpOwner h ≠ S.evilOwner e := by
  simp only [helpOwner, evilOwner, ne_eq, Sum.inr.injEq]
  exact S.helpFace_ne_evilFace h e

lemma helperCapacity (o : Vertex ⊕ Face) (ho : 0 ≤ S.objectCharge o) :
    ((Finset.univ.filter fun h => S.helpOwner h = o).card : ℤ) ≤
      S.objectCharge o := by
  cases o with
  | inl v =>
      simpa [helpOwner, objectCharge] using A.step1VertexCharge4_nonnegative v
  | inr f =>
      simpa [helpOwner, objectCharge] using S.helpFace_capacity f ho

lemma evilCharge (e : Evil) : S.objectCharge (S.evilOwner e) = -1 := by
  simpa [objectCharge, evilOwner] using
    A.step3FaceCharge4_evil (S.evilFace_isEvil e)

lemma negative_is_evil
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking) (o : Vertex ⊕ Face)
    (ho : S.objectCharge o < 0) : ∃ e, S.evilOwner e = o := by
  cases o with
  | inl v =>
      exact (not_lt_of_ge (A.step1VertexCharge4_nonnegative v) ho).elim
  | inr f =>
      have hf : A.IsEvilTriangle f :=
        (A.step3FaceCharge4_negative_iff_evil H hrest hpack f).mp ho
      obtain ⟨e, he⟩ := S.everyEvilFace f hf
      exact ⟨e, by simp [evilOwner, he]⟩

lemma totalObjectCharge : (∑ o, S.objectCharge o) = -24 := by
  simpa only [objectCharge, Fintype.sum_sum_type] using A.step3_total_charge

/-- Stage-3 arrangement data instantiates the abstract final-charge
bookkeeping without placing a capacity demand on a negative evil owner. -/
noncomputable def toFinalChargeData
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking) :
    FinalChargeData (Vertex ⊕ Face) Help Evil S.graph where
  baseCharge := S.objectCharge
  helpOwner := S.helpOwner
  evilOwner := S.evilOwner
  evilOwner_injective := S.evilOwner_injective
  helperCapacity := S.helperCapacity
  helperOwner_ne_evilOwner := S.helperOwner_ne_evilOwner
  evilCharge := S.evilCharge
  negative_is_evil := S.negative_is_evil H hrest hpack
  totalBaseCharge := S.totalObjectCharge

/-- The Stage-4 contradiction from the exact remaining Levi input: the
helping/evil graph satisfies the Hall count implied by the absence of an
evil--evil path. -/
theorem contradiction
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking) (hpath : S.graph.NoEvilEvilPath) : False :=
  (S.toFinalChargeData H hrest hpack).contradiction hpath

end Stage4Geometry

namespace Stage4FaceGeometry

variable {A : ABKPR.Data C}
variable {Help : Type uH} [Fintype Help] [DecidableEq Help]
variable (S : A.Stage4FaceGeometry Help)

/-- Forgetting that evil faces were represented canonically gives the
general Stage-4 geometry used by the bookkeeping theorem. -/
noncomputable def toStage4Geometry : A.Stage4Geometry Help A.EvilFace where
  graph := S.graph
  helpFace := S.helpFace
  evilFace := Subtype.val
  evilFace_injective := Subtype.val_injective
  evilFace_isEvil := fun e => e.2
  everyEvilFace := fun f hf => ⟨⟨f, hf⟩, rfl⟩
  helpFace_ne_evilFace := S.helpFace_ne_evilFace
  helpFace_capacity := S.helpFace_capacity

/-- Final contradiction with no separately assumed enumeration of evil
triangles. -/
theorem contradiction
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking) (hpath : S.graph.NoEvilEvilPath) : False :=
  S.toStage4Geometry.contradiction H hrest hpack hpath

end Stage4FaceGeometry

end Data

end ABKPR

end Erdos735
