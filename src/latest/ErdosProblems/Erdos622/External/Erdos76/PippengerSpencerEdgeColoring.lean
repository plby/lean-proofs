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
import ErdosProblems.Erdos622.External.Erdos76.HypergraphGreedyColoring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# From near-regular edge colourings to Pippenger--Spencer matchings

This file gives the deterministic completion reduction.  It does not assume the
Pippenger--Spencer edge-colouring theorem: that theorem is exposed as a proposition.

The completion uses a private affine gadget for each original vertex.  An incidence
`v ∈ e` is assigned a distinct affine row through the distinguished point of the
gadget for `v`.  For every original `k`-edge, its `k` assigned rows are replaced by
the `k` column transversals of the resulting `k × k` array.  The zeroth column is the
original edge (on distinguished gadget vertices), while the other columns are private
auxiliary edges.  Transposing each array preserves all vertex degrees.  Private
ownership prevents the global part-consistency gap in the naive affine-layer construction.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PippengerSpencerEdgeColoring

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Indexed edges incident with `v`. -/
abbrev IncidentEdges (H : FiniteHypergraph V E) (v : V) :=
  {e : E // v ∈ H.support e}

lemma card_incidentEdges (H : FiniteHypergraph V E) (v : V) :
    Fintype.card (IncidentEdges H v) = H.edgeDegree v := by
  simpa [IncidentEdges, FiniteHypergraph.edgeDegree] using
    (Fintype.card_subtype (fun e : E ↦ v ∈ H.support e))

/-- The incidence slots at a vertex embed into `Fin D` under the maximum-degree bound. -/
def incidenceSlot (H : FiniteHypergraph V E) (D : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (v : ↑H.vertexSet) :
    IncidentEdges H v.1 ↪ Fin D where
  toFun e :=
    ⟨(Fintype.equivFin (IncidentEdges H v.1) e).1,
      lt_of_lt_of_le (Fintype.equivFin (IncidentEdges H v.1) e).2
        (by simpa [card_incidentEdges] using hdeg v.1 v.2)⟩
  inj' := by
    intro e f hef
    have hval :
        ((Fintype.equivFin (IncidentEdges H v.1) e).1) =
          ((Fintype.equivFin (IncidentEdges H v.1) f).1) :=
      congrArg (fun i : Fin D ↦ i.1) hef
    exact (Fintype.equivFin (IncidentEdges H v.1)).injective
      (Fin.ext hval)

/-- Vertices in the private affine gadgets. -/
abbrev PrivateVertex (H : FiniteHypergraph V E) (k q : ℕ) :=
  ↑H.vertexSet × (Fin k × ZMod q)

/-- Rows in the disjoint union of the private affine gadgets. -/
abbrev GadgetEdge (H : FiniteHypergraph V E) (D q : ℕ) :=
  ↑H.vertexSet × (Fin D × ZMod q)

/-- The affine row of slope `s` and intercept `b` in the gadget owned by `v`. -/
def gadgetSupport (H : FiniteHypergraph V E) (k q : ℕ)
    (g : GadgetEdge H D q) : Finset (PrivateVertex H k q) :=
  (Finset.univ : Finset (Fin k)).image fun j ↦
    (g.1, (j, g.2.2 + (j.1 : ZMod q) * (g.2.1.1 : ZMod q)))

lemma mem_gadgetSupport_iff (H : FiniteHypergraph V E) (k q : ℕ)
    (g : GadgetEdge H D q) (z : PrivateVertex H k q) :
    z ∈ gadgetSupport H k q g ↔
      z.1 = g.1 ∧ z.2.2 = g.2.2 + (z.2.1.1 : ZMod q) * (g.2.1.1 : ZMod q) := by
  rcases z with ⟨zv, ⟨j, y⟩⟩
  simp only [gadgetSupport, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have hcol : i = j := Fin.ext (congrArg (fun x : PrivateVertex H k q ↦ x.2.1.1) hi)
    subst i
    exact ⟨(congrArg (fun x : PrivateVertex H k q ↦ x.1) hi).symm,
      (congrArg (fun x : PrivateVertex H k q ↦ x.2.2) hi).symm⟩
  · rintro ⟨howner, hvalue⟩
    refine ⟨j, ?_⟩
    apply Prod.ext
    · exact howner.symm
    · apply Prod.ext
      · rfl
      · exact hvalue.symm

lemma card_gadgetSupport (H : FiniteHypergraph V E) (k q : ℕ)
    (g : GadgetEdge H D q) : (gadgetSupport H k q g).card = k := by
  rw [gadgetSupport, card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun z : PrivateVertex H k q ↦ z.2.1.1) hij)

/-- The private row selected by the incidence `v ∈ e`. -/
def selectedRow (H : FiniteHypergraph V E) (D q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (v : ↑H.vertexSet) (e : IncidentEdges H v.1) : GadgetEdge H D q :=
  (v, (incidenceSlot H D hdeg v e, 0))

/-- A gadget row is selected exactly when it is the row assigned to an original incidence. -/
def IsSelectedRow (H : FiniteHypergraph V E) (D q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (g : GadgetEdge H D q) : Prop :=
  ∃ e : IncidentEdges H g.1.1, selectedRow H D q hdeg g.1 e = g

lemma selectedRow_injective (H : FiniteHypergraph V E) (D q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (v : ↑H.vertexSet) :
    Function.Injective (selectedRow H D q hdeg v) := by
  intro e f hef
  exact (incidenceSlot H D hdeg v).injective (congrArg (fun g ↦ g.2.1) hef)

/-- Unselected affine rows are retained in the completion. -/
abbrev RemainingRow (H : FiniteHypergraph V E) (D q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :=
  {g : GadgetEdge H D q // ¬ IsSelectedRow H D q hdeg g}

/-- Completion edges: retained private rows and the transposed columns for original edges. -/
abbrev CompletionEdge (H : FiniteHypergraph V E) (D k q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :=
  RemainingRow H D q hdeg ⊕ (E × Fin k)

/-- One column of the trade belonging to an original edge. -/
def tradeSupport (H : FiniteHypergraph V E) (D k q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (e : E) (c : Fin k) : Finset (PrivateVertex H k q) :=
  (H.support e).attach.image fun v : ↑(H.support e) ↦
    let v' : ↑H.vertexSet := ⟨v.1, H.support_subset_vertexSet e v.2⟩
    let e' : IncidentEdges H v.1 := ⟨e, v.2⟩
    (v', (c, (c.1 : ZMod q) * ((incidenceSlot H D hdeg v' e').1 : ZMod q)))

lemma mem_tradeSupport_iff (H : FiniteHypergraph V E) (D k q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) (c : Fin k)
    (z : PrivateVertex H k q) :
    z ∈ tradeSupport H D k q hdeg e c ↔
      ∃ hz : z.1.1 ∈ H.support e, z.2.1 = c ∧
        z.2.2 = (c.1 : ZMod q) *
          ((incidenceSlot H D hdeg z.1 ⟨e, hz⟩).1 : ZMod q) := by
  rcases z with ⟨zv, ⟨j, y⟩⟩
  simp only [tradeSupport, mem_image]
  constructor
  · rintro ⟨v, hv, hz⟩
    have howner : (⟨v.1, H.support_subset_vertexSet e v.2⟩ : ↑H.vertexSet) = zv :=
      congrArg (fun x : PrivateVertex H k q ↦ x.1) hz
    cases howner
    refine ⟨v.2, ?_⟩
    exact ⟨(congrArg (fun x : PrivateVertex H k q ↦ x.2.1) hz).symm,
      (congrArg (fun x : PrivateVertex H k q ↦ x.2.2) hz).symm⟩
  · rintro ⟨hv, hc, hz⟩
    let v : ↑(H.support e) := ⟨zv.1, hv⟩
    refine ⟨v, by simp [v], ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hc.symm
      · simpa [hc] using hz.symm

lemma card_tradeSupport (H : FiniteHypergraph V E) (D k q : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) {c : Fin k} :
    (tradeSupport H D k q hdeg e c).card = (H.support e).card := by
  rw [tradeSupport, card_image_of_injective]
  · exact card_attach
  · intro u v huv
    exact Subtype.ext (congrArg (fun z : PrivateVertex H k q ↦ z.1.1) huv)

/-- The private-gadget completion obtained by transposing every incidence trade. -/
def regularCompletion (H : FiniteHypergraph V E) (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    FiniteHypergraph (PrivateVertex H k q) (CompletionEdge H D k q hdeg) where
  vertexSet := Finset.univ
  support
    | Sum.inl g => gadgetSupport H k q g.1
    | Sum.inr ec => tradeSupport H D k q hdeg ec.1 ec.2
  support_subset_vertexSet _ := by simp

@[simp] lemma regularCompletion_vertexSet (H : FiniteHypergraph V E) (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    (regularCompletion H D k q hdeg).vertexSet = Finset.univ := rfl

lemma regularCompletion_isUniform {H : FiniteHypergraph V E} {D k q : ℕ}
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hunif : H.IsUniform k) :
    (regularCompletion H D k q hdeg).IsUniform k := by
  rintro (g | ⟨e, c⟩)
  · exact card_gadgetSupport H k q g.1
  · rw [regularCompletion, card_tradeSupport, hunif]

/-- The unique full affine row of slope `s` through `z`. -/
def rowThrough (H : FiniteHypergraph V E) (D k q : ℕ)
    (z : PrivateVertex H k q) (s : Fin D) : GadgetEdge H D q :=
  (z.1, (s, z.2.2 - (z.2.1.1 : ZMod q) * (s.1 : ZMod q)))

lemma mem_gadgetSupport_rowThrough (H : FiniteHypergraph V E) (D k q : ℕ)
    (z : PrivateVertex H k q) (s : Fin D) :
    z ∈ gadgetSupport H k q (rowThrough H D k q z s) := by
  rw [mem_gadgetSupport_iff]
  constructor
  · rfl
  · dsimp [rowThrough]
    ring

lemma rowThrough_eq_of_mem {H : FiniteHypergraph V E} {D k q : ℕ}
    {z : PrivateVertex H k q} {g : GadgetEdge H D q}
    (hz : z ∈ gadgetSupport H k q g) :
    rowThrough H D k q z g.2.1 = g := by
  rw [mem_gadgetSupport_iff] at hz
  apply Prod.ext
  · exact hz.1
  · apply Prod.ext
    · rfl
    · dsimp [rowThrough]
      rw [hz.2]
      ring

/-- The selected row through a point determines a completion trade column through it. -/
lemma mem_tradeSupport_of_selected_rowThrough {H : FiniteHypergraph V E} {D k q : ℕ}
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (s : Fin D)
    (hs : IsSelectedRow H D q hdeg (rowThrough H D k q z s)) :
    z ∈ tradeSupport H D k q hdeg hs.choose.1 z.2.1 := by
  rw [mem_tradeSupport_iff]
  let e : IncidentEdges H z.1.1 := hs.choose
  have hrow : selectedRow H D q hdeg z.1 e = rowThrough H D k q z s := hs.choose_spec
  have hslope : incidenceSlot H D hdeg z.1 e = s :=
    congrArg (fun g : GadgetEdge H D q ↦ g.2.1) hrow
  have hintercept : (0 : ZMod q) =
      z.2.2 - (z.2.1.1 : ZMod q) * (s.1 : ZMod q) :=
    congrArg (fun g : GadgetEdge H D q ↦ g.2.2) hrow
  refine ⟨e.2, rfl, ?_⟩
  rw [show (⟨hs.choose.1, e.2⟩ : IncidentEdges H z.1.1) = e from rfl, hslope]
  rw [sub_eq_zero.mp hintercept.symm]

/-- The affine slope attached to a completion incidence. -/
def completionIncidenceSlope {H : FiniteHypergraph V E} (D k q : ℕ) [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q)
    (a : IncidentEdges (regularCompletion H D k q hdeg) z) : Fin D := by
  rcases a with ⟨a, ha⟩
  cases a with
  | inl g => exact g.1.2.1
  | inr ec =>
      change z ∈ tradeSupport H D k q hdeg ec.1 ec.2 at ha
      exact incidenceSlot H D hdeg z.1
        ⟨ec.1, (mem_tradeSupport_iff H D k q hdeg ec.1 ec.2 z).mp ha |>.choose⟩

@[simp] lemma completionIncidenceSlope_inl {H : FiniteHypergraph V E} (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (g : RemainingRow H D q hdeg)
    (hz : z ∈ gadgetSupport H k q g.1) :
    completionIncidenceSlope D k q hdeg z ⟨Sum.inl g, hz⟩ = g.1.2.1 := by
  rfl

@[simp] lemma completionIncidenceSlope_inr {H : FiniteHypergraph V E} (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (e : E) (c : Fin k)
    (hz : z ∈ tradeSupport H D k q hdeg e c) (he : z.1.1 ∈ H.support e) :
    completionIncidenceSlope D k q hdeg z ⟨Sum.inr (e, c), hz⟩ =
      incidenceSlot H D hdeg z.1 ⟨e, he⟩ := by
  unfold completionIncidenceSlope
  congr 2

/-- The completion incidence of a prescribed affine slope. -/
def completionIncidenceOfSlope {H : FiniteHypergraph V E} (D k q : ℕ) [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (s : Fin D) :
    IncidentEdges (regularCompletion H D k q hdeg) z :=
  let g := rowThrough H D k q z s
  if hs : IsSelectedRow H D q hdeg g then
    ⟨Sum.inr (hs.choose.1, z.2.1), mem_tradeSupport_of_selected_rowThrough hdeg z s hs⟩
  else
    ⟨Sum.inl ⟨g, hs⟩, mem_gadgetSupport_rowThrough H D k q z s⟩

lemma completionIncidenceOfSlope_val_neg {H : FiniteHypergraph V E} (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (s : Fin D)
    (hs : ¬IsSelectedRow H D q hdeg (rowThrough H D k q z s)) :
    (completionIncidenceOfSlope D k q hdeg z s).1 =
      Sum.inl (⟨rowThrough H D k q z s, hs⟩ : RemainingRow H D q hdeg) := by
  simp [completionIncidenceOfSlope, hs]

lemma completionIncidenceOfSlope_val_pos {H : FiniteHypergraph V E} (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (s : Fin D)
    (hs : IsSelectedRow H D q hdeg (rowThrough H D k q z s)) :
    (completionIncidenceOfSlope D k q hdeg z s).1 =
      Sum.inr (hs.choose.1, z.2.1) := by
  simp [completionIncidenceOfSlope, hs]

lemma completionIncidenceSlope_ofSlope {H : FiniteHypergraph V E} (D k q : ℕ)
    [NeZero q] (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) (s : Fin D) :
    completionIncidenceSlope D k q hdeg z
        (completionIncidenceOfSlope D k q hdeg z s) = s := by
  by_cases hs : IsSelectedRow H D q hdeg (rowThrough H D k q z s)
  · have hval := completionIncidenceOfSlope_val_pos D k q hdeg z s hs
    have hmem : z ∈ tradeSupport H D k q hdeg hs.choose.1 z.2.1 :=
      mem_tradeSupport_of_selected_rowThrough hdeg z s hs
    have hslope := congrArg (fun g : GadgetEdge H D q ↦ g.2.1) hs.choose_spec
    rw [show completionIncidenceOfSlope D k q hdeg z s =
        ⟨Sum.inr (hs.choose.1, z.2.1), hmem⟩ from Subtype.ext hval]
    rw [completionIncidenceSlope_inr]
    convert hslope using 1
    · congr 2
    · rfl
    · simpa [rowThrough] using hs.choose.2
  · have hval := completionIncidenceOfSlope_val_neg D k q hdeg z s hs
    have hmem := mem_gadgetSupport_rowThrough H D k q z s
    rw [show completionIncidenceOfSlope D k q hdeg z s =
        ⟨Sum.inl (⟨rowThrough H D k q z s, hs⟩ : RemainingRow H D q hdeg), hmem⟩ from
          Subtype.ext hval]
    exact completionIncidenceSlope_inl D k q hdeg z _ hmem

/-- Incidences in the completed hypergraph are in bijection with affine slopes. -/
def completionIncidenceEquivSlope {H : FiniteHypergraph V E} (D k q : ℕ) [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) :
    IncidentEdges (regularCompletion H D k q hdeg) z ≃ Fin D where
  toFun := completionIncidenceSlope D k q hdeg z
  invFun := completionIncidenceOfSlope D k q hdeg z
  left_inv := by
    rintro ⟨a, ha⟩
    cases a with
    | inl g =>
        have hgmem : z ∈ gadgetSupport H k q g.1 := ha
        have hrow : rowThrough H D k q z g.1.2.1 = g.1 := rowThrough_eq_of_mem hgmem
        have hnsel : ¬IsSelectedRow H D q hdeg (rowThrough H D k q z g.1.2.1) := by
          simpa [hrow] using g.2
        have haeq :
            (⟨Sum.inl g, ha⟩ : IncidentEdges (regularCompletion H D k q hdeg) z) =
              ⟨Sum.inl g, hgmem⟩ := Subtype.ext rfl
        rw [haeq, completionIncidenceSlope_inl]
        apply Subtype.ext
        rw [completionIncidenceOfSlope_val_neg D k q hdeg z _ hnsel]
        exact congrArg Sum.inl (Subtype.ext hrow)
    | inr ec =>
        rcases ec with ⟨e, c⟩
        have ht := (mem_tradeSupport_iff H D k q hdeg e c z).mp ha
        let he : z.1.1 ∈ H.support e := ht.choose
        have hc : z.2.1 = c := ht.choose_spec.1
        have hzval : z.2.2 = (c.1 : ZMod q) *
            ((incidenceSlot H D hdeg z.1 ⟨e, he⟩).1 : ZMod q) := ht.choose_spec.2
        let s : Fin D := incidenceSlot H D hdeg z.1 ⟨e, he⟩
        have hrow : selectedRow H D q hdeg z.1 ⟨e, he⟩ =
            rowThrough H D k q z s := by
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · rfl
            · dsimp [selectedRow, rowThrough, s]
              rw [hzval, hc]
              ring
        have hsel : IsSelectedRow H D q hdeg (rowThrough H D k q z s) :=
          ⟨⟨e, he⟩, hrow⟩
        have hslope_a : completionIncidenceSlope D k q hdeg z ⟨Sum.inr (e, c), ha⟩ = s := by
          rw [completionIncidenceSlope_inr D k q hdeg z e c ha he]
        rw [hslope_a]
        apply Subtype.ext
        rw [completionIncidenceOfSlope_val_pos D k q hdeg z s hsel]
        apply congrArg Sum.inr
        apply Prod.ext
        · have hchosen := hsel.choose_spec
          let e2 : IncidentEdges H z.1.1 :=
            ⟨hsel.choose.1, by simpa [rowThrough] using hsel.choose.2⟩
          have hslope : incidenceSlot H D hdeg z.1 e2 = s := by
            have hx := congrArg (fun g : GadgetEdge H D q ↦ g.2.1) hchosen
            change incidenceSlot H D hdeg z.1 _ = s at hx
            have heq : e2 = hsel.choose := Subtype.ext rfl
            rw [heq]
            exact hx
          have he2 : e2 = (⟨e, he⟩ : IncidentEdges H z.1.1) := by
            apply (incidenceSlot H D hdeg z.1).injective
            simpa [s] using hslope
          exact congrArg Subtype.val he2
        · exact hc
  right_inv := completionIncidenceSlope_ofSlope D k q hdeg z

lemma edgeDegree_regularCompletion {H : FiniteHypergraph V E} {D k q : ℕ} [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z : PrivateVertex H k q) :
    (regularCompletion H D k q hdeg).edgeDegree z = D := by
  rw [← card_incidentEdges]
  simpa using Fintype.card_congr (completionIncidenceEquivSlope D k q hdeg z)

/-- Natural numbers below `n ≤ q` have distinct casts in `ZMod q`. -/
lemma fin_natCast_zmod_injective {n q : ℕ} [NeZero q] (hnq : n ≤ q) :
    Function.Injective (fun i : Fin n ↦ (i.1 : ZMod q)) := by
  intro i j hij
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at hij
  simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le i.2 hnq),
    Nat.mod_eq_of_lt (lt_of_lt_of_le j.2 hnq)] using hij

/-- Two distinct points of one private gadget lie on at most one affine row. -/
lemma gadgetEdge_eq_of_pair_mem {H : FiniteHypergraph V E} {D k q : ℕ}
    [NeZero q] [Fact q.Prime] (hkq : k ≤ q) (hDq : D ≤ q)
    {z z' : PrivateVertex H k q} (hzz' : z ≠ z')
    {g g' : GadgetEdge H D q}
    (hzg : z ∈ gadgetSupport H k q g) (hz'g : z' ∈ gadgetSupport H k q g)
    (hzg' : z ∈ gadgetSupport H k q g') (hz'g' : z' ∈ gadgetSupport H k q g') :
    g = g' := by
  rw [mem_gadgetSupport_iff] at hzg hz'g hzg' hz'g'
  have hcol : z.2.1 ≠ z'.2.1 := by
    intro hc
    apply hzz'
    apply Prod.ext
    · exact hzg.1.trans hz'g.1.symm
    · apply Prod.ext
      · exact hc
      · rw [hzg.2, hz'g.2, hc]
  have hcastcol : (z.2.1.1 : ZMod q) ≠ (z'.2.1.1 : ZMod q) :=
    (fin_natCast_zmod_injective hkq).ne hcol
  have hdiffg : z.2.2 - z'.2.2 =
      ((z.2.1.1 : ZMod q) - (z'.2.1.1 : ZMod q)) * (g.2.1.1 : ZMod q) := by
    rw [hzg.2, hz'g.2]
    ring
  have hdiffg' : z.2.2 - z'.2.2 =
      ((z.2.1.1 : ZMod q) - (z'.2.1.1 : ZMod q)) * (g'.2.1.1 : ZMod q) := by
    rw [hzg'.2, hz'g'.2]
    ring
  have hmul :
      ((z.2.1.1 : ZMod q) - (z'.2.1.1 : ZMod q)) *
          ((g.2.1.1 : ZMod q) - (g'.2.1.1 : ZMod q)) = 0 := by
    calc
      _ = ((z.2.1.1 : ZMod q) - (z'.2.1.1 : ZMod q)) * (g.2.1.1 : ZMod q) -
          ((z.2.1.1 : ZMod q) - (z'.2.1.1 : ZMod q)) * (g'.2.1.1 : ZMod q) := by ring
      _ = (z.2.2 - z'.2.2) - (z.2.2 - z'.2.2) := by rw [← hdiffg, ← hdiffg']
      _ = 0 := sub_self _
  have hslopeCast : (g.2.1.1 : ZMod q) = (g'.2.1.1 : ZMod q) := by
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact (sub_ne_zero.mpr hcastcol) hzero |>.elim
    · exact sub_eq_zero.mp hzero
  have hslope : g.2.1 = g'.2.1 := (fin_natCast_zmod_injective hDq) hslopeCast
  apply Prod.ext
  · exact hzg.1.symm.trans hzg'.1
  · apply Prod.ext
    · exact hslope
    · calc
        g.2.2 = z.2.2 - (z.2.1.1 : ZMod q) * (g.2.1.1 : ZMod q) := by
          rw [hzg.2]
          ring
        _ = z.2.2 - (z.2.1.1 : ZMod q) * (g'.2.1.1 : ZMod q) := by rw [hslope]
        _ = g'.2.2 := by
          rw [hzg'.2]
          ring

/-- A trade column contains at most one vertex owned by each original vertex. -/
lemma eq_of_mem_tradeSupport_of_same_owner {H : FiniteHypergraph V E} {D k q : ℕ}
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {e : E} {c : Fin k} {z z' : PrivateVertex H k q}
    (hz : z ∈ tradeSupport H D k q hdeg e c)
    (hz' : z' ∈ tradeSupport H D k q hdeg e c) (howner : z.1 = z'.1) :
    z = z' := by
  rcases z with ⟨zv, ⟨j, y⟩⟩
  rcases z' with ⟨zv', ⟨j', y'⟩⟩
  simp only at howner
  cases howner
  rw [mem_tradeSupport_iff] at hz hz'
  rcases hz with ⟨hze, hzc, hzval⟩
  rcases hz' with ⟨hz'e, hz'c, hz'val⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hzc.trans hz'c.symm
    · rw [hzval, hz'val]

/-- Indexed edges containing both specified vertices. -/
abbrev PairEdges (H : FiniteHypergraph V E) (u v : V) :=
  {e : E // u ∈ H.support e ∧ v ∈ H.support e}

lemma card_pairEdges (H : FiniteHypergraph V E) (u v : V) :
    Fintype.card (PairEdges H u v) = H.edgePairDegree u v := by
  simpa [PairEdges, FiniteHypergraph.edgePairDegree] using
    (Fintype.card_subtype (fun e : E ↦ u ∈ H.support e ∧ v ∈ H.support e))

/-- Inside one private gadget the completed codegree is at most one. -/
lemma edgePairDegree_regularCompletion_le_one_same_owner
    {H : FiniteHypergraph V E} {D k q : ℕ} [NeZero q] [Fact q.Prime]
    (hkq : k ≤ q) (hDq : D ≤ q)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {z z' : PrivateVertex H k q} (hzz' : z ≠ z') (howner : z.1 = z'.1) :
    (regularCompletion H D k q hdeg).edgePairDegree z z' ≤ 1 := by
  rw [← card_pairEdges, Fintype.card_le_one_iff]
  intro a b
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | inl ga =>
      cases b with
      | inl gb =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact gadgetEdge_eq_of_pair_mem hkq hDq hzz' ha.1 ha.2 hb.1 hb.2
      | inr eb =>
          exact (hzz' (eq_of_mem_tradeSupport_of_same_owner hdeg hb.1 hb.2 howner)).elim
  | inr ea =>
      exact (hzz' (eq_of_mem_tradeSupport_of_same_owner hdeg ha.1 ha.2 howner)).elim

lemma owner_eq_of_pair_mem_gadgetSupport {H : FiniteHypergraph V E} {D k q : ℕ}
    {z z' : PrivateVertex H k q} {g : GadgetEdge H D q}
    (hz : z ∈ gadgetSupport H k q g) (hz' : z' ∈ gadgetSupport H k q g) :
    z.1 = z'.1 := by
  rw [mem_gadgetSupport_iff] at hz hz'
  exact hz.1.trans hz'.1.symm

/-- Between two different private gadgets, every completion edge projects to the unique
original edge whose trade produced it. -/
def pairProjection {H : FiniteHypergraph V E} (D k q : ℕ) [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z z' : PrivateVertex H k q) (howner : z.1 ≠ z'.1)
    (a : PairEdges (regularCompletion H D k q hdeg) z z') :
    PairEdges H z.1.1 z'.1.1 := by
  rcases a with ⟨a, ha⟩
  cases a with
  | inl g =>
      exact (howner (owner_eq_of_pair_mem_gadgetSupport ha.1 ha.2)).elim
  | inr ec =>
      rcases ec with ⟨e, c⟩
      have hz := (mem_tradeSupport_iff H D k q hdeg e c z).mp ha.1
      have hz' := (mem_tradeSupport_iff H D k q hdeg e c z').mp ha.2
      exact ⟨e, hz.choose, hz'.choose⟩

lemma pairProjection_injective {H : FiniteHypergraph V E} (D k q : ℕ) [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (z z' : PrivateVertex H k q) (howner : z.1 ≠ z'.1) :
    Function.Injective (pairProjection D k q hdeg z z' howner) := by
  intro a b hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | inl ga => exact (howner (owner_eq_of_pair_mem_gadgetSupport ha.1 ha.2)).elim
  | inr ea =>
      cases b with
      | inl gb => exact (howner (owner_eq_of_pair_mem_gadgetSupport hb.1 hb.2)).elim
      | inr eb =>
          rcases ea with ⟨e, c⟩
          rcases eb with ⟨f, d⟩
          have he : e = f := by
            have hval := congrArg Subtype.val hab
            simpa [pairProjection] using hval
          have hc := (mem_tradeSupport_iff H D k q hdeg e c z).mp ha.1 |>.choose_spec.1
          have hd := (mem_tradeSupport_iff H D k q hdeg f d z).mp hb.1 |>.choose_spec.1
          apply Subtype.ext
          apply congrArg Sum.inr
          apply Prod.ext
          · exact he
          · exact hc.symm.trans hd

/-- Between different owners, the completion codegree is bounded by the original codegree. -/
lemma edgePairDegree_regularCompletion_le_of_owner_ne
    {H : FiniteHypergraph V E} {D k q : ℕ} [NeZero q]
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {z z' : PrivateVertex H k q} (howner : z.1 ≠ z'.1) :
    (regularCompletion H D k q hdeg).edgePairDegree z z' ≤
      H.edgePairDegree z.1.1 z'.1.1 := by
  rw [← card_pairEdges, ← card_pairEdges]
  exact Fintype.card_le_of_injective _ (pairProjection_injective D k q hdeg z z' howner)

/-- The completion codegree is at most the larger of the corresponding original codegree and one. -/
lemma edgePairDegree_regularCompletion_le_max
    {H : FiniteHypergraph V E} {D k q : ℕ} [NeZero q] [Fact q.Prime]
    (hkq : k ≤ q) (hDq : D ≤ q)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {z z' : PrivateVertex H k q} (hzz' : z ≠ z') :
    (regularCompletion H D k q hdeg).edgePairDegree z z' ≤
      max (H.edgePairDegree z.1.1 z'.1.1) 1 := by
  by_cases howner : z.1 = z'.1
  · exact (edgePairDegree_regularCompletion_le_one_same_owner hkq hDq hdeg hzz' howner).trans
      (le_max_right _ _)
  · exact (edgePairDegree_regularCompletion_le_of_owner_ne hdeg howner).trans
      (le_max_left _ _)

/-- The zeroth internal column, available for positive uniformity. -/
def zeroColumn {k : ℕ} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- The distinguished copy of an original vertex in its private gadget. -/
def distinguishedVertex (H : FiniteHypergraph V E) {k q : ℕ} (hk : 0 < k)
    (v : ↑H.vertexSet) : PrivateVertex H k q :=
  (v, (zeroColumn hk, 0))

/-- Original indexed edges are retained as the zeroth columns of their trades. -/
def originalEdgeEmbedding (H : FiniteHypergraph V E) (D q : ℕ) {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    E ↪ CompletionEdge H D k q hdeg where
  toFun e := Sum.inr (e, zeroColumn hk)
  inj' := by intro e f hef; simpa using hef

lemma distinguishedVertex_mem_originalEdge {H : FiniteHypergraph V E}
    {D k q : ℕ} (hk : 0 < k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {e : E} {v : V} (hve : v ∈ H.support e) :
    distinguishedVertex H hk ⟨v, H.support_subset_vertexSet e hve⟩ ∈
      tradeSupport H D k q hdeg e (zeroColumn hk) := by
  rw [mem_tradeSupport_iff]
  refine ⟨hve, rfl, ?_⟩
  simp [distinguishedVertex, zeroColumn]

/-- Restricting a completion colouring to the preserved original edges is proper. -/
def restrict_originalEdgeColoring {H : FiniteHypergraph V E}
    {D k q r : ℕ} [NeZero q] (hk : 0 < k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (c : (regularCompletion H D k q hdeg).EdgeColoring r) :
    H.EdgeColoring r := by
  refine SimpleGraph.Coloring.mk
    (fun e ↦ c (originalEdgeEmbedding H D q hk hdeg e)) ?_
  intro e f hef
  have hembed : originalEdgeEmbedding H D q hk hdeg e ≠
      originalEdgeEmbedding H D q hk hdeg f :=
    (originalEdgeEmbedding H D q hk hdeg).injective.ne hef.1
  apply c.valid
  refine ⟨hembed, ?_⟩
  intro hdis
  apply hef.2
  rw [Finset.disjoint_left]
  intro v hve hvf
  let ve : ↑H.vertexSet := ⟨v, H.support_subset_vertexSet e hve⟩
  let vf : ↑H.vertexSet := ⟨v, H.support_subset_vertexSet f hvf⟩
  have hve' : distinguishedVertex H hk ve ∈
      tradeSupport H D k q hdeg e (zeroColumn hk) :=
    distinguishedVertex_mem_originalEdge hk hdeg hve
  have hvf' : distinguishedVertex H hk vf ∈
      tradeSupport H D k q hdeg f (zeroColumn hk) :=
    distinguishedVertex_mem_originalEdge hk hdeg hvf
  change Disjoint (tradeSupport H D k q hdeg e (zeroColumn hk))
    (tradeSupport H D k q hdeg f (zeroColumn hk)) at hdis
  have hvtx : distinguishedVertex (q := q) H hk ve = distinguishedVertex H hk vf := by
    simp [distinguishedVertex, ve, vf]
  exact (Finset.disjoint_left.mp hdis) hve' (hvtx.symm ▸ hvf')

end PippengerSpencerEdgeColoring

open PippengerSpencerEdgeColoring

/-- The near-regular Pippenger--Spencer edge-colouring statement.  It is deliberately a
proposition parameter: this file proves its deterministic matching consequence, not the
probabilistic edge-colouring theorem itself. -/
def NearRegularPippengerSpencerEdgeColoring : Prop :=
  ∀ k : ℕ, 0 < k → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
        ∀ (H : FiniteHypergraph V E) (D : ℕ),
          D₀ ≤ D → H.IsUniform k →
          (∀ v ∈ H.vertexSet, (1 - delta) * (D : ℝ) ≤ (H.edgeDegree v : ℝ)) →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
            (H.edgePairDegree u v : ℝ) < delta * (D : ℝ)) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ (1 + epsilon) * (D : ℝ) ∧
            Nonempty (H.EdgeColoring q)

/-- Near-regular Pippenger--Spencer edge colouring implies the maximum-degree
Pippenger--Spencer matching theorem.  The proof completes the input to an exactly regular
private affine gadget hypergraph, restricts a colouring to the preserved original edges,
and takes a largest colour class. -/
theorem nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching_via_completion
    (hColor : NearRegularPippengerSpencerEdgeColoring) : PippengerSpencerMatching := by
  intro k hk epsilon hepsilon
  by_cases hepsilon_one : 1 ≤ epsilon
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    intro V E _ _ _ H D _ _ _ _
    refine ⟨∅, H.empty_isMatching, ?_⟩
    simp only [card_empty, Nat.cast_zero]
    have hcard : (0 : ℝ) ≤ Fintype.card E := by positivity
    have hD : (0 : ℝ) ≤ D := by positivity
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hepsilon_one) hcard) hD
  · have hepsilon_lt_one : epsilon < 1 := lt_of_not_ge hepsilon_one
    obtain ⟨delta, hdelta, D₀, hround⟩ := hColor k hk epsilon hepsilon
    obtain ⟨D₁, hD₁⟩ := exists_nat_gt (1 / delta)
    refine ⟨delta / 2, div_pos hdelta (by norm_num), max D₀ D₁, ?_⟩
    intro V E _ _ _ H D hDlarge hunif hdeg hpair
    have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDlarge
    have hD₁le : D₁ ≤ D := (le_max_right _ _).trans hDlarge
    have hratio : 1 / delta < (D : ℝ) := hD₁.trans_le (by exact_mod_cast hD₁le)
    have hdeltaD : 1 < delta * (D : ℝ) := by
      have := (div_lt_iff₀ hdelta).mp hratio
      nlinarith
    have hDposR : (0 : ℝ) < D := by nlinarith
    have hDpos : 0 < D := by exact_mod_cast hDposR
    obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (max k D)
    letI : Fact q.Prime := ⟨hqprime⟩
    letI : NeZero q := ⟨hqprime.ne_zero⟩
    have hkq : k ≤ q := (le_max_left _ _).trans hqge
    have hDq : D ≤ q := (le_max_right _ _).trans hqge
    let HC := regularCompletion H D k q hdeg
    obtain ⟨r, hrpos, hrle, ⟨c⟩⟩ := hround
      (PrivateVertex H k q) (CompletionEdge H D k q hdeg) HC D hD₀
      (regularCompletion_isUniform hdeg hunif)
      (by
        intro z hz
        rw [edgeDegree_regularCompletion hdeg]
        nlinarith [mul_nonneg (le_of_lt hdelta) (Nat.cast_nonneg D)])
      (by
        intro z hz
        exact (edgeDegree_regularCompletion hdeg z).le)
      (by
        intro z hz z' hz' hzz'
        by_cases howner : z.1 = z'.1
        · have hle := edgePairDegree_regularCompletion_le_one_same_owner
            hkq hDq hdeg hzz' howner
          have hleR : ((HC.edgePairDegree z z' : ℕ) : ℝ) ≤ (1 : ℝ) := by
            exact_mod_cast hle
          exact hleR.trans_lt hdeltaD
        · have hle := edgePairDegree_regularCompletion_le_of_owner_ne hdeg howner
          have howners : z.1.1 ≠ z'.1.1 := by
            intro hv
            exact howner (Subtype.ext hv)
          have horiginal := hpair z.1.1 z.1.2 z'.1.1 z'.1.2 howners
          have hsmall : (delta / 2) * (D : ℝ) < delta * (D : ℝ) := by
            nlinarith
          exact (Nat.cast_le.mpr hle).trans_lt (horiginal.trans hsmall))
    let c₀ : H.EdgeColoring r := restrict_originalEdgeColoring hk hdeg c
    obtain ⟨i, hi⟩ := c₀.exists_div_le_card_restrictedColorClass
      (Finset.univ : Finset E) hrpos
    let M : Finset E := c₀.restrictedColorClass (Finset.univ : Finset E) i
    refine ⟨M, c₀.restrictedColorClass_isMatching Finset.univ i, ?_⟩
    have hi' : (Fintype.card E : ℝ) / (r : ℝ) ≤ (M.card : ℝ) := by
      simpa [M] using hi
    have hcardnonneg : (0 : ℝ) ≤ Fintype.card E := by positivity
    have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
    have hdenpos : 0 < (1 + epsilon) * (D : ℝ) :=
      mul_pos (by linarith) hDposR
    calc
      (1 - epsilon) * (Fintype.card E : ℝ) / (D : ℝ) ≤
          (Fintype.card E : ℝ) / ((1 + epsilon) * (D : ℝ)) := by
        rw [div_le_div_iff₀ hDposR hdenpos]
        have hfactor : (1 - epsilon) * (1 + epsilon) ≤ (1 : ℝ) := by
          nlinarith [sq_nonneg epsilon]
        calc
          (1 - epsilon) * (Fintype.card E : ℝ) * ((1 + epsilon) * (D : ℝ)) =
              ((1 - epsilon) * (1 + epsilon)) *
                ((Fintype.card E : ℝ) * (D : ℝ)) := by ring
          _ ≤ 1 * ((Fintype.card E : ℝ) * (D : ℝ)) :=
            mul_le_mul_of_nonneg_right hfactor
              (mul_nonneg hcardnonneg (le_of_lt hDposR))
          _ = (Fintype.card E : ℝ) * (D : ℝ) := by ring
      _ ≤ (Fintype.card E : ℝ) / (r : ℝ) :=
        div_le_div_of_nonneg_left hcardnonneg hrposR hrle
      _ ≤ (M.card : ℝ) := hi'

/-- The final reduction treats rank one directly by the shared finite greedy edge-colouring
lemma.  For rank at least two it uses the private affine regular completion above. -/
theorem nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching
    (hColor : NearRegularPippengerSpencerEdgeColoring) : PippengerSpencerMatching := by
  intro k hk epsilon hepsilon
  by_cases hkone : k = 1
  · subst k
    by_cases hepsilon_one : 1 ≤ epsilon
    · refine ⟨1, zero_lt_one, 0, ?_⟩
      intro V E _ _ _ H D _ _ _ _
      refine ⟨∅, H.empty_isMatching, ?_⟩
      simp only [card_empty, Nat.cast_zero]
      have hcard : (0 : ℝ) ≤ Fintype.card E := by positivity
      have hD : (0 : ℝ) ≤ D := by positivity
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hepsilon_one) hcard) hD
    · have hepsilon_lt_one : epsilon < 1 := lt_of_not_ge hepsilon_one
      obtain ⟨D₀, hD₀⟩ := exists_nat_gt ((1 - epsilon) / epsilon)
      refine ⟨1, zero_lt_one, D₀, ?_⟩
      intro V E _ _ _ H D hDlarge hunif hdeg _hpair
      have hratio : (1 - epsilon) / epsilon < (D : ℝ) :=
        hD₀.trans_le (by exact_mod_cast hDlarge)
      have hepsD : 1 - epsilon < epsilon * (D : ℝ) := by
        have := (div_lt_iff₀ hepsilon).mp hratio
        nlinarith
      have hDposR : (0 : ℝ) < D := by nlinarith
      obtain ⟨c⟩ := H.exists_edgeColoring_uniform_degree hunif hdeg
      have hcolors : 0 < 1 * D + 1 := by omega
      obtain ⟨i, hi⟩ := c.exists_div_le_card_restrictedColorClass
        (Finset.univ : Finset E) hcolors
      let M : Finset E := c.restrictedColorClass (Finset.univ : Finset E) i
      refine ⟨M, c.restrictedColorClass_isMatching Finset.univ i, ?_⟩
      have hi' : (Fintype.card E : ℝ) / ((D + 1 : ℕ) : ℝ) ≤ (M.card : ℝ) := by
        simpa [M] using hi
      have hcardnonneg : (0 : ℝ) ≤ Fintype.card E := by positivity
      have hDsuccR : (0 : ℝ) < (D + 1 : ℕ) := by positivity
      calc
        (1 - epsilon) * (Fintype.card E : ℝ) / (D : ℝ) ≤
            (Fintype.card E : ℝ) / ((D + 1 : ℕ) : ℝ) := by
          rw [div_le_div_iff₀ hDposR hDsuccR]
          have hfactor : (1 - epsilon) * ((D + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by
            push_cast
            nlinarith
          calc
            (1 - epsilon) * (Fintype.card E : ℝ) * ((D + 1 : ℕ) : ℝ) =
                (Fintype.card E : ℝ) *
                  ((1 - epsilon) * ((D + 1 : ℕ) : ℝ)) := by ring
            _ ≤ (Fintype.card E : ℝ) * (D : ℝ) :=
              mul_le_mul_of_nonneg_left hfactor hcardnonneg
        _ ≤ (M.card : ℝ) := hi'
  · have hk_two : 2 ≤ k := by omega
    exact (nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching_via_completion
      hColor) k hk epsilon hepsilon

end

end Erdos76
