/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeBernoulliConcentration
import ErdosProblems.Erdos207.ReserveSampledLinkConcentration

/-! # Sharp relative tails for actual reserve link sizes, degrees, and codegrees -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem reserveEdgeLaw_probability_abs_sampledLinkDegree_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V) (htri : ConsistsOfTriangles G A)
    (center x : V) (hc : center ∉ U) (r : ℝ≥0) (hr : r ≤ 1) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      delta*((r : ℝ)*(ambientLinkNeighborsIn center A U x).card) <
        |((ambientLinkNeighborsIn center A (spokeVerticesIn U (reserveEdges G U bits) center) x).card : ℝ)-
          (r : ℝ)*(ambientLinkNeighborsIn center A U x).card|) : ℝ) ≤
      2*Real.exp (-delta^2*((r : ℝ)*(ambientLinkNeighborsIn center A U x).card)/4) := by
  have hb := reserveEdgeLaw_probability_abs_inter_count_gt G U r hr (ambientLinkSpokeEdges center A U x)
    (ambientLinkSpokeEdges_subset_crossingEdges htri hc) delta hdelta hdelta1
  simpa only [ambientLinkSpokeEdges_card center A U x hc,
    sampledAmbientLinkNeighbors_card_eq_inter center A U _ x hc] using hb

theorem reserveEdgeLaw_probability_abs_sampledLinkCodegree_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V) (htri : ConsistsOfTriangles G A)
    (center x y : V) (hc : center ∉ U) (r : ℝ≥0) (hr : r ≤ 1) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      delta*((r : ℝ)*(ambientLinkCommonNeighborsIn center A U x y).card) <
        |((ambientLinkCommonNeighborsIn center A (spokeVerticesIn U (reserveEdges G U bits) center) x y).card : ℝ)-
          (r : ℝ)*(ambientLinkCommonNeighborsIn center A U x y).card|) : ℝ) ≤
      2*Real.exp (-delta^2*((r : ℝ)*(ambientLinkCommonNeighborsIn center A U x y).card)/4) := by
  have hb := reserveEdgeLaw_probability_abs_inter_count_gt G U r hr (ambientLinkCommonSpokeEdges center A U x y)
    (ambientLinkCommonSpokeEdges_subset_crossingEdges htri hc) delta hdelta hdelta1
  simpa only [ambientLinkCommonSpokeEdges_card center A U x y hc,
    sampledAmbientLinkCommonNeighbors_card_eq_inter center A U _ x y hc] using hb

theorem reserve_neighbor_spoke_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (center : V) (_hc : center ∉ U) (bits : Sym2 V → Bool) :
    (spokeVerticesIn U (reserveEdges G U bits) center).image (fun x ↦ s(center,x)) =
      ((neighborsIn G U center).image (fun x ↦ s(center,x))) ∩ reserveEdges G U bits := by
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have hh := mem_spokeVerticesIn_iff.mp hx
    have hxG : G.Adj center x := (mem_crossingEdges_iff.mp (mem_reserveEdges_iff.mp hh.2).1).1
    exact mem_inter.mpr ⟨mem_image.mpr ⟨x, mem_neighborsIn_iff.mpr ⟨hh.1, hxG⟩, rfl⟩, hh.2⟩
  · intro he
    have hh := mem_inter.mp he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hh.1
    exact mem_image.mpr ⟨x, mem_spokeVerticesIn_iff.mpr ⟨(mem_neighborsIn_iff.mp hx).1, hh.2⟩, rfl⟩

theorem reserveEdgeLaw_probability_abs_sampledNeighborSize_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (center : V) (hc : center ∉ U)
    (r : ℝ≥0) (hr : r ≤ 1) (delta : ℝ) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      delta*((r : ℝ)*(neighborsIn G U center).card) <
        |((spokeVerticesIn U (reserveEdges G U bits) center).card : ℝ)-
          (r : ℝ)*(neighborsIn G U center).card|) : ℝ) ≤
      2*Real.exp (-delta^2*((r : ℝ)*(neighborsIn G U center).card)/4) := by
  let E := (neighborsIn G U center).image (fun x ↦ s(center,x))
  have hE : E ⊆ crossingEdges G U := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have hh := mem_neighborsIn_iff.mp hx
    exact mem_crossingEdges_iff.mpr ⟨hh.2, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hh.1, hc⟩)⟩
  have hinj : Function.Injective (fun x : V ↦ s(center,x)) := fun _ _ h ↦ Sym2.congr_right.mp h
  have hcard : E.card = (neighborsIn G U center).card := card_image_of_injective _ hinj
  have hsample (bits : Sym2 V → Bool) : (E ∩ reserveEdges G U bits).card =
      (spokeVerticesIn U (reserveEdges G U bits) center).card := by
    rw [← reserve_neighbor_spoke_image G U center hc bits, card_image_of_injective _ hinj]
  have hb := reserveEdgeLaw_probability_abs_inter_count_gt G U r hr E hE delta hdelta hdelta1
  simpa only [hcard, hsample] using hb

end

end Erdos207
