/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.NestedDomains
import Wikipedia.SchoenfliesTheorem.PolygonalJordan
import Wikipedia.SchoenfliesTheorem.FaceCyclesLand

/-!
# Polygonal Jordan filling for sublevel components

This file connects the polygonal Jordan curve theorem proved in the Erdős 223 development to
the maximum-principle interface used for Erdős 515.  The two developments use isometric models
of the plane (`ℂ` and `EuclideanSpace ℝ (Fin 2)`); `complexPlaneEquiv` transports the bounded
inside of a closed polygon between them.
-/

open Bornology Set
open scoped Graph

namespace Erdos515

/-- The canonical real-linear isometry from the complex plane to the Euclidean plane used by
the Schoenflies development. -/
noncomputable def complexPlaneEquiv : ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane :=
  Complex.orthonormalBasisOneI.repr

@[simp] lemma complexPlaneEquiv_apply (z : ℂ) :
    complexPlaneEquiv z = ![z.re, z.im] := by
  rfl

@[simp] lemma complexPlaneEquiv_symm_apply (x : Schoenflies.Plane) :
    complexPlaneEquiv.symm x = x 0 + x 1 * Complex.I := by
  rfl

/-- The bounded side of a simple closed polygon, transported to the complex plane. -/
noncomputable def complexPolygonInside {m : ℕ} (P : Schoenflies.ClosedPolygon m) : Set ℂ :=
  complexPlaneEquiv ⁻¹' Schoenflies.inside P.carrier

/-- The polygon itself, transported to the complex plane. -/
noncomputable def complexPolygonCarrier {m : ℕ} (P : Schoenflies.ClosedPolygon m) : Set ℂ :=
  complexPlaneEquiv ⁻¹' P.carrier

lemma isOpen_complexPolygonInside {m : ℕ} (P : Schoenflies.ClosedPolygon m) :
    IsOpen (complexPolygonInside P) := by
  exact (complexPlaneEquiv.toHomeomorph.isOpen_preimage).2
    P.isSeparating_carrier.isOpen_inside

lemma isPreconnected_complexPolygonInside {m : ℕ} (P : Schoenflies.ClosedPolygon m) :
    IsPreconnected (complexPolygonInside P) := by
  exact complexPlaneEquiv.toHomeomorph.isPreconnected_preimage.mpr
    P.isSeparating_carrier.isConnected_inside.isPreconnected

lemma isBounded_complexPolygonInside {m : ℕ} (P : Schoenflies.ClosedPolygon m) :
    IsBounded (complexPolygonInside P) := by
  exact complexPlaneEquiv.antilipschitz.isBounded_preimage
    P.isSeparating_carrier.isBounded_inside

lemma frontier_complexPolygonInside {m : ℕ} (P : Schoenflies.ClosedPolygon m) :
    frontier (complexPolygonInside P) = complexPolygonCarrier P := by
  change frontier (complexPlaneEquiv.toHomeomorph ⁻¹' Schoenflies.inside P.carrier) =
    complexPlaneEquiv.toHomeomorph ⁻¹' P.carrier
  rw [← complexPlaneEquiv.toHomeomorph.preimage_frontier,
    P.isSeparating_carrier.frontier_inside]

lemma frontier_complexPolygonInside_nonempty {m : ℕ} (P : Schoenflies.ClosedPolygon m) :
    (frontier (complexPolygonInside P)).Nonempty := by
  rw [frontier_complexPolygonInside, complexPolygonCarrier]
  exact P.carrier_nonempty.preimage complexPlaneEquiv.surjective

/-- **Polygonal Jordan filling inside a sublevel component.** If a simple closed polygon is
carried by one strict-sublevel component, then its bounded side is carried by that same component.

This is the precise analytic use of the polygonal Jordan theorem in the simple-connectivity
argument: the polygonal theorem supplies a bounded connected open inside whose frontier is the
polygon, and the bounded-open maximum principle fills it without leaving the sublevel component.
-/
theorem complexPolygonInside_subset_sublevelComponent
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} {m : ℕ} (P : Schoenflies.ClosedPolygon m)
    (hcarrier : complexPolygonCarrier P ⊆ sublevelComponent u c a) :
    complexPolygonInside P ⊆ sublevelComponent u c a := by
  apply bounded_open_subset_sublevelComponent_of_frontier_subset hu hmax
    (isOpen_complexPolygonInside P) (isBounded_complexPolygonInside P)
    (isPreconnected_complexPolygonInside P) (frontier_complexPolygonInside_nonempty P)
  rw [frontier_complexPolygonInside]
  exact hcarrier

/-! ## Filling all bounded faces of a polygonal plane graph -/

/-- A face of a plane graph, transported from `EuclideanSpace ℝ (Fin 2)` to `ℂ`. -/
noncomputable def complexGraphFace {β : Type*} (G : Graph Schoenflies.Plane β)
    (drawing : β → ℝ → Schoenflies.Plane) (z : Schoenflies.Plane) : Set ℂ :=
  complexPlaneEquiv ⁻¹' Graph.face G drawing z

/-- The point set of a plane drawing, transported to `ℂ`. -/
noncomputable def complexGraphPointSet {β : Type*} (G : Graph Schoenflies.Plane β)
    (drawing : β → ℝ → Schoenflies.Plane) : Set ℂ :=
  complexPlaneEquiv ⁻¹' Graph.pointSet G drawing

lemma isOpen_complexGraphFace {β : Type*} {G : Graph Schoenflies.Plane β} [G.Finite]
    {drawing : β → ℝ → Schoenflies.Plane} (hd : Graph.IsDrawing G drawing)
    (z : Schoenflies.Plane) :
    IsOpen (complexGraphFace G drawing z) := by
  exact (complexPlaneEquiv.toHomeomorph.isOpen_preimage).2 (hd.isOpen_face z)

lemma isPreconnected_complexGraphFace {β : Type*} {G : Graph Schoenflies.Plane β}
    {drawing : β → ℝ → Schoenflies.Plane} {z : Schoenflies.Plane}
    (hz : z ∈ Graph.exterior G drawing) :
    IsPreconnected (complexGraphFace G drawing z) := by
  exact complexPlaneEquiv.toHomeomorph.isPreconnected_preimage.mpr
    (Graph.isConnected_face hz).isPreconnected

lemma isBounded_complexGraphFace {β : Type*} {G : Graph Schoenflies.Plane β}
    {drawing : β → ℝ → Schoenflies.Plane} {z : Schoenflies.Plane}
    (hb : IsBounded (Graph.face G drawing z)) :
    IsBounded (complexGraphFace G drawing z) := by
  exact complexPlaneEquiv.antilipschitz.isBounded_preimage hb

/-- **All bounded polygonal faces fill.**  Let a finite two-connected polygonal plane graph be
drawn inside one strict-sublevel component.  Then every bounded face of the drawing belongs to
the same component.

`Graph.face_cycles'` supplies a simple cycle whose carrier is the frontier of the face.  The
bounded-open maximum principle then fills the face.  This is the form needed after subdividing a
self-intersecting polygonal loop into a plane graph. -/
theorem complexGraphFace_subset_sublevelComponent
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} {β : Type*} {G : Graph Schoenflies.Plane β} [G.Finite]
    {drawing : β → ℝ → Schoenflies.Plane}
    (hd : Graph.IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), Schoenflies.IsPolygonal (Graph.edgeArc drawing g))
    (hG : G.IsTwoConnected) {z : Schoenflies.Plane}
    (hz : z ∈ Graph.exterior G drawing)
    (hb : IsBounded (Graph.face G drawing z))
    (hpoint : complexGraphPointSet G drawing ⊆ sublevelComponent u c a) :
    complexGraphFace G drawing z ⊆ sublevelComponent u c a := by
  obtain ⟨e, v, w, D, hf⟩ := Graph.face_cycles' hd hpoly hG z hz
  have hfront : frontier (complexGraphFace G drawing z) =
      complexPlaneEquiv ⁻¹' Graph.edgesCover drawing (e :: D) := by
    change frontier (complexPlaneEquiv.toHomeomorph ⁻¹' Graph.face G drawing z) = _
    rw [← complexPlaneEquiv.toHomeomorph.preimage_frontier, hf.frontier_eq]
    rfl
  have hfront_ne : (frontier (complexGraphFace G drawing z)).Nonempty := by
    rw [hfront]
    apply Set.Nonempty.preimage (f := complexPlaneEquiv)
      ⟨w, hf.isCycle.isWalk_cons.left_mem_edgesCover hd (by simp)⟩
    exact complexPlaneEquiv.surjective
  apply bounded_open_subset_sublevelComponent_of_frontier_subset hu hmax
    (isOpen_complexGraphFace hd z) (isBounded_complexGraphFace hb)
    (isPreconnected_complexGraphFace hz) hfront_ne
  rw [hfront]
  intro x hx
  apply hpoint
  exact Graph.edgesCover_subset_pointSet hf.isCycle.isWalk_cons.edgeSet_subset hx

end Erdos515
