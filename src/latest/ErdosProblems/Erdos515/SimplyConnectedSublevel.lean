/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.PlaneTopology
import ErdosProblems.Erdos515.ClosedJordanSimplyConnected
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Loop homotopies in sublevel components

This file develops the endpoint-fixed homotopy layer used to pass from an arbitrary loop in a
strict-sublevel component to a sufficiently close polygonal loop.  The planar filling input is
`complexPolygonInside_subset_sublevelComponent` and
`complexGraphFace_subset_sublevelComponent` from `PlaneTopology`.
-/

open Set
open unitInterval

namespace Erdos515

/-! ## Jordan discs in the complex plane -/

/-- A planar Jordan curve, transported to the complex plane. -/
noncomputable def complexJordanCarrier (C : Set Schoenflies.Plane) : Set ℂ :=
  complexPlaneEquiv ⁻¹' C

/-- The bounded complementary component of a planar Jordan curve, transported to `ℂ`. -/
noncomputable def complexJordanInside (C : Set Schoenflies.Plane) : Set ℂ :=
  complexPlaneEquiv ⁻¹' Schoenflies.inside C

/-- The transported closed Jordan disc is simply connected. -/
lemma isSimplyConnected_complexJordanClosedDisk {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) :
    IsSimplyConnected (complexJordanCarrier C ∪ complexJordanInside C) := by
  change IsSimplyConnected
    (complexPlaneEquiv.toHomeomorph ⁻¹' (C ∪ Schoenflies.inside C))
  rw [complexPlaneEquiv.toHomeomorph.isSimplyConnected_preimage]
  exact Schoenflies.IsJordanCurve.isSimplyConnected_union_inside hC

/-- **Jordan filling for an arbitrary Jordan curve.**  If its carrier belongs to one strict
sublevel component, then its bounded side belongs to that component too. -/
theorem complexJordanInside_subset_sublevelComponent
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hcarrier : complexJordanCarrier C ⊆ sublevelComponent u c a) :
    complexJordanInside C ⊆ sublevelComponent u c a := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hopen : IsOpen (complexJordanInside C) :=
    (complexPlaneEquiv.toHomeomorph.isOpen_preimage).2 hsep.isOpen_inside
  have hconn : IsPreconnected (complexJordanInside C) :=
    complexPlaneEquiv.toHomeomorph.isPreconnected_preimage.mpr
      hsep.isConnected_inside.isPreconnected
  have hbounded : Bornology.IsBounded (complexJordanInside C) :=
    complexPlaneEquiv.antilipschitz.isBounded_preimage hsep.isBounded_inside
  have hfront : frontier (complexJordanInside C) = complexJordanCarrier C := by
    change frontier (complexPlaneEquiv.toHomeomorph ⁻¹' Schoenflies.inside C) =
      complexPlaneEquiv.toHomeomorph ⁻¹' C
    rw [← complexPlaneEquiv.toHomeomorph.preimage_frontier, hsep.frontier_inside]
  have hfront_ne : (frontier (complexJordanInside C)).Nonempty := by
    rw [hfront, complexJordanCarrier]
    exact hC.nonempty.preimage complexPlaneEquiv.surjective
  apply bounded_open_subset_sublevelComponent_of_frontier_subset hu hmax hopen hbounded hconn
    hfront_ne
  rwa [hfront]

/-- A plane set has Jordan enclosures if each compact connected subset can be surrounded by a
Jordan curve carried by the set.  Only the carrier is required to lie in the set; the bounded
side is deliberately part of the conclusion to be obtained later from the maximum principle. -/
def HasJordanEnclosures (D : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ D →
    ∃ C : Set Schoenflies.Plane, Schoenflies.IsJordanCurve C ∧
      K ⊆ complexJordanCarrier C ∪ complexJordanInside C ∧
      complexJordanCarrier C ⊆ D

/-- Once a loop is enclosed by a Jordan curve carried by the sublevel component, it contracts
inside that component.  This isolates the remaining geometric enclosure lemma from the
analytic maximum-principle argument. -/
theorem isSimplyConnected_sublevelComponent_of_jordan_enclosure
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} (ha : u a < c)
    (henclose : ∀ x : ℂ, ∀ p : Path x x,
      (∀ t, p t ∈ sublevelComponent u c a) →
      ∃ C : Set Schoenflies.Plane, Schoenflies.IsJordanCurve C ∧
        range p ⊆ complexJordanCarrier C ∪ complexJordanInside C ∧
        complexJordanCarrier C ⊆ sublevelComponent u c a) :
    IsSimplyConnected (sublevelComponent u c a) := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨isPathConnected_sublevelComponent hu ha, ?_⟩
  intro x p hp
  obtain ⟨C, hC, hpC, hcarrier⟩ := henclose x p hp
  have hin := complexJordanInside_subset_sublevelComponent hu hmax hC hcarrier
  have hdisc : complexJordanCarrier C ∪ complexJordanInside C ⊆
      sublevelComponent u c a := union_subset hcarrier hin
  have hsimply := isSimplyConnected_complexJordanClosedDisk hC
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem] at hsimply
  obtain ⟨F, hF⟩ := hsimply.2 x p (fun t ↦ hpC (mem_range_self t))
  exact ⟨F, fun z ↦ hdisc (hF z)⟩

/-- Compact-connected Jordan enclosure is the sole planar-topology input needed to deduce
simple connectivity of a strict-sublevel component from the bounded-open maximum principle. -/
theorem isSimplyConnected_sublevelComponent_of_hasJordanEnclosures
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} (ha : u a < c)
    (henclose : HasJordanEnclosures (sublevelComponent u c a)) :
    IsSimplyConnected (sublevelComponent u c a) := by
  apply isSimplyConnected_sublevelComponent_of_jordan_enclosure hu hmax ha
  intro x p hp
  exact henclose (range p) (_root_.isCompact_range p.continuous)
    (_root_.isConnected_range p.continuous) (by rintro _ ⟨t, rfl⟩; exact hp t)

namespace Path

/-- The pointwise affine homotopy between two paths with the same endpoints. -/
noncomputable def affineHomotopy {x y : ℂ} (p q : Path x y) : p.Homotopy q where
  toHomotopy := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  prop' := by
    intro t z hz
    rcases hz with (rfl | hz)
    · simp
    · have : z = 1 := by simpa using hz
      subst z
      simp

@[simp] lemma affineHomotopy_apply {x y : ℂ} (p q : Path x y) (t s : I) :
    affineHomotopy p q (t, s) = AffineMap.lineMap (p s) (q s) (t : ℝ) := by
  rfl

/-- If every pointwise joining segment lies in `D`, the affine path homotopy stays in `D`. -/
lemma affineHomotopy_mem {x y : ℂ} {p q : Path x y} {D : Set ℂ}
    (hsegment : ∀ s : I, segment ℝ (p s) (q s) ⊆ D) :
    ∀ z : I × I, affineHomotopy p q z ∈ D := by
  rintro ⟨t, s⟩
  rw [affineHomotopy_apply]
  apply hsegment s
  rw [segment_eq_image_lineMap]
  exact ⟨(t : ℝ), t.2, rfl⟩

/-- A pointwise affine homotopy stays in a convex set containing both paths. -/
lemma affineHomotopy_mem_of_convex {x y : ℂ} {p q : Path x y} {D : Set ℂ}
    (hD : Convex ℝ D) (hp : ∀ s, p s ∈ D) (hq : ∀ s, q s ∈ D) :
    ∀ z : I × I, affineHomotopy p q z ∈ D := by
  apply affineHomotopy_mem
  intro s
  exact hD.segment_subset (hp s) (hq s)

/-- Any loop carried by a convex set contracts to its base point through that set. -/
lemma exists_homotopy_refl_of_convex {x : ℂ} {p : Path x x} {D : Set ℂ}
    (hD : Convex ℝ D) (hp : ∀ s, p s ∈ D) :
    ∃ F : p.Homotopy (.refl x), ∀ z, F z ∈ D := by
  refine ⟨affineHomotopy p (.refl x), ?_⟩
  apply affineHomotopy_mem_of_convex hD hp
  intro s
  simpa using hp (0 : I)

/-- The image of a path is compact.  We name this elementary fact because it is the compact
set to which the thickening lemma is applied in polygonal approximation arguments. -/
lemma isCompact_range {x y : ℂ} (p : Path x y) : IsCompact (range p) :=
  _root_.isCompact_range p.continuous

/-- An open set containing a path contains a uniform metric thickening of the path image. -/
lemma exists_thickening_range_subset {x y : ℂ} {p : Path x y} {D : Set ℂ}
    (hD : IsOpen D) (hp : ∀ s, p s ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (range p) ⊆ D := by
  apply (isCompact_range p).exists_thickening_subset_open hD
  rintro z ⟨s, rfl⟩
  exact hp s

/-- A path that is pointwise uniformly close to `p` is joined to `p` by an endpoint-fixed
affine homotopy inside any prescribed thickening of the image of `p`. -/
lemma affineHomotopy_mem_of_dist_lt_thickening {x y : ℂ} {p q : Path x y} {D : Set ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hthick : Metric.thickening δ (range p) ⊆ D)
    (hdist : ∀ s, dist (q s) (p s) < δ) :
    ∀ z : I × I, affineHomotopy p q z ∈ D := by
  rintro ⟨t, s⟩
  apply hthick
  rw [Metric.mem_thickening_iff_exists_edist_lt]
  refine ⟨p s, mem_range_self s, ?_⟩
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ, affineHomotopy_apply,
    dist_lineMap_left]
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact t.2.2
  calc
    ‖(t : ℝ)‖ * dist (p s) (q s) ≤ dist (p s) (q s) :=
      mul_le_of_le_one_left dist_nonneg ht
    _ = dist (q s) (p s) := dist_comm _ _
    _ < δ := hdist s

/-- Uniformly close paths with the same endpoints are homotopic through any open set carrying
the first path.  This is the stability lemma needed to replace a loop by a polygonal loop. -/
lemma exists_affineHomotopy_mem_of_uniformly_close {x y : ℂ} {p : Path x y} {D : Set ℂ}
    (hD : IsOpen D) (hp : ∀ s, p s ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Path x y, (∀ s, dist (q s) (p s) < δ) →
      ∃ F : p.Homotopy q, ∀ z, F z ∈ D := by
  obtain ⟨δ, hδ, hthick⟩ := exists_thickening_range_subset hD hp
  refine ⟨δ, hδ, fun q hq => ⟨affineHomotopy p q, ?_⟩⟩
  exact affineHomotopy_mem_of_dist_lt_thickening hδ hthick hq

end Path

end Erdos515
