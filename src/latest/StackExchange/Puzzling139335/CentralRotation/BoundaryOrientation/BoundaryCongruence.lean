import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CoherentWinding
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleReparam
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.BoundaryTransport
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero

/-!
# Increasing lifts of direct congruences between Jordan boundaries

Equal nonzero winding forces the actual induced boundary homeomorphism to
have an increasing real lift.  The equality and nonvanishing used here are
separately proved from Jordan topology and from cancellation of an actual cut.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

/-- Angular directions of all points of an embedded circle about a point
outside its image. -/
def circleDirection (f : C(AddCircle (1 : ℝ), Plane)) (x : Plane)
    (hx : ∀ t, f t ≠ x) : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  (directionFrom x).comp ⟨fun t => ⟨f t, hx t⟩, f.continuous.subtype_mk _⟩

theorem circleDirection_apply (f : C(AddCircle (1 : ℝ), Plane)) (x : Plane)
    (hx : ∀ t, f t ≠ x) (t : AddCircle (1 : ℝ)) :
    circleDirection f x hx t = directionAt x (f t) :=
  (directionAt_of_ne (hx t)).symm

theorem circleTrace_circleDirection (f : C(AddCircle (1 : ℝ), Plane)) (x : Plane)
    (hx : ∀ t, f t ≠ x) :
    circleTrace (circleDirection f x hx) =
      directionPath (f.comp CircleDegree.onceAround) x
        (fun t => hx ((t : ℝ) : AddCircle (1 : ℝ))) := by
  ext t
  rfl

theorem inside_frontier_eq {P : Set Plane} (hP : IsJordanRegion P) :
    Schoenflies.inside (frontier P) = interior P := by
  obtain ⟨C, hC, rfl⟩ := hP
  rw [frontier_closure_inside (Schoenflies.jordan_curve_theorem hC),
    interior_closure_inside (Schoenflies.jordan_curve_theorem hC)]

theorem circleBoundary_avoids {P : Set Plane}
    (f : C(AddCircle (1 : ℝ), Plane)) (hfront : range f ⊆ frontier P)
    {x : Plane} (hx : x ∈ interior P) : ∀ t, f t ≠ x := by
  intro t ht
  have hmem := hfront (mem_range_self t)
  rw [ht] at hmem
  exact hmem.2 hx

/-- Nonvanishing of winding for an actual embedded Jordan boundary. -/
theorem winding_circle_boundary_ne_zero {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(AddCircle (1 : ℝ), Plane)) (hfi : Function.Injective f)
    (hfront : range f = frontier P) {x : Plane} (hx : x ∈ interior P)
    (havoid : ∀ t, (f.comp CircleDegree.onceAround) t ≠ x) :
    winding (f.comp CircleDegree.onceAround) x havoid ≠ 0 := by
  have hinside : x ∈ Schoenflies.inside (range f) := by
    rw [hfront, inside_frontier_eq hP]
    exact hx
  have hnot := JordanNonzero.directionLoop_not_homotopic_const f.continuous hfi hinside
  intro hz
  apply hnot
  apply (CircleDegree.displacement_eq_zero_iff_homotopicRel_const _).mp
  exact hz

/-- An induced boundary map has an increasing real lift when the two actual
boundary winding values agree and are nonzero. -/
theorem exists_increasing_boundary_lift_of_winding_eq
    (fA fB : C(AddCircle (1 : ℝ), Plane))
    (hiA : Function.Injective fA) (hiB : Function.Injective fB)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    (hset : g '' range fA = range fB) (x : Plane)
    (hxA : ∀ t, fA t ≠ x) (hxB : ∀ t, fB t ≠ g x)
    (heq : winding (fA.comp CircleDegree.onceAround) x
        (fun t => hxA ((t : ℝ) : AddCircle (1 : ℝ))) =
      winding (fB.comp CircleDegree.onceAround) (g x)
        (fun t => hxB ((t : ℝ) : AddCircle (1 : ℝ))))
    (hne : winding (fB.comp CircleDegree.onceAround) (g x)
        (fun t => hxB ((t : ℝ) : AddCircle (1 : ℝ))) ≠ 0) :
    ∃ G : ℝ ≃ₜ ℝ, StrictMono G ∧ (∀ t, G (t + 1) = G t + 1) ∧
      ∀ t : ℝ, fB (G t : AddCircle (1 : ℝ)) = g (fA (t : AddCircle (1 : ℝ))) := by
  obtain ⟨e, he⟩ := exists_boundary_transport fA fB fA.continuous hiA
    fB.continuous hiB g.toHomeomorph hset
  let F := circleDirection fB (g x) hxB
  have htrace : circleTrace (F.comp (e : C(_, _))) =
      ContinuousMap.const I (circleAngle a) +
        directionPath (fA.comp CircleDegree.onceAround) x
          (fun t => hxA ((t : ℝ) : AddCircle (1 : ℝ))) := by
    ext t
    change circleDirection fB (g x) hxB (e ((t : ℝ) : AddCircle (1 : ℝ))) = _
    rw [circleDirection_apply, he]
    change directionAt (g x) (g (fA ((t : ℝ) : AddCircle (1 : ℝ)))) =
      circleAngle a + directionPath (fA.comp CircleDegree.onceAround) x _ t
    exact (directionAt_direct g hg (hxA ((t : ℝ) : AddCircle (1 : ℝ)))).trans
      (congrArg (circleAngle a + ·)
        (directionAt_of_ne (hxA ((t : ℝ) : AddCircle (1 : ℝ)))))
  have hF : CircleDegree.displacement (circleTrace F) =
      winding (fB.comp CircleDegree.onceAround) (g x)
        (fun t => hxB ((t : ℝ) : AddCircle (1 : ℝ))) := by
    rw [show F = circleDirection fB (g x) hxB from rfl, circleTrace_circleDirection]
    rfl
  have hFcomp : CircleDegree.displacement (circleTrace (F.comp (e : C(_, _)))) =
      CircleDegree.displacement (circleTrace F) := by
    rw [htrace, CircleDegree.displacement_const_add, hF]
    exact heq
  obtain ⟨G, hG, hpos | hneg⟩ := exists_monotone_homeomorph_lift e
  · refine ⟨G, hpos.1, hpos.2, ?_⟩
    intro t
    exact (congrArg fB (hG t)).trans (he _)
  · have hrev := displacement_trace_comp_of_negative_lift F e G.continuous hG hneg.2
    have hzero : CircleDegree.displacement (circleTrace F) = 0 := by linarith
    exact False.elim (hne (hF.symm.trans hzero))

/-- Every direct affine symmetry of a Jordan region preserves the order of
its boundary parameters.  The result returns the actual real homeomorphism. -/
theorem exists_increasing_boundary_lift_of_preserves_jordan
    {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(AddCircle (1 : ℝ), Plane)) (hfi : Function.Injective f)
    (hfront : range f = frontier P)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) {a : Circle} {b : ℂ}
    (hg : ∀ p, PlaneIsometries.complexEquiv (g p) =
      (a : ℂ) * PlaneIsometries.complexEquiv p + b)
    (hmap : g '' P = P) :
    ∃ G : ℝ ≃ₜ ℝ, StrictMono G ∧ (∀ t, G (t + 1) = G t + 1) ∧
      ∀ t : ℝ, f (G t : AddCircle (1 : ℝ)) = g (f (t : AddCircle (1 : ℝ))) := by
  obtain ⟨x, hx⟩ := hP.interior_nonempty
  have himage : g '' interior P = interior P := by
    calc
      g '' interior P = interior (g '' P) := g.toHomeomorph.image_interior P
      _ = interior P := congrArg interior hmap
  have hgx : g x ∈ interior P := himage ▸ mem_image_of_mem g hx
  have hxA := circleBoundary_avoids f hfront.le hx
  have hxB := circleBoundary_avoids f hfront.le hgx
  have hset : g '' range f = range f := by
    calc
      g '' range f = g '' frontier P := congrArg (g '' ·) hfront
      _ = frontier (g '' P) := g.toHomeomorph.image_frontier P
      _ = frontier P := congrArg frontier hmap
      _ = range f := hfront.symm
  have htrace : range (f.comp CircleDegree.onceAround) ⊆ frontier P := by
    rintro _ ⟨t, rfl⟩
    exact hfront ▸ mem_range_self ((t : ℝ) : AddCircle (1 : ℝ))
  have hclosed : (f.comp CircleDegree.onceAround) 0 =
      (f.comp CircleDegree.onceAround) 1 := by
    change f ((0 : ℝ) : AddCircle (1 : ℝ)) = f ((1 : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_zero, AddCircle.coe_period]
  apply exists_increasing_boundary_lift_of_winding_eq f f hfi hfi g hg hset x hxA hxB
  · exact winding_eq_inside_jordan hP _ htrace hclosed hx hgx _ _
  · exact winding_circle_boundary_ne_zero hP f hfi hfront hgx _

end

end Puzzling139335.CentralRotation.BoundaryOrientation
