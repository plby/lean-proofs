import StackExchange.Puzzling139335.JordanAccessibility
import Wikipedia.JordanCurveTheorem.Brouwer
import Wikipedia.SchoenfliesTheorem.MatchedArc

/-!
# Fixed points in a Jordan region

A closed Jordan region is homeomorphic to the closed model square.  Transporting
the existing planar Brouwer theorem along this homeomorphism gives the fixed
point property without any boundary rectifiability assumption.
-/

open Set

namespace Puzzling139335.IsJordanRegion

variable {P : Set Plane}

/-- Every closed Jordan region is homeomorphic to the closed model square. -/
theorem nonempty_homeomorph_closedSquare (hP : IsJordanRegion P) :
    Nonempty (↥P ≃ₜ ↥(Schoenflies.Plane.closedSquare 0 1)) := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hsep := Schoenflies.jordan_curve_theorem hC
  obtain ⟨x, hx⟩ := hsep.isConnected_inside.nonempty
  obtain ⟨F, G, hFG, -⟩ := hC.exists_pointed_square_chart hx
  have hclosure : closure (Schoenflies.inside C) = C ∪ Schoenflies.inside C :=
    ((Schoenflies.IsRegionOf.inside C).closure_eq hsep).trans (union_comm _ _)
  rw [← hclosure] at hFG
  exact ⟨{
    toFun := fun x => ⟨F x, hFG.mapsTo x.property⟩
    invFun := fun y => ⟨G y, hFG.mapsTo_inv y.property⟩
    left_inv := fun x => Subtype.ext (hFG.invOn.1 x.property)
    right_inv := fun y => Subtype.ext (hFG.invOn.2 y.property)
    continuous_toFun := hFG.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hFG.continuousOn_inv.domRestrict.subtype_mk _ }⟩

/-- Brouwer's fixed point theorem for an arbitrary closed Jordan region. -/
theorem brouwer_fixedPoint (hP : IsJordanRegion P) (f : C(↥P, ↥P)) :
    ∃ x, f x = x := by
  obtain ⟨e⟩ := hP.nonempty_homeomorph_closedSquare
  apply JordanCurve.Brouwer.fixedPoint_transfer e ?_ f
  apply JordanCurve.Brouwer.brouwerFPT _
    (Schoenflies.Plane.convex_closedSquare 0 1) (Schoenflies.isCompact_closedSquare 0 1)
  exact ⟨0, by
    simp [Schoenflies.Plane.closedSquare, Schoenflies.Plane.supDist,
      Schoenflies.Plane.supNorm]⟩

/-- The ambient-map formulation of the fixed point theorem only requires
continuity on the Jordan region and preservation of that region. -/
theorem exists_fixedPoint_of_continuousOn (hP : IsJordanRegion P) {f : Plane → Plane}
    (hf : ContinuousOn f P) (hmap : MapsTo f P P) : ∃ x ∈ P, f x = x := by
  let g : C(↥P, ↥P) :=
    ⟨fun x => ⟨f x, hmap x.property⟩, hf.domRestrict.subtype_mk _⟩
  obtain ⟨x, hx⟩ := hP.brouwer_fixedPoint g
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- In particular, every continuous ambient map preserving a Jordan region
has a fixed point in it. -/
theorem exists_fixedPoint (hP : IsJordanRegion P) {f : Plane → Plane}
    (hf : Continuous f) (hmap : MapsTo f P P) : ∃ x ∈ P, f x = x :=
  hP.exists_fixedPoint_of_continuousOn hf.continuousOn hmap

end Puzzling139335.IsJordanRegion

namespace Schoenflies.IsArcBetween

variable {A : Set Plane} {p q : Plane}

/-- A named simple arc is homeomorphic to the segment joining its endpoints. -/
theorem nonempty_homeomorph_segment (hA : IsArcBetween A p q) :
    Nonempty (↥A ≃ₜ ↥(segment ℝ p q)) := by
  obtain ⟨e⟩ := exists_arcHomeo hA (isArcBetween_segment hA.ne)
  exact ⟨{
    toFun := fun x => ⟨e.toFun x, e.mapsTo x.property⟩
    invFun := fun y => ⟨e.invFun y, e.mapsTo_invFun y.property⟩
    left_inv := fun x => Subtype.ext (e.leftInvOn x.property)
    right_inv := fun y => Subtype.ext (e.rightInvOn y.property)
    continuous_toFun := e.continuousOn_toFun.domRestrict.subtype_mk _
    continuous_invFun := e.continuousOn_invFun.domRestrict.subtype_mk _ }⟩

/-- Every continuous self-map of a simple arc has a fixed point. -/
theorem exists_fixedPoint (hA : IsArcBetween A p q) (f : C(↥A, ↥A)) :
    ∃ x, f x = x := by
  obtain ⟨e⟩ := hA.nonempty_homeomorph_segment
  exact JordanCurve.Brouwer.fixedPoint_transfer e
    (JordanCurve.Brouwer.brouwerFPT _ (convex_segment p q) (isCompact_segment p q)
      ⟨p, left_mem_segment ℝ p q⟩) f

/-- Ambient formulation of the fixed point property for a named simple arc. -/
theorem exists_fixedPoint_of_continuousOn (hA : IsArcBetween A p q) {f : Plane → Plane}
    (hf : ContinuousOn f A) (hmap : MapsTo f A A) : ∃ x ∈ A, f x = x := by
  let g : C(↥A, ↥A) :=
    ⟨fun x => ⟨f x, hmap x.property⟩, hf.domRestrict.subtype_mk _⟩
  obtain ⟨x, hx⟩ := hA.exists_fixedPoint g
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

end Schoenflies.IsArcBetween

namespace Schoenflies.IsArc

/-- The fixed point property does not require naming the endpoints of the arc. -/
theorem exists_fixedPoint_of_continuousOn {A : Set Plane} (hA : IsArc A)
    {f : Plane → Plane} (hf : ContinuousOn f A) (hmap : MapsTo f A A) :
    ∃ x ∈ A, f x = x := by
  obtain ⟨p, q, hpq⟩ := hA.exists_isArcBetween
  exact hpq.exists_fixedPoint_of_continuousOn hf hmap

end Schoenflies.IsArc
