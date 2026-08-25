import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.BoundaryCongruence
import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths

/-!
# Boundary orientation for a pair of Jordan regions separated by a crosscut

The compatible boundary coordinates come from the three actual simple paths.
The direct congruence between the two closed sides and any direct symmetry of
the whole region admit increasing real lifts in these coordinates.  All
orientation claims are consequences of winding; none is a geometric premise.
-/

open Set Schoenflies unitInterval

namespace Puzzling139335.CentralRotation.CrosscutPaths.Data

noncomputable section

open BoundaryOrientation

/-- Actual direct congruences provide the increasing boundary lifts required
by the central-rotation argument.  The only geometric premises are the Jordan
crosscut, the congruence between its two closed sides, and preservation of the
outer curve by a direct isometry. -/
theorem exists_boundaryLifts_of_direct
    {C Γ M N : Set Plane} {p q : Plane} (d : Data C Γ M N p q)
    (hcut : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N)
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {ag ah : Circle} {bg bh : ℂ}
    (hg : ∀ z, PlaneIsometries.complexEquiv (g z) =
      (ag : ℂ) * PlaneIsometries.complexEquiv z + bg)
    (hh : ∀ z, PlaneIsometries.complexEquiv (h z) =
      (ah : ℂ) * PlaneIsometries.complexEquiv z + bh)
    (hmapg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hmaph : h '' C = C) :
    Nonempty (BoundaryLifts d.boundaryCoordinates g h) := by
  let A := closure (inside (M ∪ Γ))
  let B := closure (inside (N ∪ Γ))
  let U := closure (inside C)
  have hA : IsJordanRegion A := hcut.side_isJordanRegion hc
  have hB : IsJordanRegion B := hcut.side_isJordanRegion hc.symm
  have hU : IsJordanRegion U := ⟨C, hcut.curve, rfl⟩
  have hsepA := jordan_curve_theorem (hcut.isJordanCurve_union hc)
  have hsepB := jordan_curve_theorem (hcut.isJordanCurve_union hc.symm)
  have hsepU := jordan_curve_theorem hcut.curve
  have hfrontA : frontier A = M ∪ Γ := frontier_closure_inside hsepA
  have hfrontB : frontier B = N ∪ Γ := frontier_closure_inside hsepB
  have hfrontU : frontier U = C := frontier_closure_inside hsepU
  have hunion : A ∪ B = U := (hcut.closure_inside_eq_union hc).symm
  have hdis : Disjoint (interior A) (interior B) := by
    rw [show interior A = inside (M ∪ Γ) from interior_closure_inside hsepA,
      show interior B = inside (N ∪ Γ) from interior_closure_inside hsepB]
    exact hcut.disjoint_sides hc
  let fA : C(AddCircle (1 : ℝ), Plane) := ⟨d.fA, d.fA_continuous⟩
  let fB : C(AddCircle (1 : ℝ), Plane) := ⟨d.fB, d.fB_continuous⟩
  let fU : C(AddCircle (1 : ℝ), Plane) := ⟨d.fU, d.fU_continuous⟩
  have hrangeA : range fA = frontier A := d.range_fA.trans hfrontA.symm
  have hrangeB : range fB = frontier B :=
    d.range_fB.trans ((union_comm Γ N).trans hfrontB.symm)
  have hrangeU : range fU = frontier U := d.range_fU.trans hfrontU.symm
  have htraceA : fA.comp CircleDegree.onceAround = (d.loopA : C(I, Plane)) := by
    apply ContinuousMap.ext
    intro t
    exact d.fA_coe t
  have htraceB : fB.comp CircleDegree.onceAround = (d.loopB : C(I, Plane)) := by
    apply ContinuousMap.ext
    intro t
    exact d.fB_coe t
  have hLA : range d.loopA = frontier A := d.range_loopA.trans hfrontA.symm
  have hLB : range d.loopB = frontier B :=
    d.range_loopB.trans ((union_comm Γ N).trans hfrontB.symm)
  have hLU : range d.loopU = frontier U := d.range_loopU.trans hfrontU.symm
  obtain ⟨x, hx⟩ := hA.interior_nonempty
  have hgx : g x ∈ interior B := by
    have himage : g '' interior A = interior B := by
      calc
        g '' interior A = interior (g '' A) := g.toHomeomorph.image_interior A
        _ = interior B := congrArg interior hmapg
    exact himage ▸ mem_image_of_mem g hx
  have hxA := circleBoundary_avoids fA hrangeA.le hx
  have hxB := circleBoundary_avoids fB hrangeB.le hgx
  have hAx := boundaryPath_avoids d.loopA hLA.le hx
  have hBy := boundaryPath_avoids d.loopB hLB.le hgx
  have hwind := winding_boundary_pieces_eq d.m d.gamma d.n hA hB hU hunion hdis
    hLA hLB hLU hx hgx hAx hBy
  have hsetg : g '' range fA = range fB := by
    rw [hrangeA, hrangeB]
    exact (g.toHomeomorph.image_frontier A).trans (congrArg frontier hmapg)
  obtain ⟨G, hGmono, hGperiod, hG⟩ :=
    exists_increasing_boundary_lift_of_winding_eq fA fB d.fA_injective d.fB_injective
      g hg hsetg x hxA hxB
      ((winding_congr htraceA x _ hAx).trans
        (hwind.trans (winding_congr htraceB (g x) _ hBy).symm))
      (winding_circle_boundary_ne_zero hB fB d.fB_injective hrangeB hgx _)
  have hUmap : h '' U = U := by
    change h '' closure (inside C) = closure (inside C)
    calc
      h '' closure (inside C) = closure (h '' inside C) :=
        h.toHomeomorph.image_closure (inside C)
      _ = closure (inside (h '' C)) :=
        congrArg closure (homeomorph_image_inside h.toHomeomorph C)
      _ = closure (inside C) := by rw [hmaph]
  obtain ⟨H, hHmono, hHperiod, hH⟩ :=
    exists_increasing_boundary_lift_of_preserves_jordan hU fU d.fU_injective hrangeU
      h hh hUmap
  exact ⟨{
    G := G
    H := H
    G_increasing := hGmono
    H_increasing := hHmono
    G_period := hGperiod
    H_period := hHperiod
    left_to_right := hG
    outer_to_outer := hH }⟩

end

end Puzzling139335.CentralRotation.CrosscutPaths.Data
