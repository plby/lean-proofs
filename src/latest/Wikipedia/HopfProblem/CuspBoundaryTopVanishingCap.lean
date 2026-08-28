import Wikipedia.HopfProblem.CuspBoundaryTopVanishingSupport
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingCollapse
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingCapHomotopy

/-!
# The gamma-zero sub-boundary has zero top image in the original cusp cap

Choose a sufficiently small norm circle inside the original fixed-radius
cap.  The one controlled deformation on its containing closed tube has
the independently prescribed collapse at every angular position.  The
actual logarithmic period calculation puts the entire collapsed
gamma-zero boundary over the zero first base coordinate.  Its fourth
homology image therefore vanishes by the genuine central radial
Mayer--Vietoris argument.

The closed-tube deformation takes place in the original cap, and the
actual whole-boundary height homotopy returns to any original allowed
height.  No strong deformation of the entire original open cap, and no
claim about a class chosen only by its Wang coordinate, is used.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open SpecialPeriods.CuspFamily CuspRetraction ThreefoldOverlapMappingTorus.Cusp
open ThreefoldHomologyCuspFibre CuspCentralHomology SingularMayerVietoris
open CuspBoundaryTopVanishingCircle

/-- The literal gamma-zero sub-mapping-torus map into the original
full cusp cap induces the zero map on fourth integral singular homology,
at every allowed height.  All required small radii and the actual
controlled deformation are derived from the original holomorphic data. -/
theorem gammaBoundaryToFull_homologyFour_eq_zero (D : Data) (h : Height D.radius) :
    singularHomologyMap (gammaBoundaryToFull D h) 4 = 0 := by
  obtain ⟨δ, hδ, _hδr, _hδ1, hbase⟩ := exists_period_base_radius D
  obtain ⟨η₀, hη₀, hη₀r, _hη₀1, hret⟩ :=
    exists_controlled_circle_retraction D.correction D.radius_pos D.holomorphic
  let η := min η₀ δ
  have hη : 0 < η := lt_min hη₀ hδ
  have hηr : η < D.radius := (min_le_left η₀ δ).trans_lt hη₀r
  obtain ⟨h', hh'⟩ := exists_smallHeight D hη
  have hρ : 0 < ‖heightParameter D h'‖ := norm_pos_iff.mpr (heightParameter_ne_zero D h')
  obtain ⟨R, _hR, H, _hmono, hEnd, _hall⟩ :=
    hret η hη (min_le_left η₀ δ) ‖heightParameter D h'‖ hρ hh'.le
  have hzero : singularHomologyMap (R.comp (gammaBoundaryToClosed D h' η hh'.le)) 4 = 0 := by
    apply central_homologyFourMap_eq_zero_of_baseFirstZero
      D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
    intro q
    exact retraction_gammaBoundary_base_zero D δ hbase h' η hh'.le hηr
      (hh'.trans_le (min_le_right η₀ δ)) R hEnd q
  rw [gammaBoundaryToFull_homology_eq D h h' 4]
  exact gammaBoundaryToFull_homologyFour_eq_zero_of_retraction
    D η hη.le R H.toHomotopy h' hh'.le hzero

/-- Pointwise vanishing on every actual source top class. -/
theorem gammaBoundaryToFull_homologyFour_apply (D : Data) (h : Height D.radius)
    (a : SingularHomology CuspBoundaryGammaZero.Boundary 4) :
    singularHomologyMap (gammaBoundaryToFull D h) 4 a = 0 := by
  rw [gammaBoundaryToFull_homologyFour_eq_zero, LinearMap.zero_apply]

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
