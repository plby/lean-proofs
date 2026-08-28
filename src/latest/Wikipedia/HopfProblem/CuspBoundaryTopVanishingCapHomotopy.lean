import Wikipedia.HopfProblem.CuspBoundaryTopVanishingBoundary
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspRetraction

/-!
# Transporting a controlled whole-boundary endpoint into the full cap

A homotopy on a containing closed tube gives an actual homotopy of the
entire gamma-zero boundary map in the original full cusp quotient.  Its
endpoint is the literal central inclusion after the retraction.  No
strong deformation of the whole fixed-radius cap is assumed here.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open SpecialPeriods.CuspFamily CuspUniformization CuspRetraction CuspPositiveRetraction
open ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyCuspFibre
open ThreefoldHomologyFinitenessCusp SingularMayerVietoris PeriodTorusHigherHomology

variable (D : Data) (η : ℝ) (hη₀ : 0 ≤ η)
    (R : C(ClosedQuotient D.correction D.radius η,
      QuotientCentralFibre D.correction D.radius))
    (H : (ContinuousMap.id (ClosedQuotient D.correction D.radius η)).Homotopy
      ((quotientCentralIntoClosed D.correction D.radius η hη₀).comp R))
    (h : Height D.radius) (hη : ‖heightParameter D h‖ ≤ η)

/-- The given closed-tube homotopy, evaluated on the actual whole
gamma-zero boundary, with values in the unchanged full cusp quotient. -/
def gammaBoundaryCentralHomotopy :
    (gammaBoundaryToFull D h).Homotopy
      ((fullCentralInclusion D).comp (R.comp (gammaBoundaryToClosed D h η hη))) where
  toFun p := (H (p.1, gammaBoundaryToClosed D h η hη p.2)).val
  continuous_toFun := continuous_subtype_val.comp
    (H.continuous.comp (continuous_fst.prodMk
      ((gammaBoundaryToClosed D h η hη).continuous.comp continuous_snd)))
  map_zero_left q := congrArg Subtype.val
    (H.map_zero_left (gammaBoundaryToClosed D h η hη q))
  map_one_left q := congrArg Subtype.val
    (H.map_one_left (gammaBoundaryToClosed D h η hη q))

/-- The homotopy is literally the supplied deformation at the original
closed-tube boundary point, followed by the original subtype inclusion. -/
@[simp] theorem gammaBoundaryCentralHomotopy_apply
    (s : unitInterval) (q : CuspBoundaryGammaZero.Boundary) :
    gammaBoundaryCentralHomotopy D η hη₀ R H h hη (s, q) =
      (H (s, gammaBoundaryToClosed D h η hη q)).val := rfl

include H in
/-- The genuine whole-boundary homology map factors through the actual
central endpoint in every integral degree. -/
theorem gammaBoundaryToFull_homology_eq_central (n : ℕ) :
    singularHomologyMap (gammaBoundaryToFull D h) n =
      (singularHomologyMap (fullCentralInclusion D) n).comp
        (singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) n) := by
  rw [homotopy_homologyMap (gammaBoundaryCentralHomotopy D η hη₀ R H h hη) n,
    singularHomologyMap_comp]

include H in
/-- Vanishing of the actual central endpoint map implies vanishing in
the original full cap, without any separate full-cap deformation premise. -/
theorem gammaBoundaryToFull_homology_eq_zero_of_retraction (n : ℕ)
    (hzero : singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) n = 0) :
    singularHomologyMap (gammaBoundaryToFull D h) n = 0 := by
  rw [gammaBoundaryToFull_homology_eq_central D η hη₀ R H h hη n,
    hzero, LinearMap.comp_zero]

include H in
/-- The degree-four consequence used for the original gamma-zero
mapping torus and its actual inclusion into the full cusp cap. -/
theorem gammaBoundaryToFull_homologyFour_eq_zero_of_retraction
    (hzero : singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) 4 = 0) :
    singularHomologyMap (gammaBoundaryToFull D h) 4 = 0 :=
  gammaBoundaryToFull_homology_eq_zero_of_retraction D η hη₀ R H h hη 4 hzero

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
