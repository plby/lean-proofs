import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleFibreGeometry
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleFibreLocal
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCech
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreGeometry
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultInclusion

/-!
# Actual fibre restrictions and negative smooth local period primitives

Restrict the original family cover and its genuine cocycle along the
original fibre inclusion and original coefficient sheaf pullback. The
negative marked real-linear primitive on each actual local lift is a
native smooth section. Its second-minus-first overlap difference is
exactly the smooth inclusion of the actual restricted cocycle value.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre

open HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original varying-family primitive restricted to its original
fibre lift is the actual marked primitive of the evaluated coefficients. -/
theorem primitive_fibreLift (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂)
    {t : (P.point b).Torus} (ht : t ∈ fibreCover P b i) :
    Cocycle.primitive P a (Cocycle.lift P i (P.fibreInclusion b t)) =
      MarkedLinear.primitive (P.point b) (fun j => a j b) (fibreLift P b i t) := by
  rw [lift_fibreInclusion_eq P b i ht, MarkedLinear.primitive_apply]
  rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual original cocycle restricted to the original fibre cover
by the original coefficient sheaf pullback. -/
def fibreCocycle (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b))
      (fibreCover P b) :=
  CechFibre.pullbackCocycle (PeriodFamilyHigherDirectImage.FibreGeometry.fibreMap P b)
    (PeriodFamilyHigherDirectImage.FibreGeometry.coefficientPullback P b) (Cocycle.cocycle P a)

/-- The actual restricted value is literally the original difference
evaluated at the original fibre inclusion. -/
@[simp] theorem fibreCocycle_value_apply (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i j : B × ComplexPlane₂)
    (t : ↥(fibreCover P b i ⊓ fibreCover P b j)) :
    Subtype.val ((fibreCocycle P b a).value i j :
      PeriodTorusHolomorphicCohomology.Dolbeault.HolomorphicSection (P.point b)
        (fibreCover P b i ⊓ fibreCover P b j)) t =
      Cocycle.primitive P a (Cocycle.lift P i (P.fibreInclusion b t)) -
        Cocycle.primitive P a (Cocycle.lift P j (P.fibreInclusion b t)) := rfl

/-- The actual negative local primitive on each open of the original
pulled-back cover, in the unchanged native real torus atlas. -/
def fibreNegativeSection (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂) :
    PeriodTorusHolomorphicCohomology.Dolbeault.SmoothSection (P.point b) (fibreCover P b i) :=
  negativeLocalSection (P.point b) (fun j => a j b) (fibreCover P b i)
    (fibreLift P b i) (fibreLift_holomorphic P b i)

@[simp] theorem fibreNegativeSection_apply (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i : B × ComplexPlane₂) (t : fibreCover P b i) :
    fibreNegativeSection P b a i t =
      -MarkedLinear.primitive (P.point b) (fun j => a j b) (fibreLift P b i t) := rfl

/-- The smooth overlap difference has exactly the sign required by
the actual extension's local lifts: `t_j - t_i = c_ij`. -/
theorem fibreNegativeSection_difference (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i j : B × ComplexPlane₂) :
    PeriodTorusHolomorphicCohomology.Dolbeault.restriction (P.point b) inf_le_right
        (fibreNegativeSection P b a j) -
      PeriodTorusHolomorphicCohomology.Dolbeault.restriction (P.point b) inf_le_left
        (fibreNegativeSection P b a i) =
      PeriodTorusHolomorphicCohomology.Dolbeault.inclusionSection (P.point b)
        (fibreCover P b i ⊓ fibreCover P b j) ((fibreCocycle P b a).value i j) := by
  apply ContMDiffMap.ext
  intro t
  change -MarkedLinear.primitive (P.point b) (fun k => a k b) (fibreLift P b j t) -
      -MarkedLinear.primitive (P.point b) (fun k => a k b) (fibreLift P b i t) =
    Cocycle.primitive P a (Cocycle.lift P i (P.fibreInclusion b t)) -
      Cocycle.primitive P a (Cocycle.lift P j (P.fibreInclusion b t))
  rw [primitive_fibreLift P b a i t.property.1,
    primitive_fibreLift P b a j t.property.2]
  abel

/-- The same genuine difference equation, expressed directly in the
original smooth sheaf's actual restrictions and inclusion morphism. -/
theorem fibreNegativeSection_difference_sheaf (P : HolomorphicPeriodMap V B) (b : B)
    (a : Cocycle.Coefficients V B) (i j : B × ComplexPlane₂) :
    res (PeriodTorusHolomorphicCohomology.Dolbeault.smoothSheaf (P.point b)) inf_le_right
        (fibreNegativeSection P b a j) -
      res (PeriodTorusHolomorphicCohomology.Dolbeault.smoothSheaf (P.point b)) inf_le_left
        (fibreNegativeSection P b a i) =
      (PeriodTorusHolomorphicCohomology.Dolbeault.inclusion (P.point b)).hom.app
        (Opposite.op (fibreCover P b i ⊓ fibreCover P b j)) ((fibreCocycle P b a).value i j) :=
  fibreNegativeSection_difference P b a i j

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre
