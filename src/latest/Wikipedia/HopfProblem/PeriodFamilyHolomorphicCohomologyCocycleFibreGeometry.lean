import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleFibreGeometryBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCover

/-!
# Holomorphic fibre lifts in the original period-family atlases

The fibre lift is the original holomorphic fibre inclusion followed by
the original quotient-cover local inverse and the upstairs second
projection. Holomorphy is proved in the unchanged native torus atlas,
the unchanged family quotient atlas, and the original product atlas
upstairs. Only the original base manifold hypothesis is used.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- At every point of the actual fibre-cover open, its literal lift
is holomorphic in the original native torus charts. -/
theorem fibreLift_holomorphicAt (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) {t : (P.point b).Torus} (ht : t ∈ fibreCover P b i) :
    ContMDiffAt I₂ I₂ ω (fibreLift P b i) t := by
  let := Cocycle.coverChartedSpace (V := V) (B := B)
  let := P.totalChartedSpace
  have hL : ContMDiffAt IT IT ω (Cocycle.lift P i) (P.fibreInclusion b t) :=
    (Cocycle.lift_holomorphic P i).contMDiffAt
      ((Cocycle.coverOpen P i).isOpen.mem_nhds ht)
  have hsnd : ContMDiff IT I₂ ω (Prod.snd : B × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  exact hsnd.contMDiffAt.comp t
    (hL.comp t (P.fibreInclusion_holomorphic b).contMDiffAt)

/-- The original fibre lift is holomorphic on the literal inverse-image
open set, without any additional separation hypothesis. -/
theorem fibreLift_holomorphic (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) :
    ContMDiffOn I₂ I₂ ω (fibreLift P b i) (fibreCover P b i) :=
  fun _ ht => (fibreLift_holomorphicAt P b i ht).contMDiffWithinAt

/-- The same actual lift is holomorphic as a map on its original open subtype. -/
theorem fibreLiftOn_holomorphic (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) : ContMDiff I₂ I₂ ω (fibreLiftOn P b i) := by
  intro t
  exact (fibreLift_holomorphicAt P b i t.property).comp t (contMDiff_subtype_val t)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre
