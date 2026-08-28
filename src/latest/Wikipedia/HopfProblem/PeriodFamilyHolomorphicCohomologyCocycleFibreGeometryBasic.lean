import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCoverBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreGeometryBasic

/-!
# Restriction of the actual local-lift cover to an original torus fibre

The cover is the literal inverse image under the original fibre
inclusion. Its lifts are the second coordinates of the actual family
covering lifts. The full lifts retain the original base point, and
their fibre components project to the original native torus points.
No separation or manifold hypothesis is needed for these identities.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The actual inverse image of the original family covering open in
the original complex period torus. -/
def fibreCover (P : HolomorphicPeriodMap V B) (b : B) (i : B × ComplexPlane₂) :
    Opens (P.point b).Torus :=
  (Opens.map (PeriodFamilyHigherDirectImage.FibreGeometry.fibreMap P b)).obj
    (Cocycle.coverOpen P i)

@[simp] theorem mem_fibreCover (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) (t : (P.point b).Torus) :
    t ∈ fibreCover P b i ↔ P.fibreInclusion b t ∈ Cocycle.coverOpen P i := Iff.rfl

/-- Pulling back the proved original cover covers every native fibre. -/
theorem fibreCover_covers (P : HolomorphicPeriodMap V B) (b : B)
    (t : (P.point b).Torus) : ∃ i : B × ComplexPlane₂, t ∈ fibreCover P b i :=
  Cocycle.coverOpen_covers P (P.fibreInclusion b t)

/-- The literal second coordinate of the original local covering lift
at the original fibre inclusion. -/
def fibreLift (P : HolomorphicPeriodMap V B) (b : B) (i : B × ComplexPlane₂)
    (t : (P.point b).Torus) : ComplexPlane₂ :=
  (Cocycle.lift P i (P.fibreInclusion b t)).2

/-- The same actual lift, on the subtype of its genuine fibre-cover open. -/
def fibreLiftOn (P : HolomorphicPeriodMap V B) (b : B) (i : B × ComplexPlane₂) :
    fibreCover P b i → ComplexPlane₂ := fun t => fibreLift P b i t

@[simp] theorem fibreLiftOn_apply (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) (t : fibreCover P b i) :
    fibreLiftOn P b i t = fibreLift P b i t := rfl

/-- The full actual local lift retains the original base point. -/
theorem lift_fibreInclusion_base (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) {t : (P.point b).Torus} (ht : t ∈ fibreCover P b i) :
    (Cocycle.lift P i (P.fibreInclusion b t)).1 = b :=
  Cocycle.lift_base P i ht

/-- The full actual local lift is exactly the base point paired with
the defined fibre component. -/
theorem lift_fibreInclusion_eq (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) {t : (P.point b).Torus} (ht : t ∈ fibreCover P b i) :
    Cocycle.lift P i (P.fibreInclusion b t) = (b, fibreLift P b i t) := by
  apply Prod.ext
  · exact lift_fibreInclusion_base P b i ht
  · rfl

/-- The actual native lattice quotient of the fibre lift is the
original torus point, not a point in a replacement torus model. -/
theorem fibreLift_project (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) {t : (P.point b).Torus} (ht : t ∈ fibreCover P b i) :
    (P.point b).lattice.mkQ (fibreLift P b i t) = t := by
  apply P.fibreInclusion_injective b
  rw [P.fibreInclusion_mkQ, ← lift_fibreInclusion_eq P b i ht]
  exact Cocycle.project_lift P i ht

/-- Projection of the same lift on its original open subtype. -/
@[simp] theorem fibreLiftOn_project (P : HolomorphicPeriodMap V B) (b : B)
    (i : B × ComplexPlane₂) (t : fibreCover P b i) :
    (P.point b).lattice.mkQ (fibreLiftOn P b i t) = t :=
  fibreLift_project P b i t.property

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre
