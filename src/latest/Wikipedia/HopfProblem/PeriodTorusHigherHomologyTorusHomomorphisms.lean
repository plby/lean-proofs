import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Additive compatibility of the actual period-coordinate maps

The circle-coordinate homeomorphisms and period-change maps preserve
the actual additive group laws. Their degree-one homology formulas
retain the positive period-loop convention. These facts let the
higher product construction use the actual continuous group maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic FirstHurewicz

@[simp] theorem flatTorusCircleHomeomorph_add (x y : RealTorus₄) :
    flatTorusCircleHomeomorph (x + y) =
      flatTorusCircleHomeomorph x + flatTorusCircleHomeomorph y :=
  flatTorusCircleMap.map_add x y

/-- The real coordinate homeomorphism also preserves the integral module structure. -/
def flatTorusCircleLinearEquiv : RealTorus₄ ≃ₗ[ℤ] ProductTorus 4 :=
  LinearEquiv.ofBijective flatTorusCircleMap
    ⟨flatTorusCircleMap_injective, flatTorusCircleMap_surjective⟩

@[simp] theorem flatTorusCircleLinearEquiv_apply (x : RealTorus₄) :
    flatTorusCircleLinearEquiv x = flatTorusCircleHomeomorph x := rfl

/-- Complex period coordinates preserve the actual addition of quotient points. -/
@[simp] theorem periodTorusCircleHomeomorph_add (p : PeriodDomain) (x y : p.Torus) :
    periodTorusCircleHomeomorph p (x + y) =
      periodTorusCircleHomeomorph p x + periodTorusCircleHomeomorph p y := by
  obtain ⟨a, rfl⟩ := flatProjection_surjective p x
  obtain ⟨b, rfl⟩ := flatProjection_surjective p y
  rw [← flatProjection_add, periodTorusCircleHomeomorph_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, periodTorusCircleHomeomorph_flatProjection]
  exact (coordinateProjection 4).map_add a b

/-- The actual period-to-circle homeomorphism, as an additive group equivalence. -/
def periodTorusCircleAddEquiv (p : PeriodDomain) : p.Torus ≃+ ProductTorus 4 where
  toEquiv := (periodTorusCircleHomeomorph p).toEquiv
  map_add' := periodTorusCircleHomeomorph_add p

@[simp] theorem periodTorusCircleAddEquiv_apply (p : PeriodDomain) (x : p.Torus) :
    periodTorusCircleAddEquiv p x = periodTorusCircleHomeomorph p x := rfl

/-- The same actual map preserves integral scalar multiplication. -/
def periodTorusCircleLinearEquiv (p : PeriodDomain) : p.Torus ≃ₗ[ℤ] ProductTorus 4 :=
  (periodTorusCircleAddEquiv p).toIntLinearEquiv

@[simp] theorem periodTorusCircleLinearEquiv_apply (p : PeriodDomain) (x : p.Torus) :
    periodTorusCircleLinearEquiv p x = periodTorusCircleHomeomorph p x := rfl

theorem step₁ContinuousMap_add (p : PeriodDomain) (x y : p.Torus) :
    p.step₁ContinuousMap (x + y) = p.step₁ContinuousMap x + p.step₁ContinuousMap y := by
  apply (periodTorusCircleHomeomorph p.step₁).injective
  rw [periodTorusCircleHomeomorph_add, periodTorusCircleHomeomorph_step₁,
    periodTorusCircleHomeomorph_step₁, periodTorusCircleHomeomorph_step₁,
    periodTorusCircleHomeomorph_add]
  exact (torusMatrixLinearMap A₁).map_add _ _

theorem step₂ContinuousMap_add (p : PeriodDomain) (x y : p.Torus) :
    p.step₂ContinuousMap (x + y) = p.step₂ContinuousMap x + p.step₂ContinuousMap y := by
  apply (periodTorusCircleHomeomorph p.step₂).injective
  rw [periodTorusCircleHomeomorph_add, periodTorusCircleHomeomorph_step₂,
    periodTorusCircleHomeomorph_step₂, periodTorusCircleHomeomorph_step₂,
    periodTorusCircleHomeomorph_add]
  exact (torusMatrixLinearMap A₂).map_add _ _

theorem step₀ContinuousMap_add (p : PeriodDomain) (x y : p.Torus) :
    p.step₀ContinuousMap (x + y) = p.step₀ContinuousMap x + p.step₀ContinuousMap y := by
  apply (periodTorusCircleHomeomorph p.step₀).injective
  rw [periodTorusCircleHomeomorph_add, periodTorusCircleHomeomorph_step₀,
    periodTorusCircleHomeomorph_step₀, periodTorusCircleHomeomorph_step₀,
    periodTorusCircleHomeomorph_add]
  exact (torusMatrixLinearMap M₀).map_add _ _

/-- The actual first biholomorphism as an integral linear map of quotient groups. -/
def step₁TorusLinearMap (p : PeriodDomain) : p.Torus →ₗ[ℤ] p.step₁.Torus :=
  ({ toFun := p.step₁ContinuousMap
     map_zero' := p.step₁ContinuousMap_zero
     map_add' := step₁ContinuousMap_add p } : p.Torus →+ p.step₁.Torus).toIntLinearMap

/-- The actual second biholomorphism as an integral linear map of quotient groups. -/
def step₂TorusLinearMap (p : PeriodDomain) : p.Torus →ₗ[ℤ] p.step₂.Torus :=
  ({ toFun := p.step₂ContinuousMap
     map_zero' := p.step₂ContinuousMap_zero
     map_add' := step₂ContinuousMap_add p } : p.Torus →+ p.step₂.Torus).toIntLinearMap

/-- The actual cusp biholomorphism as an integral linear map of quotient groups. -/
def step₀TorusLinearMap (p : PeriodDomain) : p.Torus →ₗ[ℤ] p.step₀.Torus :=
  ({ toFun := p.step₀ContinuousMap
     map_zero' := p.step₀ContinuousMap_zero
     map_add' := step₀ContinuousMap_add p } : p.Torus →+ p.step₀.Torus).toIntLinearMap

@[simp] theorem step₁TorusLinearMap_apply (p : PeriodDomain) (x : p.Torus) :
    step₁TorusLinearMap p x = p.step₁ContinuousMap x := rfl

@[simp] theorem step₂TorusLinearMap_apply (p : PeriodDomain) (x : p.Torus) :
    step₂TorusLinearMap p x = p.step₂ContinuousMap x := rfl

@[simp] theorem step₀TorusLinearMap_apply (p : PeriodDomain) (x : p.Torus) :
    step₀TorusLinearMap p x = p.step₀ContinuousMap x := rfl

/-- The actual homology map preserves the positive, ordered coordinate-loop classes. -/
theorem periodTorusCircle_inducedHomology_periodLoop (p : PeriodDomain) (v : Lattice) :
    inducedHomology (periodTorusCircleHomeomorph p : C(_, _))
        (loopHomologyClass (p.periodLoop v)) =
      loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [inducedHomology_loopHomologyClass, periodTorusCircleHomeomorph_periodLoop]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
