import Wikipedia.HopfProblem.CuspCentralHomologyPhaseTori
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality

/-!
# Vanishing of actual circle-parametrized attaching maps

The proved circle-product decomposition writes each homology class as an
actual fixed-circle section class plus an actual positive-circle cross
product. If the circle parameter has zero induced first homology, the
mixed term vanishes by cross-product naturality. The section term is
exactly the induced map of the orbit through the parameter's base point.
No coefficient matrix or homology formula for the attaching map is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]

/-- Evaluation of a continuous family along the actual unit-circle parameter. -/
def circleParametrizedMap (a : C(X × D, D)) (α : C(_root_.Circle, D)) :
    C(X × _root_.Circle, D) :=
  a.comp ((ContinuousMap.id X).prodMap α)

@[simp] theorem circleParametrizedMap_apply (a : C(X × D, D))
    (α : C(_root_.Circle, D)) (p : X × _root_.Circle) :
    circleParametrizedMap a α p = a (p.1, α p.2) := rfl

/-- The actual fixed-parameter orbit, at the identity of the parameter circle. -/
def circleParametrizedOrbit (a : C(X × D, D)) (α : C(_root_.Circle, D)) : C(X, D) :=
  a.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X (α 1)))

@[simp] theorem circleParametrizedOrbit_apply (a : C(X × D, D))
    (α : C(_root_.Circle, D)) (x : X) :
    circleParametrizedOrbit a α x = a (x, α 1) := rfl

/-- Reorder the source while replacing the additive unit circle by the actual complex circle. -/
def circleParametrizedSourceHomeomorph (X : Type) [TopologicalSpace X] :
    (AddCircle (1 : ℝ) × X) ≃ₜ (X × _root_.Circle) :=
  (circleCoordinateHomeomorph.symm.prodCongr (Homeomorph.refl X)).trans
    (Homeomorph.prodComm _root_.Circle X)

@[simp] theorem circleParametrizedSourceHomeomorph_apply (p : AddCircle (1 : ℝ) × X) :
    circleParametrizedSourceHomeomorph X p = (p.2, circleCoordinateHomeomorph.symm p.1) := rfl

/-- The same family, with the additive circle first as in the actual cross-product construction. -/
def additiveCircleParametrizedMap (a : C(X × D, D)) (β : C(AddCircle (1 : ℝ), D)) :
    C(AddCircle (1 : ℝ) × X, D) :=
  (a.comp (Homeomorph.prodComm D X : C(D × X, X × D))).comp
    (β.prodMap (ContinuousMap.id X))

theorem circleParametrizedMap_comp_source (a : C(X × D, D)) (α : C(_root_.Circle, D)) :
    (circleParametrizedMap a α).comp
        (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle)) =
      additiveCircleParametrizedMap a
        (α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) := rfl

/-- The mixed actual homology summand is killed by a parameter with zero induced first homology. -/
theorem parameterMap_positiveCircleCross_eq_zero (β : C(AddCircle (1 : ℝ), D))
    (hβ : singularHomologyMap β 1 = 0) (n : ℕ) (b : SingularHomology X n) :
    singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
      (positiveCircleCross X n b) = 0 := by
  have h := crossProductHomology_natural β (ContinuousMap.id X) n
    (loopHomologyClass CirclePaths.positiveLoop) b
  change singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
      (positiveCircleCross X n b) =
    crossProductHomology D X n
      (singularHomologyMap β 1 (loopHomologyClass CirclePaths.positiveLoop))
      (singularHomologyMap (ContinuousMap.id X) n b) at h
  rw [hβ, LinearMap.zero_apply, map_zero, LinearMap.zero_apply] at h
  exact h

/-- The actual section-plus-cross-product decomposition proves vanishing
in every positive degree. -/
theorem additiveCircleParametrizedHomologyMap_eq_zero (a : C(X × D, D))
    (β : C(AddCircle (1 : ℝ), D)) (hβ : singularHomologyMap β 1 = 0) (n : ℕ)
    (hsection : singularHomologyMap
      ((additiveCircleParametrizedMap a β).comp (CircleTopology.productSection X)) (n + 1) = 0) :
    singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 := by
  have hs (c : SingularHomology X (n + 1)) :
      singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (circleSectionHomology X (n + 1) c) = 0 := by
    change ((singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)).comp
      (singularHomologyMap (CircleTopology.productSection X) (n + 1))) c = 0
    rw [← singularHomologyMap_comp, hsection, LinearMap.zero_apply]
  have hc (c : SingularHomology X n) :
      singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (positiveCircleCross X n c) = 0 := by
    rw [additiveCircleParametrizedMap, singularHomologyMap_comp, LinearMap.comp_apply,
      parameterMap_positiveCircleCross_eq_zero β hβ, map_zero]
  apply LinearMap.ext
  intro c
  change singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) c = 0
  obtain ⟨p, rfl⟩ := (circleProductHomologyEquiv X n).symm.surjective c
  rw [circleProductHomologyEquiv_symm_eq_section_add_cross, map_add, hs, hc, add_zero]

/-- A circle-parametrized family kills positive-degree homology when its actual circle and
fixed-parameter maps kill the two corresponding summands. -/
theorem circleParametrizedHomologyMap_eq_zero (a : C(X × D, D))
    (α : C(_root_.Circle, D)) (hα : singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit : singularHomologyMap (circleParametrizedOrbit a α) (n + 1) = 0) :
    singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp
      (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle)) from rfl,
      singularHomologyMap_comp, hα, LinearMap.zero_comp]
  have hsectionMap :
      (additiveCircleParametrizedMap a β).comp (CircleTopology.productSection X) =
        circleParametrizedOrbit a α := by
    apply ContinuousMap.ext
    intro x
    change a (x, α (circleCoordinateHomeomorph.symm 0)) = a (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hzero : singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 :=
    additiveCircleParametrizedHomologyMap_eq_zero a β hβ n (by rw [hsectionMap]; exact horbit)
  have hcomp : (singularHomologyMap (circleParametrizedMap a α) (n + 1)).comp
      (homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X) (n + 1)).toLinearMap = 0 := by
    rw [homeomorphHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
      circleParametrizedMap_comp_source]
    exact hzero
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ :=
    (homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X) (n + 1)).surjective c
  exact LinearMap.congr_fun hcomp d

/-- The requested degree-two vanishing criterion for an actual compact-phase attaching map. -/
theorem attachingHomologyTwo_eq_zero
    (a : C(ToricSpace.CompactFibreTorus × D, D)) (α : C(_root_.Circle, D))
    (hα : singularHomologyMap α 1 = 0)
    (horbit : singularHomologyMap (circleParametrizedOrbit a α) 2 = 0) :
    singularHomologyMap (circleParametrizedMap a α) 2 = 0 :=
  circleParametrizedHomologyMap_eq_zero a α hα 1 horbit

/-- A proved nullhomotopy of the actual fixed-parameter orbit supplies the orbit-map hypothesis. -/
theorem circleParametrizedHomologyMap_eq_zero_of_nullhomotopic (a : C(X × D, D))
    (α : C(_root_.Circle, D)) (hα : singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit : (circleParametrizedOrbit a α).Nullhomotopic) :
    singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 :=
  circleParametrizedHomologyMap_eq_zero a α hα n
    (singularHomologyMap_eq_zero_of_nullhomotopic _ horbit (n + 1) (Nat.succ_ne_zero n))

/-- The compact-phase attaching criterion with a genuine nullhomotopic orbit. -/
theorem attachingHomologyTwo_eq_zero_of_nullhomotopic
    (a : C(ToricSpace.CompactFibreTorus × D, D)) (α : C(_root_.Circle, D))
    (hα : singularHomologyMap α 1 = 0)
    (horbit : (circleParametrizedOrbit a α).Nullhomotopic) :
    singularHomologyMap (circleParametrizedMap a α) 2 = 0 :=
  circleParametrizedHomologyMap_eq_zero_of_nullhomotopic a α hα 1 horbit

/-- The same actual vanishing statement after the ordered three-torus coordinate change. -/
theorem attachingHomologyTwo_eq_zero_productTorus
    (a : C(ToricSpace.CompactFibreTorus × D, D)) (α : C(_root_.Circle, D))
    (hα : singularHomologyMap α 1 = 0)
    (horbit : singularHomologyMap (circleParametrizedOrbit a α) 2 = 0) :
    singularHomologyMap ((circleParametrizedMap a α).comp
      (fibreTorusCircleHomeomorph.symm :
        C(ProductTorus 3, ToricSpace.CompactFibreTorus × _root_.Circle))) 2 = 0 := by
  rw [singularHomologyMap_comp, attachingHomologyTwo_eq_zero a α hα horbit, LinearMap.zero_comp]

end Wikipedia.HopfProblem.CuspCentralHomology
