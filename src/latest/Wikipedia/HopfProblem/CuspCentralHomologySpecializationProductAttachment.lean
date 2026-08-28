import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossProjection

/-!
# Product attaching maps whose circle has zero first homology

The actual circle-product decomposition implies that a product attaching
map factors on positive-degree homology through the projection to its
unchanged factor.  This is the source-cover counterpart of the vanishing
criterion used for the central cusp cover: the fixed-parameter section
need not be nullhomotopic here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]

/-- The fixed-parameter section in the product target. -/
def productParameterSection (X : Type) [TopologicalSpace X] (d : D) : C(X, X × D) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X d)

/-- A zero first-homology parameter kills every mixed circle-product
summand.  Its remaining map is the actual fixed-parameter section. -/
theorem additiveProductParameter_homology_factor
    (β : C(AddCircle (1 : ℝ), D)) (hβ : singularHomologyMap β 1 = 0) (n : ℕ) :
    singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1) =
      (singularHomologyMap
        ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1)).comp
          (circleProjectionHomology X (n + 1)) := by
  have hs (a : SingularHomology X (n + 1)) :
      singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
          (circleSectionHomology X (n + 1) a) =
        singularHomologyMap
          ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1) a := by
    change ((singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)).comp
      (singularHomologyMap (CircleTopology.productSection X) (n + 1))) a = _
    rw [← singularHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := (circleProductHomologyEquiv X n).symm.surjective a
  have hp : circleProjectionHomology X (n + 1)
      ((circleProductHomologyEquiv X n).symm p) = p.1 := by
    change (circleProductHomologyEquiv X n
      ((circleProductHomologyEquiv X n).symm p)).1 = p.1
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, hp, circleProductHomologyEquiv_symm_eq_section_add_cross,
    map_add, hs, parameterMap_positiveCircleCross_eq_zero β hβ, add_zero]

/-- The same factorization for the actual complex circle on the right. -/
theorem productParameter_homology_factor
    (α : C(_root_.Circle, D)) (hα : singularHomologyMap α 1 = 0) (n : ℕ) :
    singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) =
      (singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
        (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)) := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp
      (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle)) from rfl,
      singularHomologyMap_comp, hα, LinearMap.zero_comp]
  let g : C(AddCircle (1 : ℝ) × X, X × _root_.Circle) :=
    (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle))
  have hmap : ((ContinuousMap.id X).prodMap α).comp g =
      (Homeomorph.prodComm D X : C(D × X, X × D)).comp
        (β.prodMap (ContinuousMap.id X)) := rfl
  have hsection :
      (Homeomorph.prodComm D X : C(D × X, X × D)).comp
          ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) =
        productParameterSection X (α 1) := by
    apply ContinuousMap.ext
    intro x
    change (x, α (circleCoordinateHomeomorph.symm 0)) = (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hprojection :
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)).comp
        (singularHomologyMap g (n + 1)) = circleProjectionHomology X (n + 1) := by
    rw [← singularHomologyMap_comp]
    rfl
  have hpre : (singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1)).comp
      (singularHomologyMap g (n + 1)) =
        ((singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
          (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1))).comp
            (singularHomologyMap g (n + 1)) := by
    rw [← singularHomologyMap_comp, hmap, singularHomologyMap_comp,
      additiveProductParameter_homology_factor β hβ n, ← LinearMap.comp_assoc,
      ← singularHomologyMap_comp, hsection, LinearMap.comp_assoc, hprojection]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ :=
    (homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X) (n + 1)).surjective a
  exact LinearMap.congr_fun hpre b

/-- In particular, every actual class killed by the unchanged-factor
projection is killed by the product attaching map. -/
theorem productParameter_homology_eq_zero_of_projection
    (α : C(_root_.Circle, D)) (hα : singularHomologyMap α 1 = 0) (n : ℕ)
    (a : SingularHomology (X × _root_.Circle) (n + 1))
    (ha : singularHomologyMap
      (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1) a = 0) :
    singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) a = 0 := by
  rw [productParameter_homology_factor α hα n, LinearMap.comp_apply, ha, map_zero]

end Wikipedia.HopfProblem.CuspCentralHomology
