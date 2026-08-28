import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShearH1
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginNaturality

/-!
# Literal vertical shears of a circle times an additive group

For an actual continuous additive circle map, the shear preserves the
circle coordinate and adds that map to the unchanged group coordinate.
Both coordinate insertions and their exact compositions are retained.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology CircleTopology
open PeriodTorusHigherHomologyPontryagin

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- Insert the actual circle at the additive identity of the other factor. -/
def circleHeadMap : C(Circle, Circle × G) :=
  (ContinuousMap.id Circle).prodMk (ContinuousMap.const Circle 0)

omit [IsTopologicalAddGroup G] in
@[simp] theorem circleHeadMap_apply (c : Circle) : circleHeadMap G c = (c, 0) := rfl

omit [IsTopologicalAddGroup G] in
@[simp] theorem circleHeadMap_zero : circleHeadMap G 0 = 0 := rfl

omit [IsTopologicalAddGroup G] in
theorem productSection_add (x y : G) :
    productSection G (x + y) = productSection G x + productSection G y := by
  exact Prod.ext (zero_add 0).symm rfl

/-- The actual translation shear; no coordinates on the group have been chosen. -/
def verticalProductShear (v : C(Circle, G)) : C(Circle × G, Circle × G) :=
  ⟨fun p => (p.1, p.2 + v p.1),
    continuous_fst.prodMk (continuous_snd.add (v.continuous.comp continuous_fst))⟩

@[simp] theorem verticalProductShear_apply (v : C(Circle, G)) (p : Circle × G) :
    verticalProductShear G v p = (p.1, p.2 + v p.1) := rfl

/-- The genuine shear is a homeomorphism even without additivity of the circle map. -/
def verticalProductShearHomeomorph (v : C(Circle, G)) :
    (Circle × G) ≃ₜ (Circle × G) where
  toFun := verticalProductShear G v
  invFun p := (p.1, p.2 - v p.1)
  left_inv p := Prod.ext rfl (add_sub_cancel_right p.2 (v p.1))
  right_inv p := Prod.ext rfl (sub_add_cancel p.2 (v p.1))
  continuous_toFun := (verticalProductShear G v).continuous
  continuous_invFun :=
    continuous_fst.prodMk (continuous_snd.sub (v.continuous.comp continuous_fst))

@[simp] theorem verticalProductShearHomeomorph_apply (v : C(Circle, G)) (p : Circle × G) :
    verticalProductShearHomeomorph G v p = (p.1, p.2 + v p.1) := rfl

@[simp] theorem verticalProductShearHomeomorph_symm_apply (v : C(Circle, G))
    (p : Circle × G) :
    (verticalProductShearHomeomorph G v).symm p = (p.1, p.2 - v p.1) := rfl

@[simp] theorem verticalProductShearHomeomorph_toContinuousMap (v : C(Circle, G)) :
    (verticalProductShearHomeomorph G v : C(Circle × G, Circle × G)) =
      verticalProductShear G v := rfl

omit [IsTopologicalAddGroup G] in
theorem circleMorphism_zero (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) : v 0 = 0 := by
  have h : v 0 + v 0 = v 0 + 0 := by
    simpa only [zero_add, add_zero] using (hv 0 0).symm
  exact add_left_cancel h

theorem verticalProductShear_add (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) (x y : Circle × G) :
    verticalProductShear G v (x + y) =
      verticalProductShear G v x + verticalProductShear G v y := by
  apply Prod.ext
  · rfl
  · change x.2 + y.2 + v (x.1 + y.1) = (x.2 + v x.1) + (y.2 + v y.1)
    rw [hv]
    abel

/-- The vertical shear leaves the original zero-circle section unchanged. -/
theorem verticalProductShear_comp_section (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) :
    (verticalProductShear G v).comp (productSection G) = productSection G := by
  ext x
  · rfl
  · change x + v 0 = x
    rw [circleMorphism_zero G v hv, add_zero]

/-- On the original circle insertion it is the literal sum of the two coordinate insertions. -/
theorem verticalProductShear_comp_head (v : C(Circle, G)) :
    (verticalProductShear G v).comp (circleHeadMap G) =
      circleHeadMap G + (productSection G).comp v := by
  ext c
  · exact (add_zero c).symm
  · rfl

/-- Addition of the two insertions recovers the identity on the original product. -/
theorem circleProduct_identity_eq_add :
    ContinuousMap.id (Circle × G) =
      (additionMap (Circle × G)).comp ((circleHeadMap G).prodMap (productSection G)) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  exact Prod.ext (add_zero c).symm (zero_add x).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
