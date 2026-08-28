import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts

/-!
# Interval coordinates for the mapping-torus Mayer–Vietoris cover

The first chart uses `(0,1)` and the second uses `(-1/2,1/2)`.
Their overlap, read in the first chart, has the two actual components
`(0,1/2)` and `(1/2,1)`. These elementary homeomorphisms retain both
the real coordinate and the unchanged fibre coordinate.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.MappingTorus.HomologyCover

open PeriodTorusHigherHomology.CircleTopology

theorem negativeHalf_coe : ((-(1 / 2 : ℝ)) : Circle) = halfPoint := by
  have h := AddCircle.coe_add_period (p := (1 : ℝ)) (-(1 / 2 : ℝ))
  norm_num [halfPoint] at h ⊢
  exact h.symm

theorem negativeHalf_coe_ne_zero : ((-(1 / 2 : ℝ)) : Circle) ≠ 0 := by
  rw [negativeHalf_coe]
  exact halfPoint_ne_zero

/-- A point of the first period interval lies over the omitted point of
the second chart exactly when it is the real midpoint. -/
theorem unitInterval_coe_eq_negativeHalf_iff (t : Ioo (0 : ℝ) 1) :
    ((t : ℝ) : Circle) = ((-(1 / 2 : ℝ)) : Circle) ↔ (t : ℝ) = 1 / 2 := by
  rw [negativeHalf_coe]
  exact AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    ⟨le_of_lt t.property.1, by simpa only [zero_add] using t.property.2⟩
    (by norm_num)

theorem unitInterval_coe_ne_negativeHalf_iff (t : Ioo (0 : ℝ) 1) :
    ((t : ℝ) : Circle) ≠ ((-(1 / 2 : ℝ)) : Circle) ↔ (t : ℝ) ≠ 1 / 2 :=
  not_congr (unitInterval_coe_eq_negativeHalf_iff t)

/-- Restricting the first coordinate of a product is an actual product
of a subtype with the unchanged second factor. -/
def firstPredicateHomeomorph (A X : Type*) [TopologicalSpace A]
    [TopologicalSpace X] (p : A → Prop) :
    {z : A × X // p z.1} ≃ₜ ({a : A // p a} × X) where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

variable (X : Type*) [TopologicalSpace X]

/-- The genuine punctured interval product, separated into its two open components. -/
def intervalIntersectionHomeomorph :
    {p : Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2} ≃ₜ
      ((Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Ioo (1 / 2 : ℝ) 1 × X)) :=
  ((firstPredicateHomeomorph (Ioo (0 : ℝ) 1) X (fun t => (t : ℝ) ≠ 1 / 2)).trans
    (puncturedIntervalHomeomorph.prodCongr (Homeomorph.refl X))).trans
      Homeomorph.sumProdDistrib

@[simp] theorem intervalIntersectionHomeomorph_symm_inl
    (p : Ioo (0 : ℝ) (1 / 2) × X) :
    (intervalIntersectionHomeomorph X).symm (Sum.inl p) =
      ⟨((puncturedIntervalInl p.1).val, p.2), (puncturedIntervalInl p.1).property⟩ := rfl

@[simp] theorem intervalIntersectionHomeomorph_symm_inr
    (p : Ioo (1 / 2 : ℝ) 1 × X) :
    (intervalIntersectionHomeomorph X).symm (Sum.inr p) =
      ⟨((puncturedIntervalInr p.1).val, p.2), (puncturedIntervalInr p.1).property⟩ := rfl

@[simp] theorem intervalIntersectionHomeomorph_symm_inl_snd
    (p : Ioo (0 : ℝ) (1 / 2) × X) :
    ((intervalIntersectionHomeomorph X).symm (Sum.inl p)).val.2 = p.2 := rfl

@[simp] theorem intervalIntersectionHomeomorph_symm_inr_snd
    (p : Ioo (1 / 2 : ℝ) 1 × X) :
    ((intervalIntersectionHomeomorph X).symm (Sum.inr p)).val.2 = p.2 := rfl

end Wikipedia.HopfProblem.MappingTorus.HomologyCover
