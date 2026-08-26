import ErdosProblems.Erdos1148.FormIdealAction

/-! # The ideal class attached to a primitive integral form -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups nonZeroDivisors

lemma classGroup_mk_principal {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K u) = 1 := by
  apply ClassGroup.mk_eq_one_iff.mpr
  refine ⟨⟨(u : K), ?_⟩⟩
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]

noncomputable def primitiveFormIdealUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ :=
  (formFractionalIdeal_isUnit ht hprim ha).unit

lemma primitiveFormIdealUnit_val {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    (primitiveFormIdealUnit ht hprim ha :
      FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) = formFractionalIdeal ht ha :=
  (formFractionalIdeal_isUnit ht hprim ha).unit_spec

noncomputable def primitiveFormClass {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    ClassGroup (quadraticOrder d) :=
  ClassGroup.mk (QuadraticDiscrAlgebra d) (primitiveFormIdealUnit ht hprim ha)

theorem primitiveFormClass_action {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0)
    (γ : SL(2, ℤ)) (ha' : (formAction γ t).1 ≠ 0) :
    primitiveFormClass ((discr_formAction γ t).trans ht)
        ((primitiveIntegralForm_formAction_iff γ t).mpr hprim) ha' =
      primitiveFormClass ht hprim ha := by
  let u := Units.mk0 (formActionScale (d := d) t ha γ) (formActionScale_ne_zero ht ha γ ha')
  have hu : primitiveFormIdealUnit ht hprim ha =
      toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d) u *
        primitiveFormIdealUnit ((discr_formAction γ t).trans ht)
          ((primitiveIntegralForm_formAction_iff γ t).mpr hprim) ha' := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, primitiveFormIdealUnit_val]
    exact formFractionalIdeal_action_eq_span_mul ht ha γ ha'
  symm
  rw [primitiveFormClass, hu, map_mul, classGroup_mk_principal, one_mul]
  rfl

end Erdos1148.DukeArithmetic
