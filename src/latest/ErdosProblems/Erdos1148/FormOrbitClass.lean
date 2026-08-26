import ErdosProblems.Erdos1148.PrimitiveFormClass
import ErdosProblems.Erdos1148.PrimitivePacketMass

/-! # The map from primitive form orbits to the class group of the order -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def primitiveDiscrFormClass {d : ℤ} [hns : Fact (¬IsSquare d)]
    (t : IntegralDiscrForm d) (hprim : PrimitiveIntegralForm t.1) :
    ClassGroup (quadraticOrder d) :=
  primitiveFormClass t.2 hprim (fst_ne_zero_of_nonsquare_discr hns.out t.2)

lemma primitiveDiscrFormClass_action {d : ℤ} [hns : Fact (¬IsSquare d)]
    (t : IntegralDiscrForm d) (hprim : PrimitiveIntegralForm t.1) (γ : SL(2, ℤ)) :
    primitiveDiscrFormClass (γ • t) ((primitiveIntegralForm_formAction_iff γ t.1).mpr hprim) =
      primitiveDiscrFormClass t hprim := by
  exact primitiveFormClass_action t.2 hprim (fst_ne_zero_of_nonsquare_discr hns.out t.2) γ
    (fst_ne_zero_of_nonsquare_discr hns.out (γ • t).2)

theorem primitiveDiscrFormClass_eq_of_orbit {d : ℤ} [Fact (¬IsSquare d)]
    (t u : IntegralDiscrForm d) (ht : PrimitiveIntegralForm t.1) (hu : PrimitiveIntegralForm u.1)
    (horbit : integralFormOrbitMk t = integralFormOrbitMk u) :
    primitiveDiscrFormClass t ht = primitiveDiscrFormClass u hu := by
  obtain ⟨γ, hγ⟩ := (integralFormOrbitMk_eq_iff t u).mp horbit
  have hsub : γ • t = u := Subtype.ext hγ
  subst u
  exact (primitiveDiscrFormClass_action t ht γ).symm

noncomputable def primitiveIntegralFormOrbitMk {d : ℤ} (t : IntegralDiscrForm d)
    (ht : PrimitiveIntegralForm t.1) : PrimitiveIntegralFormOrbits d :=
  ⟨integralFormOrbitMk t, (primitiveIntegralForm_out_mk_iff t).mpr ht⟩

noncomputable def primitiveFormOrbitClass {d : ℤ} [Fact (¬IsSquare d)]
    (q : PrimitiveIntegralFormOrbits d) : ClassGroup (quadraticOrder d) :=
  primitiveDiscrFormClass q.1.out q.2

theorem primitiveFormOrbitClass_mk {d : ℤ} [Fact (¬IsSquare d)]
    (t : IntegralDiscrForm d) (ht : PrimitiveIntegralForm t.1) :
    primitiveFormOrbitClass (primitiveIntegralFormOrbitMk t ht) = primitiveDiscrFormClass t ht := by
  apply primitiveDiscrFormClass_eq_of_orbit _ t _ ht
  exact Quotient.out_eq (integralFormOrbitMk t)

end Erdos1148.DukeArithmetic
