import ErdosProblems.Erdos1148.FormAction

/-! # Integral orbits of individual forms of a fixed discriminant -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

abbrev IntegralDiscrForm (d : ℤ) := {t : ℤ × ℤ × ℤ // discr t = d}

def integralFormAction {d : ℤ} (g : SL(2, ℤ)) (t : IntegralDiscrForm d) : IntegralDiscrForm d :=
  ⟨formAction g t.1, (discr_formAction g t.1).trans t.2⟩

instance integralDiscrFormMulAction (d : ℤ) : MulAction SL(2, ℤ) (IntegralDiscrForm d) where
  smul := integralFormAction
  one_smul t := Subtype.ext (formAction_one t.1)
  mul_smul g h t := Subtype.ext (formAction_mul g h t.1)

lemma integralFormAction_val {d : ℤ} (g : SL(2, ℤ)) (t : IntegralDiscrForm d) :
    (g • t).1 = formAction g t.1 := rfl

abbrev IntegralFormOrbits (d : ℤ) := Quotient (MulAction.orbitRel SL(2, ℤ) (IntegralDiscrForm d))

def integralFormOrbitMk {d : ℤ} (t : IntegralDiscrForm d) : IntegralFormOrbits d :=
  Quotient.mk _ t

lemma integralFormOrbitMk_eq_iff {d : ℤ} (t u : IntegralDiscrForm d) :
    integralFormOrbitMk t = integralFormOrbitMk u ↔ ∃ g : SL(2, ℤ), formAction g t.1 = u.1 := by
  constructor
  · intro heq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact heq.symm))
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    apply Eq.symm
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨g, Subtype.ext hg⟩

lemma integralFormOrbitMk_action {d : ℤ} (g : SL(2, ℤ)) (t : IntegralDiscrForm d) :
    integralFormOrbitMk (g • t) = integralFormOrbitMk t :=
  ((integralFormOrbitMk_eq_iff t (g • t)).mpr ⟨g, rfl⟩).symm

end Erdos1148.DukeArithmetic
