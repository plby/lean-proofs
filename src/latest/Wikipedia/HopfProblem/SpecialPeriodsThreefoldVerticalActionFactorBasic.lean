import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionExponential
import Mathlib.Algebra.Group.Action.Faithful

/-!
# Factoring an integral-period additive flow through the actual exponential

An additive flow with the proved integer-period law descends through the
ordinary additive quotient `ℂ / ℤ`. The genuine exponential group equivalence
then gives an action of `ℂˣ`. No topology or atlas on the acted-on space is
changed, and no existence or faithfulness of a geometric flow is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor

open Exponential

/-- The algebraic data of an actual additive flow whose integer parameters
act trivially. Holomorphy and its exact kernel are separate assertions. -/
structure AdditiveFlow (M : Type*) where
  toFun : ℂ → M → M
  zero_apply : ∀ x, toFun 0 x = x
  add_apply : ∀ s t x, toFun (s + t) x = toFun s (toFun t x)
  int_apply : ∀ (n : ℤ) x, toFun (n : ℂ) x = x

instance {M : Type*} : CoeFun (AdditiveFlow M) (fun _ => ℂ → M → M) :=
  ⟨AdditiveFlow.toFun⟩

namespace AdditiveFlow

variable {M : Type*} (F : AdditiveFlow M)

theorem apply_eq_of_parameterProjection_eq {s t : ℂ}
    (h : parameterProjection s = parameterProjection t) (x : M) : F s x = F t x := by
  obtain ⟨n, hn⟩ := (parameterProjection_eq_iff s t).mp h
  have hs : s = t + (n : ℂ) := by linear_combination hn
  rw [hs, F.add_apply, F.int_apply]

/-- Literal quotient descent of the additive flow. -/
def parameterAct (p : Parameter) (x : M) : M :=
  Quotient.lift (fun s : ℂ => F s x)
    (fun _ _ h => F.apply_eq_of_parameterProjection_eq (Quotient.sound h) x) p

@[simp] theorem parameterAct_projection (s : ℂ) (x : M) :
    F.parameterAct (parameterProjection s) x = F s x := rfl

@[simp] theorem parameterAct_zero (x : M) : F.parameterAct 0 x = x := by
  rw [← map_zero parameterProjection, F.parameterAct_projection, F.zero_apply]

theorem parameterAct_add (p q : Parameter) (x : M) :
    F.parameterAct (p + q) x = F.parameterAct p (F.parameterAct q x) := by
  obtain ⟨s, rfl⟩ := parameterProjection_surjective p
  obtain ⟨t, rfl⟩ := parameterProjection_surjective q
  rw [← map_add parameterProjection, F.parameterAct_projection,
    F.parameterAct_projection, F.parameterAct_projection, F.add_apply]

/-- The actual action of the quotient parameter group, selected explicitly. -/
@[instance_reducible] def parameterAction : MulAction (Multiplicative Parameter) M where
  smul p x := F.parameterAct p.toAdd x
  one_smul := F.parameterAct_zero
  mul_smul p q x := F.parameterAct_add p.toAdd q.toAdd x

/-- The quotient action transported along the proved exponential group
equivalence, on the existing group of nonzero complex numbers. -/
def act (u : ℂˣ) (x : M) : M :=
  F.parameterAct (parameterMulEquiv.symm u).toAdd x

@[simp] theorem act_normalizedExponential (s : ℂ) (x : M) :
    F.act (normalizedExponential s) x = F s x := by
  have he : parameterMulEquiv.symm (normalizedExponential s) =
      Multiplicative.ofAdd (parameterProjection s) := by
    apply parameterMulEquiv.injective
    rw [parameterMulEquiv.apply_symm_apply, parameterMulEquiv_projection]
  rw [act, he]
  exact F.parameterAct_projection s x

@[simp] theorem act_one (x : M) : F.act 1 x = x := by
  simpa only [normalizedExponential_zero, F.zero_apply] using
    F.act_normalizedExponential 0 x

theorem act_mul (u v : ℂˣ) (x : M) : F.act (u * v) x = F.act u (F.act v x) := by
  obtain ⟨s, rfl⟩ := normalizedExponential_surjective u
  obtain ⟨t, rfl⟩ := normalizedExponential_surjective v
  rw [← normalizedExponential_add, F.act_normalizedExponential,
    F.act_normalizedExponential, F.act_normalizedExponential, F.add_apply]

/-- The multiplicative action factored from the given additive flow. -/
@[instance_reducible] def action : MulAction ℂˣ M where
  smul := F.act
  one_smul := F.act_one
  mul_smul := F.act_mul

@[simp] theorem action_smul (u : ℂˣ) (x : M) :
    letI := F.action
    u • x = F.act u x := rfl

@[simp] theorem action_normalizedExponential (s : ℂ) (x : M) :
    letI := F.action
    normalizedExponential s • x = F s x := F.act_normalizedExponential s x

@[simp] theorem act_inv_act (u : ℂˣ) (x : M) : F.act u⁻¹ (F.act u x) = x := by
  rw [← F.act_mul, inv_mul_cancel, F.act_one]

@[simp] theorem act_act_inv (u : ℂˣ) (x : M) : F.act u (F.act u⁻¹ x) = x := by
  rw [← F.act_mul, mul_inv_cancel, F.act_one]

/-- Every parameter acts by the explicit permutation with inverse
given by the inverse parameter. -/
def equiv (u : ℂˣ) : M ≃ M where
  toFun := F.act u
  invFun := F.act u⁻¹
  left_inv := F.act_inv_act u
  right_inv := F.act_act_inv u

@[simp] theorem equiv_apply (u : ℂˣ) (x : M) : F.equiv u x = F.act u x := rfl

@[simp] theorem equiv_symm_apply (u : ℂˣ) (x : M) :
    (F.equiv u).symm x = F.act u⁻¹ x := rfl

/-- An exact integer kernel for the original flow proves faithfulness of
the factored multiplicative action. -/
theorem faithfulSMul
    (hkernel : ∀ s : ℂ, (∀ x : M, F s x = x) ↔ ∃ n : ℤ, s = (n : ℂ)) :
    letI := F.action
    FaithfulSMul ℂˣ M := by
  let := F.action
  apply _root_.faithfulSMul_iff.mpr
  intro u hu
  obtain ⟨s, rfl⟩ := normalizedExponential_surjective u
  apply (normalizedExponential_eq_one_iff s).mpr
  apply (hkernel s).mp
  intro x
  have hx := hu x
  change F.act (normalizedExponential s) x = x at hx
  rwa [F.act_normalizedExponential] at hx

/-- Faithfulness of this specific descended action is equivalent to the
integer-period assertion being the exact kernel of the original flow. -/
theorem faithfulSMul_iff :
    (letI := F.action; FaithfulSMul ℂˣ M) ↔
      ∀ s : ℂ, (∀ x : M, F s x = x) ↔ ∃ n : ℤ, s = (n : ℂ) := by
  constructor
  · intro hfaith
    let := F.action
    let := hfaith
    intro s
    constructor
    · intro hs
      apply (normalizedExponential_eq_one_iff s).mp
      apply eq_of_smul_eq_smul (α := M)
      intro x
      change F.act (normalizedExponential s) x = F.act 1 x
      rw [F.act_normalizedExponential, F.act_one]
      exact hs x
    · rintro ⟨n, rfl⟩
      exact F.int_apply n
  · exact F.faithfulSMul

end AdditiveFlow

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor
