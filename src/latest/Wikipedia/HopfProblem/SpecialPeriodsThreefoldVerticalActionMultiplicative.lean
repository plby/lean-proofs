import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFlow
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFactor

/-!
# The actual effective fibrewise holomorphic multiplicative action

The global additive flow has exactly the integral kernel.  Its literal
descent through the genuine quotient `ℂ / ℤ`, followed by the proved
normalized-exponential equivalence, constructs a faithful holomorphic
action of the existing complex multiplicative group on the original
compact threefold.  No automorphism-group classification is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] chartedSpace

/-- The already constructed global flow supplies every algebraic law. -/
def additiveFlow : Factor.AdditiveFlow Space where
  toFun := flow
  zero_apply := flow_zero
  add_apply := flow_add
  int_apply := flow_int_cast

theorem additiveFlow_kernel (s : ℂ) :
    (∀ x : Space, additiveFlow s x = x) ↔ ∃ n : ℤ, s = (n : ℂ) := by
  constructor
  · intro h
    exact (flow_eq_id_iff s).mp (funext h)
  · rintro ⟨n, rfl⟩
    exact flow_int_cast n

/-- The genuine multiplicative action obtained by quotient descent,
selected explicitly rather than replacing any topology or atlas. -/
@[instance_reducible] def action : MulAction ℂˣ Space := additiveFlow.action

theorem action_faithful : letI := action; FaithfulSMul ℂˣ Space :=
  additiveFlow.faithfulSMul additiveFlow_kernel

theorem action_continuous : letI := action; ContinuousSMul ℂˣ Space :=
  additiveFlow.continuousSMul jointFlow_holomorphic

/-- The exact normalized-exponential lift of the actual group action. -/
@[simp] theorem action_normalizedExponential (s : ℂ) (x : Space) :
    letI := action
    Exponential.normalizedExponential s • x = flow s x :=
  additiveFlow.action_normalizedExponential s x

theorem action_joint_holomorphic :
    letI := action
    ContMDiff ((IF).prod I₁) IF ω (fun p : Space × ℂˣ => p.2 • p.1) :=
  additiveFlow.action_holomorphic jointFlow_holomorphic

/-- Joint holomorphicity in the customary parameter-first convention. -/
theorem action_holomorphic :
    letI := action
    ContMDiff ((I₁).prod IF) IF ω (fun p : ℂˣ × Space => p.1 • p.2) := by
  let := action
  have hs : ContMDiff ((I₁).prod IF) ((IF).prod I₁) ω
      (fun p : ℂˣ × Space => (p.2, p.1)) := contMDiff_snd.prodMk contMDiff_fst
  have hh := action_joint_holomorphic.comp hs
  simpa only [Function.comp_def] using hh

@[simp] theorem projection_action (u : ℂˣ) (x : Space) :
    letI := action
    projection (u • x) = projection x := by
  let := action
  obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
  rw [action_normalizedExponential, projection_flow]

@[simp] theorem projectionSphere_action (u : ℂˣ) (x : Space) :
    letI := action
    projectionSphere (u • x) = projectionSphere x := by
  let := action
  obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
  rw [action_normalizedExponential, projectionSphere_flow]

/-- The actual biholomorphic time maps for nonzero complex parameters. -/
def actionBiholomorph (u : ℂˣ) : Diffeomorph IF IF Space Space ω :=
  additiveFlow.biholomorph IF jointFlow_holomorphic u

@[simp] theorem actionBiholomorph_apply (u : ℂˣ) (x : Space) :
    letI := action
    actionBiholomorph u x = u • x := rfl

@[simp] theorem actionBiholomorph_exponential (s : ℂ) (x : Space) :
    actionBiholomorph (Exponential.normalizedExponential s) x = flow s x :=
  additiveFlow.biholomorph_normalizedExponential jointFlow_holomorphic s x

theorem actionBiholomorph_injective : Function.Injective actionBiholomorph := by
  let := action
  let := action_faithful
  intro u v huv
  apply eq_of_smul_eq_smul (α := Space)
  intro x
  exact congrArg (fun e : Diffeomorph IF IF Space Space ω => e x) huv

/-- The constructed action is effective, jointly holomorphic, and
preserves every fibre of the actual map to the sphere. -/
theorem effective_fibrewise_holomorphic_action :
    letI := action
    FaithfulSMul ℂˣ Space ∧ ContinuousSMul ℂˣ Space ∧
      ContMDiff ((I₁).prod IF) IF ω (fun p : ℂˣ × Space => p.1 • p.2) ∧
      ∀ u : ℂˣ, ∀ x : Space, projectionSphere (u • x) = projectionSphere x :=
  ⟨action_faithful, action_continuous, action_holomorphic, projectionSphere_action⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
