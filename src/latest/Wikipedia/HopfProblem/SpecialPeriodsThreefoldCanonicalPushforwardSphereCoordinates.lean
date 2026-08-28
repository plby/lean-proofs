import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwist
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsCharts

/-!
# The genuine cotangent cocycle of the Riemann sphere

The native tangent coordinates have transition `-1 / z²`, so the dual
coefficient transition is `-z²`.  The open sets here are exactly the
existing finite and reciprocal charts, including their chart centres.
-/

open Set Topology Bundle TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

open RiemannSphere
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The native tangent-bundle chart and the actual sheaf frame chart
are the same open subset of the existing Riemann sphere. -/
theorem chartOpen_eq_frameChart (b : Bool) :
    HolomorphicVectorFields.chartOpen b = frameChart b := by
  apply SetLike.coe_injective
  rw [HolomorphicVectorFields.chartOpen_eq_range]
  cases b <;> rfl

/-- Cotangent coefficient transitions, with the derivative's exact sign.
Away from the actual overlap the arbitrary unit extension only supplies
a globally defined cocycle function. -/
noncomputable def transition : Bool → Bool → RiemannSphere → ℂˣ
  | false, true => fun p => -(BaseTwist.overlapUnit p ^ 2)
  | true, false => fun p => (-(BaseTwist.overlapUnit p ^ 2))⁻¹
  | _, _ => fun _ => 1

@[simp] theorem transition_self (b : Bool) (p : RiemannSphere) :
    transition b b p = 1 := by
  cases b <;> rfl

theorem transition_comp (a b c : Bool) (p : RiemannSphere) :
    transition b c p * transition a b p = transition a c p := by
  cases a <;> cases b <;> cases c <;> simp [transition]

theorem transition_false_true {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (transition false true p : ℂ) = -(BaseTwist.finiteCoordinate p ^ 2) := by
  simp only [transition, Units.val_neg, Units.val_pow_eq_pow_val,
    BaseTwist.overlapUnit_val hp]

theorem transition_true_false {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (transition true false p : ℂ) = -(BaseTwist.infinityCoordinate p ^ 2) := by
  simp only [transition, Units.val_inv_eq_inv_val, Units.val_neg,
    Units.val_pow_eq_pow_val, BaseTwist.overlapUnit_val hp, neg_inv,
    BaseTwist.infinityCoordinate_eq_inv_finiteCoordinate, inv_pow]

theorem transition_holomorphicOn (a b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun p => (transition a b p : ℂ))
      ((frameChart a : Set RiemannSphere) ∩ frameChart b) := by
  cases a <;> cases b
  · exact contMDiffOn_const
  · apply ((BaseTwist.finiteCoordinate_holomorphicOn.pow 2).neg.mono
      inter_subset_left).congr
    intro p hp
    exact transition_false_true hp
  · apply ((BaseTwist.infinityCoordinate_holomorphicOn.pow 2).neg.mono
      inter_subset_left).congr
    intro p hp
    exact transition_true_false ⟨hp.2, hp.1⟩
  · exact contMDiffOn_const

/-- The native cotangent scalar cocycle, on the original two-chart cover. -/
noncomputable def data : HolomorphicCharacterBundle.TransitionData RiemannSphere Bool where
  baseSet b := frameChart b
  isOpen_baseSet b := (frameChart b).isOpen
  indexAt := BaseTwist.indexAt
  mem_baseSet_at := BaseTwist.mem_frameChart_indexAt
  transition := transition
  transition_self b p _ := transition_self b p
  transition_comp a b c p _ := transition_comp a b c p
  continuousOn_transition a b := (transition_holomorphicOn a b).continuousOn

@[simp] theorem data_baseSet (b : Bool) :
    data.baseSet b = (frameChart b : Set RiemannSphere) := rfl

@[simp] theorem data_indexAt (p : RiemannSphere) :
    data.indexAt p = BaseTwist.indexAt p := rfl

@[simp] theorem data_transition (a b : Bool) (p : RiemannSphere) :
    data.transition a b p = transition a b p := rfl

theorem data_transition_false_true {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition false true p : ℂ) = -(BaseTwist.finiteCoordinate p ^ 2) :=
  transition_false_true hp

theorem data_transition_true_false {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition true false p : ℂ) = -(BaseTwist.infinityCoordinate p ^ 2) :=
  transition_true_false hp

instance data_isHolomorphic : data.IsHolomorphic 𝓘(ℂ) where
  contMDiffOn_transition := transition_holomorphicOn

/-- The actual native tangent-coordinate change is the inverse of the
cotangent coefficient transition, including its minus sign. -/
theorem tangentCoordinate_false_true (p : RiemannSphere) (hp : p ∈ chartOverlap)
    (v : TangentSpace 𝓘(ℂ) p) :
    HolomorphicVectorFields.coordinate true p v =
      (data.transition false true p : ℂ)⁻¹ *
        HolomorphicVectorFields.coordinate false p v := by
  induction p using OnePoint.rec with
  | infty => exact (infty_not_mem_finiteChart hp.1).elim
  | coe z =>
    have hz : z ≠ 0 := (coe_mem_infinityChart_iff z).mp hp.2
    have hfalse := HolomorphicVectorFields.coe_mem_chartOpen_false z
    have htrue := HolomorphicVectorFields.coe_mem_chartOpen_true hz
    have hcomp := tangentCoordChange_comp (I := 𝓘(ℂ))
      (w := (z : RiemannSphere)) (x := HolomorphicVectorFields.chartCenter false)
      (y := HolomorphicVectorFields.chartCenter true) (z := (z : RiemannSphere)) (v := v)
      ⟨⟨mem_extChartAt_source _, by rw [extChartAt_source]; exact hfalse⟩,
        by rw [extChartAt_source]; exact htrue⟩
    rw [data_transition_false_true hp, BaseTwist.finiteCoordinate_coe, ← neg_inv,
      HolomorphicVectorFields.coordinate_eq_tangentCoordChange,
      HolomorphicVectorFields.coordinate_eq_tangentCoordChange, ← hcomp,
      HolomorphicVectorFields.tangentCoordChange_false_true hz]

/-- All four chart-pair identities follow from the derivative of the
native reciprocal chart, rather than an assumed scalar convention. -/
theorem tangentCoordinate_transition (a b : Bool) (p : RiemannSphere)
    (hp : p ∈ (frameChart a : Set RiemannSphere) ∩ frameChart b)
    (v : TangentSpace 𝓘(ℂ) p) :
    HolomorphicVectorFields.coordinate b p v =
      (data.transition a b p : ℂ)⁻¹ * HolomorphicVectorFields.coordinate a p v := by
  cases a <;> cases b
  · simp only [data_transition, transition_self, Units.val_one, inv_one, one_mul]
  · exact tangentCoordinate_false_true p hp v
  · have h := tangentCoordinate_false_true p ⟨hp.2, hp.1⟩ v
    change HolomorphicVectorFields.coordinate false p v =
      (↑((transition false true p)⁻¹) : ℂ)⁻¹ *
        HolomorphicVectorFields.coordinate true p v
    rw [Units.val_inv_eq_inv_val, inv_inv, h]
    exact (mul_inv_cancel_left₀ (transition false true p).ne_zero _).symm
  · simp only [data_transition, transition_self, Units.val_one, inv_one, one_mul]

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
