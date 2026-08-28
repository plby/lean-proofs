import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartier

/-!
# The actual base twist on the Riemann sphere

The finite and infinity ideal frames satisfy `e∞ = w efin`. Consequently
the coefficient transition from the finite chart to the infinity chart
is `1 / w`, not `w`. This file constructs that native holomorphic line
bundle using the existing variable-cocycle core, together with the
Cartier presentation having local fractions `1` and `1 / w`.

The scalar transition is extended by the unit `1` away from the overlap;
all asserted geometric coordinate formulas use the actual open charts.
-/

noncomputable section

open Set Topology Bundle TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
open RiemannSphere

/-- The actual finite coordinate on the overlap, extended by a unit
outside the overlap only to supply a globally defined cocycle function. -/
def overlapUnit (p : RiemannSphere) : ℂˣ := by
  classical
  exact if hp : p ∈ chartOverlap then
    Units.mk0 (finiteCoordinate p) (finiteCoordinate_ne_zero hp) else 1

theorem overlapUnit_val {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (overlapUnit p : ℂ) = finiteCoordinate p := by
  classical
  simp only [overlapUnit, dif_pos hp, Units.val_mk0]

theorem overlapUnit_inv_val {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (↑((overlapUnit p)⁻¹) : ℂ) = infinityCoordinate p := by
  rw [Units.val_inv_eq_inv_val, overlapUnit_val hp]
  exact (infinityCoordinate_eq_inv_finiteCoordinate p).symm

/-- Coefficient, rather than frame, transitions for the two actual ideal frames. -/
def transition : Bool → Bool → RiemannSphere → ℂˣ
  | false, true => overlapUnit
  | true, false => fun p => (overlapUnit p)⁻¹
  | _, _ => fun _ => 1

@[simp] theorem transition_self (b : Bool) (p : RiemannSphere) :
    transition b b p = 1 := by
  cases b <;> rfl

theorem transition_comp (a b c : Bool) (p : RiemannSphere) :
    transition b c p * transition a b p = transition a c p := by
  cases a <;> cases b <;> cases c <;> simp [transition]

theorem transition_holomorphicOn (a b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun p => (transition a b p : ℂ))
      ((frameChart a : Set RiemannSphere) ∩ frameChart b) := by
  cases a <;> cases b
  · exact contMDiffOn_const
  · apply (finiteCoordinate_holomorphicOn.mono inter_subset_left).congr
    intro p hp
    exact overlapUnit_val hp
  · apply (infinityCoordinate_holomorphicOn.mono inter_subset_left).congr
    intro p hp
    exact overlapUnit_inv_val ⟨hp.2, hp.1⟩
  · exact contMDiffOn_const

/-- The finite chart is selected except at the actual point at infinity. -/
def indexAt (p : RiemannSphere) : Bool := by
  classical
  exact if p = (∞ : RiemannSphere) then true else false

theorem mem_frameChart_indexAt (p : RiemannSphere) : p ∈ frameChart (indexAt p) := by
  classical
  by_cases hp : p = (∞ : RiemannSphere)
  · subst p
    simp [indexAt, frameChart]
  · simpa only [indexAt, if_neg hp, frameChart] using (mem_finiteChart p).mpr hp

/-- The actual variable unit cocycle defining the base twist. -/
def data : HolomorphicCharacterBundle.TransitionData RiemannSphere Bool where
  baseSet b := frameChart b
  isOpen_baseSet b := (frameChart b).isOpen
  indexAt := indexAt
  mem_baseSet_at := mem_frameChart_indexAt
  transition := transition
  transition_self b p _ := transition_self b p
  transition_comp a b c p _ := transition_comp a b c p
  continuousOn_transition a b := (transition_holomorphicOn a b).continuousOn

@[simp] theorem data_baseSet (b : Bool) :
    data.baseSet b = (frameChart b : Set RiemannSphere) := rfl

@[simp] theorem data_indexAt (p : RiemannSphere) : data.indexAt p = indexAt p := rfl

@[simp] theorem data_transition (a b : Bool) (p : RiemannSphere) :
    data.transition a b p = transition a b p := rfl

theorem data_transition_false_true {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition false true p : ℂ) = finiteCoordinate p := overlapUnit_val hp

theorem data_transition_true_false {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition true false p : ℂ) = infinityCoordinate p := overlapUnit_inv_val hp

@[simp] theorem data_transition_false_true_coe (z : ℂ) (hz : z ≠ 0) :
    (data.transition false true (z : RiemannSphere) : ℂ) = z := by
  rw [data_transition_false_true ⟨coe_mem_finiteChart z,
    (coe_mem_infinityChart_iff z).mpr hz⟩, finiteCoordinate_coe]

@[simp] theorem data_transition_true_false_coe (z : ℂ) (hz : z ≠ 0) :
    (data.transition true false (z : RiemannSphere) : ℂ) = z⁻¹ := by
  rw [data_transition_true_false ⟨coe_mem_finiteChart z,
    (coe_mem_infinityChart_iff z).mpr hz⟩, infinityCoordinate_coe]

instance data_isHolomorphic : data.IsHolomorphic 𝓘(ℂ) where
  contMDiffOn_transition := transition_holomorphicOn

/-- The native line bundle, with the topology and atlas supplied by the
existing `VectorBundleCore` construction. -/
abbrev bundle := data.core

theorem bundle_contMDiffVectorBundle :
    ContMDiffVectorBundle ω ℂ bundle.Fiber 𝓘(ℂ) := inferInstance

/-- The local numerators of the meromorphic section are both the unit `1`. -/
def numerator (_ : Bool) (_ : RiemannSphere) : ℂ := 1

/-- The local denominator is `1` in the finite chart and the actual
reciprocal coordinate `w` in the infinity chart. -/
def denominator : Bool → RiemannSphere → ℂ
  | false => fun _ => 1
  | true => infinityCoordinate

theorem numerator_holomorphic (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (numerator b) (data.baseSet b) := contMDiffOn_const

theorem denominator_holomorphic (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (denominator b) (data.baseSet b) := by
  cases b
  · exact contMDiffOn_const
  · exact infinityCoordinate_holomorphicOn

theorem numerator_ne_zero (b : Bool) (p : RiemannSphere) : numerator b p ≠ 0 :=
  one_ne_zero

theorem denominator_ne_zero (b : Bool) {p : RiemannSphere}
    (hb : p ∈ data.baseSet b) (hp : p ∈ finiteChart) : denominator b p ≠ 0 := by
  cases b
  · exact one_ne_zero
  · exact infinityCoordinate_ne_zero ⟨hp, hb⟩

/-- The defining Cartier identity holds on the entire actual overlap,
not only after removing the zero of the infinity denominator. -/
theorem fraction_ratio (a b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet a ∩ data.baseSet b) :
    numerator b p * denominator a p =
      (data.transition a b p : ℂ) * numerator a p * denominator b p := by
  cases a <;> cases b
  · simp [numerator, denominator, data_transition, transition]
  · change (1 : ℂ) * 1 = (data.transition false true p : ℂ) * 1 * infinityCoordinate p
    simp only [data_transition_false_true hp, mul_one]
    exact (finiteCoordinate_mul_infinityCoordinate hp).symm
  · change (1 : ℂ) * infinityCoordinate p = (data.transition true false p : ℂ) * 1 * 1
    rw [data_transition_true_false ⟨hp.2, hp.1⟩, one_mul, mul_one, mul_one]
  · simp [numerator, denominator, data_transition, transition]

/-- A genuine Cartier presentation of the sphere base twist: local
fractions `1` and `1 / w`, with dense finite-chart generic set. -/
def cartier : CartierData 𝓘(ℂ) RiemannSphere Bool where
  transitions := data
  isHolomorphic := data_isHolomorphic
  numerator := numerator
  denominator := denominator
  numerator_holomorphic := numerator_holomorphic
  denominator_holomorphic := denominator_holomorphic
  genericSet := finiteChart
  genericSet_dense := finiteChart_dense
  numerator_ne_zero b p _ _ := numerator_ne_zero b p
  denominator_ne_zero b _ hb hp := denominator_ne_zero b hb hp
  ratio := fraction_ratio

@[simp] theorem cartier_transitions : cartier.transitions = data := rfl

@[simp] theorem cartier_genericSet : cartier.genericSet = finiteChart := rfl

@[simp] theorem cartier_numerator (b : Bool) (p : RiemannSphere) :
    cartier.numerator b p = 1 := rfl

@[simp] theorem cartier_denominator_false (p : RiemannSphere) :
    cartier.denominator false p = 1 := rfl

@[simp] theorem cartier_denominator_true (p : RiemannSphere) :
    cartier.denominator true p = infinityCoordinate p := rfl

@[simp] theorem localFraction_false (p : RiemannSphere) :
    cartier.localFraction false p = 1 := by
  change (1 : ℂ) / 1 = 1
  exact div_one 1

@[simp] theorem localFraction_true (p : RiemannSphere) :
    cartier.localFraction true p = (infinityCoordinate p)⁻¹ := one_div _

@[simp] theorem localFraction_infinityParametrization (u : ℂ) :
    cartier.localFraction true (infinityParametrization u) = u⁻¹ := by
  rw [localFraction_true, infinityCoordinate_infinityParametrization]

/-- This is the actual local bundle coefficient of the Cartier section
on the punctured infinity chart, not only a formal fraction expression. -/
theorem rawSection_infinity_coordinate (u : ℂ) (hu : u ≠ 0) :
    data.localCoefficient cartier.rawSection true (infinityParametrization u) = u⁻¹ := by
  calc
    data.localCoefficient cartier.rawSection true (infinityParametrization u) =
        cartier.localFraction true (infinityParametrization u) :=
      cartier.rawSection_localCoefficient true (infinityParametrization_mem u)
        ((infinityParametrization_mem_finiteChart_iff u).mpr hu)
    _ = _ := localFraction_infinityParametrization u

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
