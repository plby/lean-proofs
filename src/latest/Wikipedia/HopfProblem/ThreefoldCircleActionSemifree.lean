import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedLocus
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.DenseEmbedding

/-!
# The original circle action is free away from its fixed curve

The circle is the original period-one real-time quotient, acting through the
already constructed multiplicative action. A nonzero finite-order parameter
has exactly the proved fixed curve. An infinite-order parameter generates a
dense subgroup of the circle, so continuity forces any of its fixed points
to be fixed by every circle parameter, including the original half-turn.

Thus every nonidentity circle element fixes precisely the original `D₀`.
This gives the genuine semifree action, not an inference from normal weights.
No assertion about the global orbit space or sphere recognition is made.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CircleActionSemifree

open Homology.DeltaSweep VerticalAction.Exponential

local notation "Circle" => PeriodTorusHigherHomology.CircleTopology.Circle

attribute [local instance] Threefold.space_t2Space

/-- The actual circle parameter has precisely its original integral kernel. -/
theorem circleParameter_eq_one_iff (t : Circle) : circleParameter t = 1 ↔ t = 0 := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [circleParameter_real, normalizedExponential_eq_one_iff, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hr : s = (k : ℝ) := by
      simpa only [Complex.ofReal_re, Complex.intCast_re] using congrArg Complex.re hk
    simpa only [zsmul_one] using hr.symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hr : s = (k : ℝ) := by simpa only [zsmul_one] using hk.symm
    simpa only [Complex.ofReal_intCast] using congrArg Complex.ofReal hr

/-- Distinct original circle parameters give distinct nonzero complex scalars. -/
theorem circleParameter_injective : Function.Injective circleParameter := by
  intro s t h
  apply sub_eq_zero.mp
  apply (circleParameter_eq_one_iff (s - t)).mp
  change circleParameterAddHom (s - t) = 0
  rw [map_sub, show circleParameterAddHom s = circleParameterAddHom t from
    congrArg Additive.ofMul h, sub_self]

theorem circleParameter_isOfFinOrder {t : Circle} (ht : IsOfFinAddOrder t) :
    IsOfFinOrder (circleParameter t) := by
  obtain ⟨n, hn, hnt⟩ := ht.exists_nsmul_eq_zero
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have h := congrArg Additive.toMul (circleParameterAddHom.map_nsmul n t)
  change circleParameter (n • t) = circleParameter t ^ n at h
  rw [hnt, circleParameter_zero] at h
  exact h.symm

/-- A nonzero finite-order parameter fixes exactly the original cusp curve. -/
theorem finite_actionMap_fixed_iff (t : Circle) (ht : t ≠ 0)
    (hfin : IsOfFinAddOrder t) (x : Space) :
    actionMap (t, x) = x ↔ x ∈ VerticalAction.D₀ := by
  exact FiniteActionFixed.actionBiholomorph_fixed_iff_D₀ (circleParameter t)
    (fun h => ht ((circleParameter_eq_one_iff t).mp h))
    (circleParameter_isOfFinOrder hfin) x

/-- Fixing an infinite-order circle parameter forces every circle parameter to fix the point. -/
theorem actionMap_fixed_all_of_infinite_order (t : Circle)
    (ht : ¬ IsOfFinAddOrder t) (x : Space) (hx : actionMap (t, x) = x) :
    ∀ s : Circle, actionMap (s, x) = x := by
  let := circleAction
  have hmem : t ∈ AddAction.stabilizer Circle x := hx
  have hd : DenseRange (fun n : ℤ => n • t) :=
    AddCircle.denseRange_zsmul_iff.mpr (addOrderOf_eq_zero ht)
  have heq : (fun s : Circle => actionMap (s, x)) = fun _ => x := by
    apply hd.equalizer (actionMap.continuous.comp (continuous_id.prodMk continuous_const))
      continuous_const
    funext n
    exact (AddAction.stabilizer Circle x).zsmul_mem hmem n
  exact fun s => congrFun heq s

/-- Every nonidentity element of the actual circle has precisely the same fixed curve. -/
theorem actionMap_fixed_iff (t : Circle) (ht : t ≠ 0) (x : Space) :
    actionMap (t, x) = x ↔ x ∈ VerticalAction.D₀ := by
  constructor
  · intro hx
    by_cases hfin : IsOfFinAddOrder t
    · exact (finite_actionMap_fixed_iff t ht hfin x).mp hx
    · have hall := actionMap_fixed_all_of_infinite_order t hfin x hx
      have hhalf := hall ((FiniteActionFixed.generatorTime 2 : ℝ) : Circle)
      exact (FiniteActionFixed.actionBiholomorph_fixed_iff_D₀
        (FiniteActionFixed.standardRoot 2) (FiniteActionFixed.standardRoot_ne_one (by decide))
        (FiniteActionFixed.standardRoot_isOfFinOrder (by decide)) x).mp hhalf
  · intro hx
    exact (VerticalAction.action_fixed_iff x).mpr hx (circleParameter t)

/-- Off the actual fixed curve, a circle parameter fixes a point only when it is zero. -/
theorem actionMap_eq_self_iff (x : Space) (hx : x ∉ VerticalAction.D₀) (t : Circle) :
    actionMap (t, x) = x ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact hx ((actionMap_fixed_iff t ht x).mp h)
  · rintro rfl
    let := circleAction
    exact zero_vadd Circle x

/-- The literal original circle orbit has no repeated parameters away from the fixed curve. -/
theorem orbitMap_injective (x : Space) (hx : x ∉ VerticalAction.D₀) :
    Function.Injective (fun t : Circle => actionMap (t, x)) := by
  let := circleAction
  intro s t h
  have h' : s +ᵥ x = t +ᵥ x := h
  have hfix : (-t + s) +ᵥ x = x := by
    rw [add_vadd, h', neg_vadd_vadd]
  have hz := (actionMap_eq_self_iff x hx (-t + s)).mp hfix
  simpa only [neg_add_eq_sub, sub_eq_zero] using hz

/-- The native fixed-point set of the entire additive circle is the original curve. -/
theorem fixedPoints_eq_D₀ :
    letI := circleAction
    AddAction.fixedPoints Circle Space = VerticalAction.D₀ := by
  let := circleAction
  ext x
  constructor
  · intro hx
    exact (actionMap_fixed_iff PeriodTorusHigherHomology.CircleTopology.halfPoint
      PeriodTorusHigherHomology.CircleTopology.halfPoint_ne_zero x).mp
        (hx PeriodTorusHigherHomology.CircleTopology.halfPoint)
  · intro hx t
    exact (VerticalAction.action_fixed_iff x).mpr hx (circleParameter t)

/-- Every nonfixed orbit is an actual closed embedded circle in the original space. -/
theorem orbitMap_isClosedEmbedding (x : Space) (hx : x ∉ VerticalAction.D₀) :
    Topology.IsClosedEmbedding (fun t : Circle => actionMap (t, x)) :=
  (actionMap.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
    (orbitMap_injective x hx)

/-- The native orbit, with its actual subspace topology, is homeomorphic to the circle. -/
def orbitHomeomorph (x : Space) (hx : x ∉ VerticalAction.D₀) :
    Circle ≃ₜ Set.range (fun t : Circle => actionMap (t, x)) :=
  (orbitMap_isClosedEmbedding x hx).isEmbedding.toHomeomorph

@[simp] theorem orbitHomeomorph_apply (x : Space) (hx : x ∉ VerticalAction.D₀)
    (t : Circle) : (orbitHomeomorph x hx t : Space) = actionMap (t, x) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CircleActionSemifree
