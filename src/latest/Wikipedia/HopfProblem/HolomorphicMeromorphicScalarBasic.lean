import Wikipedia.HopfProblem.HolomorphicMeromorphicValue
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Scalar representatives of genuine meromorphic sections on the complex plane

The scalar representative is the native ordinary value on the actual
open domain, extended by zero outside it. Every local fraction agrees
with this representative on a punctured neighborhood, by isolated zeros
of its genuinely nonzero holomorphic denominator germ.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

/-- Native ordinary values on an actual plane domain, extended by zero
outside that domain. The full meromorphic section retains its pole germs. -/
def scalarValue {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then value 𝓘(ℂ) ℂ s ⟨z, hz⟩ else 0

@[simp] theorem scalarValue_apply {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∈ U) : scalarValue s z = value 𝓘(ℂ) ℂ s ⟨z, hz⟩ := by
  classical
  simp only [scalarValue, dif_pos hz]

@[simp] theorem scalarValue_of_not_mem {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∉ U) : scalarValue s z = 0 := by
  classical
  simp only [scalarValue, dif_neg hz]

theorem scalarValue_restrict {U V : Opens ℂ} (hUV : U ≤ V)
    (s : Section 𝓘(ℂ) ℂ V) (z : ℂ) (hz : z ∈ U) :
    scalarValue (restrict 𝓘(ℂ) ℂ hUV s) z = scalarValue s z := by
  rw [scalarValue_apply _ z hz, scalarValue_apply s z (hUV hz)]
  rfl

theorem scalarValue_restrict_eventuallyEq {U V : Opens ℂ} (hUV : U ≤ V)
    (s : Section 𝓘(ℂ) ℂ V) (z : ℂ) (hz : z ∈ U) :
    scalarValue (restrict 𝓘(ℂ) ℂ hUV s) =ᶠ[𝓝 z] scalarValue s := by
  filter_upwards [U.isOpen.mem_nhds hz] with w hw
  exact scalarValue_restrict hUV s w hw

/-- Vanishing of a native holomorphic stalk germ is vanishing of the
literal ambient section extension on a neighborhood. -/
theorem holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero
    (U : Opens ℂ) (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∈ U) :
    holomorphicGerm 𝓘(ℂ) ℂ U ⟨z, hz⟩ p = 0 ↔
      HolomorphicFunctionSheaf.extendSection U p =ᶠ[𝓝 z] 0 :=
  HolomorphicFunctionSheaf.germ_eq_zero_iff_extend_eventuallyEq_zero 𝓘(ℂ) U p z hz

/-- A genuinely nonzero plane denominator germ is nonzero on a small
punctured neighborhood, even if its value at the center is zero. -/
theorem extendSection_eventually_ne_zero_of_holomorphicGerm_ne_zero
    (U : Opens ℂ) (q : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∈ U) (hq : holomorphicGerm 𝓘(ℂ) ℂ U ⟨z, hz⟩ q ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, HolomorphicFunctionSheaf.extendSection U q w ≠ 0 := by
  have ha := HolomorphicFunctionSheaf.extendSection_analyticAt U q z hz
  apply ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro hzero
  exact hq ((holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero U q z hz).mpr hzero)

/-- Canonical scalar values agree with every actual local fraction on a
punctured neighborhood of the base point. -/
theorem scalarValue_eventuallyEq_local_fraction {U V : Opens ℂ}
    (s : Section 𝓘(ℂ) ℂ U) (hVU : V ≤ U)
    (p q : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ V)
    (z : ℂ) (hz : z ∈ V) (hq : holomorphicGerm 𝓘(ℂ) ℂ V ⟨z, hz⟩ q ≠ 0)
    (hs : ∀ y : V, s (Set.inclusion hVU y) = fraction 𝓘(ℂ) ℂ V p q y) :
    scalarValue s =ᶠ[𝓝[≠] z] fun w =>
      HolomorphicFunctionSheaf.extendSection V p w /
        HolomorphicFunctionSheaf.extendSection V q w := by
  filter_upwards [nhdsWithin_le_nhds (V.isOpen.mem_nhds hz),
    extendSection_eventually_ne_zero_of_holomorphicGerm_ne_zero V q z hz hq] with w hw hqw
  rw [HolomorphicFunctionSheaf.extendSection_apply V q w hw] at hqw
  rw [scalarValue_apply s w (hVU hw),
    HolomorphicFunctionSheaf.extendSection_apply V p w hw,
    HolomorphicFunctionSheaf.extendSection_apply V q w hw]
  exact value_eq_local_fraction 𝓘(ℂ) ℂ s p q w (hVU hw) hw (hs ⟨w, hw⟩) hqw

/-- Scalar local analytic numerator and denominator germs are obtained
from the genuine native local fraction presentation. -/
theorem exists_scalarValue_local_fraction {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∈ U) :
    ∃ p q : ℂ → ℂ, AnalyticAt ℂ p z ∧ AnalyticAt ℂ q z ∧
      ¬ q =ᶠ[𝓝 z] 0 ∧ scalarValue s =ᶠ[𝓝[≠] z] fun w => p w / q w := by
  obtain ⟨V, hVU, hzV, p, q, hq, hs⟩ := local_representation 𝓘(ℂ) ℂ s ⟨z, hz⟩
  refine ⟨HolomorphicFunctionSheaf.extendSection V p,
    HolomorphicFunctionSheaf.extendSection V q,
    HolomorphicFunctionSheaf.extendSection_analyticAt V p z hzV,
    HolomorphicFunctionSheaf.extendSection_analyticAt V q z hzV, ?_, ?_⟩
  · intro hzero
    exact hq ⟨z, hzV⟩
      ((holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero V q z hzV).mpr hzero)
  · exact scalarValue_eventuallyEq_local_fraction s hVU p q z hzV (hq ⟨z, hzV⟩) hs

/-- The canonical scalar representative is Mathlib-meromorphic at every
point of the original native section domain. -/
theorem scalarValue_meromorphicAt {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : ℂ) (hz : z ∈ U) : MeromorphicAt (scalarValue s) z := by
  obtain ⟨p, q, hp, hq, _, he⟩ := exists_scalarValue_local_fraction s z hz
  exact (hp.meromorphicAt.div hq.meromorphicAt).congr he.symm

theorem scalarValue_meromorphicOn {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U) :
    MeromorphicOn (scalarValue s) U := fun z hz => scalarValue_meromorphicAt s z hz

end Wikipedia.HopfProblem.HolomorphicMeromorphic
