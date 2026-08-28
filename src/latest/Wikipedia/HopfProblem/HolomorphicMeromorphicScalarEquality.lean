import Wikipedia.HopfProblem.HolomorphicMeromorphicScalarBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentativeEqualityAnalytic

/-!
# Scalar punctured germs detect native meromorphic germs

The analytic cross-product identity detects equality in the original
holomorphic stalk and hence in its fraction field. Consequently the
canonical scalar representatives determine native meromorphic germs,
including at poles and across different actual open section domains.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

/-- Punctured scalar agreement of two genuine local fractions detects
equality in the original native meromorphic stalk. -/
theorem fraction_eq_of_scalar_fraction_eventuallyEq (U : Opens ℂ)
    (p q r s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ U)
    (x : ℂ) (hx : x ∈ U)
    (hq : holomorphicGerm 𝓘(ℂ) ℂ U ⟨x, hx⟩ q ≠ 0)
    (hs : holomorphicGerm 𝓘(ℂ) ℂ U ⟨x, hx⟩ s ≠ 0)
    (he : (fun z => HolomorphicFunctionSheaf.extendSection U p z /
        HolomorphicFunctionSheaf.extendSection U q z) =ᶠ[𝓝[≠] x]
      (fun z => HolomorphicFunctionSheaf.extendSection U r z /
        HolomorphicFunctionSheaf.extendSection U s z)) :
    fraction 𝓘(ℂ) ℂ U p q ⟨x, hx⟩ = fraction 𝓘(ℂ) ℂ U r s ⟨x, hx⟩ := by
  apply (fraction_eq_iff_cross_germ_zero 𝓘(ℂ) ℂ U p q r s ⟨x, hx⟩ hq hs).mpr
  apply (holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero
    U (p * s - r * q) x hx).mpr
  have hq' : ¬ HolomorphicFunctionSheaf.extendSection U q =ᶠ[𝓝 x] 0 := fun h =>
    hq ((holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero U q x hx).mpr h)
  have hs' : ¬ HolomorphicFunctionSheaf.extendSection U s =ᶠ[𝓝 x] 0 := fun h =>
    hs ((holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero U s x hx).mpr h)
  have hcross := SphereRepresentative.analytic_cross_eventuallyEq_zero_of_fraction_eventuallyEq
    (HolomorphicFunctionSheaf.extendSection_analyticAt U p x hx)
    (HolomorphicFunctionSheaf.extendSection_analyticAt U q x hx)
    (HolomorphicFunctionSheaf.extendSection_analyticAt U r x hx)
    (HolomorphicFunctionSheaf.extendSection_analyticAt U s x hx) hq' hs' he
  filter_upwards [U.isOpen.mem_nhds hx, hcross] with z hz hcz
  rw [HolomorphicFunctionSheaf.extendSection_apply U (p * s - r * q) z hz]
  change p ⟨z, hz⟩ * s ⟨z, hz⟩ - r ⟨z, hz⟩ * q ⟨z, hz⟩ = 0
  simpa only [HolomorphicFunctionSheaf.extendSection_apply U p z hz,
    HolomorphicFunctionSheaf.extendSection_apply U q z hz,
    HolomorphicFunctionSheaf.extendSection_apply U r z hz,
    HolomorphicFunctionSheaf.extendSection_apply U s z hz, Pi.zero_apply] using hcz

/-- Scalar punctured agreement detects the native germ for sections on
the same original plane domain. -/
theorem germ_eq_of_scalarValue_eventuallyEq_on {U : Opens ℂ}
    (s t : Section 𝓘(ℂ) ℂ U) (x : ℂ) (hx : x ∈ U)
    (he : scalarValue s =ᶠ[𝓝[≠] x] scalarValue t) : s ⟨x, hx⟩ = t ⟨x, hx⟩ := by
  obtain ⟨V, hVU, hxV, p, q, r, a, hq, ha, hs, ht⟩ :=
    common_local_representation 𝓘(ℂ) ℂ s t ⟨x, hx⟩
  have hs' := scalarValue_eventuallyEq_local_fraction s hVU p q x hxV (hq ⟨x, hxV⟩) hs
  have ht' := scalarValue_eventuallyEq_local_fraction t hVU r a x hxV (ha ⟨x, hxV⟩) ht
  have hfrac := fraction_eq_of_scalar_fraction_eventuallyEq V p q r a x hxV
    (hq ⟨x, hxV⟩) (ha ⟨x, hxV⟩) (hs'.symm.trans (he.trans ht'))
  exact (hs ⟨x, hxV⟩).trans (hfrac.trans (ht ⟨x, hxV⟩).symm)

/-- Scalar punctured agreement detects native meromorphic germs even
when their sections are defined on different open neighborhoods. -/
theorem germ_eq_of_scalarValue_eventuallyEq {U V : Opens ℂ}
    (s : Section 𝓘(ℂ) ℂ U) (t : Section 𝓘(ℂ) ℂ V)
    (x : ℂ) (hxU : x ∈ U) (hxV : x ∈ V)
    (he : scalarValue s =ᶠ[𝓝[≠] x] scalarValue t) : s ⟨x, hxU⟩ = t ⟨x, hxV⟩ := by
  let W : Opens ℂ := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hs : scalarValue (restrict 𝓘(ℂ) ℂ hWU s) =ᶠ[𝓝[≠] x] scalarValue s :=
    (scalarValue_restrict_eventuallyEq hWU s x hxW).filter_mono nhdsWithin_le_nhds
  have ht : scalarValue (restrict 𝓘(ℂ) ℂ hWV t) =ᶠ[𝓝[≠] x] scalarValue t :=
    (scalarValue_restrict_eventuallyEq hWV t x hxW).filter_mono nhdsWithin_le_nhds
  exact germ_eq_of_scalarValue_eventuallyEq_on (restrict 𝓘(ℂ) ℂ hWU s)
    (restrict 𝓘(ℂ) ℂ hWV t) x hxW (hs.trans (he.trans ht.symm))

/-- Equal native germs have equal canonical ordinary values, including
the convention of zero at a nonregular germ. -/
theorem scalarValue_eq_of_germ_eq {U V : Opens ℂ}
    (s : Section 𝓘(ℂ) ℂ U) (t : Section 𝓘(ℂ) ℂ V)
    (x : ℂ) (hxU : x ∈ U) (hxV : x ∈ V) (he : s ⟨x, hxU⟩ = t ⟨x, hxV⟩) :
    scalarValue s x = scalarValue t x := by
  classical
  rw [scalarValue_apply s x hxU, scalarValue_apply t x hxV]
  let ev : Germ 𝓘(ℂ) ℂ x → ℂ := fun a =>
    if h : ∃ p : HolomorphicStalk 𝓘(ℂ) ℂ x, ofHolomorphicGerm 𝓘(ℂ) ℂ x p = a then
      HolomorphicFunctionSheaf.stalkEval 𝓘(ℂ) ℂ x (Classical.choose h) else 0
  exact congrArg ev he

/-- Equal native germs have equal scalar representatives on a genuine
neighborhood, not only on its punctured part. -/
theorem scalarValue_eventuallyEq_of_germ_eq {U V : Opens ℂ}
    (s : Section 𝓘(ℂ) ℂ U) (t : Section 𝓘(ℂ) ℂ V)
    (x : ℂ) (hxU : x ∈ U) (hxV : x ∈ V) (he : s ⟨x, hxU⟩ = t ⟨x, hxV⟩) :
    scalarValue s =ᶠ[𝓝 x] scalarValue t := by
  obtain ⟨W, hWU, hWV, hxW, hW⟩ :=
    exists_neighborhood_eq_of_germ_eq 𝓘(ℂ) ℂ s t x hxU hxV he
  filter_upwards [W.isOpen.mem_nhds hxW] with z hz
  exact scalarValue_eq_of_germ_eq s t z (hWU hz) (hWV hz) (hW ⟨z, hz⟩)

/-- Native meromorphic germs are precisely detected by the ordinary
punctured scalar representatives. -/
theorem germ_eq_iff_scalarValue_eventuallyEq {U V : Opens ℂ}
    (s : Section 𝓘(ℂ) ℂ U) (t : Section 𝓘(ℂ) ℂ V)
    (x : ℂ) (hxU : x ∈ U) (hxV : x ∈ V) :
    s ⟨x, hxU⟩ = t ⟨x, hxV⟩ ↔ scalarValue s =ᶠ[𝓝[≠] x] scalarValue t := by
  refine ⟨?_, germ_eq_of_scalarValue_eventuallyEq s t x hxU hxV⟩
  intro h
  exact (scalarValue_eventuallyEq_of_germ_eq s t x hxU hxV h).filter_mono nhdsWithin_le_nhds

/-- The canonical scalar representative forgets no native meromorphic
section on any open plane domain. No connectedness assumption is needed. -/
theorem scalarValue_injective (U : Opens ℂ) :
    _root_.Function.Injective (scalarValue (U := U)) := by
  intro s t h
  apply section_ext
  intro x
  exact germ_eq_of_scalarValue_eventuallyEq_on s t x.val x.property
    (Filter.Eventually.of_forall fun z => congrFun h z)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
