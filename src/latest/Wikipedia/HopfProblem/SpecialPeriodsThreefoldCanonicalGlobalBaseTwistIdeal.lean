import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwist
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealFrames
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealBundleSections

/-!
# Actual local section identification with the O(-infinity) ideal sheaf

On every subopen of either sphere chart, holomorphic sections of the
independently constructed native base-twist bundle correspond to the
actual ideal sections vanishing at infinity.  The correspondence reads
the original bundle coefficient and multiplies by the genuine frame
`1` or `w`.  Its inverse uses the original bundle trivialization inverse.

These identifications commute with literal restrictions in both
directions and agree whenever both chart descriptions are available.
In particular they concern the actual bundle's holomorphic sections,
not a replacement defined to be the ideal sheaf.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open HolomorphicFunctionSheaf.SphereH1

/-- The actual holomorphic sections over an open set, taking values in
the native bundle fibres and holomorphic into the original total space. -/
abbrev BundleSection (U : Opens RiemannSphere) :=
  IdealBundleSections.Section data 𝓘(ℂ) U

/-- Literal restriction of the actual native bundle sections. -/
def bundleSectionRestrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : BundleSection V) : BundleSection U :=
  IdealBundleSections.Section.restrict data 𝓘(ℂ) h s

@[simp] theorem bundleSectionRestrict_apply {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : BundleSection V) (p : U) :
    bundleSectionRestrict h s p = s ⟨(p : RiemannSphere), h p.property⟩ := rfl

/-- The native coefficient identification followed by multiplication
by the already proved actual ideal-sheaf frame. -/
def idealEquiv (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    BundleSection U ≃ NegativeOneSection U :=
  (IdealBundleSections.coefficientEquiv data 𝓘(ℂ) b U (fun _ hp => hU hp)).trans
    (NegativeOneFrames.chartTrivialization b U hU).toEquiv

/-- In every chart this is exactly the ideal frame times the native
bundle coefficient. -/
theorem idealEquiv_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection U) (p : U) :
    (idealEquiv b U hU s).val p =
      (bundle.localTriv b ⟨(p : RiemannSphere), s p⟩).2 * idealFrameValue b p := by
  change (NegativeOneFrames.chartTrivialization b U hU
    (IdealBundleSections.coefficientEquiv data 𝓘(ℂ) b U (fun _ hp => hU hp) s)).val p = _
  exact chartTrivialization_value b U hU _ p

/-- Reconstruction uses the actual fibrewise inverse of the bundle
chart, applied to the ideal section's genuine holomorphic coefficient. -/
theorem idealEquiv_symm_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection U) (p : U) :
    (idealEquiv b U hU).symm f p =
      (bundle.localTriv b).symm (p : RiemannSphere)
        ((NegativeOneFrames.chartTrivialization b U hU).symm f p) := rfl

/-- The genuine native bundle frame is reconstructed from the constant
coefficient one by the original bundle chart inverse. -/
def nativeFrame (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) : BundleSection U :=
  (IdealBundleSections.coefficientEquiv data 𝓘(ℂ) b U (fun _ hp => hU hp)).symm 1

@[simp] theorem nativeFrame_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (p : U) :
    nativeFrame b U hU p = (bundle.localTriv b).symm (p : RiemannSphere) 1 := rfl

/-- Its coefficient in its actual bundle trivialization is literally one. -/
theorem nativeFrame_localCoefficient (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (p : U) :
    (bundle.localTriv b ⟨(p : RiemannSphere), nativeFrame b U hU p⟩).2 = 1 :=
  congrArg Prod.snd ((bundle.localTriv b).apply_mk_symm (hU p.property) 1)

/-- The section identification sends the genuine native unit frame
to the existing ideal-sheaf frame `1` or `w`, not to an arbitrary generator. -/
theorem idealEquiv_nativeFrame (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    idealEquiv b U hU (nativeFrame b U hU) = NegativeOneFrames.chartFrame b U hU := by
  change NegativeOneFrames.chartTrivialization b U hU
    ((IdealBundleSections.coefficientEquiv data 𝓘(ℂ) b U (fun _ hp => hU hp))
      ((IdealBundleSections.coefficientEquiv data 𝓘(ℂ) b U
        (fun _ hp => hU hp)).symm 1)) = _
  rw [Equiv.apply_symm_apply, NegativeOneFrames.chartTrivialization_as_frame, one_smul]

/-- The actual ideal frame reconstructs the native bundle unit frame. -/
theorem idealEquiv_symm_chartFrame (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    (idealEquiv b U hU).symm (NegativeOneFrames.chartFrame b U hU) =
      nativeFrame b U hU := by
  apply (idealEquiv b U hU).injective
  rw [Equiv.apply_symm_apply, idealEquiv_nativeFrame]

/-- In particular the inverse ideal-frame image has native coefficient
one even at infinity, where its underlying ideal function vanishes. -/
theorem idealEquiv_symm_chartFrame_localCoefficient (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (p : U) :
    (bundle.localTriv b ⟨(p : RiemannSphere),
      (idealEquiv b U hU).symm (NegativeOneFrames.chartFrame b U hU) p⟩).2 = 1 := by
  rw [idealEquiv_symm_chartFrame]
  exact nativeFrame_localCoefficient b U hU p

/-- The ideal frame value is the actual local denominator of the
constructed base-twist Cartier presentation. -/
theorem idealFrameValue_eq_denominator (b : Bool) (p : RiemannSphere) :
    idealFrameValue b p = denominator b p := by
  cases b <;> rfl

/-- The actual ideal frames transform by the coefficient cocycle of
the independently constructed base-twist bundle. -/
theorem idealFrameValue_transition (a b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet a ∩ data.baseSet b) :
    idealFrameValue a p = (data.transition a b p : ℂ) * idealFrameValue b p := by
  rw [idealFrameValue_eq_denominator, idealFrameValue_eq_denominator]
  simpa only [numerator, one_mul, mul_one] using fraction_ratio a b p hp

/-- Native chart coefficients obey the original bundle cocycle,
including when the section's preferred chart is a third choice. -/
theorem bundleSection_coefficient_change (a b : Bool) (U : Opens RiemannSphere)
    (ha : U ≤ NegativeOneFrames.frameChart a) (hb : U ≤ NegativeOneFrames.frameChart b)
    (s : BundleSection U) (p : U) :
    (bundle.localTriv b ⟨(p : RiemannSphere), s p⟩).2 =
      (data.transition a b p : ℂ) * (bundle.localTriv a ⟨(p : RiemannSphere), s p⟩).2 := by
  have hc := congrArg (fun u : ℂˣ => (u : ℂ))
    (data.transition_comp (data.indexAt p) a b p
      ⟨⟨data.mem_baseSet_at p, ha p.property⟩, hb p.property⟩)
  change (data.transition a b p : ℂ) * (data.transition (data.indexAt p) a p : ℂ) =
    (data.transition (data.indexAt p) b p : ℂ) at hc
  change (data.transition (data.indexAt p) b p : ℂ) * id (α := ℂ) (s p) =
    (data.transition a b p : ℂ) *
      ((data.transition (data.indexAt p) a p : ℂ) * id (α := ℂ) (s p))
  rw [← mul_assoc, hc]

/-- Both charts give the same actual ideal section on every common
subopen; the comparison is not dependent on a choice of frame. -/
theorem idealEquiv_chart_independent (a b : Bool) (U : Opens RiemannSphere)
    (ha : U ≤ NegativeOneFrames.frameChart a) (hb : U ≤ NegativeOneFrames.frameChart b)
    (s : BundleSection U) : idealEquiv a U ha s = idealEquiv b U hb s := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rw [idealEquiv_apply, idealEquiv_apply,
    bundleSection_coefficient_change a b U ha hb s p,
    idealFrameValue_transition a b p ⟨ha p.property, hb p.property⟩]
  rw [← mul_assoc, mul_comm (bundle.localTriv a ⟨(p : RiemannSphere), s p⟩).2]

/-- The native-to-ideal identification commutes with every literal
restriction inside a chart. -/
theorem idealEquiv_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (idealEquiv b V hV s) =
      idealEquiv b U (h.trans hV) (bundleSectionRestrict h s) := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  change (idealEquiv b V hV s).val ⟨(p : RiemannSphere), h p.property⟩ =
    (idealEquiv b U (h.trans hV) (bundleSectionRestrict h s)).val p
  rw [idealEquiv_apply, idealEquiv_apply]
  rfl

/-- Inverse reconstruction also commutes with every literal restriction. -/
theorem idealEquiv_symm_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection V) :
    (idealEquiv b U (h.trans hV)).symm (negativeOneRestriction h f) =
      bundleSectionRestrict h ((idealEquiv b V hV).symm f) := by
  apply (idealEquiv b U (h.trans hV)).injective
  rw [Equiv.apply_symm_apply, ← idealEquiv_restrict b h hV, Equiv.apply_symm_apply]

/-- Restricting a chart description and then changing to another valid
chart gives the same actual ideal section. -/
theorem idealEquiv_restrict_change_chart (a b : Bool) {U V : Opens RiemannSphere}
    (h : U ≤ V) (hV : V ≤ NegativeOneFrames.frameChart a)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (idealEquiv a V hV s) =
      idealEquiv b U hU (bundleSectionRestrict h s) := by
  rw [idealEquiv_restrict]
  exact idealEquiv_chart_independent a b U (h.trans hV) hU _

/-- Every point has an actual chart neighborhood on all of whose subopens
the native bundle sections agree with the literal O(-infinity) ideal sections. -/
theorem native_bundle_locally_identifies_ideal (p : RiemannSphere) :
    ∃ b : Bool, p ∈ NegativeOneFrames.frameChart b ∧
      ∀ (U : Opens RiemannSphere) (_hU : U ≤ NegativeOneFrames.frameChart b),
        Nonempty (BundleSection U ≃ NegativeOneSection U) := by
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact ⟨b, hb, fun U hU => ⟨idealEquiv b U hU⟩⟩

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
