import Wikipedia.HopfProblem.HolomorphicMeromorphicScalarBasic

/-!
# Realizing scalar meromorphic germs by genuine native sections

Two actual analytic germs with nonzero denominator give a fraction of
native holomorphic sections on an original open neighborhood. The native
nonzero-germ theorem supplies a smaller neighborhood on which this is a
genuine meromorphic section. Applying this to the analytic power-clearing
representation in Mathlib's definition of `MeromorphicAt` gives the
converse to the scalar representative construction.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

/-- Every actual analytic fraction germ is the scalar representative of
a genuine native meromorphic section on an open neighborhood. -/
theorem exists_section_of_analytic_fraction {p q : ℂ → ℂ} {x : ℂ}
    (hp : AnalyticAt ℂ p x) (hq : AnalyticAt ℂ q x) (hqne : ¬ q =ᶠ[𝓝 x] 0) :
    ∃ (U : Opens ℂ) (_hx : x ∈ U) (s : Section 𝓘(ℂ) ℂ U),
      scalarValue s =ᶠ[𝓝[≠] x] fun z => p z / q z := by
  let U : Opens ℂ := ⟨{z | AnalyticAt ℂ p z} ∩ {z | AnalyticAt ℂ q z},
    (isOpen_analyticAt ℂ p).inter (isOpen_analyticAt ℂ q)⟩
  have hxU : x ∈ U := ⟨hp, hq⟩
  let pU : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ U :=
    ⟨fun z => p z.val, fun z =>
      contMDiffAt_subtype_iff.mpr z.property.1.contDiffAt.contMDiffAt⟩
  let qU : HolomorphicFunctionSheaf.Section 𝓘(ℂ) ℂ U :=
    ⟨fun z => q z.val, fun z =>
      contMDiffAt_subtype_iff.mpr z.property.2.contDiffAt.contMDiffAt⟩
  have hqU : holomorphicGerm 𝓘(ℂ) ℂ U ⟨x, hxU⟩ qU ≠ 0 := by
    intro hzero
    have he := HolomorphicFunctionSheaf.extendSection_eventuallyEq U qU x hxU q
      (fun _ _ => rfl)
    exact hqne (he.symm.trans
      ((holomorphicGerm_eq_zero_iff_extendSection_eventuallyEq_zero U qU x hxU).mp hzero))
  obtain ⟨V, hVU, hxV, hqV⟩ :=
    HolomorphicFunctionSheaf.exists_open_restriction_germs_ne_zero 𝓘(ℂ) U qU x hxU hqU
  let pV := HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) ℂ hVU pU
  let qV := HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) ℂ hVU qU
  have hqV' : ∀ z : V, holomorphicGerm 𝓘(ℂ) ℂ V z qV ≠ 0 := hqV
  let s := ofFraction 𝓘(ℂ) ℂ V pV qV hqV'
  refine ⟨V, hxV, s, ?_⟩
  have he := scalarValue_eventuallyEq_local_fraction s le_rfl pV qV x hxV
    (hqV' ⟨x, hxV⟩) (fun _ => rfl)
  filter_upwards [he, nhdsWithin_le_nhds (V.isOpen.mem_nhds hxV)] with z hz hzV
  rw [HolomorphicFunctionSheaf.extendSection_apply V pV z hzV,
    HolomorphicFunctionSheaf.extendSection_apply V qV z hzV] at hz
  exact hz

/-- A genuine scalar meromorphic germ is realized by a section of the
native meromorphic sheaf, with equality on a punctured neighborhood. -/
theorem exists_section_of_meromorphicAt {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    ∃ (U : Opens ℂ) (_hx : x ∈ U) (s : Section 𝓘(ℂ) ℂ U),
      scalarValue s =ᶠ[𝓝[≠] x] f := by
  obtain ⟨m, hm⟩ := hf
  have hp : AnalyticAt ℂ (fun z : ℂ => (z - x) ^ m * f z) x := by
    simpa only [smul_eq_mul] using hm
  have hq : AnalyticAt ℂ (fun z : ℂ => (z - x) ^ m) x :=
    (analyticAt_id.sub analyticAt_const).pow m
  have hqne : ¬ (fun z : ℂ => (z - x) ^ m) =ᶠ[𝓝 x] 0 := by
    intro hzero
    have hne : ∀ᶠ z in 𝓝[≠] x, (z - x) ^ m ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact pow_ne_zero m (sub_ne_zero.mpr hz)
    obtain ⟨z, hz, hzn⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and hne).exists
    exact hzn hz
  obtain ⟨U, hx, s, hs⟩ := exists_section_of_analytic_fraction hp hq hqne
  refine ⟨U, hx, s, hs.trans ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact mul_div_cancel_left₀ (f z) (pow_ne_zero m (sub_ne_zero.mpr hz))

/-- The native local sheaf and scalar `MeromorphicAt` describe the same
germs, with the ordinary punctured-neighborhood notion of equality. -/
theorem meromorphicAt_iff_exists_section {f : ℂ → ℂ} {x : ℂ} :
    MeromorphicAt f x ↔
      ∃ (U : Opens ℂ) (_hx : x ∈ U) (s : Section 𝓘(ℂ) ℂ U),
        scalarValue s =ᶠ[𝓝[≠] x] f := by
  refine ⟨exists_section_of_meromorphicAt, ?_⟩
  rintro ⟨U, hx, s, hs⟩
  exact (scalarValue_meromorphicAt s x hx).congr hs

end Wikipedia.HopfProblem.HolomorphicMeromorphic
