import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Bases

/-!
# One-dimensional parameter identity for holomorphic product charts

A nonzero analytic function on a product chart has at most countably many
whole slices on which it vanishes, when the parameter is one-dimensional.
For analytic numerator and denominator functions, genuine quotient agreement
on the denominator's nonzero locus gives the same conclusion for the
cross-multiplication identity.  Only ordinary analytic functions and the
analytic identity principle are used here.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicSlices

/-- The zeros of a nonzero analytic function on a preconnected subset of
the complex plane form a countable set. -/
theorem countable_zero_set {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ a ∈ U, f a ≠ 0) :
    Set.Countable {z | z ∈ U ∧ f z = 0} := by
  obtain ⟨a, ha, hfa⟩ := hne
  have hz := hf.preimage_zero_mem_codiscreteWithin hfa ha ⟨⟨a, ha⟩, hU⟩
  have hd : IsDiscrete ((f ⁻¹' {0}) ∩ U) :=
    isDiscrete_of_codiscreteWithin (by simpa only [preimage_compl] using hz)
  let := isDiscrete_iff_discreteTopology.mp hd
  have hc : Countable {z : ℂ // z ∈ (f ⁻¹' {0}) ∩ U} :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hs : Set.Countable ((f ⁻¹' {0}) ∩ U) := Set.countable_coe_iff.mp hc
  apply hs.mono
  intro z hz
  exact ⟨hz.2, hz.1⟩

/-- Uncountably many zeros force an analytic function of one complex
parameter to vanish throughout its preconnected domain. -/
theorem eqOn_zero_of_uncountable {U S : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hSU : S ⊆ U) (hS : ¬ S.Countable) (hzero : EqOn f 0 S) :
    EqOn f 0 U := by
  intro a ha
  by_contra hfa
  apply hS
  apply (countable_zero_set hU hf ⟨a, ha, hfa⟩).mono
  intro z hz
  exact ⟨hSU hz, hzero hz⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero analytic function on a product has only countably many
identically zero slices in the complex parameter. -/
theorem countable_zero_slices {U : Set ℂ} {V : Set E} {F : ℂ × E → ℂ}
    (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F (U ×ˢ V))
    (hne : ∃ a ∈ U, ∃ v ∈ V, F (a, v) ≠ 0) :
    Set.Countable {z | z ∈ U ∧ ∀ v ∈ V, F (z, v) = 0} := by
  obtain ⟨a, ha, v, hv, hne⟩ := hne
  have hs : AnalyticOnNhd ℂ (fun z => F (z, v)) U :=
    fun z hz => (hF (z, v) ⟨hz, hv⟩).curry_left
  apply (countable_zero_set hU hs ⟨a, ha, hne⟩).mono
  intro z hz
  exact ⟨hz.1, hz.2 v hv⟩

/-- Uncountably many whole zero slices determine the analytic function
on the entire product. -/
theorem eqOn_zero_of_uncountable_zero_slices {U S : Set ℂ} {V : Set E}
    {F : ℂ × E → ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ V)) (hSU : S ⊆ U)
    (hS : ¬ S.Countable) (hzero : ∀ z ∈ S, ∀ v ∈ V, F (z, v) = 0) :
    EqOn F 0 (U ×ˢ V) := by
  rintro ⟨z, v⟩ ⟨hz, hv⟩
  exact eqOn_zero_of_uncountable hU
    (fun a ha => (hF (a, v) ⟨ha, hv⟩).curry_left) hSU hS
    (fun a ha => hzero a ha v hv) hz

/-- Equality of actual quotient values wherever both denominators are
nonzero implies the cross-multiplication identity everywhere on a
connected open chart.  The denominator may even vanish identically. -/
theorem cross_mul_eq_of_quotient_eq {V : Set E} {p q : E → ℂ}
    (hVopen : IsOpen V) (hV : IsPreconnected V)
    (hp : AnalyticOnNhd ℂ p V) (hq : AnalyticOnNhd ℂ q V)
    (hratio : ∀ v ∈ V, ∀ w ∈ V, q v ≠ 0 → q w ≠ 0 → p v / q v = p w / q w) :
    ∀ v ∈ V, ∀ w ∈ V, p v * q w = p w * q v := by
  classical
  by_cases hzero : ∀ v ∈ V, q v = 0
  · intro v hv w hw
    rw [hzero v hv, hzero w hw]
    simp
  push Not at hzero
  obtain ⟨a, ha, hqa⟩ := hzero
  have hlocal : (fun v => p v * q a) =ᶠ[𝓝 a] (fun v => p a * q v) := by
    filter_upwards [hVopen.mem_nhds ha, (hq a ha).continuousAt.eventually_ne hqa]
      with v hv hqv
    exact (div_eq_div_iff hqv hqa).mp (hratio v hv a ha hqv hqa)
  have hanchor : EqOn (fun v => p v * q a) (fun v => p a * q v) V :=
    (hp.mul analyticOnNhd_const).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const.mul hq) hV ha hlocal
  intro v hv w hw
  apply mul_right_cancel₀ hqa
  calc
    (p v * q w) * q a = (p v * q a) * q w := by ac_rfl
    _ = (p a * q v) * q w := congrArg (fun c : ℂ => c * q w) (hanchor hv)
    _ = (p a * q w) * q v := by ac_rfl
    _ = (p w * q a) * q v := congrArg (fun c : ℂ => c * q v) (hanchor hw).symm
    _ = (p w * q v) * q a := by ac_rfl

/-- If the cross-multiplication identity fails at one point of a product
chart, only countably many parameter slices can have constant quotient
values on their genuine denominator-nonzero loci. -/
theorem countable_constant_quotient_slices {U : Set ℂ} {V : Set E}
    {p q : ℂ × E → ℂ} (hU : IsPreconnected U)
    (hVopen : IsOpen V) (hV : IsPreconnected V)
    (hp : AnalyticOnNhd ℂ p (U ×ˢ V)) (hq : AnalyticOnNhd ℂ q (U ×ˢ V))
    (hne : ∃ a ∈ U, ∃ v ∈ V, ∃ w ∈ V,
      p (a, v) * q (a, w) ≠ p (a, w) * q (a, v)) :
    Set.Countable {z | z ∈ U ∧ ∀ v ∈ V, ∀ w ∈ V,
      q (z, v) ≠ 0 → q (z, w) ≠ 0 → p (z, v) / q (z, v) = p (z, w) / q (z, w)} := by
  obtain ⟨a, ha, v, hv, w, hw, hne⟩ := hne
  have hpv : AnalyticOnNhd ℂ (fun z => p (z, v)) U :=
    fun z hz => (hp (z, v) ⟨hz, hv⟩).curry_left
  have hpw : AnalyticOnNhd ℂ (fun z => p (z, w)) U :=
    fun z hz => (hp (z, w) ⟨hz, hw⟩).curry_left
  have hqv : AnalyticOnNhd ℂ (fun z => q (z, v)) U :=
    fun z hz => (hq (z, v) ⟨hz, hv⟩).curry_left
  have hqw : AnalyticOnNhd ℂ (fun z => q (z, w)) U :=
    fun z hz => (hq (z, w) ⟨hz, hw⟩).curry_left
  have hc := countable_zero_set hU ((hpv.mul hqw).sub (hpw.mul hqv))
    ⟨a, ha, sub_ne_zero.mpr hne⟩
  apply hc.mono
  intro z hz
  refine ⟨hz.1, sub_eq_zero.mpr ?_⟩
  exact cross_mul_eq_of_quotient_eq hVopen hV
    (fun y hy => (hp (z, y) ⟨hz.1, hy⟩).curry_right)
    (fun y hy => (hq (z, y) ⟨hz.1, hy⟩).curry_right) hz.2 v hv w hw

/-- Uncountably many constant quotient slices force the full analytic
cross-multiplication identity, including points where denominators vanish. -/
theorem cross_mul_eq_of_uncountable_constant_quotient_slices
    {U S : Set ℂ} {V : Set E} {p q : ℂ × E → ℂ}
    (hU : IsPreconnected U) (hVopen : IsOpen V) (hV : IsPreconnected V)
    (hp : AnalyticOnNhd ℂ p (U ×ˢ V)) (hq : AnalyticOnNhd ℂ q (U ×ˢ V))
    (hSU : S ⊆ U) (hS : ¬ S.Countable)
    (hratio : ∀ z ∈ S, ∀ v ∈ V, ∀ w ∈ V,
      q (z, v) ≠ 0 → q (z, w) ≠ 0 → p (z, v) / q (z, v) = p (z, w) / q (z, w)) :
    ∀ z ∈ U, ∀ v ∈ V, ∀ w ∈ V, p (z, v) * q (z, w) = p (z, w) * q (z, v) := by
  intro z hz v hv w hw
  by_contra hne
  apply hS
  apply (countable_constant_quotient_slices hU hVopen hV hp hq
    ⟨z, hz, v, hv, w, hw, hne⟩).mono
  intro a ha
  exact ⟨hSU ha, hratio a ha⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphicSlices
