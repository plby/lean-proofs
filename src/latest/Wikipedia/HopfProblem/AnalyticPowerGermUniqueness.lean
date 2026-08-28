import Wikipedia.HopfProblem.EllipticDiscLocalInverse
import Mathlib.Analysis.Calculus.DSlope

/-!
# Uniqueness of simple analytic power germs

After dividing out a simple zero, the power map is locally injective at
the nonzero common derivative.  This identifies the correct root of
unity in a local analytic power chart from its actual derivative.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Simple differentiable germs with the same power and derivative agree
on a neighbourhood. No choice of a multivalued root is assumed. -/
theorem power_germs_eq_of_same_deriv {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hm : 0 < m) (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a)
    (hf0 : f a = 0) (hg0 : g a = 0) (hd : deriv f a = deriv g a)
    (hne : deriv g a ≠ 0)
    (hp : (fun z => f z ^ m) =ᶠ[𝓝 a] (fun z => g z ^ m)) :
    f =ᶠ[𝓝 a] g := by
  let e := Elliptic.complexPowerChart m hm (deriv g a) hne
  have he : deriv g a ∈ e.source := Elliptic.mem_complexPowerChart_source m hm _ hne
  have hfnear : ∀ᶠ z in 𝓝 a, dslope f a z ∈ e.source := by
    apply (continuousAt_dslope_same.mpr hf).preimage_mem_nhds
    simpa only [dslope_same, hd] using e.open_source.mem_nhds he
  have hgnear : ∀ᶠ z in 𝓝 a, dslope g a z ∈ e.source := by
    apply (continuousAt_dslope_same.mpr hg).preimage_mem_nhds
    simpa only [dslope_same] using e.open_source.mem_nhds he
  filter_upwards [hfnear, hgnear, hp] with z hfz hgz hpz
  by_cases hza : z = a
  · simp only [hza, hf0, hg0]
  have heq : e (dslope f a z) = e (dslope g a z) := by
    change (dslope f a z) ^ m = (dslope g a z) ^ m
    simp only [dslope_of_ne _ hza, slope, hf0, hg0, vsub_eq_sub, sub_zero, smul_eq_mul,
      mul_pow, hpz]
  have hdsl := e.injOn hfz hgz heq
  have hmul := congrArg (fun w : ℂ => (z - a) • w) hdsl
  simpa only [sub_smul_dslope, hf0, hg0, sub_zero] using hmul

/-- Analytic inverse charts have nonzero complex derivative throughout
their sources. This follows from differentiating the actual inverse law. -/
theorem analytic_chart_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target) :
    deriv e a ≠ 0 := by
  have hii := hi (e a) (e.map_source ha)
  have hc := hii.differentiableAt.hasDerivAt.comp a (hf a ha).differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, z ∈ e.source := e.open_source.mem_nhds ha
  have heq : (fun z : ℂ => e.symm (e z)) =ᶠ[𝓝 a] id :=
    hnear.mono fun z hz => e.left_inv hz
  have hm : deriv e.symm (e a) * deriv e a = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id a)
  intro h
  rw [h, mul_zero] at hm
  exact zero_ne_one hm

/-- In a centered power chart, an automorphism preserving the power acts
by its derivative at the fixed point. -/
theorem analytic_power_chart_equivariant (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : e a = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    {A : ℂ → ℂ} (hA : AnalyticAt ℂ A a) (hAa : A a = a)
    {ξ : ℂ} {m : ℕ} (hm : 0 < m) (hξ : ξ ^ m = 1) (hA' : deriv A a = ξ)
    (hp : (fun z => e (A z) ^ m) =ᶠ[𝓝 a] (fun z => e z ^ m)) :
    (fun z => e (A z)) =ᶠ[𝓝 a] (fun z => ξ * e z) := by
  have hξne : ξ ≠ 0 := by
    intro hz
    apply zero_ne_one (α := ℂ)
    simpa only [hz, zero_pow hm.ne'] using hξ
  have hea : AnalyticAt ℂ e (A a) := by
    rw [hAa]
    exact hf a ha
  have hleft := hea.differentiableAt.hasDerivAt.comp a hA.differentiableAt.hasDerivAt
  have hright := (hf a ha).differentiableAt.hasDerivAt.const_mul ξ
  refine power_germs_eq_of_same_deriv hm hleft.differentiableAt hright.differentiableAt
    (by rw [hAa, he]) (by rw [he, mul_zero]) ?_ ?_ ?_
  · change deriv (e ∘ A) a = deriv (fun z => ξ * e z) a
    rw [hleft.deriv, hright.deriv, hAa, hA', mul_comm]
  · rw [hright.deriv]
    exact mul_ne_zero hξne (analytic_chart_deriv_ne_zero e ha hf hi)
  · filter_upwards [hp] with z hz
    simpa only [mul_pow, hξ, one_mul] using hz

/-- Exact equivariance of an inverse power branch, as an equality on a
genuine neighbourhood of its center. -/
theorem inverse_power_branch_rotation_eventually (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : e a = 0)
    (hi : AnalyticOnNhd ℂ e.symm e.target)
    {A : ℂ → ℂ} (hA : ContinuousAt A a) (hAa : A a = a)
    {ξ η : ℂ} {k : ℕ} (hk : 0 < k) (hη : η ^ k = ξ) (c : ℂ)
    (heq : (fun z => e (A z)) =ᶠ[𝓝 a] (fun z => ξ * e z)) :
    (fun s : ℂ => e.symm (c * (η * s) ^ k)) =ᶠ[𝓝 0]
      (fun s : ℂ => A (e.symm (c * s ^ k))) := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hia : e.symm 0 = a := by rw [← he, e.left_inv ha]
  have hc : ContinuousAt (fun s : ℂ => c * s ^ k) 0 := by fun_prop
  have hcl : ContinuousAt (fun s : ℂ => c * (η * s) ^ k) 0 := by fun_prop
  have hc0 : c * (0 : ℂ) ^ k = 0 := by simp [hk.ne']
  have hcl0 : c * (η * (0 : ℂ)) ^ k = 0 := by simp [hk.ne']
  have hτ : Tendsto (fun s : ℂ => e.symm (c * s ^ k)) (𝓝 0) (𝓝 a) := by
    have hh := (hi 0 ht).continuousAt.tendsto.comp (by simpa only [hc0] using hc.tendsto)
    simpa only [Function.comp_def, hia] using hh
  have hτA : Tendsto (fun s : ℂ => A (e.symm (c * s ^ k))) (𝓝 0) (𝓝 a) := by
    simpa only [Function.comp_def, hAa] using hA.tendsto.comp hτ
  have htnear : ∀ᶠ s : ℂ in 𝓝 0, c * s ^ k ∈ e.target := by
    apply hc.preimage_mem_nhds
    simpa only [hc0] using e.open_target.mem_nhds ht
  have htlnear : ∀ᶠ s : ℂ in 𝓝 0, c * (η * s) ^ k ∈ e.target := by
    apply hcl.preimage_mem_nhds
    simpa only [hcl0] using e.open_target.mem_nhds ht
  have hAnear : ∀ᶠ s : ℂ in 𝓝 0, A (e.symm (c * s ^ k)) ∈ e.source :=
    hτA (e.open_source.mem_nhds ha)
  filter_upwards [htnear, htlnear, hAnear, heq.comp_tendsto hτ] with s hs hls hAs hes
  dsimp only [Function.comp_def] at hes
  apply e.injOn (e.map_target hls) hAs
  rw [e.right_inv hls, hes, e.right_inv hs, mul_pow, hη]
  ring

end Wikipedia.HopfProblem.SpecialPeriods
