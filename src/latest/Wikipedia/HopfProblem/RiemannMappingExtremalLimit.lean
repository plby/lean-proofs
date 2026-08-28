/-
Parts of this file are derived from Yury Kudryashov's Mathlib development.

Source: https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov
-/
import Wikipedia.HopfProblem.RiemannMappingCompact
import Wikipedia.HopfProblem.RiemannMappingHurwitz

/-!
# Attainment of the extremal normalized conformal map

The extremizer is obtained from an actual compact closure in the
compact-convergence topology.  Hurwitz proves both its injectivity and
its everywhere nonzero derivative; neither is assumed as a limit property.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Uniformity UniformConvergence

namespace Wikipedia.HopfProblem.RiemannMapping

/-- The actual normalized injective holomorphic maps into the unit disc,
with the nonvanishing derivative needed for a genuine analytic inverse. -/
def normalizedClass (U : Set ℂ) (x₀ : ℂ) : Set (FunctionSpace U) :=
  {f | MapsTo (evaluation f) U (ball 0 1) ∧ InjOn (evaluation f) U ∧
    DifferentiableOn ℂ (evaluation f) U ∧
    (∀ z ∈ U, deriv (evaluation f) z ≠ 0) ∧ evaluation f x₀ = 0}

theorem normalizedClass_compact_closure {U : Set ℂ} (hUo : IsOpen U) (x₀ : ℂ) :
    IsCompact (closure (normalizedClass U x₀)) := by
  apply isCompact_closure_of_bounded_holomorphic hUo
    (fun f hf => hf.2.2.1)
  exact ⟨1, fun f hf z hz => (mem_ball_zero_iff.mp (hf.1 hz)).le⟩

/-- Closure limits remain holomorphic and normalized.  Their functions
and derivatives each satisfy the corresponding genuine Hurwitz dichotomy. -/
theorem closure_normalizedClass {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    closure (normalizedClass U x₀) ⊆
      {f | MapsTo (evaluation f) U (ball 0 1) ∧
        ((∃ C, EqOn (evaluation f) (const ℂ C) U) ∨ InjOn (evaluation f) U) ∧
        DifferentiableOn ℂ (evaluation f) U ∧ evaluation f x₀ = 0 ∧
        (EqOn (deriv (evaluation f)) 0 U ∨ ∀ z ∈ U, deriv (evaluation f) z ≠ 0)} := by
  let := uniformity_isCountablyGenerated hUo
  intro f hf
  let : (𝓝[normalizedClass U x₀] f).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hf
  have htendsto : TendstoLocallyUniformlyOn evaluation (evaluation f)
      (𝓝[normalizedClass U x₀] f) U := evaluation_tendstoLocallyUniformlyOn hUo
  have hFd : ∀ᶠ g in 𝓝[normalizedClass U x₀] f,
      DifferentiableOn ℂ (evaluation g) U :=
    eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1
  have hdf : DifferentiableOn ℂ (evaluation f) U := htendsto.differentiableOn hFd hUo
  have hf_le : ∀ z ∈ U, ‖evaluation f z‖ ≤ 1 := by
    intro z hz
    refine le_of_tendsto (htendsto.tendsto_at hz).norm
      (eventually_mem_nhdsWithin.mono ?_)
    intro g hg
    exact (mem_ball_zero_iff.mp (hg.1 hz)).le
  have hfx₀ : evaluation f x₀ = 0 := by
    refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
    refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg => ?_)
    exact hg.2.2.2.2.symm
  refine ⟨?_, ?_, hdf, hfx₀, ?_⟩
  · by_contra hf_ball
    obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖evaluation f z‖ := by
      simpa [MapsTo] using hf_ball
    have hm : IsMaxOn (fun z => ‖evaluation f z‖) U z := by
      intro y hy
      exact (hf_le y hy).trans hz
    have he : evaluation f x₀ = evaluation f z :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdf hzU hm hx₀
    norm_num [← he, hfx₀] at hz
  · exact Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo hUc
      (eventually_mem_nhdsWithin.mono fun g hg => hg.2.1) hFd htendsto
  · apply Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn hUo hUc
      (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.1)
      (hFd.mono fun g hg => hg.deriv hUo)
    exact htendsto.deriv hFd hUo

/-- The derivative at the normalizing point is a continuous objective
on the actual compact closure, by locally uniform convergence of derivatives. -/
theorem norm_deriv_continuousOn_closure {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ContinuousOn (fun f : FunctionSpace U => ‖deriv (evaluation f) x₀‖)
      (closure (normalizedClass U x₀)) := by
  have hc := closure_normalizedClass hUo hUc hx₀
  refine ContinuousOn.mono (ContinuousOn.norm fun f hf => ?_) hc
  refine TendstoLocallyUniformlyOn.tendsto_at
    (TendstoLocallyUniformlyOn.deriv (evaluation_tendstoLocallyUniformlyOn hUo) ?_ hUo) hx₀
  exact eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1

/-- A normalized conformal map maximizing the actual derivative exists,
provided that the admissible class contains one map. -/
theorem exists_maximal_normalizedMap {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    (hne : (normalizedClass U x₀).Nonempty) :
    ∃ f : FunctionSpace U, f ∈ normalizedClass U x₀ ∧
      ∀ g ∈ normalizedClass U x₀, ‖deriv (evaluation g) x₀‖ ≤
        ‖deriv (evaluation f) x₀‖ := by
  obtain ⟨f, hf, hmax⟩ := (normalizedClass_compact_closure hUo x₀).exists_isMaxOn
    hne.closure (norm_deriv_continuousOn_closure hUo hUc hx₀)
  have hpos : 0 < ‖deriv (evaluation f) x₀‖ := by
    obtain ⟨g, hg⟩ := hne
    exact (norm_pos_iff.mpr (hg.2.2.2.1 x₀ hx₀)).trans_le (hmax (subset_closure hg))
  obtain ⟨hmap, hinj, hdiff, hzero, hderiv⟩ := closure_normalizedClass hUo hUc hx₀ hf
  have hinj' : InjOn (evaluation f) U := by
    apply hinj.resolve_left
    rintro ⟨C, hC⟩
    rw [(hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq] at hpos
    change 0 < ‖deriv (fun _ : ℂ => C) x₀‖ at hpos
    simp only [deriv_const, norm_zero, lt_self_iff_false] at hpos
  have hderiv' : ∀ z ∈ U, deriv (evaluation f) z ≠ 0 := by
    apply hderiv.resolve_left
    intro hzero'
    have hz : deriv (evaluation f) x₀ = 0 := hzero' hx₀
    simp only [hz, norm_zero, lt_self_iff_false] at hpos
  exact ⟨f, ⟨hmap, hinj', hdiff, hderiv', hzero⟩,
    fun g hg => hmax (subset_closure hg)⟩

end Wikipedia.HopfProblem.RiemannMapping
