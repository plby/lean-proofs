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
import Wikipedia.HopfProblem.RiemannMappingExtremalLimit
import Wikipedia.HopfProblem.RiemannMappingDisc

/-!
# The Riemann mapping theorem

The derivative maximizer in the actual compact normal family is
surjective: otherwise the square-root and disc-automorphism construction
strictly increases its derivative.  The resulting map is bijective,
holomorphic, and has nonzero derivative at every point of the domain.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Uniformity UniformConvergence

namespace Wikipedia.HopfProblem.RiemannMapping

/-- Extending a disc-valued map by zero outside its actual domain. -/
def discExtension {U : Set ℂ} (f : ℂ → ℂ) (hf : MapsTo f U (ball 0 1)) : ℂ → UnitDisc := by
  classical
  exact fun z => if hz : z ∈ U then UnitDisc.mk (f z) (mem_ball_zero_iff.mp (hf hz)) else 0

@[simp] theorem discExtension_coe {U : Set ℂ} (f : ℂ → ℂ)
    (hf : MapsTo f U (ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    (discExtension f hf z : ℂ) = f z := by
  simp only [discExtension, dif_pos hz, UnitDisc.coe_mk]

theorem discExtension_eqOn {U : Set ℂ} (f : ℂ → ℂ)
    (hf : MapsTo f U (ball 0 1)) : EqOn (UnitDisc.coe ∘ discExtension f hf) f U :=
  fun _ hz => discExtension_coe f hf hz

theorem discExtension_deriv {U : Set ℂ} (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : MapsTo f U (ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    deriv (UnitDisc.coe ∘ discExtension f hf) z = deriv f z :=
  ((discExtension_eqOn f hf).eventuallyEq_of_mem (hUo.mem_nhds hz)).deriv_eq

theorem normalizedClass_nonempty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    (normalizedClass U x₀).Nonempty := by
  obtain ⟨f, hf₀, hf_inj, hfd⟩ :=
    Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx₀
  refine ⟨UniformOnFun.ofFun (compactSubsets U) (UnitDisc.coe ∘ f), ?_⟩
  refine ⟨fun z _ => (f z).property, ?_, ?_, hfd, ?_⟩
  · intro z hz w hw he
    exact hf_inj hz hw (UnitDisc.coe_injective he)
  · intro z hz
    exact (differentiableAt_of_deriv_ne_zero (hfd z hz)).differentiableWithinAt
  · change (f x₀ : ℂ) = 0
    rw [hf₀]
    rfl

/-- **Riemann mapping theorem**, with an everywhere nonzero derivative
and a prescribed point mapping to the centre of the actual unit disc. -/
theorem exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧ f x₀ = 0 := by
  obtain ⟨f, hf, hmax⟩ := exists_maximal_normalizedMap hUo
    hUc.isPathConnected.isConnected.isPreconnected hx₀
    (normalizedClass_nonempty hUo hUc hU hx₀)
  obtain ⟨hfmap, hfinj, hfdiff, hfderiv, hfzero⟩ := hf
  refine ⟨evaluation f, hfdiff, ⟨hfmap, hfinj, ?_⟩, hfderiv, hfzero⟩
  by_contra hsurj
  let fDisc := discExtension (evaluation f) hfmap
  have hfeq : EqOn (UnitDisc.coe ∘ fDisc) (evaluation f) U :=
    discExtension_eqOn (evaluation f) hfmap
  have hfdDisc : DifferentiableOn ℂ (UnitDisc.coe ∘ fDisc) U :=
    (differentiableOn_congr hfeq).mpr hfdiff
  have hfDisc0 : fDisc x₀ = 0 := by
    apply UnitDisc.coe_injective
    change (fDisc x₀ : ℂ) = 0
    exact (hfeq hx₀).trans hfzero
  have hfDiscInj : InjOn fDisc U := by
    intro z hz w hw he
    apply hfinj hz hw
    exact (hfeq hz).symm.trans ((congrArg UnitDisc.coe he).trans (hfeq hw))
  have hfDiscDeriv : ∀ z ∈ U, deriv (UnitDisc.coe ∘ fDisc) z ≠ 0 := by
    intro z hz
    rw [(hfeq.eventuallyEq_of_mem (hUo.mem_nhds hz)).deriv_eq]
    exact hfderiv z hz
  have hfDiscSurj : ¬SurjOn fDisc U univ := by
    intro hs
    apply hsurj
    intro w hw
    obtain ⟨z, hz, he⟩ := hs (mem_univ (UnitDisc.mk w (mem_ball_zero_iff.mp hw)))
    refine ⟨z, hz, ?_⟩
    exact (hfeq hz).symm.trans (congrArg UnitDisc.coe he)
  obtain ⟨g, hg₀, hginj, hgdiff, hgderiv, hglt⟩ :=
    Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt hUo hUc hU hx₀
      hfdDisc hfDisc0 hfDiscInj hfDiscSurj hfDiscDeriv
  let gFun : FunctionSpace U := UniformOnFun.ofFun (compactSubsets U) (UnitDisc.coe ∘ g)
  have hgmem : gFun ∈ normalizedClass U x₀ := by
    refine ⟨fun z _ => (g z).property, ?_, hgdiff, hgderiv, ?_⟩
    · intro z hz w hw he
      exact hginj hz hw (UnitDisc.coe_injective he)
    · change (g x₀ : ℂ) = 0
      rw [hg₀]
      rfl
  have hle := hmax gFun hgmem
  have heDeriv : deriv (UnitDisc.coe ∘ fDisc) x₀ = deriv (evaluation f) x₀ :=
    (hfeq.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq
  rw [heDeriv] at hglt
  exact hle.not_gt hglt

/-- The usual unbundled Riemann mapping theorem, retaining the source
statement as a direct corollary of the stronger checked construction. -/
theorem exists_bijOn_unitBall_map_eq_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 := by
  obtain ⟨f, hf, hbij, _, hzero⟩ :=
    exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero hUo hUc hU hx₀
  exact ⟨f, hf, hbij, hzero⟩

end Wikipedia.HopfProblem.RiemannMapping
