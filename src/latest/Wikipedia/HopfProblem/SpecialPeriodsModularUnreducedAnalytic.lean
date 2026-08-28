import Wikipedia.HopfProblem.SpecialPeriodsModularUnreducedBasic

/-!
# Analyticity of continuous lifts through the regular modular function

The explicit analytic local inverse of the actual modular function shows
that every continuous lift of a holomorphic map is holomorphic wherever
its modular value avoids `0` and `1728`. This will be used for global lifts
through the unreduced modular covering; no holomorphicity of a continuous
covering lift is assumed.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)

theorem modularJ_contMDiffAt_lift {f : M → ℍ} {x : M}
    (hf : ContinuousAt f x) (h₀ : modularJ (f x) ≠ 0) (h₁ : modularJ (f x) ≠ 1728)
    (hj : ContMDiffAt I 𝓘(ℂ) ω (modularJ ∘ f) x) : ContMDiffAt I 𝓘(ℂ) ω f x := by
  let g := modularLocalInverse (f x) h₀ h₁
  have hself : g (modularJ (f x)) = (f x : ℂ) := by
    simpa only [ofComplex_apply] using
      (modularLocalInverse_eventually_left_inverse (f x) h₀ h₁).self_of_nhds
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (modularJ (f x)) :=
    (modularLocalInverse_analyticAt (f x) h₀ h₁).contDiffAt.contMDiffAt
  have hpos : 0 < (g (modularJ (f x))).im := by rw [hself]; exact (f x).im_pos
  have hη : ContMDiffAt I 𝓘(ℂ) ω (fun y => ofComplex (g (modularJ (f y)))) x :=
    (UpperHalfPlane.contMDiffAt_ofComplex hpos).comp x (hg.comp x hj)
  have hleft : ∀ᶠ y in 𝓝 x, g (modularJ (f y)) = (f y : ℂ) := by
    have h := (continuous_coe.continuousAt.comp hf).tendsto.eventually
      (modularLocalInverse_eventually_left_inverse (f x) h₀ h₁)
    simpa only [Function.comp_apply, ofComplex_apply] using h
  apply hη.congr_of_eventuallyEq
  filter_upwards [hleft] with y hy
  rw [hy, ofComplex_apply]

theorem modularJ_contMDiff_lift {f : M → ℍ} (hf : Continuous f)
    (hreg : ∀ x, modularJ (f x) ∈ modularRegularValues)
    (hj : ContMDiff I 𝓘(ℂ) ω (modularJ ∘ f)) : ContMDiff I 𝓘(ℂ) ω f := by
  intro x
  obtain ⟨h₀, h₁⟩ := (mem_modularRegularValues _).mp (hreg x)
  exact modularJ_contMDiffAt_lift I hf.continuousAt h₀ h₁ (hj x)

/-- A continuous lift into the actual regular source inherits analyticity
from its composition with the unreduced modular map. -/
theorem modularUnreducedJ_contMDiffAt_lift {f : M → modularRegularUpper} {x : M}
    (hf : ContinuousAt f x)
    (hj : ContMDiffAt I 𝓘(ℂ) ω (modularUnreducedJ ∘ f) x) :
    ContMDiffAt I 𝓘(ℂ) ω f x := by
  have hbase : ContMDiffAt I 𝓘(ℂ) ω
      (fun y => modularJ (f y : ℍ)) x :=
    contMDiff_subtype_val.contMDiffAt.comp x hj
  have hreg := (mem_modularRegularValues _).mp (f x).2
  have hval := modularJ_contMDiffAt_lift I (continuous_subtype_val.continuousAt.comp hf)
    hreg.1 hreg.2 hbase
  have he : ContMDiffAt I 𝓘(ℂ) ω (fun y => (f y : ℍ)) x ↔
      ContMDiffAt I 𝓘(ℂ) ω f x := ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp hval

theorem modularUnreducedJ_contMDiff_lift {f : M → modularRegularUpper}
    (hf : Continuous f) (hj : ContMDiff I 𝓘(ℂ) ω (modularUnreducedJ ∘ f)) :
    ContMDiff I 𝓘(ℂ) ω f :=
  fun x => modularUnreducedJ_contMDiffAt_lift I hf.continuousAt (hj x)

end Wikipedia.HopfProblem.SpecialPeriods
