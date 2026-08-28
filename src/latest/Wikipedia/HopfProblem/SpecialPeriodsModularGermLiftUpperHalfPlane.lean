import Wikipedia.HopfProblem.SpecialPeriodsModularGermLift
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftNativeOrders
import Wikipedia.HopfProblem.AnalyticRootCoverUpperHalfPlane

/-!
# Global modular lifts on the actual upper half-plane

The analytic lifting theorem on an open complex domain gives a genuine
holomorphic manifold map `ℍ → ℍ`.  The conversion uses the existing analytic
charts of the upper half-plane and preserves a prescribed initial complex
germ.  The finite critical-order conditions permit ramification over both
elliptic values of the modular j-function.
-/

noncomputable section

open Complex Filter Function Set TopologicalSpace
open scoped Topology UpperHalfPlane Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

/-- Convert an ambient complex map into an actual upper-half-plane-valued map.
Target membership on the true domain is proved separately in the lemmas below. -/
def upperHalfPlaneLift (g : ℂ → ℂ) : ℍ → ℍ :=
  fun z => UpperHalfPlane.ofComplex (g (z : ℂ))

theorem upperHalfPlaneLift_coe {g : ℂ → ℂ}
    (hpos : MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (z : ℍ) : (upperHalfPlaneLift g z : ℂ) = g (z : ℂ) := by
  rw [upperHalfPlaneLift, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos z.im_pos)]

/-- Ambient analyticity and the proved image condition imply holomorphicity
of the actual map between the native upper-half-plane manifolds. -/
theorem upperHalfPlaneLift_holomorphic {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g UpperHalfPlane.upperHalfPlaneSet)
    (hpos : MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (upperHalfPlaneLift g) := by
  intro z
  exact (UpperHalfPlane.contMDiffAt_ofComplex (hpos z.im_pos)).comp z
    ((hg z z.im_pos).contDiffAt.contMDiffAt.comp z (UpperHalfPlane.contMDiff_coe z))

/-- Passing to a native upper-half-plane map does not change its ambient
complex germ at any upper-half-plane point. -/
theorem upperHalfPlaneLift_eventuallyEq {g : ℂ → ℂ}
    (hpos : MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (a : ℍ) :
    (fun z => (upperHalfPlaneLift g (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] g := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos] with z hz
  change (UpperHalfPlane.ofComplex (g (UpperHalfPlane.ofComplex z : ℂ)) : ℂ) = g z
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos (hpos hz)]

/-- The finite critical-order conditions for a native function on `ℍ`
become exactly the corresponding conditions on its ambient-coordinate function. -/
theorem upperHalfPlane_critical_orders {F : ℍ → ℂ}
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ)) :
    (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet, (F ∘ UpperHalfPlane.ofComplex) a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) a = (3 * k : ℕ)) ∧
    (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet, (F ∘ UpperHalfPlane.ofComplex) a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => (F ∘ UpperHalfPlane.ofComplex) z - 1728)
        a = (2 * k : ℕ)) := by
  constructor
  · intro a ha hFa
    apply h₃ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa
  · intro a ha hFa
    apply h₂ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa

/-- A holomorphic function on `ℍ` with the required finite ramification
orders has an actual global holomorphic modular lift `ℍ → ℍ`. -/
theorem exists_holomorphic_modularJ_lift_upperHalfPlane (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ)) :
    ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
      ∀ z : ℍ, modularJ (τ z) = F z := by
  have hF' : AnalyticOnNhd ℂ (F ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hF).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨h₃', h₂'⟩ := upperHalfPlane_critical_orders h₃ h₂
  obtain ⟨g, hg, hpos, hJ⟩ := exists_analytic_modularJ_lift_on
    AnalyticRootCover.upperHalfPlaneOpen (F ∘ UpperHalfPlane.ofComplex) hF' h₃' h₂'
  refine ⟨upperHalfPlaneLift g, upperHalfPlaneLift_holomorphic hg hpos, ?_⟩
  intro z
  simpa only [upperHalfPlaneLift, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    using hJ z.im_pos

/-- The native global modular lift can be chosen to preserve a prescribed
initial analytic complex germ, including one at either elliptic value. -/
theorem exists_holomorphic_modularJ_lift_upperHalfPlane_extending (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ))
    (a : ℍ) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ (a : ℂ))
    (hpos₀ : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 (a : ℂ)]
      F ∘ UpperHalfPlane.ofComplex) :
    ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
      (∀ z : ℍ, modularJ (τ z) = F z) ∧
      (fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] τ₀ := by
  have hF' : AnalyticOnNhd ℂ (F ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hF).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨h₃', h₂'⟩ := upperHalfPlane_critical_orders h₃ h₂
  obtain ⟨g, hg, hpos, hJ, hg₀⟩ := exists_analytic_modularJ_lift_extending
    AnalyticRootCover.upperHalfPlaneOpen (F ∘ UpperHalfPlane.ofComplex) hF' h₃' h₂'
    a.im_pos τ₀ hτ₀ hpos₀ hJ₀
  refine ⟨upperHalfPlaneLift g, upperHalfPlaneLift_holomorphic hg hpos, ?_,
    (upperHalfPlaneLift_eventuallyEq hpos a).trans hg₀⟩
  intro z
  simpa only [upperHalfPlaneLift, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    using hJ z.im_pos

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
