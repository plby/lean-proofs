import Wikipedia.HopfProblem.AnalyticRootCover
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Holomorphic square roots on the actual upper half plane

Every holomorphic function on `ℍ` whose zeros have finite even order has a
global holomorphic square root.  The construction uses the proved two-sheet
cover of analytic germs, so it passes through even-order zeros without
identifying the two root germs there.  The native upper-half-plane formulation
returns an analytic manifold map and the exact halving of each zero order.
-/

noncomputable section

open Complex Filter Metric Set TopologicalSpace
open scoped Topology UpperHalfPlane Manifold ContDiff

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- The upper half plane as an actual open complex domain. -/
def upperHalfPlaneOpen : Opens ℂ :=
  ⟨UpperHalfPlane.upperHalfPlaneSet, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

instance : ContractibleSpace upperHalfPlaneOpen :=
  (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, by simp⟩

/-- The ambient-coordinate form of the square-root theorem on `ℍ`. -/
theorem exists_analytic_square_root_upperHalfPlane (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (hzero : ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet, F a = 0 →
      ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r UpperHalfPlane.upperHalfPlaneSet ∧
      EqOn (fun z => r z ^ 2) F UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet, ∀ n : ℕ,
        analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on_of_even_zeros upperHalfPlaneOpen F hF hzero

/-- **Global square root on the upper half plane.** Only holomorphy and
finite even order at the actual zeros are required.  In particular, zeros
are allowed; no nonvanishing replacement is used. -/
theorem exists_holomorphic_square_root_upperHalfPlane (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f)
    (hzero : ∀ a : ℍ, f a = 0 →
      ∃ n : ℕ, analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ)) :
    ∃ r : ℍ → ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω r ∧
      (∀ a : ℍ, r a ^ 2 = f a) ∧
      ∀ a : ℍ, ∀ n : ℕ,
        analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ) →
          analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = n := by
  let F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hzeroF : ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet, F a = 0 →
      ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) := by
    intro a ha hfa
    apply hzero ⟨a, ha⟩
    simpa only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hfa
  obtain ⟨g, hg, hgsquare, hgorder⟩ :=
    exists_analytic_square_root_upperHalfPlane F hF hzeroF
  let r : ℍ → ℂ := fun a => g a
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a
    exact (hg a a.im_pos).contDiffAt.contMDiffAt.comp a (UpperHalfPlane.contMDiff_coe a)
  · intro a
    simpa only [r, F, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hgsquare a.im_pos
  · intro a n hn
    have he : (r ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (a : ℂ)] g := by
      filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
      exact congrArg g hz
    exact (analyticOrderAt_congr he).trans (hgorder a a.im_pos n hn)

end Wikipedia.HopfProblem.AnalyticRootCover
