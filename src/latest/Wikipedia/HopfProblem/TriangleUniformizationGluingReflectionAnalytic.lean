import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingReflections
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic reflection of an upper-half-plane function

The actual right-side reflection is `z ↦ -1 - conj z`.  Conjugating the
value of a holomorphic function after this reflection gives a holomorphic
function on the reflected open set.  The proof uses conjugation on both
sides of a complex derivative and the holomorphic affine map `z ↦ -1-z`.
-/

noncomputable section

open Function Set UpperHalfPlane
open scoped Topology ContDiff Manifold ComplexConjugate

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods.Triangle

private theorem differentiableAt_conj_affine_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (-1 - conj z)) :
    DifferentiableAt ℂ (fun w => conj (f (-1 - conj w))) z := by
  have hc : DifferentiableAt ℂ (conj ∘ f ∘ conj) (-1 - z) := by
    simpa only [map_sub, map_neg, map_one, Complex.conj_conj] using hf.conj_conj
  have ha : DifferentiableAt ℂ (fun w : ℂ => -1 - w) z :=
    (differentiableAt_const (-1 : ℂ)).sub differentiableAt_id
  simpa only [comp_def, map_sub, map_neg, map_one] using hc.comp z ha

/-- Holomorphic reflection across the actual right vertical side.  The
reflection itself is antiholomorphic; conjugation of the function value
is part of the constructed holomorphic map. -/
theorem contMDiffOn_conj_rightReflection {f : ℍ → ℂ} {S : Set ℍ}
    (hS : IsOpen S) (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f S) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun z => conj (f (rightReflection z)))
      (rightReflection '' S) := by
  let F : ℂ → ℂ := fun z => conj (f (UpperHalfPlane.ofComplex (-1 - conj z)))
  have hU : IsOpen (((↑) : ℍ → ℂ) '' (rightReflection '' S)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (rightReflection.isOpenMap _ hS)
  have hF : DifferentiableOn ℂ F (((↑) : ℍ → ℂ) '' (rightReflection '' S)) := by
    rintro z ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hfx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x :=
      (hf x hx).contMDiffAt (hS.mem_nhds hx)
    have hfd : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (x : ℂ) :=
      (UpperHalfPlane.contMDiffAt_iff.mp hfx).differentiableAt (by simp)
    have hr : (-1 : ℂ) - conj (rightReflection x : ℂ) = (x : ℂ) :=
      (rightReflection_coe (rightReflection x)).symm.trans
        (congrArg ((↑) : ℍ → ℂ) (rightReflection_involutive x))
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_conj_affine_reflection (f := f ∘ UpperHalfPlane.ofComplex)
    rw [hr]
    exact hfd
  have hFM : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω F
      (((↑) : ℍ → ℂ) '' (rightReflection '' S)) :=
    contMDiffOn_iff_contDiffOn.mpr ((hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn)
  have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F ∘ ((↑) : ℍ → ℂ))
      (rightReflection '' S) :=
    hFM.comp UpperHalfPlane.contMDiff_coe.contMDiffOn (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z _
  change conj (f (rightReflection z)) =
    conj (f (UpperHalfPlane.ofComplex (-1 - conj (z : ℂ))))
  rw [← rightReflection_coe, UpperHalfPlane.ofComplex_apply]

end Wikipedia.HopfProblem.TriangleUniformizationGluing
