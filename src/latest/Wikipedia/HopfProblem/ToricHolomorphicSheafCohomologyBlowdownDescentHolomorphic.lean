import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowdownDescentBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowdownDescentRemovable
import Wikipedia.HopfProblem.AffineBlowupPuncturedBiholomorph

/-!
# Actual holomorphic descent through blowdown

The descended function is holomorphic off the origin by the actual
punctured biholomorphism. Its proved global continuity removes the
origin by coordinatewise one-variable removability.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent

open AffineBlowup ToricCharts

local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)

theorem descend_contDiffAt_of_ne_zero {f : Space → ℂ}
    (hf : ContMDiff I₂ 𝓘(ℂ) ω f) {q : CoordinateSpace 2} (hq : q ≠ 0) :
    ContDiffAt ℂ ω (descend f) q := by
  have hm : ContMDiff I₂ 𝓘(ℂ) ω
      (fun v : puncturedBase => f (puncturedHomeomorph.symm v).1) :=
    (hf.comp contMDiff_subtype_val).comp puncturedHomeomorph_symm_holomorphic
  have he : (fun v : puncturedBase => descend f v.1) =
      (fun v : puncturedBase => f (puncturedHomeomorph.symm v).1) := by
    funext v
    rw [← projection_puncturedHomeomorph_symm v, descend_projection hf]
  have hd : ContMDiff I₂ 𝓘(ℂ) ω (fun v : puncturedBase => descend f v.1) := by
    rw [he]
    exact hm
  exact (contMDiffAt_subtype_iff.mp (hd (⟨q, hq⟩ : puncturedBase))).contDiffAt

theorem descend_analytic {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    AnalyticOnNhd ℂ (descend f) univ :=
  analyticOnNhd_native_of_continuous_of_differentiable_off_origin (descend_continuous hf)
    (fun _ hq => (descend_contDiffAt_of_ne_zero hf hq).differentiableAt (by simp))

theorem descend_holomorphic {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    ContMDiff I₂ 𝓘(ℂ) ω (descend f) := (descend_analytic hf).contDiff.contMDiff

/-- Holomorphic functions on the actual blowup descend uniquely along
its actual projection, with literal equality at every point. -/
theorem exists_unique_holomorphic_descent {f : Space → ℂ}
    (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    ∃! g : CoordinateSpace 2 → ℂ, AnalyticOnNhd ℂ g univ ∧
      ∀ x : Space, g (projection x) = f x := by
  refine ⟨descend f, ⟨descend_analytic hf, descend_projection hf⟩, ?_⟩
  intro g hg
  exact descent_unique hg.2 (descend_projection hf)

theorem exists_unique_native_holomorphic_descent {f : Space → ℂ}
    (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    ∃! g : CoordinateSpace 2 → ℂ, ContMDiff I₂ 𝓘(ℂ) ω g ∧
      ∀ x : Space, g (projection x) = f x := by
  refine ⟨descend f, ⟨descend_holomorphic hf, descend_projection hf⟩, ?_⟩
  intro g hg
  exact descent_unique hg.2 (descend_projection hf)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent
