import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeBasic
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmooth

/-!
# Native smooth formulas for the standard equatorial tube

The square-root factor is smooth strictly inside the unit normal ball.
Normalization uses the nonzero original base coordinate. All manifold
structures below are Mathlib's existing sphere, Euclidean, and open-subset
structures.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube.Smooth

local notation "ProductModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, Normal)

theorem contDiffAt_baseFactor {n : WithTop ℕ∞} {y : Normal} (hy : ‖y‖ < 1) :
    ContDiffAt ℝ n baseFactor y := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  exact (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt hpos.ne'

section Maps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_baseFactor {n : WithTop ℕ∞} {f : M → Normal}
    (hf : ContMDiff I 𝓘(ℝ, Normal) n f) (h : ∀ p, ‖f p‖ < 1) :
    ContMDiff I 𝓘(ℝ, ℝ) n (fun p => baseFactor (f p)) :=
  fun p => (contDiffAt_baseFactor (h p)).comp_contMDiffAt (hf p)

/-- Normalization into the original stereographic two-sphere atlas. -/
theorem contMDiff_normalizedBase [IsManifold I ∞ M]
    (f : M → Sphere) (hf : ContMDiff I (𝓡 6) ∞ f)
    (h : ∀ p, ‖normal (f p).val‖ < 1) :
    ContMDiff I (𝓡 2) ∞ (fun p => normalizedBase (f p) (h p)) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  have : Fact (Module.finrank ℝ Base = 2 + 1) := ⟨by simp [Base]⟩
  have ha : ContMDiff I 𝓘(ℝ, Ambient) ∞ (fun p => (f p).val) :=
    (contMDiff_coe_sphere (n := 6)).comp hf
  have hb : ContMDiff I 𝓘(ℝ, Base) ∞ (fun p => base (f p).val) :=
    contDiff_base.comp_contMDiff ha
  have hn : ContMDiff I 𝓘(ℝ, Base) ∞
      (fun p => ‖base (f p).val‖⁻¹ • base (f p).val) :=
    contMDiff_normalize_of_ne_zero hb (fun p => base_ne_zero (f p) (h p))
  exact hn.codRestrict_sphere (fun p => normalizedBase_mem_sphere (f p) (h p))

end Maps

theorem normalBall_norm_lt_one (r : ℝ) (hr1 : r ≤ 1) (y : normalBall r) :
    ‖y.val‖ < 1 :=
  lt_of_lt_of_le ((mem_normalBall r y.val).mp y.property) hr1

/-- The original last four coordinates on the native product domain. -/
theorem contMDiff_normalBall_coordinate (r : ℝ) :
    ContMDiff ProductModel 𝓘(ℝ, Normal) ∞
      (fun q : BaseSphere × normalBall r => q.2.val) :=
  (contMDiff_subtype_val (I := 𝓘(ℝ, Normal)) (U := normalBall r)).comp contMDiff_snd

theorem contMDiff_baseSphere_coordinate (r : ℝ) :
    ContMDiff ProductModel 𝓘(ℝ, Base) ∞
      (fun q : BaseSphere × normalBall r => q.1.val) := by
  have : Fact (Module.finrank ℝ Base = 2 + 1) := ⟨by simp [Base]⟩
  exact (contMDiff_coe_sphere (n := 2)).comp contMDiff_fst

/-- Smoothness of the literal ambient tube formula, including radius one. -/
theorem contMDiff_ambient_normalBall (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff ProductModel 𝓘(ℝ, Ambient) ∞
      (fun q : BaseSphere × normalBall r => ambient q.1 q.2.val) := by
  have hy := contMDiff_normalBall_coordinate r
  have hb := contMDiff_baseSphere_coordinate r
  have hf : ContMDiff ProductModel 𝓘(ℝ, ℝ) ∞
      (fun q : BaseSphere × normalBall r => baseFactor q.2.val) :=
    contMDiff_baseFactor hy (fun q => normalBall_norm_lt_one r hr1 q.2)
  have hp : ContMDiff ProductModel 𝓘(ℝ, Base × Normal) ∞
      (fun q : BaseSphere × normalBall r => (baseFactor q.2.val • q.1.val, q.2.val)) :=
    (hf.smul hb).prodMk_space hy
  exact split.symm.contDiff.comp_contMDiff hp

/-- The same map into the original six-sphere atlas. -/
theorem contMDiff_point_normalBall (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff ProductModel (𝓡 6) ∞
      (fun q : BaseSphere × normalBall r =>
        point q.1 q.2.val (normalBall_norm_lt_one r hr1 q.2).le) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  exact (contMDiff_ambient_normalBall r hr1).codRestrict_sphere
    (fun q => ambient_mem_sphere q.1 q.2.val (normalBall_norm_lt_one r hr1 q.2).le)

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube.Smooth
