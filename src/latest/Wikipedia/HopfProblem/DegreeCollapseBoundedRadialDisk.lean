import Wikipedia.HopfProblem.DegreeCollapseSmoothBeltMeridian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A globally smooth bounded radial disk with exact sphere values

The unit-ball diffeomorphism, scaled by sqrt(2) times s, has value s times
the original vector on the whole unit sphere. It remains a global smooth
immersion and embedding, and for s at most one half its image stays in the
unit ball. This supplies global disk maps inside a native local chart.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]

def smoothUnitBallChart : PartialDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ where
  toPartialEquiv := OpenPartialHomeomorph.univUnitBall.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_ball
  contMDiffOn_toFun := OpenPartialHomeomorph.contDiff_univUnitBall.contMDiff.contMDiffOn
  contMDiffOn_invFun := OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.contMDiffOn

def boundedRadialDiskMap (s : ℝ) (x : N) : N :=
  (Real.sqrt 2 * s) • OpenPartialHomeomorph.univUnitBall x

theorem boundedRadialDiskMap_smooth (s : ℝ) : ContDiff ℝ ∞ (boundedRadialDiskMap (N := N) s) :=
  OpenPartialHomeomorph.contDiff_univUnitBall.const_smul (Real.sqrt 2 * s)

theorem boundedRadialDiskMap_zero (s : ℝ) : boundedRadialDiskMap s (0 : N) = 0 := by
  rw [boundedRadialDiskMap, OpenPartialHomeomorph.univUnitBall_apply_zero, smul_zero]

theorem boundedRadialDiskMap_sphere (s : ℝ) {x : N} (hx : ‖x‖ = 1) :
    boundedRadialDiskMap s x = s • x := by
  rw [boundedRadialDiskMap, OpenPartialHomeomorph.univUnitBall_apply, hx,
    one_pow, show (1 : ℝ) + 1 = 2 by norm_num, smul_smul]
  congr 1
  have hr : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp

theorem boundedRadialDiskMap_injective {s : ℝ} (hs : 0 < s) :
    Injective (boundedRadialDiskMap (N := N) s) := by
  intro x y hxy
  have he : OpenPartialHomeomorph.univUnitBall x = OpenPartialHomeomorph.univUnitBall y :=
    smul_right_injective N (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs).ne' hxy
  exact OpenPartialHomeomorph.univUnitBall.injOn (mem_univ x) (mem_univ y) he

theorem boundedRadialDiskMap_derivative_injective {s : ℝ} (hs : 0 < s) (x : N) :
    Injective (fderiv ℝ (boundedRadialDiskMap (N := N) s) x) := by
  have hunit : ContDiff ℝ ∞ (OpenPartialHomeomorph.univUnitBall : N → N) :=
    OpenPartialHomeomorph.contDiff_univUnitBall
  have he : fderiv ℝ (boundedRadialDiskMap (N := N) s) x =
      (Real.sqrt 2 * s) • fderiv ℝ (OpenPartialHomeomorph.univUnitBall : N → N) x :=
    ((hunit.differentiable (by simp) x).hasFDerivAt.const_smul (Real.sqrt 2 * s)).fderiv
  have hi : Injective (fderiv ℝ (OpenPartialHomeomorph.univUnitBall : N → N) x) := by
    have hh := (PartialChart.bijective_mfderiv (smoothUnitBallChart (N := N)) (mem_univ x)).injective
    change Injective (mfderiv 𝓘(ℝ, N) 𝓘(ℝ, N)
      (OpenPartialHomeomorph.univUnitBall : N → N) x : N →L[ℝ] N) at hh
    rwa [mfderiv_eq_fderiv] at hh
  rw [he]
  intro u v huv
  exact hi (smul_right_injective N (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs).ne' huv)

theorem boundedRadialDiskMap_norm_le_one {s : ℝ} (hs : 0 ≤ s) (hs₁ : s ≤ 1 / 2) (x : N) :
    ‖boundedRadialDiskMap s x‖ ≤ 1 := by
  have hnorm : ‖(OpenPartialHomeomorph.univUnitBall : N → N) x‖ < 1 :=
    mem_ball_zero_iff.mp (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ x))
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hscalar : 0 ≤ Real.sqrt 2 * s := mul_nonneg (Real.sqrt_nonneg _) hs
  rw [boundedRadialDiskMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar]
  exact mul_le_one₀ (by nlinarith) (norm_nonneg _) hnorm.le

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
