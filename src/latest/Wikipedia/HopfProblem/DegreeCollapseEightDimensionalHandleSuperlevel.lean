import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The transverse-ball superlevel for the unchanged handle

The function `r² - ‖v‖²` on the actual four-plus-four dimensional product
has zero set exactly the transverse sphere and is regular there for `r > 0`.
This gives a boundary atlas before restricting the four-disk coordinate to
its open unit ball.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel

open NoExoticSixSphere GLOrthonormalization

def level (r : ℝ) (p : Vector 4 × Vector 4) : ℝ := r ^ 2 - ‖p.2‖ ^ 2

theorem nonneg_iff {r : ℝ} (hr : 0 < r) (p : Vector 4 × Vector 4) :
    0 ≤ level r p ↔ p.2 ∈ closedBall (0 : Vector 4) r := by
  rw [mem_closedBall, dist_zero_right]
  change 0 ≤ r ^ 2 - ‖p.2‖ ^ 2 ↔ ‖p.2‖ ≤ r
  constructor <;> intro hp <;> nlinarith [norm_nonneg p.2]

theorem zero_iff {r : ℝ} (hr : 0 < r) (p : Vector 4 × Vector 4) :
    level r p = 0 ↔ p.2 ∈ sphere (0 : Vector 4) r := by
  rw [mem_sphere, dist_zero_right]
  change r ^ 2 - ‖p.2‖ ^ 2 = 0 ↔ ‖p.2‖ = r
  constructor <;> intro hp <;> nlinarith [norm_nonneg p.2]

theorem contDiff_level (r : ℝ) : ContDiff ℝ ∞ (level r) :=
  contDiff_const.sub (contDiff_snd.norm_sq ℝ)

theorem fderiv_level_apply (r : ℝ) (p w : Vector 4 × Vector 4) :
    fderiv ℝ (level r) p w = -2 * inner ℝ p.2 w.2 := by
  have hs : HasFDerivAt (Prod.snd : Vector 4 × Vector 4 → Vector 4)
      (ContinuousLinearMap.snd ℝ (Vector 4) (Vector 4)) p := hasFDerivAt_snd
  have hn := (hasStrictFDerivAt_norm_sq p.2).hasFDerivAt.comp p hs
  have hd := ((hasFDerivAt_const (r ^ 2) p).sub hn).fderiv
  change fderiv ℝ (level r) p = _ at hd
  rw [hd]
  change 0 - (2 • innerSL ℝ p.2) w.2 = -2 * inner ℝ p.2 w.2
  rw [two_smul, add_apply]
  change 0 - (inner ℝ p.2 w.2 + inner ℝ p.2 w.2) = -2 * inner ℝ p.2 w.2
  ring

theorem regular_zero {r : ℝ} (hr : 0 < r) {p : Vector 4 × Vector 4}
    (hp : level r p = 0) : Surjective (fderiv ℝ (level r) p) := by
  have hv : ‖p.2‖ = r := by
    simpa only [mem_sphere, dist_zero_right] using (zero_iff hr p).mp hp
  have hn : ‖p.2‖ ≠ 0 := by rw [hv]; exact ne_of_gt hr
  intro y
  refine ⟨(0, (-y / (2 * ‖p.2‖ ^ 2)) • p.2), ?_⟩
  rw [fderiv_level_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

def superlevelAtlas {r : ℝ} (hr : 0 < r) :
    SuperlevelAtlas (K := Vector 7) 𝓘(ℝ, Vector 4 × Vector 4) (level r) :=
  Classical.choice (nonempty_superlevelAtlas (contDiff_level r).contMDiff
    (fun _ hp ↦ by rw [mfderiv_eq_fderiv]; exact regular_zero hr hp) 7 (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]))

end Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalHandleSuperlevel
