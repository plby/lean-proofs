import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Ordinary derivatives are determined by the original closed annulus

Every annulus point belongs to a closed ball of radius one half contained
in the annulus. Thus within-derivatives are unique even at either boundary
sphere. Exact agreement on an inner or outer annulus collar consequently
determines the ordinary derivative there. No equality outside the annulus
is inferred from the retained collar values.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

theorem uniqueDiffOn_domain (p : ℕ) : UniqueDiffOn ℝ (domain p) := by
  intro x hx
  have hx₀ : x ≠ 0 := ne_zero ⟨x, hx⟩
  let q := NormedSpace.normalize x
  let c := (3 / 2 : ℝ) • q
  have hq : ‖q‖ = 1 := NormedSpace.norm_normalize hx₀
  have hc : ‖c‖ = 3 / 2 := by
    change ‖(3 / 2 : ℝ) • q‖ = 3 / 2
    rw [norm_smul, hq]
    norm_num
  have hball : closedBall c (1 / 2) ⊆ domain p := by
    intro y hy
    have hd : ‖y - c‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hn : |‖y‖ - 3 / 2| ≤ 1 / 2 := by
      simpa only [hc] using (abs_norm_sub_norm_le y c).trans hd
    obtain ⟨hl, hr⟩ := abs_le.mp hn
    constructor <;> linarith
  have he : x - c = (‖x‖ - 3 / 2) • q := by
    dsimp only [c]
    rw [sub_smul]
    change x - (3 / 2 : ℝ) • q = ‖x‖ • NormedSpace.normalize x - (3 / 2 : ℝ) • q
    rw [NormedSpace.norm_smul_normalize]
  have hxball : x ∈ closedBall c (1 / 2) := by
    rw [mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, hq, mul_one]
    have hl := hx.1
    have hr := hx.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hu : UniqueDiffOn ℝ (closedBall c (1 / 2)) :=
    uniqueDiffOn_convex (convex_closedBall c (1 / 2))
      ⟨c, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds c (by norm_num))⟩
  exact (hu x hxball).mono hball

variable {p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_eq_of_inner_collar (H G : Vector (p + 1) → F) (r : ℝ)
    (heq : ∀ y ∈ domain p, ‖y‖ ≤ r → H y = G y)
    {x : Vector (p + 1)} (hx : x ∈ domain p) (hxr : ‖x‖ < r)
    (hH : DifferentiableAt ℝ H x) (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ H x = fderiv ℝ G x := by
  have hn : {y : Vector (p + 1) | ‖y‖ < r} ∈ 𝓝 x :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hxr
  have he : H =ᶠ[𝓝[domain p] x] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with y hy hyr
    exact heq y hy hyr.le
  have hd : fderivWithin ℝ H (domain p) x = fderivWithin ℝ G (domain p) x :=
    he.fderivWithin_eq_of_mem hx
  have hu := uniqueDiffOn_domain p x hx
  rw [fderivWithin_eq_fderiv hu hH, fderivWithin_eq_fderiv hu hG] at hd
  exact hd

theorem fderiv_eq_of_outer_collar (H G : Vector (p + 1) → F) (r : ℝ)
    (heq : ∀ y ∈ domain p, r ≤ ‖y‖ → H y = G y)
    {x : Vector (p + 1)} (hx : x ∈ domain p) (hxr : r < ‖x‖)
    (hH : DifferentiableAt ℝ H x) (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ H x = fderiv ℝ G x := by
  have hn : {y : Vector (p + 1) | r < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hxr
  have he : H =ᶠ[𝓝[domain p] x] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with y hy hyr
    exact heq y hy hyr.le
  have hd : fderivWithin ℝ H (domain p) x = fderivWithin ℝ G (domain p) x :=
    he.fderivWithin_eq_of_mem hx
  have hu := uniqueDiffOn_domain p x hx
  rw [fderivWithin_eq_fderiv hu hH, fderivWithin_eq_fderiv hu hG] at hd
  exact hd

end NoExoticSixSphere.SphereAnnulus
