/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted to this repository's Mathlib version from the complete proof in
https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962.
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Local equicontinuity of bounded holomorphic families

Schwarz's derivative estimate gives the equicontinuity needed for the
actual compact normal-family argument in the Riemann mapping theorem.
All proofs run with the ordinary Lean resource limits.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Uniformity

namespace Wikipedia.HopfProblem.RiemannMapping

theorem uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ι → E → F} {s U : Set E} {r : ℝ} (hr₀ : 0 < r) (hU : thickening r s ⊆ U)
    (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (self_subset_thickening hr₀ _).trans hU
  rw [(uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use min δ r, by positivity
  simp only [mem_ofPred, mem_inter_iff, prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [thickening_eq_biUnion_ball, iUnion₂_subset_iff] at hU
  calc
    dist (f i x) (f i y) ≤ (2 * C / r) * dist x y := by
      apply dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [mem_closedBall, two_mul]
        exact dist_le_norm_add_norm _ _ |>.trans <|
          add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

theorem equicontinuousAt_of_forall_norm_le {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ι → E → F} {U : Set E} {x : E} (hU : U ∈ 𝓝 x)
    (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    EquicontinuousAt f x := by
  rcases nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have : thickening (r / 2) (ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have := uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le (by positivity) this
    hfd hf |>.equicontinuousOn x (by simpa)
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.mpr (ball_mem_nhds _ (by positivity))] at this

end Wikipedia.HopfProblem.RiemannMapping
