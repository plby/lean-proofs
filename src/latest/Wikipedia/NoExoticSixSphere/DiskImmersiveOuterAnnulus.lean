import Wikipedia.NoExoticSixSphere.GenericProperFourDisk
import Mathlib.Topology.Order.Compact

/-!
# Boundary immersion gives an actual immersive outer annulus

The singular set of a continuous operator field on the closed disk is
compact. If it misses the boundary, its norm has maximum strictly below
one. This produces a uniform outer annulus with no singularities; it does
not infer immersion on the rest of the disk.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_injective_outer_annulus (D : Vector 4 → Vector 4 →L[ℝ] F)
    (hD : ContinuousOn D (closedBall 0 1))
    (hi : ∀ x, ‖x‖ = 1 → Injective (D x)) :
    ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧
      ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (D x) := by
  let S : Set (Vector 4) := closedBall 0 1 ∩ {x | ¬ Injective (D x)}
  have hSc : IsClosed S :=
    hD.preimage_isClosed_of_isClosed isClosed_closedBall
      ContinuousLinearMap.isOpen_injective.isClosed_compl
  have hS : IsCompact S := (isCompact_closedBall (0 : Vector 4) 1).of_isClosed_subset
    hSc inter_subset_left
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne continuous_norm.continuousOn
    have hnorm : ‖x‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx.1) (by
      intro he
      exact hx.2 (hi x he))
    obtain ⟨ρ, hρ, hρ1⟩ := exists_between (max_lt (by norm_num : (3 / 4 : ℝ) < 1) hnorm)
    refine ⟨ρ, (le_max_left _ _).trans_lt hρ, hρ1, ?_⟩
    intro y hy hyρ
    by_contra hsing
    have hle : ‖y‖ ≤ ‖x‖ := hmax ⟨hy, hsing⟩
    exact (not_lt_of_ge (hle.trans' hyρ)) ((le_max_right _ _).trans_lt hρ)
  · refine ⟨7 / 8, by norm_num, by norm_num, ?_⟩
    intro x hx _
    by_contra hsing
    exact hne ⟨x, hx, hsing⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)

theorem exists_immersive_outer_annulus (f : Vector 4 → M)
    (hf : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ f x)
    (hi : ∀ q : Sphere 3, Injective (fderiv ℝ (e.toFun ∘ f) q.val)) :
    ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧
      ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  apply exists_injective_outer_annulus (fderiv ℝ (e.toFun ∘ f))
  · intro x hx
    exact ((e.smooth.contMDiffAt.comp x (hf x hx)).contDiffAt.continuousAt_fderiv
      (by simp)).continuousWithinAt
  · intro x hx
    exact hi ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩

end NoExoticSixSphere.GenericFourDisk
