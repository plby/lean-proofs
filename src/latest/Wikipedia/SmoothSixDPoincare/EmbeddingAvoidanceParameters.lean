import Wikipedia.SmoothSixDPoincare.SelfIntersectionParameters
import Wikipedia.SmoothSixDPoincare.ObstacleParameters

/-!
# Simultaneous self-intersection control and obstacle avoidance

The union of the self-intersection and obstacle bad-parameter images still
has dimension less than the parameter space. A single small good parameter
therefore removes obstacle collisions without introducing any source-source
coincidences. In particular it preserves every existing injective restriction.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E E' G F H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [TopologicalSpace N] [ChartedSpace K N]
  [LindelofSpace (X × X)] [LindelofSpace (X × Y)]

/-- One arbitrarily small valid parameter simultaneously avoids the smooth obstacle on the
active support and creates no new coincidences anywhere in the original source. -/
theorem exists_small_embedding_avoiding_parameter (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ Valid c f β a ∧ ContMDiff I J ∞ (perturb c f β a) ∧
      (∀ x y, perturb c f β a x = perturb c f β a y → f x = f y) ∧
      ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  have hdself : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hself
  have hdobstacle : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hobstacle
  have hs := GeneralPosition.dimH_image_manifold_le
    (isOpen_collisionDomain c hf.continuous hβ.continuous)
    (contMDiffOn_collisionParameter c hf hβ)
  have ho := GeneralPosition.dimH_image_manifold_le
    (isOpen_obstacleDomain c hf.continuous hg.continuous hβ.continuous)
    (contMDiffOn_obstacleParameter c hf hg hβ)
  have hdense : Dense ((collisionParameter c f β '' collisionDomain c f β) ∪
      (obstacleParameter c f g β '' obstacleDomain c f g β))ᶜ := by
    apply dense_compl_of_dimH_lt_finrank
    rw [dimH_union]
    exact max_lt (hs.trans_lt (Nat.cast_lt.mpr hdself))
      (ho.trans_lt (Nat.cast_lt.mpr hdobstacle))
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < min ε δ := by simpa only [dist_zero_left] using hnorm
  have hv := hvalid a (lt_min_iff.mp ha).2
  refine ⟨a, (lt_min_iff.mp ha).1, hv, contMDiff_perturb c hf hβ hsupport hv, ?_, ?_⟩
  · intro x y hxy
    exact (collision_imp_old_and_equal_cutoff c hsupport hv
      (fun h => hgood (Or.inl h)) hxy).1
  · exact avoids_of_not_obstacle_parameter c hsupport hv (fun h => hgood (Or.inr h))

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
