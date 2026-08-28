import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
import Wikipedia.SmoothSixDPoincare.CompactAmbientIsotopy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Constructed supported point-moving isotopies

The scalar cutoff and positive motion radius are constructed from the open
chart domain. Every sufficiently nearby coordinate point can be reached by
a smooth family of global native diffeomorphisms fixed outside that chart.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

/-- The point-moving family, its compactly supported cutoff, and its radius are all constructed. -/
theorem exists_supported_pointMoving {x : E} (hx : x ∈ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ Φ.source ∧ ∀ y ∈ Metric.ball x ε,
      ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
        (∀ z, A (0, z) = z) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
        (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧
        A (1, Φ x) = Φ y := by
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hx)
  obtain ⟨δ, hδ, hmove⟩ := exists_small_supported_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx)
  refine ⟨min δ ρ, lt_min hδ hρ, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hρsource
  · intro y hy
    have hnear : ‖y - x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show dist y x < min δ ρ from hy).trans_le (min_le_left _ _)
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove (y - x) hnear
    refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
    · intro t z hz
      apply hfix t z
      rintro ⟨q, hq, rfl⟩
      exact hz (Φ.map_source' (hβsupport hq))
    · have hterminal := hend x hx
      rw [hβx, one_smul] at hterminal
      have hxy : x + (y - x) = y := by abel
      exact hterminal.trans (congrArg Φ hxy)

variable [CompactSpace M]

/-- On the original compact manifold these supported motions give an actual ambient isotopy:
a time-preserving cylinder homeomorphism through smooth diffeomorphisms,
starting at the identity. -/
theorem exists_supported_pointMoving_cylinder {x : E} (hx : x ∈ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ Φ.source ∧ ∀ y ∈ Metric.ball x ε,
      ∃ F : (unitInterval × M) ≃ₜ (unitInterval × M),
        (∀ p, (F p).1 = p.1) ∧ (∀ z, F (0, z) = (0, z)) ∧
        (∀ t : unitInterval, ∃ d : Diffeomorph J J M M ∞, ∀ z, F (t, z) = (t, d z)) ∧
        (∀ p, p.2 ∉ Φ.target → F p = p) ∧ F (1, Φ x) = (1, Φ y) := by
  obtain ⟨ε, hε, hsource, hmove⟩ := exists_supported_pointMoving Φ hx
  refine ⟨ε, hε, hsource, ?_⟩
  intro y hy
  obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove y hy
  have hbij : ∀ t, Function.Bijective (fun z => A (t, z)) := by
    intro t
    obtain ⟨d, hd⟩ := hdiff t
    have heq : (fun z => A (t, z)) = d := funext hd
    rw [heq]
    exact d.bijective
  let F := AmbientIsotopy.cylinderHomeomorph A hA.continuous hbij
  refine ⟨F, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro z
    exact Prod.ext rfl (hzero z)
  · intro t
    obtain ⟨d, hd⟩ := hdiff t
    exact ⟨d, fun z => Prod.ext rfl (hd z)⟩
  · rintro ⟨t, z⟩ hz
    exact Prod.ext rfl (hfix t z hz)
  · exact Prod.ext rfl hend

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
