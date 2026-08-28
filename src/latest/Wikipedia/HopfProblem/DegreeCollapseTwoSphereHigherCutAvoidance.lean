import Wikipedia.HopfProblem.DegreeCollapseLevelBackwardObstruction
import Wikipedia.HopfProblem.DegreeCollapseRelativeOpenImageAvoidance

/-!
# Make the whole native two-sphere reach the higher cut without changing its belt relation

The complete noncrossing set is the constructed closed projected endpoint
image. Relative image avoidance changes the sphere only inside the whole
belt complement. The prescribed closed source set stays fixed, and every
coincidence with the original belt is retained exactly.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  [TopologicalSpace Y] [CompactSpace Y]

theorem AdaptedSurgeryWindows.exists_two_sphere_reaching_higher_cut_preserving_belt
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c b a : ℝ} (hcb : c < b) (hba : b ≤ a)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hlow : ∀ p : criticalPoints E f, c < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 2 + d < Module.finrank ℝ (RegularLevel.Model E))
    (γ : C(Hemisphere.Sphere 2, {y : M // f y = b}))
    (β : C(Y, {y : M // f y = b})) {C : Set (Hemisphere.Sphere 2)} (hC : IsClosed C)
    (hfixed : ∀ x ∈ C, (γ x).val ∈ FlowCancellation.levelBasin A.flow f a)
    (hcoincidence : ∀ x y, γ x = β y → x ∈ C) :
    let _ := RegularLevel.chartedSpace hf hb
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
    ∃ δ : C(Hemisphere.Sphere 2, {y : M // f y = b}),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ δ ∧ γ.HomotopicRel δ C ∧
      (∀ x, (δ x).val ∈ FlowCancellation.levelBasin A.flow f a) ∧
      ∀ x y, δ x = β y ↔ γ x = β y := by
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf hb
  dsimp only
  intro hγ
  let _ := A.finite.fintype
  let K := BetweenBackwardBasinIndex A c a
  let _ : Countable K := betweenBackwardBasinIndex_countable A c a
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold (𝓡 0) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨U, g, hg, hrange, hclosed⟩ := A.exists_native_higher_cut_obstacle hf
    hcb hba hb ha (γ (Hemisphere.point false ⟨0, mem_closedBall_self zero_le_one⟩)) hlow
  let V : Set {y : M // f y = b} := (range β)ᶜ
  have hV : IsOpen V := (isCompact_range β.continuous).isClosed.isOpen_compl
  have hfixed' (x : Hemisphere.Sphere 2) (hx : x ∈ C) : γ x ∉ range g := by
    rw [hrange]
    exact not_not.mpr (hfixed x hx)
  have hbadV (x : Hemisphere.Sphere 2) (hx : γ x ∈ range g) : γ x ∈ V := by
    rintro ⟨y, hy⟩
    exact hfixed' x (hcoincidence x y hy.symm) hx
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin d)) <
        Module.finrank ℝ (RegularLevel.Model E) := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  obtain ⟨δ, hδ, hrel, hdisj, heq⟩ :=
    RelativeOpenImageAvoidance.exists_disjoint_smooth_map_preserving_complement
      γ g hγ hg hclosed hdim' hC hfixed' hV hbadV
  refine ⟨δ, hδ, hrel, ?_, ?_⟩
  · intro x
    by_contra hx
    have hgx : δ x ∈ range g := by rw [hrange]; exact hx
    exact disjoint_left.mp hdisj (mem_range_self x) hgx
  · intro x y
    exact heq x (β y) (fun hy => hy (mem_range_self y))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
