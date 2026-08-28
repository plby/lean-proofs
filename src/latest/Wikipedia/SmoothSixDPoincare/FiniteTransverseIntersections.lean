import Wikipedia.SmoothSixDPoincare.EmbeddedSubmanifoldCrossing
import Mathlib.Topology.DiscreteSubset

/-!
# Isolated and finite intersections of native transverse embedded submanifolds

The constructed clean crossing chart isolates each intersection of the full
images. When the sheet manifolds are compact, their actual intersection set
is compact and discrete, hence finite. No finiteness assumption is used.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]

theorem exists_isolating_crossing_neighborhood {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G) (x : N) (y : P) (hxy : G y = F x)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    ∃ O : Set M, IsOpen O ∧ F x ∈ O ∧ O ∩ (range F ∩ range G) = {F x} := by
  obtain ⟨a, ha, Φ, hprod, -, -, hcenter, -, -, himages⟩ :=
    exists_clean_crossingChart hF hG hembF hembG x y hxy hdim ht isOpen_univ (mem_univ _)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩
  have hFx : F x ∈ Φ.target := hcenter ▸ Φ.map_source' h0Φ
  refine ⟨Φ.target, Φ.open_target, hFx, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwF, hwG⟩
    let q := Φ.invFun w
    have hq : q ∈ Φ.source := Φ.map_target' hw
    have heq : Φ q = w := Φ.right_inv' hw
    have hqF : Φ q ∈ range F := heq.symm ▸ hwF
    have hqG : Φ q ∈ range G := heq.symm ▸ hwG
    have hq0 : q = (0, 0) := Prod.ext ((himages q hq).2.mp hqG) ((himages q hq).1.mp hqF)
    exact mem_singleton_iff.mpr (heq.symm.trans ((congrArg Φ hq0).trans hcenter))
  · intro hw
    rcases mem_singleton_iff.mp hw with rfl
    exact ⟨hFx, ⟨x, rfl⟩, ⟨y, hxy⟩⟩

theorem isDiscrete_transverse_intersections {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) : IsDiscrete (range F ∩ range G) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro z ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
  obtain ⟨O, hO, -, heq⟩ :=
    exists_isolating_crossing_neighborhood hF hG hembF hembG x y hxy hdim (ht x y hxy)
  exact ⟨O, hO, heq⟩

/-- Compact native embedded submanifolds of complementary dimension have finitely many
intersections when their actual native tangent maps are transverse everywhere they meet. -/
theorem finite_transverse_intersections [CompactSpace N] [CompactSpace P]
    {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) : (range F ∩ range G).Finite := by
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  exact ((isCompact_range hF.continuous).inter_right
    (isCompact_range hG.continuous).isClosed).finite
    (isDiscrete_transverse_intersections hF hG hembF hembG hdim ht)

end Wikipedia.SmoothSixDPoincare
