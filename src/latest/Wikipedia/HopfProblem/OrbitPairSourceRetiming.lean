import Wikipedia.HopfProblem.OrbitPairTimeProfileDiffeomorph
import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# Retiming a sphere family while restoring its new time coordinate

The retimed family is `F ∘ Ψ`, but its track is `(t, F (Ψ (t,x)))`.
It is not the old track precomposed by `Ψ`, whose first coordinate would be
the changed old time. Smoothness, exact support, and the prescribed local
collision are proved here. Global collision control and spatial immersion
after a nonuniform time change are separate geometric requirements.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

def retimedFamily (F : ℝ × M → N)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞) :
    ℝ × M → N := F ∘ Ψ

theorem retimedFamily_smooth {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (retimedFamily F Ψ) := hF.comp Ψ.contMDiff

theorem track_retimedFamily (F : ℝ × M → N)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞)
    (p : ℝ × M) : track (retimedFamily F Ψ) p = (p.1, F (Ψ p)) := rfl

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_supported_retimed_family {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    {C U : Set M} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    {a b t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (ht₁ : t₁ ∈ Ioo a b) :
    ∃ G : ℝ × M → N, ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ G ∧
      (∀ t x, x ∉ U ∨ t ∉ Ioo a b → G (t, x) = F (t, x)) ∧
      (∀ x ∈ C, G =ᶠ[𝓝 (t₀, x)] fun p => F (p.1 + (t₁ - t₀), p.2)) ∧
      (∀ x ∈ C, G (t₀, x) = F (t₁, x)) := by
  obtain ⟨Ψ, -, hfixed, hgerm, hpoint, -⟩ :=
    exists_supported_source_time_diffeomorph (I := I) hC hU hCU ht₀ ht₁
  refine ⟨retimedFamily F Ψ, retimedFamily_smooth hF Ψ, ?_, ?_, ?_⟩
  · intro t x h
    change F (Ψ (t, x)) = F (t, x)
    rw [hfixed t x h]
  · intro x hx
    filter_upwards [hgerm x hx] with p hp
    exact congrArg F hp
  · intro x hx
    exact congrArg F (hpoint x hx)

theorem exists_supported_retimed_collision {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    {x y : M} (hne : x ≠ y) {U : Set M} (hU : IsOpen U) (hx : x ∈ U) (hy : y ∈ U)
    {a b t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (ht₁ : t₁ ∈ Ioo a b)
    (hcollision : F (t₁, x) = F (t₁, y)) :
    ∃ G : ℝ × M → N, ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ G ∧
      (∀ t z, z ∉ U ∨ t ∉ Ioo a b → G (t, z) = F (t, z)) ∧
      (t₀, (x, y)) ∈ FamilyDoublePoints.doublePoints G := by
  have hCU : ({x, y} : Set M) ⊆ U := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · rcases mem_singleton_iff.mp hz with rfl
      exact hy
  obtain ⟨G, hG, hfixed, -, hpoint⟩ :=
    exists_supported_retimed_family hF ((finite_singleton y).insert x).isClosed hU hCU ht₀ ht₁
  refine ⟨G, hG, hfixed, hne, ?_⟩
  rw [hpoint x (mem_insert _ _), hpoint y (mem_insert_of_mem _ (mem_singleton _))]
  exact hcollision

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
