import Wikipedia.NoExoticSixSphere.RelativeSphereNormalization
import Wikipedia.NoExoticSixSphere.CylinderTime

/-!
# Smooth sphere-valued homotopies with exact constant end collars

Extend a continuous homotopy to real time with constant ends, then apply
relative smooth approximation on the boundaryless real cylinder. Entire
closed end neighborhoods are protected, so the smooth representative has
exactly the original smooth endpoint maps on open collars. The original
homotopy class relative to the two endpoint slices is also preserved.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_smoothCollaredSphereHomotopy {n : ℕ} {f₀ f₁ : C(M, Sphere n)}
    (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (H : f₀.Homotopy f₁) :
    ∃ G : C(ℝ × M, Sphere n), ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ G ∧
      (∀ t : ℝ, t ≤ 1 / 4 → ∀ x, G (t, x) = f₀ x) ∧
      (∀ t : ℝ, 3 / 4 ≤ t → ∀ x, G (t, x) = f₁ x) ∧
      H.toContinuousMap.HomotopicRel (G.comp CylinderTime.inclusion) CylinderTime.boundary := by
  let F := CylinderTime.realCollaredMap H.toContinuousMap
  let S : Set (ℝ × M) := {p | p.1 ≤ 1 / 4 ∨ 3 / 4 ≤ p.1}
  let U : Set (ℝ × M) := {p | p.1 < 1 / 3 ∨ 2 / 3 < p.1}
  have hleft (p : ℝ × M) (hp : p.1 ≤ 1 / 3) : F p = f₀ p.2 := by
    change H (CylinderTime.collar p.1, p.2) = f₀ p.2
    rw [CylinderTime.collar_left hp]
    exact H.map_zero_left p.2
  have hright (p : ℝ × M) (hp : 2 / 3 ≤ p.1) : F p = f₁ p.2 := by
    change H (CylinderTime.collar p.1, p.2) = f₁ p.2
    rw [CylinderTime.collar_right hp]
    exact H.map_one_left p.2
  have hS : IsClosed S := (isClosed_le continuous_fst continuous_const).union
    (isClosed_le continuous_const continuous_fst)
  have hU : IsOpen U := (isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_const continuous_fst)
  have hSU : S ⊆ U := by
    intro p hp
    rcases hp with hp | hp
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hFU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ F U := by
    intro p hp
    rcases hp with hp | hp
    · have heq : (F : ℝ × M → Sphere n) =ᶠ[𝓝 p] (fun q ↦ f₀ q.2) := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
        exact hleft q hq.le
      exact ((h₀.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq : (F : ℝ × M → Sphere n) =ᶠ[𝓝 p] (fun q ↦ f₁ q.2) := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
        exact hright q hq.le
      exact ((h₁.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  obtain ⟨G, hG, hrel, _⟩ := exists_smoothSphereApproximation_rel
    (I := (𝓘(ℝ, ℝ)).prod I) n F hS (hU.mem_nhdsSet.mpr hSU) hFU 1 zero_lt_one
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro t ht x
    exact (hrel.fst_eq_snd (show (t, x) ∈ S from Or.inl ht)).symm.trans
      (hleft (t, x) (by change t ≤ 1 / 3; linarith))
  · intro t ht x
    exact (hrel.fst_eq_snd (show (t, x) ∈ S from Or.inr ht)).symm.trans
      (hright (t, x) (by change 2 / 3 ≤ t; linarith))
  · obtain ⟨K⟩ := hrel
    let K' : (CylinderTime.collaredMap H.toContinuousMap).HomotopyRel
        (G.comp CylinderTime.inclusion) CylinderTime.boundary :=
      { toHomotopy := K.toHomotopy.compContinuousMap CylinderTime.inclusion
        prop' := fun t p hp ↦ K.eq_fst t (by
          change (p.1 : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (p.1 : ℝ)
          rcases hp with hp | hp
          · left
            rw [hp]
            norm_num
          · right
            rw [hp]
            norm_num) }
    exact ⟨(CylinderTime.collarHomotopy H.toContinuousMap).trans K'⟩

end NoExoticSixSphere
