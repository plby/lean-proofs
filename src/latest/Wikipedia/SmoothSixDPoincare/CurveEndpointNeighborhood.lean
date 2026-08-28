import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity
import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability
import Mathlib.Topology.DiscreteSubset

/-!
# Constructed clean endpoint neighborhoods

Distinct endpoint values and injective native derivatives at the two endpoints
give one compact neighborhood on which the whole curve is embedded and immersive.
It misses every finite obstacle away from the endpoint parameters, even when
the endpoints themselves belong to that obstacle.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Clean endpoint neighborhoods follow from the actual endpoint values and derivatives. -/
theorem exists_clean_curve_endpoint_neighborhood {f : ℝ → N}
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hxy : f 0 ≠ f 1)
    (hi0 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 1)) {S : Set N} (hS : S.Finite) :
    ∃ C : Set ℝ, IsCompact C ∧ {(0 : ℝ), 1} ⊆ interior C ∧ InjOn f C ∧
      (∀ t ∈ C, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      (∀ t ∈ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ S) := by
  let B : Set ℝ := {0, 1}
  have hB : IsCompact B := ((finite_singleton (1 : ℝ)).insert 0).isCompact
  have h0B : (0 : ℝ) ∈ B := by simp [B]
  have h1B : (1 : ℝ) ∈ B := by simp [B]
  have hinjB : InjOn f B := by
    intro s hs t ht heq
    simp only [B, mem_insert_iff, mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact (hxy heq).elim
    · exact (hxy heq.symm).elim
    · rfl
  have hiB : ∀ t ∈ B, Injective (mfderiv 𝓘(ℝ, ℝ) J f t) := by
    intro t ht
    simp only [B, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hi0
    · exact hi1
  obtain ⟨V, hV, hBV, hinjV⟩ := exists_open_injOn_near_compact hf hB hinjB hiB
  let R := S \ {f 0, f 1}
  have hR : IsClosed R := (hS.subset sdiff_subset).isClosed
  let U := (V ∩ {t | Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}) ∩ f ⁻¹' Rᶜ
  have hU : IsOpen U := (hV.inter (isOpen_injective_derivative hf)).inter
    (hR.isOpen_compl.preimage hf.continuous)
  have hBU : B ⊆ U := by
    intro t ht
    refine ⟨⟨hBV ht, hiB t ht⟩, ?_⟩
    simp only [B, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [R]
  obtain ⟨C, hC, hBC, hCU⟩ := exists_compact_between hB hU hBU
  refine ⟨C, hC, hBC, hinjV.mono (fun t ht => (hCU ht).1.1),
    fun t ht => (hCU ht).1.2, ?_⟩
  intro t ht htB htS
  apply (hCU ht).2
  refine ⟨htS, ?_⟩
  intro hends
  simp only [mem_insert_iff, mem_singleton_iff] at hends
  rcases hends with h0 | h1
  · have ht0 : t = 0 := hinjV (hCU ht).1.1 (hBV h0B) h0
    exact htB (by simp [ht0])
  · have ht1 : t = 1 := hinjV (hCU ht).1.1 (hBV h1B) h1
    exact htB (by simp [ht1])

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
