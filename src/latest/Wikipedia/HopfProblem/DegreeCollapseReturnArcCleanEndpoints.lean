import Wikipedia.HopfProblem.DegreeCollapseEmbeddedReturnArc

/-!
# Clean endpoint neighborhoods for the return arc

The continuation germs point beyond the original short arc at both ends.
Injectivity of the original arc therefore excludes all interior contacts
near the return curve's endpoints. The construction gives a closed fixed
neighborhood whose interior contains both endpoints, suitable for relative
avoidance of the whole original short arc.
-/

noncomputable section

open Set Function Filter Metric TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {N : Type*} [TopologicalSpace N]

theorem exists_clean_return_endpoint_neighborhood
    {α β : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hinj : InjOn α (Icc (-R) R))
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ∃ C : Set ℝ, IsClosed C ∧ ({0, 1} : Set ℝ) ⊆ interior C ∧
      ∀ t ∈ Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → β t ∉ α '' Icc (-r) r := by
  have hp : r ∈ Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Ioo (-R) R := ⟨by linarith, by linarith⟩
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), β t = α (t + r) ∧ t + r ∈ Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), t + r ∈ Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Ioo (-R) R ∈ 𝓝 ((0 : ℝ) + r) by simpa only [zero_add] using Ioo_mem_nhds hp.1 hp.2))
    exact h0.and hn
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), β t = α (t + (-1 - r)) ∧
      t + (-1 - r) ∈ Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (1 : ℝ), t + (-1 - r) ∈ Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Ioo (-R) R ∈ 𝓝 ((1 : ℝ) + (-1 - r)) by
          simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using Ioo_mem_nhds hm.1 hm.2))
    exact h1.and hn
  obtain ⟨δ₀, hδ₀, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := closedBall 0 δ₀ ∪ closedBall 1 δ₁
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_of_superset (ball_mem_nhds 0 hδ₀)
    (fun _ ht => Or.inl (ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_of_superset (ball_mem_nhds 1 hδ₁)
    (fun _ ht => Or.inr (ball_subset_closedBall ht))
  refine ⟨C, isClosed_closedBall.union isClosed_closedBall, ?_, ?_⟩
  · intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  · intro t ht htB
    rintro ⟨s, hs, heq⟩
    have hsR : s ∈ Icc (-R) R := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rcases ht.2 with ht0 | ht1
    · have hg := hball0 ht0
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 0 := fun h => htB (Or.inl h)
      have htpos : 0 < t := lt_of_le_of_ne ht.1.1 htne.symm
      linarith [hs.2]
    · have hg := hball1 ht1
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 1 := fun h => htB (Or.inr h)
      have htlt : t < 1 := lt_of_le_of_ne ht.1.2 htne
      linarith [hs.1]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
