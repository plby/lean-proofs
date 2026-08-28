import Wikipedia.HopfProblem.OrbitPairCleanTrackNeighborhood

/-!
# Excluding remote branches from a prescribed finite-fiber neighborhood

Compactness of the spatial source turns containment of one entire track
fiber in an open source region into an ambient neighborhood with its entire
track preimage in that region. Only a bounded time slab is used.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {M N : Type*}
  [TopologicalSpace M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N]

theorem exists_open_track_neighborhood_of_fiber_subset
    {F : ℝ × M → N} (hF : Continuous F) (q : ℝ × M)
    {V : Set (ℝ × M)} (hV : IsOpen V)
    (hfiber : ∀ x, F (q.1, x) = F q → (q.1, x) ∈ V)
    {a b : ℝ} (ha : a < q.1) (hb : q.1 < b) :
    ∃ O : Set (ℝ × N), IsOpen O ∧ track F q ∈ O ∧
      O ⊆ Ioo a b ×ˢ univ ∧ track F ⁻¹' O ⊆ V := by
  let K : Set (ℝ × M) := (Icc a b ×ˢ univ) \ V
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).diff hV
  have htrack : Continuous (track F) := continuous_fst.prodMk hF
  have hclosed : IsClosed (track F '' K) := (hK.image htrack).isClosed
  have hnot : track F q ∉ track F '' K := by
    rintro ⟨p, hp, heq⟩
    have htime : p.1 = q.1 := congrArg (fun y : ℝ × N => y.1) heq
    have hvalue : F (q.1, p.2) = F q := by
      have hh : F p = F q := congrArg (fun y : ℝ × N => y.2) heq
      change F (p.1, p.2) = F q at hh
      rwa [htime] at hh
    have hpV := hfiber p.2 hvalue
    rw [← htime] at hpV
    exact hp.2 hpV
  let O : Set (ℝ × N) := (Ioo a b ×ˢ univ) ∩ (track F '' K)ᶜ
  refine ⟨O, (isOpen_Ioo.prod isOpen_univ).inter hclosed.isOpen_compl,
    ⟨⟨⟨ha, hb⟩, mem_univ _⟩, hnot⟩, inter_subset_left, ?_⟩
  intro p hp
  by_contra hpV
  have hpK : p ∈ K := ⟨⟨⟨hp.1.1.1.le, hp.1.1.2.le⟩, mem_univ _⟩, hpV⟩
  exact hp.2 ⟨p, hpK, rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
