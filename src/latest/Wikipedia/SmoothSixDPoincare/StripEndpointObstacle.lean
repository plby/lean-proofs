import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# Exact second-sheet contact along the whole strip

If the center interior misses a closed obstacle and the two endpoint germs
meet it exactly on the vertical endpoint axes, one positive-width strip
neighborhood has precisely those contacts. This fills the gap between
compact interior avoidance and endpoint corner control, without changing
the strip map or either endpoint germ.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Shrink one strip to give exactly the prescribed endpoint contacts with the full obstacle. -/
theorem exists_strip_neighborhood_with_exact_endpoint_contacts
    {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ k W) (hW : IsOpen W)
    (hKW : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ W)
    {B : Set M} (hB : IsClosed B)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, k (t, 0) ∉ B)
    (hc₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 0)
    (hc₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (ℝ × ℝ), IsOpen U ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ U ∧ U ⊆ W ∧
      ∀ p ∈ U, k p ∈ B ↔ p.1 = 0 ∨ p.1 = 1 := by
  obtain ⟨V₀, hV₀sub, hV₀, h0V₀⟩ := _root_.mem_nhds_iff.mp hc₀
  obtain ⟨V₁, hV₁sub, hV₁, h1V₁⟩ := _root_.mem_nhds_iff.mp hc₁
  let L := V₀ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Iio (1 / 3)
  let R := V₁ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Ioi (2 / 3)
  let C := (W ∩ k ⁻¹' Bᶜ) ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Ioo 0 1
  have hL : IsOpen L := hV₀.inter (isOpen_Iio.preimage continuous_fst)
  have hR : IsOpen R := hV₁.inter (isOpen_Ioi.preimage continuous_fst)
  have hC : IsOpen C := (hk.continuousOn.isOpen_inter_preimage hW hB.isOpen_compl).inter
    (isOpen_Ioo.preimage continuous_fst)
  let U := W ∩ ((L ∪ R) ∪ C)
  have hU : IsOpen U := hW.inter ((hL.union hR).union hC)
  have hKU : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have htW := hKW ⟨ht, rfl⟩
    refine ⟨htW, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inl ⟨h0V₀, by change (0 : ℝ) < 1 / 3; norm_num⟩)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (Or.inr ⟨h1V₁, by change (2 / 3 : ℝ) < 1; norm_num⟩)
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact Or.inr ⟨⟨htW, havoid t hti⟩, hti⟩
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset isCompact_Icc hU hKU
  refine ⟨ε, hε, U, hU, ?_, inter_subset_left, ?_⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  · intro p hp
    rcases hp.2 with (hpL | hpR) | hpC
    · have hcontact : k p ∈ B ↔ p.1 = 0 := hV₀sub hpL.1
      have hlt : p.1 < 1 / 3 := hpL.2
      constructor
      · exact fun h => Or.inl (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · exact hcontact.mpr h0
        · rw [h1] at hlt
          norm_num at hlt
    · have hcontact : k p ∈ B ↔ p.1 = 1 := hV₁sub hpR.1
      have hgt : 2 / 3 < p.1 := hpR.2
      constructor
      · exact fun h => Or.inr (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · rw [h0] at hgt
          norm_num at hgt
        · exact hcontact.mpr h1
    · have hnot : k p ∉ B := hpC.1.2
      have hti : p.1 ∈ Ioo (0 : ℝ) 1 := hpC.2
      constructor
      · exact fun h => (hnot h).elim
      · intro h
        rcases h with h0 | h1
        · exact (hti.1.ne' h0).elim
        · exact (hti.2.ne h1).elim

end Wikipedia.SmoothSixDPoincare
