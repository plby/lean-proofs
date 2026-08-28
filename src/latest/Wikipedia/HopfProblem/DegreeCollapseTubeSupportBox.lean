import Wikipedia.HopfProblem.DegreeCollapseCleanTwoSheetTube

/-!
# A compact support box extending beyond both ends of the clean tube

Openness of the actual source gives a longitudinal interval extending
past zero and one. Compactness supplies one positive transverse radius on
the enlarged interval. The resulting whole closed box remains in the
original chart, including all of its boundary faces.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_tube_support_box
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) :
    ∃ l u r : ℝ, l < 0 ∧ 1 < u ∧ 0 < r ∧
      Icc l u ×ˢ closedBall (0 : V) r ⊆ Φ.source := by
  let U : Set ℝ := (fun t : ℝ => (t, (0 : V))) ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage (continuous_id.prodMk continuous_const)
  have h0U : (0 : ℝ) ∈ U := haxis ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1U : (1 : ℝ) ∈ U := haxis ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨a, ha, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0U)
  obtain ⟨b, hb, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h1U)
  have hwide : Icc (-a) (1 + b) ⊆ U := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hball0
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_neg ht0]
      linarith [ht.1]
    · by_cases ht1 : 1 < t
      · apply hball1
        rw [mem_closedBall, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
        linarith [ht.2]
      · exact haxis ⟨⟨le_of_not_gt ht0, le_of_not_gt ht1⟩, rfl⟩
  have hwideAxis : Icc (-a) (1 + b) ×ˢ {(0 : V)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hwide ht
  obtain ⟨r, hr, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_Icc Φ.open_source hwideAxis
  exact ⟨-a, 1 + b, r, by linarith, by linarith, hr, hprod⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
