import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalGluing

/-!
# Fibre-linear trivialization over a compact interval

The interval-trivialization argument is carried out with native complex-linear
trivializations throughout. The gluing operations preserve linearity, including
the coordinate adjustment at each seam. This strengthens the existing
topological interval theorem by retaining the vector-bundle structure.

This is a pathwise result. It does not supply a continuous choice of these
trivializations when the path itself varies in a family.
-/

noncomputable section

open Bundle Set Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

variable {B : Type*} [TopologicalSpace B] [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [DenselyOrdered B] (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- A native complex vector bundle with model fibre `ℂ` admits a genuinely
complex-linear trivialization over any closed interval in a densely ordered
conditionally complete base. -/
theorem exists_linear_trivialization_Icc_subset (a b : B) :
    ∃ e : Trivialization ℂ (π ℂ V), e.IsLinear ℂ ∧ Icc a b ⊆ e.baseSet := by
  classical
  let ea := trivializationAt ℂ V a
  have hea : a ∈ ea.baseSet := FiberBundle.mem_baseSet_trivializationAt ℂ V a
  rcases lt_or_ge b a with hba | hab
  · exact ⟨ea, inferInstance, by simp [Icc_eq_empty_of_lt hba]⟩
  let s : Set B := {x ∈ Icc a b |
    ∃ e : Trivialization ℂ (π ℂ V), e.IsLinear ℂ ∧ Icc a x ⊆ e.baseSet}
  have ha : a ∈ s := ⟨left_mem_Icc.mpr hab, ea, inferInstance, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have hcs : c ∈ s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    let ec := trivializationAt ℂ V c
    have hec : c ∈ ec.baseSet := FiberBundle.mem_baseSet_trivializationAt ℂ V c
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).mp
        (mem_nhdsWithin_of_mem_nhds (ec.open_baseSet.mem_nhds hec))
    obtain ⟨d, ⟨hdab, ead, hlin, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c :=
      hsc.exists_between hc'.2
    let := hlin
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd),
      inferInstance, subset_ite.mpr ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩,
      fun x hx => hc'e ⟨hd.1.trans (not_le.mp hx.2), hx.1.2⟩⟩
  obtain ⟨-, ec, hlin, hec⟩ := hcs
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, hlin, heq ▸ hec⟩
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).mp
      (mem_nhdsWithin_of_mem_nhds (ec.open_baseSet.mem_nhds (hec ⟨hc.1, le_rfl⟩)))
  have had : Ico a d ⊆ ec.baseSet :=
    Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  obtain ⟨d', hcd', hd'd⟩ := exists_between hdcb.1
  have hd's : d' ∈ s :=
    ⟨⟨hc.1.trans hcd'.le, hd'd.le.trans hdcb.2⟩, ec, hlin,
      (Icc_subset_Ico_right hd'd).trans had⟩
  exact ((hsc.1 hd's).not_gt hcd').elim

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
