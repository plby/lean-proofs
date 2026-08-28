import Wikipedia.HopfProblem.DegreeCollapseSheetArcTube

/-!
# Restricting a tube to recognize both entire closed sheets

Near the distinguished endpoint, retain the actual sheet equation supplied
by the chart germ. At every other axis point, closedness excludes the whole
sheet in an open neighborhood. These neighborhoods construct one open tube
where the exact equation holds everywhere, with a positive uniform radius.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_open_tube_sheet_recognition
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    {K : Set ℝ} (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source)
    {S : Set M} (hS : IsClosed S) (p : ℝ) (N : Set V)
    (hlocal : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (haway : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S) :
    ∃ W : Set (ℝ × V), IsOpen W ∧ K ×ˢ {(0 : V)} ⊆ W ∧ W ⊆ Φ.source ∧
      ∀ z ∈ W, Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N := by
  obtain ⟨U, hUgood, hU, hpU⟩ := _root_.mem_nhds_iff.mp hlocal
  let A : Set (ℝ × V) := (Φ.source ∩ Φ ⁻¹' Sᶜ) ∩ {z | z.1 ≠ p}
  have hA : IsOpen A :=
    (Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hS.isOpen_compl).inter
      (isOpen_ne_fun continuous_fst continuous_const)
  let W := Φ.source ∩ (U ∪ A)
  refine ⟨W, Φ.open_source.inter (hU.union hA), ?_, inter_subset_left, ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hKsource ⟨ht, rfl⟩, ?_⟩
    by_cases htp : t = p
    · subst t
      exact Or.inl hpU
    · exact Or.inr ⟨⟨hKsource ⟨ht, rfl⟩, haway t ht htp⟩, htp⟩
  · intro z hz
    rcases hz.2 with hzU | hzA
    · exact hUgood hzU
    · constructor
      · intro h
        exact (hzA.1.2 h).elim
      · rintro ⟨h, -⟩
        exact (hzA.2 h).elim

theorem exists_clean_axis_tube_restriction
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    {K : Set ℝ} (hK : IsCompact K) (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source)
    {S T : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℝ) (N P : Set V)
    (hlocalS : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (hlocalT : ∀ᶠ z in 𝓝 (q, (0 : V)), Φ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P)
    (hawayS : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S)
    (hawayT : ∀ t ∈ K, t ≠ q → Φ (t, 0) ∉ T) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞,
        K ×ˢ closedBall (0 : V) ε ⊆ Ψ.source ∧
        (∀ z, Ψ z = Φ z) ∧ Ψ.target ⊆ Φ.target ∧
        (∀ z ∈ Ψ.source, Ψ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N) ∧
        (∀ z ∈ Ψ.source, Ψ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P) := by
  obtain ⟨U, hU, hKU, -, hSU⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hS p N hlocalS hawayS
  obtain ⟨W, hW, hKW, -, hTW⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hT q P hlocalT hawayT
  let Ψ := PartialChart.restrictSource Φ (hU.inter hW)
  have hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source :=
    fun z hz => ⟨hKsource hz, hKU hz, hKW hz⟩
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzero
  exact ⟨ε, hε, Ψ, hprod, fun _ => rfl, fun _ hz => hz.1,
    fun z hz => hSU z hz.2.1, fun z hz => hTW z hz.2.2⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
