import Wikipedia.SmoothSixDPoincare.CompactCoincidenceNeighborhood
import Wikipedia.SmoothSixDPoincare.CornerOverlapNeighborhood
import Wikipedia.SmoothSixDPoincare.CornerStripData
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# Shrinking a shared-corner strip pair without extra intersections

The center arcs meet only at their matching endpoints. Compactness then
confines every intersection of sufficiently thin strips to the common corner
patches. Injectivity of the actual corner maps determines the coordinate
identifications at every such intersection.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

/-- The two strip neighborhoods have no intersections except their prescribed corner overlaps. -/
theorem exists_clean_strip_pair_neighborhoods
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hcoinc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, a t = b s →
      (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∃ U : Set (ℝ × ℝ), ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧ IsOpen V ∧
        Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ U ∧
        Icc (0 : ℝ) 1 ×ˢ Icc (-δ) δ ⊆ V ∧ U ⊆ k.domain ∧ V ⊆ l.domain ∧
        ∀ p ∈ U, ∀ q ∈ V, k.map p = l.map q →
          p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap := by
  have hswap : Continuous (Prod.swap : (ℝ × ℝ) → ℝ × ℝ) := by fun_prop
  have hrev := StripCoordinates.contDiff_reverse.continuous
  obtain ⟨U₀, V₀, hU₀, hV₀, h0U₀, h0V₀, hover₀⟩ :=
    exists_open_corner_overlap c₀.open_domain c₀.injective
      (continuousAt_id : ContinuousAt (id : (ℝ × ℝ) → ℝ × ℝ) (0, 0))
      (hswap.continuousAt (x := (0, 0))) c₀.contains_zero c₀.contains_zero
      k.left_germ l.left_germ
  obtain ⟨U₁, V₁, hU₁, hV₁, h1U₁, h1V₁, hover₁⟩ :=
    exists_open_corner_overlap c₁.open_domain c₁.injective
      (hrev.continuousAt (x := (1, 0)))
      ((hswap.comp hrev).continuousAt (x := (1, 0)))
      (by rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      (by change (StripCoordinates.reverse (1, 0)).swap ∈ c₁.domain
          rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      k.right_germ l.right_germ
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKk : K ⊆ k.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hKl : K ⊆ l.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hk : ∀ p ∈ K, ContinuousAt k.map p := fun p hp =>
    k.smooth.continuousOn.continuousAt (k.open_domain.mem_nhds (hKk hp))
  have hl : ∀ p ∈ K, ContinuousAt l.map p := fun p hp =>
    l.smooth.continuousOn.continuousAt (l.open_domain.mem_nhds (hKl hp))
  let O := (U₀ ×ˢ V₀) ∪ (U₁ ×ˢ V₁)
  have hO : IsOpen O := (hU₀.prod hV₀).union (hU₁.prod hV₁)
  have hcenter : ∀ p ∈ K, ∀ q ∈ K, k.map p = l.map q → (p, q) ∈ O := by
    rintro ⟨t, r⟩ ⟨ht, hr⟩ ⟨s, v⟩ ⟨hs, hv⟩ heq
    have hr0 : r = 0 := hr
    have hv0 : v = 0 := hv
    subst r
    subst v
    rw [k.center t ht, l.center s hs] at heq
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨h0U₀, h0V₀⟩
    · exact Or.inr ⟨h1U₁, h1V₁⟩
  obtain ⟨U', V', hU', hV', hKU', hKV', hcoinc'⟩ :=
    exists_open_neighborhoods_with_coincidences_in hK hK hk hl hO hcenter
  let U := U' ∩ k.domain
  let V := V' ∩ l.domain
  have hU : IsOpen U := hU'.inter k.open_domain
  have hV : IsOpen V := hV'.inter l.open_domain
  have hKU : K ⊆ U := fun p hp => ⟨hKU' hp, hKk hp⟩
  have hKV : K ⊆ V := fun p hp => ⟨hKV' hp, hKl hp⟩
  obtain ⟨ε, hε, hεU⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_Icc hU hKU
  obtain ⟨δ, hδ, hδV⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_Icc hV hKV
  have hrect {r : ℝ} {W : Set (ℝ × ℝ)}
      (h : Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r ⊆ W) :
      Icc (0 : ℝ) 1 ×ˢ Icc (-r) r ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply h
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  refine ⟨ε, hε, δ, hδ, U, V, hU, hV, hrect hεU, hrect hδV,
    inter_subset_right, inter_subset_right, ?_⟩
  intro p hp q hq heq
  rcases hcoinc' p hp.1 q hq.1 heq with hleft | hright
  · exact Or.inl ((hover₀ p hleft.1 q hleft.2).mp heq)
  · exact Or.inr ((hover₁ p hright.1 q hright.2).mp heq)

end Wikipedia.SmoothSixDPoincare
