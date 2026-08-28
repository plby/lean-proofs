import Wikipedia.NoExoticSixSphere.SphereFourTubeRegularTime

/-!
# Uniform time-band separation for the actual tube exterior

Compactness gives positive lower bounds for the old time on the tube
and the new time on the transition region. A common narrow band therefore
separates the old collar from the new unit-tube collar. This does not yet
construct their combined collar homeomorphism.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

theorem exists_positive_gap_on_compact {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) {K : Set X} (hK : IsCompact K) (hf : ∀ x ∈ K, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c < f x := by
  rcases K.eq_empty_or_nonempty with hKempty | hne
  · refine ⟨1, zero_lt_one, ?_⟩
    simp only [hKempty, mem_empty_iff_false, false_implies, implies_true]
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne f.continuous.continuousOn
    exact ⟨f x / 2, half_pos (hf x hx),
      fun y hy ↦ (half_lt_self (hf x hx)).trans_le (hmin hy)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

theorem exists_separated_time_bands (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
    (hpos : ∀ x ∈ Φ.target, 0 < t x)
    (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
    (houter : ∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p))
    (w : ℝ) (hw : 0 < w) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w ∧ δ ≤ 1 / 2 ∧
      (∀ x, |t x| < δ → x ∉ closedRegion Φ 2) ∧
      (∀ x ∈ closedRegion Φ 2 \ openRegion Φ (3 / 2), δ < τ x) ∧
      ∀ x, |τ x| < δ → |t x| < δ ∨ x ∈ openRegion Φ (3 / 2) := by
  obtain ⟨c₀, hc₀, hgap₀⟩ := exists_positive_gap_on_compact t
    (isCompact_closedRegion Φ hΦ 2)
    (fun x hx ↦ hpos x (closedRegion_subset_target Φ hΦ 2 hx))
  have hL : IsCompact (closedRegion Φ 2 \ openRegion Φ (3 / 2)) :=
    (isCompact_closedRegion Φ hΦ 2).diff (isOpen_openRegion Φ hΦ (3 / 2))
  have hLp (x : M) (hx : x ∈ closedRegion Φ 2 \ openRegion Φ (3 / 2)) : 0 < τ x := by
    obtain ⟨p, hp, hpx⟩ := hx.1
    have hn : ¬ ‖p.2‖ < 3 / 2 := fun h ↦
      hx.2 ⟨p, ⟨mem_univ _, mem_ball_zero_iff.mpr h⟩, hpx⟩
    have h := houter p (by linarith)
    simpa only [hpx] using h
  obtain ⟨c₁, hc₁, hgap₁⟩ := exists_positive_gap_on_compact τ hL hLp
  let δ := min w (min (1 / 2) (min c₀ c₁))
  have hδ : 0 < δ := lt_min hw (lt_min (by norm_num) (lt_min hc₀ hc₁))
  have hδw : δ ≤ w := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ min c₀ c₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hδc₀ : δ ≤ c₀ := hδc.trans (min_le_left _ _)
  have hδc₁ : δ ≤ c₁ := hδc.trans (min_le_right _ _)
  have hOld (x : M) (hx : |t x| < δ) : x ∉ closedRegion Φ 2 := by
    intro hxK
    have htx := (le_abs_self (t x)).trans_lt hx
    have hgap := hgap₀ x hxK
    linarith
  have hNew (x : M) (hx : x ∈ closedRegion Φ 2 \ openRegion Φ (3 / 2)) : δ < τ x :=
    hδc₁.trans_lt (hgap₁ x hx)
  refine ⟨δ, hδ, hδw, hδhalf, hOld, hNew, ?_⟩
  intro x hx
  by_cases hxK : x ∈ closedRegion Φ 2
  · refine Or.inr ?_
    by_contra hxU
    have hl := hNew x ⟨hxK, hxU⟩
    have hr := (le_abs_self (τ x)).trans_lt hx
    linarith
  · exact Or.inl (by simpa only [hout x hxK] using hx)

end NoExoticSixSphere.SphereFourTube
