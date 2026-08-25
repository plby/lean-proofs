import Mathlib.Tactic
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma OneEdgeEndpointNonincidentFeatureSeparation
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2))
    (hNoVertexInEdgeInterior :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ V → v ∉ openSegment ℝ e.1 e.2)
    (hpV : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ p → v ∉ Metric.ball p ρ) ∧
      (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ p → e.2 ≠ p →
          Disjoint (Metric.ball p ρ) (segment ℝ e.1 e.2)) := by
  classical
  let VertexFeature := {v : {v // v ∈ V} // v.1 ≠ p}
  let EdgeFeature :=
    {e : {e // e ∈ E} // e.1.1 ≠ p ∧ e.1.2 ≠ p}
  let Feature := VertexFeature ⊕ EdgeFeature
  have segment_compact :
      ∀ x y : EuclideanSpace ℝ (Fin 2), IsCompact (segment ℝ x y) := by
    intro x y
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous)
  have edge_p_not_segment (e : EdgeFeature) :
      p ∉ segment ℝ e.1.1.1 e.1.1.2 := by
    intro hpseg
    rw [← insert_endpoints_openSegment (𝕜 := ℝ) e.1.1.1 e.1.1.2] at hpseg
    rcases hpseg with hp_left | hp_right | hp_open
    · exact e.2.1 hp_left.symm
    · exact e.2.2 hp_right.symm
    · exact hNoVertexInEdgeInterior e.1.1 e.1.2 p hpV hp_open
  have edge_separation :
      ∀ e : EdgeFeature,
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x, x ∈ ({p} : Set (EuclideanSpace ℝ (Fin 2))) →
            ∀ y, y ∈ segment ℝ e.1.1.1 e.1.1.2 → δ ≤ dist x y := by
    intro e
    have hseg_nonempty : (segment ℝ e.1.1.1 e.1.1.2).Nonempty :=
      ⟨e.1.1.1, left_mem_segment ℝ e.1.1.1 e.1.1.2⟩
    have hdisj :
        Disjoint ({p} : Set (EuclideanSpace ℝ (Fin 2)))
          (segment ℝ e.1.1.1 e.1.1.2) := by
      rw [Set.disjoint_left]
      intro x hx hy
      simp only [Set.mem_singleton_iff] at hx
      exact edge_p_not_segment e (by simpa [hx] using hy)
    exact PositiveSeparation (by simp) hseg_nonempty isCompact_singleton
      (segment_compact e.1.1.1 e.1.1.2) hdisj
  let edgeMargin : EdgeFeature → ℝ := fun e => Classical.choose (edge_separation e)
  have edgeMargin_spec :
      ∀ e : EdgeFeature,
        0 < edgeMargin e ∧
          ∀ x, x ∈ ({p} : Set (EuclideanSpace ℝ (Fin 2))) →
            ∀ y, y ∈ segment ℝ e.1.1.1 e.1.1.2 → edgeMargin e ≤ dist x y := by
    intro e
    exact Classical.choose_spec (edge_separation e)
  let margin : Option Feature → ℝ := fun f =>
    match f with
    | none => 1
    | some (Sum.inl v) => dist p v.1.1
    | some (Sum.inr e) => edgeMargin e
  have margin_pos : ∀ f : Option Feature, 0 < margin f := by
    intro f
    cases f with
    | none =>
        norm_num [margin]
    | some f =>
        cases f with
        | inl v =>
            dsimp [margin]
            exact dist_pos.mpr (Ne.symm v.2)
        | inr e =>
            exact (edgeMargin_spec e).1
  let m : ℝ := Finset.univ.inf' (show (Finset.univ : Finset (Option Feature)).Nonempty from
    ⟨none, Finset.mem_univ none⟩) margin
  have hm_pos : 0 < m := by
    dsimp [m]
    exact (Finset.lt_inf'_iff _).2 (by
      intro f _hf
      exact margin_pos f)
  let ρ : ℝ := m / 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_margin : ∀ f : Option Feature, ρ < margin f := by
    intro f
    have hρ_lt_m : ρ < m := by
      dsimp [ρ]
      linarith
    exact lt_of_lt_of_le hρ_lt_m (Finset.inf'_le margin (Finset.mem_univ f))
  refine ⟨ρ, hρ_pos, ?_, ?_⟩
  · intro v hvV hv_ne hvball
    let vf : VertexFeature := ⟨⟨v, hvV⟩, hv_ne⟩
    have hlt : ρ < dist p v := hρ_lt_margin (some (Sum.inl vf))
    have hvdist : dist p v < ρ := by
      simpa [Metric.mem_ball, dist_comm] using hvball
    exact not_lt_of_ge (le_of_lt hlt) hvdist
  · intro e he he_src he_tgt
    let ef : EdgeFeature := ⟨⟨e, he⟩, he_src, he_tgt⟩
    rw [Set.disjoint_left]
    intro x hxball hxseg
    have hmargin_le : edgeMargin ef ≤ dist p x := by
      have h := (edgeMargin_spec ef).2 p (by simp) x hxseg
      simpa [dist_comm] using h
    have hρ_lt_edge : ρ < edgeMargin ef := hρ_lt_margin (some (Sum.inr ef))
    have hxdist : dist p x < ρ := by
      simpa [Metric.mem_ball, dist_comm] using hxball
    exact not_lt_of_ge (le_trans (le_of_lt hρ_lt_edge) hmargin_le) hxdist
