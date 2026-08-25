import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcAdjacentOutwardDirectionsNotSameRay (γ : PolygonalArc)
    {i : ℕ} (hprev : 0 < i) (hnext : i + 1 < γ.vertices.length) :
    (¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[i - 1] - γ.vertices[i] =
          a • (γ.vertices[i + 1] - γ.vertices[i])) ∧
      ¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[i + 1] - γ.vertices[i] =
          a • (γ.vertices[i - 1] - γ.vertices[i]) := by
  have no_next_pos_prev :
      ¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[i + 1] - γ.vertices[i] =
          a • (γ.vertices[i - 1] - γ.vertices[i]) := by
    rintro ⟨a, ha, hvec⟩
    let τ : ℝ := min (1 / 2 : ℝ) (1 / (2 * a))
    have htwoa_pos : 0 < 2 * a := by positivity
    have hτ_pos : 0 < τ := by
      dsimp [τ]
      exact lt_min (by norm_num) (one_div_pos.mpr htwoa_pos)
    have hτ_le_half : τ ≤ 1 / 2 := by
      dsimp [τ]
      exact min_le_left _ _
    have hτ_le_one : τ ≤ 1 := by nlinarith
    have hτ_le_inv : τ ≤ 1 / (2 * a) := by
      dsimp [τ]
      exact min_le_right _ _
    have haτ_nonneg : 0 ≤ a * τ := by positivity
    have haτ_le_half : a * τ ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hτ_le_inv (le_of_lt ha)
      have hprod : a * (1 / (2 * a)) = 1 / 2 := by
        field_simp [ne_of_gt ha]
      calc
        a * τ ≤ a * (1 / (2 * a)) := hmul
        _ = 1 / 2 := hprod
    have haτ_le_one : a * τ ≤ 1 := by nlinarith
    let q : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[i] γ.vertices[i + 1] τ
    have hq_next : q ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨τ, ⟨le_of_lt hτ_pos, hτ_le_one⟩, rfl⟩
    have hq_prev : q ∈ segment ℝ γ.vertices[i - 1] γ.vertices[i] := by
      rw [segment_eq_image_lineMap]
      refine ⟨1 - a * τ, ⟨by nlinarith, by nlinarith⟩, ?_⟩
      dsimp [q]
      apply PiLp.ext
      intro k
      have hvec_k := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x k) hvec
      simp [AffineMap.lineMap_apply_module] at hvec_k ⊢
      nlinarith [hvec_k]
    have hprevSeg : (i - 1) + 1 < γ.vertices.length := by
      have hi_lt : i < γ.vertices.length := Nat.lt_of_succ_lt hnext
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hi_lt
    have hlt : i - 1 < i := Nat.sub_lt hprev Nat.zero_lt_one
    have hinter :
        segment ℝ γ.vertices[i - 1] γ.vertices[i] ∩
            segment ℝ γ.vertices[i] γ.vertices[i + 1] =
          ({γ.vertices[i]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := i - 1) (j := i) hprevSeg hnext hlt
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hraw
    have hq_eq_vertex : q = γ.vertices[i] := by
      have hq_inter :
          q ∈
            segment ℝ γ.vertices[i - 1] γ.vertices[i] ∩
              segment ℝ γ.vertices[i] γ.vertices[i + 1] :=
        ⟨hq_prev, hq_next⟩
      rw [hinter] at hq_inter
      simpa using hq_inter
    have hneq_next : γ.vertices[i] ≠ γ.vertices[i + 1] := by
      intro hpoint
      have hidx : i = i + 1 :=
        (List.Nodup.getElem_inj_iff γ.simple_vertices).mp hpoint
      omega
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[i] γ.vertices[i + 1]
    have hf : Function.Injective f := AffineMap.lineMap_injective (k := ℝ) hneq_next
    have hτ_zero : τ = 0 := by
      exact hf (by simpa [f, q] using hq_eq_vertex)
    linarith
  constructor
  · rintro ⟨a, ha, hvec⟩
    exact no_next_pos_prev ⟨a⁻¹, inv_pos.mpr ha, by
      calc
        γ.vertices[i + 1] - γ.vertices[i] =
            a⁻¹ • (a • (γ.vertices[i + 1] - γ.vertices[i])) := by
              rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
        _ = a⁻¹ • (γ.vertices[i - 1] - γ.vertices[i]) := by
              rw [← hvec]⟩
  · exact no_next_pos_prev
