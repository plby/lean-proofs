import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.CircleLineNoThreePoints
import Mathlib.Data.List.FinRange

open Classical
noncomputable section

-- [TABLET NODE: CircularOrderedSamplesBasicChordControls]
lemma CircularOrderedSamplesBasicChordControls
    {m : ℕ}
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hγ_inj : Function.Injective γ)
    (hγ_circle : ∀ t, dist (γ t) c = r)
    (params : Fin (m + 1) → Set.Icc (0 : ℝ) 1)
    (hparams_strict :
      ∀ ⦃i j : Fin (m + 1)⦄, i < j → params i < params j) :
    let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
      List.ofFn (fun k : Fin (m + 1) => γ (params k))
    vertices.Nodup ∧
      (∀ i
        (hi : (i + 1) + 1 < vertices.length),
        (segment ℝ vertices[i] vertices[i + 1] ∩
            segment ℝ vertices[i + 1] vertices[(i + 1) + 1]) =
          {vertices[i + 1]}) ∧
      (∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < vertices.length) →
        (hk : k < vertices.length) →
        k ≠ i →
        k ≠ i + 1 →
        vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1]) := by
-- BODY
  classical
  let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
    List.ofFn (fun k : Fin (m + 1) => γ (params k))
  have hvertices_length : vertices.length = m + 1 := by
    simp [vertices]
  have sample_ne_of_ne :
      ∀ {a b : ℕ} (ha : a < m + 1) (hb : b < m + 1), a ≠ b →
        γ (params ⟨a, ha⟩) ≠ γ (params ⟨b, hb⟩) := by
    intro a b ha hb hne heq
    have hp_eq : params ⟨a, ha⟩ = params ⟨b, hb⟩ := hγ_inj heq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hltp : params ⟨a, ha⟩ < params ⟨b, hb⟩ :=
        hparams_strict (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (by simpa using hlt)
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
    · have hltp : params ⟨b, hb⟩ < params ⟨a, ha⟩ :=
        hparams_strict (i := ⟨b, hb⟩) (j := ⟨a, ha⟩) (by simpa using hgt)
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
  have sample_ne_of_lt :
      ∀ {a b : ℕ} (ha : a < m + 1) (hb : b < m + 1), a < b →
        γ (params ⟨a, ha⟩) ≠ γ (params ⟨b, hb⟩) := by
    intro a b ha hb hlt
    exact sample_ne_of_ne ha hb (Nat.ne_of_lt hlt)
  have hgetFin :
      ∀ a : Fin (m + 1),
        vertices[a.1]'(by simpa [hvertices_length] using a.2) =
          γ (params a) := by
    intro a
    dsimp [vertices]
    simp only [List.getElem_ofFn]
  have hget :
      ∀ {a : ℕ} (haV : a < vertices.length),
        vertices[a] =
          γ (params ⟨a, by simpa [hvertices_length] using haV⟩) := by
    intro a haV
    simpa using hgetFin ⟨a, by simpa [hvertices_length] using haV⟩
  have hnodup : vertices.Nodup := by
    dsimp [vertices]
    apply List.nodup_ofFn.mpr
    intro a b heq
    apply Fin.ext
    by_contra hne
    have hne_nat : a.1 ≠ b.1 := by
      intro h
      exact hne h
    have hp_eq : params a = params b := hγ_inj heq
    rcases lt_or_gt_of_ne hne_nat with hlt | hgt
    · have hltp : params a < params b := hparams_strict hlt
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
    · have hltp : params b < params a := hparams_strict hgt
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
  have hadjacent :
      ∀ i
        (hi : (i + 1) + 1 < vertices.length),
        (segment ℝ vertices[i] vertices[i + 1] ∩
            segment ℝ vertices[i + 1] vertices[(i + 1) + 1]) =
          {vertices[i + 1]} := by
    intro i hi
    apply Set.Subset.antisymm
    · intro p hp
      by_cases hp_mid : p = vertices[i + 1]
      · simp [hp_mid]
      · exfalso
        have hi_len : i < vertices.length := by omega
        have hi1_len : i + 1 < vertices.length := by omega
        have hi2_len : (i + 1) + 1 < vertices.length := hi
        have hA_ne_B :
            vertices[i] ≠ vertices[i + 1] := by
          rw [hget hi_len, hget hi1_len]
          exact sample_ne_of_lt (by simpa [hvertices_length] using hi_len)
            (by simpa [hvertices_length] using hi1_len) (by omega)
        have hA_ne_C :
            vertices[i] ≠ vertices[(i + 1) + 1] := by
          rw [hget hi_len, hget hi2_len]
          exact sample_ne_of_lt (by simpa [hvertices_length] using hi_len)
            (by simpa [hvertices_length] using hi2_len) (by omega)
        have hB_ne_C :
            vertices[i + 1] ≠ vertices[(i + 1) + 1] := by
          rw [hget hi1_len, hget hi2_len]
          exact sample_ne_of_lt (by simpa [hvertices_length] using hi1_len)
            (by simpa [hvertices_length] using hi2_len) (by omega)
        have hC_line :
            vertices[(i + 1) + 1] ∈ line[ℝ, vertices[i], vertices[i + 1]] := by
          have hp_left : p ∈ segment ℝ vertices[i] vertices[i + 1] := hp.1
          have hp_right :
              p ∈ segment ℝ vertices[i + 1] vertices[(i + 1) + 1] := hp.2
          have hpABline : p ∈ line[ℝ, vertices[i], vertices[i + 1]] := by
            rw [segment_eq_image_lineMap] at hp_left
            rcases hp_left with ⟨t, _ht, rfl⟩
            exact AffineMap.lineMap_mem_affineSpan_pair t vertices[i]
              vertices[i + 1]
          have hpBCline :
              p ∈ line[ℝ, vertices[i + 1], vertices[(i + 1) + 1]] := by
            rw [segment_eq_image_lineMap] at hp_right
            rcases hp_right with ⟨t, _ht, rfl⟩
            exact AffineMap.lineMap_mem_affineSpan_pair t vertices[i + 1]
              vertices[(i + 1) + 1]
          have hline_pB_eq_BC :
              line[ℝ, p, vertices[i + 1]] =
                line[ℝ, vertices[i + 1], vertices[(i + 1) + 1]] :=
            affineSpan_pair_eq_of_mem_of_mem_of_ne hpBCline
              (left_mem_affineSpan_pair ℝ vertices[i + 1]
                vertices[(i + 1) + 1]) hp_mid
          have hline_pB_le_AB :
              line[ℝ, p, vertices[i + 1]] ≤
                line[ℝ, vertices[i], vertices[i + 1]] :=
            affineSpan_pair_le_of_mem_of_mem hpABline
              (right_mem_affineSpan_pair ℝ vertices[i] vertices[i + 1])
          exact hline_pB_le_AB (by
            rw [hline_pB_eq_BC]
            exact right_mem_affineSpan_pair ℝ vertices[i + 1]
              vertices[(i + 1) + 1])
        exact CircleLineNoThreePoints
          (c := c) (r := r) (x := vertices[i]) (y := vertices[i + 1])
          (u := vertices[i]) (v := vertices[i + 1])
          (w := vertices[(i + 1) + 1])
          hA_ne_B
          (left_mem_affineSpan_pair ℝ vertices[i] vertices[i + 1])
          (right_mem_affineSpan_pair ℝ vertices[i] vertices[i + 1])
          hC_line
          (by rw [hget hi_len]; exact hγ_circle _)
          (by rw [hget hi1_len]; exact hγ_circle _)
          (by rw [hget hi2_len]; exact hγ_circle _)
          hA_ne_B hA_ne_C hB_ne_C
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact ⟨right_mem_segment ℝ vertices[i] vertices[i + 1],
        left_mem_segment ℝ vertices[i + 1] vertices[(i + 1) + 1]⟩
  have havoid :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < vertices.length) →
        (hk : k < vertices.length) →
        k ≠ i →
        k ≠ i + 1 →
        vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1] := by
    intro i k hi hk hki hki1 hopen
    have hi_len : i < vertices.length := by omega
    have hA_ne_B : vertices[i] ≠ vertices[i + 1] := by
      rw [hget hi_len, hget hi]
      exact sample_ne_of_lt (by simpa [hvertices_length] using hi_len)
        (by simpa [hvertices_length] using hi) (by omega)
    have hA_ne_K : vertices[i] ≠ vertices[k] := by
      rw [hget hi_len, hget hk]
      exact sample_ne_of_ne (by simpa [hvertices_length] using hi_len)
        (by simpa [hvertices_length] using hk) (by omega)
    have hB_ne_K : vertices[i + 1] ≠ vertices[k] := by
      rw [hget hi, hget hk]
      exact sample_ne_of_ne (by simpa [hvertices_length] using hi)
        (by simpa [hvertices_length] using hk) (by omega)
    have hK_line : vertices[k] ∈ line[ℝ, vertices[i], vertices[i + 1]] := by
      have hseg : vertices[k] ∈ segment ℝ vertices[i] vertices[i + 1] :=
        openSegment_subset_segment ℝ vertices[i] vertices[i + 1] hopen
      rw [segment_eq_image_lineMap] at hseg
      rcases hseg with ⟨t, _ht, ht_eq⟩
      rw [← ht_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair t vertices[i] vertices[i + 1]
    exact CircleLineNoThreePoints
      (c := c) (r := r) (x := vertices[i]) (y := vertices[i + 1])
      (u := vertices[i]) (v := vertices[i + 1]) (w := vertices[k])
      hA_ne_B
      (left_mem_affineSpan_pair ℝ vertices[i] vertices[i + 1])
      (right_mem_affineSpan_pair ℝ vertices[i] vertices[i + 1])
      hK_line
      (by rw [hget hi_len]; exact hγ_circle _)
      (by rw [hget hi]; exact hγ_circle _)
      (by rw [hget hk]; exact hγ_circle _)
      hA_ne_B hA_ne_K hB_ne_K
  exact ⟨hnodup, hadjacent, havoid⟩
