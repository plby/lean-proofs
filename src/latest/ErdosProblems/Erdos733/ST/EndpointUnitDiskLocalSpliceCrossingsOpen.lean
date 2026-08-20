import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section


-- [TABLET NODE: EndpointUnitDiskLocalSpliceCrossingsOpen]
lemma EndpointUnitDiskLocalSpliceCrossingsOpen {κ : Type*}
    (A L M R B u v : κ → EuclideanSpace ℝ (Fin 2))
    (Ω Ξ : κ → PolygonalArc)
    (hΞ_orient : ∀ i : κ,
      ((Ξ i).vertices = [u i, L i, M i, R i, v i] ∧
          u i = A i ∧ v i = B i) ∨
        ((Ξ i).vertices = [u i, R i, M i, L i, v i] ∧
          u i = B i ∧ v i = A i))
    (hΩ_vertices : ∀ i : κ, (Ω i).vertices = [L i, M i, R i])
    (hΩ_source : ∀ i : κ, (Ω i).source = L i)
    (hΩ_target : ∀ i : κ, (Ω i).target = R i)
    (hsep_LL : ∀ ⦃i j : κ⦄, i ≠ j →
      segment ℝ (A i) (L i) ∩ segment ℝ (A j) (L j) = ∅)
    (hsep_LR : ∀ i j : κ,
      segment ℝ (A i) (L i) ∩ segment ℝ (R j) (B j) = ∅)
    (hsep_RR : ∀ ⦃i j : κ⦄, i ≠ j →
      segment ℝ (R i) (B i) ∩ segment ℝ (R j) (B j) = ∅)
    (hsep_L_LM : ∀ ⦃i j : κ⦄, i ≠ j →
      segment ℝ (A i) (L i) ∩ segment ℝ (L j) (M j) = ∅)
    (hsep_L_MR : ∀ i j : κ,
      segment ℝ (A i) (L i) ∩ segment ℝ (M j) (R j) = ∅)
    (hsep_R_LM : ∀ i j : κ,
      segment ℝ (R i) (B i) ∩ segment ℝ (L j) (M j) = ∅)
    (hsep_R_MR : ∀ ⦃i j : κ⦄, i ≠ j →
      segment ℝ (R i) (B i) ∩ segment ℝ (M j) (R j) = ∅)
    (hΩ_open : ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Ω i).relativeInterior → p ∈ (Ω j).relativeInterior →
          p ∈ openSegment ℝ (M i) (R i) ∧
            p ∈ openSegment ℝ (M j) (R j)) :
    ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Ξ i).relativeInterior → p ∈ (Ξ j).relativeInterior →
          ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Ξ i).vertices.length)
              (hn : n + 1 < (Ξ j).vertices.length),
              p ∈ openSegment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                p ∈ openSegment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] := by
-- BODY
  let leftConn : κ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => segment ℝ (A i) (L i)
  let rightConn : κ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => segment ℝ (R i) (B i)
  have hcarrier_cases :
      ∀ (i : κ) ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Ξ i).carrier →
          p ∈ leftConn i ∨
            p ∈ segment ℝ (L i) (M i) ∨
              p ∈ segment ℝ (M i) (R i) ∨ p ∈ rightConn i := by
    intro i p hp
    rw [(Ξ i).carrier_eq] at hp
    rcases hp with ⟨n, hn, hpseg⟩
    rcases hΞ_orient i with hfor | hrev
    · rcases hfor with ⟨hverts, hu, hv⟩
      have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
        have : n + 1 < 5 := by simpa [hverts] using hn
        omega
      rcases hn_cases with rfl | rfl | rfl | rfl
      · left; simpa [leftConn, hverts, hu] using hpseg
      · right; left; simpa [hverts] using hpseg
      · right; right; left; simpa [hverts] using hpseg
      · right; right; right; simpa [rightConn, hverts, hv] using hpseg
    · rcases hrev with ⟨hverts, hu, hv⟩
      have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
        have : n + 1 < 5 := by simpa [hverts] using hn
        omega
      rcases hn_cases with rfl | rfl | rfl | rfl
      · right; right; right
        simpa [rightConn, hverts, hu, segment_symm] using hpseg
      · right; right; left; simpa [hverts, segment_symm] using hpseg
      · right; left; simpa [hverts, segment_symm] using hpseg
      · left; simpa [leftConn, hverts, hv, segment_symm] using hpseg
  have hrel_carrier :
      ∀ ⦃i : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Ξ i).relativeInterior → p ∈ (Ξ i).carrier := by
    intro i p hp
    rw [(Ξ i).relativeInterior_eq] at hp
    exact hp.1
  have hleft_no_other :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ leftConn i → p ∈ (Ξ j).carrier → False := by
    intro i j p hij hpleft hpj
    rcases hcarrier_cases j hpj with hpjl | hpjlm | hpjmr | hpjr
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_LL hij]
        exact ⟨hpleft, hpjl⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_L_LM hij]
        exact ⟨hpleft, hpjlm⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_L_MR i j]
        exact ⟨hpleft, hpjmr⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_LR i j]
        exact ⟨hpleft, hpjr⟩
      exact this
  have hright_no_other :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ rightConn i → p ∈ (Ξ j).carrier → False := by
    intro i j p hij hpright hpj
    rcases hcarrier_cases j hpj with hpjl | hpjlm | hpjmr | hpjr
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_LR j i]
        exact ⟨hpjl, hpright⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_R_LM i j]
        exact ⟨hpright, hpjlm⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_R_MR hij]
        exact ⟨hpright, hpjmr⟩
      exact this
    · have : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [← hsep_RR hij]
        exact ⟨hpright, hpjr⟩
      exact this
  have hshared_middle :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Ξ i).relativeInterior → p ∈ (Ξ j).relativeInterior →
            p ∈ (Ω i).relativeInterior ∧ p ∈ (Ω j).relativeInterior := by
    intro i j p hij hpi hpj
    have hpci := hrel_carrier hpi
    have hpcj := hrel_carrier hpj
    have one_side :
        ∀ ⦃i j : κ⦄, i ≠ j →
          p ∈ (Ξ i).carrier → p ∈ (Ξ j).carrier →
            p ∈ (Ω i).relativeInterior := by
      intro i j hij hpci hpcj
      rcases hcarrier_cases i hpci with hpl | hplm | hpmr | hpr
      · exact False.elim (hleft_no_other hij hpl hpcj)
      · rw [(Ω i).relativeInterior_eq, (Ω i).carrier_eq]
        refine ⟨⟨0, by simpa [hΩ_vertices i], by simpa [hΩ_vertices i] using hplm⟩, ?_⟩
        intro hpends
        rcases (by simpa [hΩ_source i, hΩ_target i] using hpends) with hpL | hpR
        · exact hleft_no_other hij
            (by simpa [leftConn, hpL] using right_mem_segment ℝ (A i) (L i)) hpcj
        · exact hright_no_other hij
            (by simpa [rightConn, hpR] using left_mem_segment ℝ (R i) (B i)) hpcj
      · rw [(Ω i).relativeInterior_eq, (Ω i).carrier_eq]
        refine ⟨⟨1, by simpa [hΩ_vertices i], by simpa [hΩ_vertices i] using hpmr⟩, ?_⟩
        intro hpends
        rcases (by simpa [hΩ_source i, hΩ_target i] using hpends) with hpL | hpR
        · exact hleft_no_other hij
            (by simpa [leftConn, hpL] using right_mem_segment ℝ (A i) (L i)) hpcj
        · exact hright_no_other hij
            (by simpa [rightConn, hpR] using left_mem_segment ℝ (R i) (B i)) hpcj
      · exact False.elim (hright_no_other hij hpr hpcj)
    exact ⟨one_side hij hpci hpcj, one_side (Ne.symm hij) hpcj hpci⟩
  intro i j p hij hpi hpj
  have hpΩ := hshared_middle hij hpi hpj
  have hopen := hΩ_open hij hpΩ.1 hpΩ.2
  have lift_open :
      ∀ (k : κ) ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ openSegment ℝ (M k) (R k) →
          ∃ s : ℕ, ∃ hs : s + 1 < (Ξ k).vertices.length,
            p ∈ openSegment ℝ (Ξ k).vertices[s] (Ξ k).vertices[s + 1] := by
    intro k p hp
    rcases hΞ_orient k with hfor | hrev
    · rcases hfor with ⟨hverts, _hu, _hv⟩
      exact ⟨2, by simpa [hverts], by simpa [hverts] using hp⟩
    · rcases hrev with ⟨hverts, _hu, _hv⟩
      exact ⟨1, by simpa [hverts], by simpa [hverts, openSegment_symm] using hp⟩
  rcases lift_open i hopen.1 with ⟨mi, hmi, hpmi⟩
  rcases lift_open j hopen.2 with ⟨mj, hmj, hpmj⟩
  exact ⟨mi, mj, hmi, hmj, hpmi, hpmj⟩
