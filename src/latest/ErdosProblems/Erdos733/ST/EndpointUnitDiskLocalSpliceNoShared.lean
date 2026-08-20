import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskLocalSpliceNoShared]
lemma EndpointUnitDiskLocalSpliceNoShared {κ : Type*}
    (A L M R B u v : κ → EuclideanSpace ℝ (Fin 2))
    (Ω Ξ : κ → PolygonalArc)
    (hΞ_orient : ∀ i : κ,
      ((Ξ i).vertices = [u i, L i, M i, R i, v i] ∧
          u i = A i ∧ v i = B i) ∨
        ((Ξ i).vertices = [u i, R i, M i, L i, v i] ∧
          u i = B i ∧ v i = A i))
    (hΩ_vertices : ∀ i : κ, (Ω i).vertices = [L i, M i, R i])
    (hsep_LL :
      ∀ ⦃i j : κ⦄,
        i ≠ j → segment ℝ (A i) (L i) ∩ segment ℝ (A j) (L j) = ∅)
    (hsep_LR :
      ∀ i j : κ, segment ℝ (A i) (L i) ∩ segment ℝ (R j) (B j) = ∅)
    (hsep_RR :
      ∀ ⦃i j : κ⦄,
        i ≠ j → segment ℝ (R i) (B i) ∩ segment ℝ (R j) (B j) = ∅)
    (hsep_L_LM :
      ∀ ⦃i j : κ⦄,
        i ≠ j → segment ℝ (A i) (L i) ∩ segment ℝ (L j) (M j) = ∅)
    (hsep_L_MR :
      ∀ i j : κ, segment ℝ (A i) (L i) ∩ segment ℝ (M j) (R j) = ∅)
    (hsep_R_LM :
      ∀ i j : κ, segment ℝ (R i) (B i) ∩ segment ℝ (L j) (M j) = ∅)
    (hsep_R_MR :
      ∀ ⦃i j : κ⦄,
        i ≠ j → segment ℝ (R i) (B i) ∩ segment ℝ (M j) (R j) = ∅)
    (hΩ_noShared :
      ∀ ⦃i j : κ⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Ω i).vertices.length)
              (hn : n + 1 < (Ω j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] ∩
                      segment ℝ (Ω j).vertices[n] (Ω j).vertices[n + 1]) :
    ∀ ⦃i j : κ⦄,
      i ≠ j →
        ¬ ∃ m n : ℕ,
          ∃ (hm : m + 1 < (Ξ i).vertices.length)
            (hn : n + 1 < (Ξ j).vertices.length),
            ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                    segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] := by
-- BODY
  let leftConn : κ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => segment ℝ (A i) (L i)
  let rightConn : κ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => segment ℝ (R i) (B i)
  have hΞ_edge_class :
      ∀ (i : κ) (n : ℕ) (hn : n + 1 < (Ξ i).vertices.length),
        segment ℝ (Ξ i).vertices[n] (Ξ i).vertices[n + 1] ⊆ leftConn i ∨
          segment ℝ (Ξ i).vertices[n] (Ξ i).vertices[n + 1] ⊆ rightConn i ∨
            ∃ k : ℕ, ∃ hk : k + 1 < (Ω i).vertices.length,
              segment ℝ (Ξ i).vertices[n] (Ξ i).vertices[n + 1] =
                segment ℝ (Ω i).vertices[k] (Ω i).vertices[k + 1] := by
    intro i n hn
    rcases hΞ_orient i with hfor | hrev
    · rcases hfor with ⟨hverts, hu, hv⟩
      have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
        have hn' : n + 1 < 5 := by
          simpa [hverts] using hn
        omega
      rcases hn_cases with rfl | rfl | rfl | rfl
      · left
        intro p hp
        simpa [leftConn, hverts, hu] using hp
      · right
        right
        refine ⟨0, ?_, ?_⟩
        · simpa [hΩ_vertices i]
        · ext p
          simp [hverts, hΩ_vertices i]
      · right
        right
        refine ⟨1, ?_, ?_⟩
        · simpa [hΩ_vertices i]
        · ext p
          simp [hverts, hΩ_vertices i]
      · right
        left
        intro p hp
        simpa [rightConn, hverts, hv] using hp
    · rcases hrev with ⟨hverts, hu, hv⟩
      have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
        have hn' : n + 1 < 5 := by
          simpa [hverts] using hn
        omega
      rcases hn_cases with rfl | rfl | rfl | rfl
      · right
        left
        intro p hp
        simpa [rightConn, hverts, hu, segment_symm] using hp
      · right
        right
        refine ⟨1, ?_, ?_⟩
        · simpa [hΩ_vertices i]
        · ext p
          simp [hverts, hΩ_vertices i, segment_symm]
      · right
        right
        refine ⟨0, ?_, ?_⟩
        · simpa [hΩ_vertices i]
        · ext p
          simp [hverts, hΩ_vertices i, segment_symm]
      · left
        intro p hp
        simpa [leftConn, hverts, hv, segment_symm] using hp
  have hleft_middle_empty :
      ∀ ⦃i j : κ⦄ (k : ℕ),
        (hk : k + 1 < (Ω j).vertices.length) →
          i ≠ j →
            leftConn i ∩ segment ℝ (Ω j).vertices[k] (Ω j).vertices[k + 1] = ∅ := by
    intro i j k hk hij
    have hk_cases : k = 0 ∨ k = 1 := by
      have hk' : k + 1 < 3 := by
        simpa [hΩ_vertices j] using hk
      omega
    rcases hk_cases with rfl | rfl
    · simpa [leftConn, hΩ_vertices j] using hsep_L_LM hij
    · simpa [leftConn, hΩ_vertices j] using hsep_L_MR i j
  have hright_middle_empty :
      ∀ ⦃i j : κ⦄ (k : ℕ),
        (hk : k + 1 < (Ω j).vertices.length) →
          i ≠ j →
            rightConn i ∩ segment ℝ (Ω j).vertices[k] (Ω j).vertices[k + 1] = ∅ := by
    intro i j k hk hij
    have hk_cases : k = 0 ∨ k = 1 := by
      have hk' : k + 1 < 3 := by
        simpa [hΩ_vertices j] using hk
      omega
    rcases hk_cases with rfl | rfl
    · simpa [rightConn, hΩ_vertices j] using hsep_R_LM i j
    · simpa [rightConn, hΩ_vertices j] using hsep_R_MR hij
  have empty_edge_contra :
      ∀ {S T U V : Set (EuclideanSpace ℝ (Fin 2))}
        {p q : EuclideanSpace ℝ (Fin 2)},
        U ∩ V = ∅ →
          S ⊆ U →
            T ⊆ V →
              segment ℝ p q ⊆ S ∩ T →
                False := by
    intro S T U V p q hempty hS hT hsub
    have hp : p ∈ U ∩ V :=
      ⟨hS (hsub (left_mem_segment ℝ p q)).1,
        hT (hsub (left_mem_segment ℝ p q)).2⟩
    rw [hempty] at hp
    exact hp
  intro i j hij hbad
  rcases hbad with ⟨m, n, hm, hn, p, q, hpq, hsub⟩
  have hci := hΞ_edge_class i m hm
  have hcj := hΞ_edge_class j n hn
  rcases hci with hciL | hciRmid
  · rcases hcj with hcjL | hcjRmid
    · exact empty_edge_contra (hsep_LL hij) hciL hcjL hsub
    · rcases hcjRmid with hcjR | hcjMid
      · exact empty_edge_contra (hsep_LR i j) hciL hcjR hsub
      · rcases hcjMid with ⟨k, hk, hkeq⟩
        exact empty_edge_contra (hleft_middle_empty k hk hij) hciL
          (by intro x hx; simpa [hkeq] using hx) hsub
  · rcases hciRmid with hciR | hciMid
    · rcases hcj with hcjL | hcjRmid
      · exact empty_edge_contra (by simpa [Set.inter_comm] using hsep_LR j i)
          hciR hcjL hsub
      · rcases hcjRmid with hcjR | hcjMid
        · exact empty_edge_contra (hsep_RR hij) hciR hcjR hsub
        · rcases hcjMid with ⟨k, hk, hkeq⟩
          exact empty_edge_contra (hright_middle_empty k hk hij) hciR
            (by intro x hx; simpa [hkeq] using hx) hsub
    · rcases hciMid with ⟨k, hk, hkeq⟩
      rcases hcj with hcjL | hcjRmid
      · exact empty_edge_contra
          (by
            have hempty := hleft_middle_empty (i := j) (j := i) k hk (Ne.symm hij)
            have hempty' :
                segment ℝ (Ω i).vertices[k] (Ω i).vertices[k + 1] ∩ leftConn j =
                  ∅ := by
              rw [Set.inter_comm]
              exact hempty
            exact hempty')
          (by intro x hx; simpa [hkeq] using hx) hcjL hsub
      · rcases hcjRmid with hcjR | hcjMid
        · exact empty_edge_contra
            (by
              have hempty := hright_middle_empty (i := j) (j := i) k hk (Ne.symm hij)
              have hempty' :
                  segment ℝ (Ω i).vertices[k] (Ω i).vertices[k + 1] ∩ rightConn j =
                    ∅ := by
                rw [Set.inter_comm]
                exact hempty
              exact hempty')
            (by intro x hx; simpa [hkeq] using hx) hcjR hsub
        · rcases hcjMid with ⟨l, hl, hleq⟩
          apply hΩ_noShared hij
          refine ⟨k, l, hk, hl, p, q, hpq, ?_⟩
          intro x hx
          have hxij := hsub hx
          exact ⟨by simpa [hkeq] using hxij.1,
            by simpa [hleq] using hxij.2⟩
