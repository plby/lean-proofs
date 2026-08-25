import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section


lemma EndpointUnitDiskLocalSpliceTransverse {κ : Type*}
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
    (hΩ_transverse :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Ω i).relativeInterior →
            p ∈ (Ω j).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Ω i).vertices.length)
                  (hn : n + 1 < (Ω j).vertices.length),
                  p ∈ segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] ∧
                    p ∈ segment ℝ (Ω j).vertices[n] (Ω j).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (Ω j).vertices[n + 1] - (Ω j).vertices[n] =
                          t • ((Ω i).vertices[m + 1] - (Ω i).vertices[m])) :
    ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Ξ i).relativeInterior →
          p ∈ (Ξ j).relativeInterior →
            ∃ m n : ℕ,
              ∃ (hm : m + 1 < (Ξ i).vertices.length)
                (hn : n + 1 < (Ξ j).vertices.length),
                p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                  p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                    ¬ ∃ t : ℝ,
                      (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                        t • ((Ξ i).vertices[m + 1] - (Ξ i).vertices[m]) := by
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
  have hrel_carrier :
      ∀ ⦃i : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ (Ξ i).relativeInterior → p ∈ (Ξ i).carrier := by
    intro i p hp
    rw [(Ξ i).relativeInterior_eq] at hp
    exact hp.1
  have hleft_no_Xi :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ leftConn i → p ∈ (Ξ j).carrier → False := by
    intro i j p hij hpleft hpΞ
    rw [(Ξ j).carrier_eq] at hpΞ
    rcases hpΞ with ⟨n, hn, hpseg⟩
    have hcj := hΞ_edge_class j n hn
    rcases hcj with hcjL | hcjRmid
    · have hpempty : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        have hpinter : p ∈ leftConn i ∩ leftConn j := ⟨hpleft, hcjL hpseg⟩
        have hpinter' :
            p ∈ segment ℝ (A i) (L i) ∩ segment ℝ (A j) (L j) := by
          simpa [leftConn] using hpinter
        rw [hsep_LL hij] at hpinter'
        exact hpinter'
      exact hpempty
    · rcases hcjRmid with hcjR | hcjMid
      · have hpempty : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          have hpinter : p ∈ leftConn i ∩ rightConn j := ⟨hpleft, hcjR hpseg⟩
          simpa [leftConn, rightConn, hsep_LR i j] using hpinter
        exact hpempty
      · rcases hcjMid with ⟨k, hk, hkeq⟩
        have hempty := hleft_middle_empty (i := i) (j := j) k hk hij
        have hpinter : p ∈ leftConn i ∩ segment ℝ (Ω j).vertices[k] (Ω j).vertices[k + 1] :=
          ⟨hpleft, by simpa [hkeq] using hpseg⟩
        rw [hempty] at hpinter
        exact hpinter
  have hright_no_Xi :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ rightConn i → p ∈ (Ξ j).carrier → False := by
    intro i j p hij hpright hpΞ
    rw [(Ξ j).carrier_eq] at hpΞ
    rcases hpΞ with ⟨n, hn, hpseg⟩
    have hcj := hΞ_edge_class j n hn
    rcases hcj with hcjL | hcjRmid
    · have hpempty : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        have hpinter : p ∈ rightConn i ∩ leftConn j := ⟨hpright, hcjL hpseg⟩
        simpa [leftConn, rightConn, Set.inter_comm, hsep_LR j i] using hpinter
      exact hpempty
    · rcases hcjRmid with hcjR | hcjMid
      · have hpempty : p ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          have hpinter : p ∈ rightConn i ∩ rightConn j := ⟨hpright, hcjR hpseg⟩
          have hpinter' :
              p ∈ segment ℝ (R i) (B i) ∩ segment ℝ (R j) (B j) := by
            simpa [rightConn] using hpinter
          rw [hsep_RR hij] at hpinter'
          exact hpinter'
        exact hpempty
      · rcases hcjMid with ⟨k, hk, hkeq⟩
        have hempty := hright_middle_empty (i := i) (j := j) k hk hij
        have hpinter :
            p ∈ rightConn i ∩ segment ℝ (Ω j).vertices[k] (Ω j).vertices[k + 1] :=
          ⟨hpright, by simpa [hkeq] using hpseg⟩
        rw [hempty] at hpinter
        exact hpinter
  have hshared_middle :
      ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Ξ i).relativeInterior →
            p ∈ (Ξ j).relativeInterior →
              p ∈ (Ω i).relativeInterior ∧ p ∈ (Ω j).relativeInterior := by
    intro i j p hij hp_i hp_j
    have hp_car_i := hrel_carrier hp_i
    have hp_car_j := hrel_carrier hp_j
    have one_side :
        ∀ ⦃i j : κ⦄,
          i ≠ j →
            p ∈ (Ξ i).relativeInterior →
              p ∈ (Ξ j).carrier →
                p ∈ (Ω i).relativeInterior := by
      intro i j hij hp_i hp_car_j
      have hp_car_i := hrel_carrier hp_i
      rw [(Ξ i).carrier_eq] at hp_car_i
      rcases hp_car_i with ⟨n, hn, hpseg⟩
      have hci := hΞ_edge_class i n hn
      rcases hci with hciL | hciRmid
      · exact False.elim (hleft_no_Xi hij (hciL hpseg) hp_car_j)
      · rcases hciRmid with hciR | hciMid
        · exact False.elim (hright_no_Xi hij (hciR hpseg) hp_car_j)
        · rcases hciMid with ⟨k, hk, hkeq⟩
          rw [(Ω i).relativeInterior_eq]
          constructor
          · rw [(Ω i).carrier_eq]
            exact ⟨k, hk, by simpa [hkeq] using hpseg⟩
          · intro hpend
            have hpend' : p = L i ∨ p = R i := by
              simpa [hΩ_source i, hΩ_target i] using hpend
            rcases hpend' with hpL | hpR
            · exact hleft_no_Xi hij (by simpa [leftConn, hpL] using right_mem_segment ℝ (A i) (L i))
                hp_car_j
            · exact hright_no_Xi hij (by simpa [rightConn, hpR] using left_mem_segment ℝ (R i) (B i))
                hp_car_j
    exact ⟨one_side hij hp_i hp_car_j, one_side (Ne.symm hij) hp_j hp_car_i⟩
  have hΩ_edge_to_Ξ :
      ∀ (i : κ) (k : ℕ) (hk : k + 1 < (Ω i).vertices.length),
        ∃ n : ℕ, ∃ hn : n + 1 < (Ξ i).vertices.length,
          segment ℝ (Ω i).vertices[k] (Ω i).vertices[k + 1] =
            segment ℝ (Ξ i).vertices[n] (Ξ i).vertices[n + 1] ∧
            ∃ s : ℝ, s ≠ 0 ∧
              (Ξ i).vertices[n + 1] - (Ξ i).vertices[n] =
                s • ((Ω i).vertices[k + 1] - (Ω i).vertices[k]) := by
    intro i k hk
    have hk_cases : k = 0 ∨ k = 1 := by
      have hk' : k + 1 < 3 := by
        simpa [hΩ_vertices i] using hk
      omega
    rcases hΞ_orient i with hfor | hrev
    · rcases hfor with ⟨hverts, hu, hv⟩
      rcases hk_cases with rfl | rfl
      · refine ⟨1, ?_, ?_, 1, by norm_num, ?_⟩
        · simpa [hverts]
        · ext p
          simp [hverts, hΩ_vertices i]
        · simp [hverts, hΩ_vertices i]
      · refine ⟨2, ?_, ?_, 1, by norm_num, ?_⟩
        · simpa [hverts]
        · ext p
          simp [hverts, hΩ_vertices i]
        · simp [hverts, hΩ_vertices i]
    · rcases hrev with ⟨hverts, hu, hv⟩
      rcases hk_cases with rfl | rfl
      · refine ⟨2, ?_, ?_, -1, by norm_num, ?_⟩
        · simpa [hverts]
        · ext p
          simp [hverts, hΩ_vertices i, segment_symm]
        · simp [hverts, hΩ_vertices i]
      · refine ⟨1, ?_, ?_, -1, by norm_num, ?_⟩
        · simpa [hverts]
        · ext p
          simp [hverts, hΩ_vertices i, segment_symm]
        · simp [hverts, hΩ_vertices i]
  have nonparallel_signed :
      ∀ {vi vj xi xj : EuclideanSpace ℝ (Fin 2)} {si sj : ℝ},
        sj ≠ 0 →
          xi = si • vi →
            xj = sj • vj →
              (¬ ∃ t : ℝ, vj = t • vi) →
                ¬ ∃ t : ℝ, xj = t • xi := by
    intro vi vj xi xj si sj hsj hxi hxj hnon hpar
    rcases hpar with ⟨t, ht⟩
    apply hnon
    refine ⟨(t * si) / sj, ?_⟩
    calc
      vj = (sj⁻¹ * sj) • vj := by
        rw [inv_mul_cancel₀ hsj, one_smul]
      _ = sj⁻¹ • (sj • vj) := by
        rw [smul_smul]
      _ = sj⁻¹ • (t • (si • vi)) := by
        rw [← hxj, ht, hxi]
      _ = ((t * si) / sj) • vi := by
        simp [smul_smul, div_eq_mul_inv, mul_assoc, mul_comm]
  intro i j p hij hp_i hp_j
  have hpΩ := hshared_middle hij hp_i hp_j
  rcases hΩ_transverse hij hpΩ.1 hpΩ.2 with
    ⟨mΩ, nΩ, hmΩ, hnΩ, hpseg_iΩ, hpseg_jΩ, hnonΩ⟩
  rcases hΩ_edge_to_Ξ i mΩ hmΩ with
    ⟨mΞ, hmΞ, hseg_i, si, hsi_ne, hdir_i⟩
  rcases hΩ_edge_to_Ξ j nΩ hnΩ with
    ⟨nΞ, hnΞ, hseg_j, sj, hsj_ne, hdir_j⟩
  refine ⟨mΞ, nΞ, hmΞ, hnΞ, ?_, ?_, ?_⟩
  · simpa [hseg_i] using hpseg_iΩ
  · simpa [hseg_j] using hpseg_jΩ
  · exact nonparallel_signed hsj_ne hdir_i hdir_j hnonΩ
