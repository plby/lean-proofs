import ErdosProblems.Erdos733.ST.PolygonalArcEndpointGluedVertices

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcEndpointGluedSegmentOccurrence]
lemma PolygonalArcEndpointGluedSegmentOccurrence
    (pieces : List PolygonalArc)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source) :
    ∀ i
      (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
      ∃ k : ℕ, ∃ hk : k < pieces.length,
        ∃ m : ℕ, ∃ hm : m + 1 < (pieces[k]).vertices.length,
          i =
              ((pieces.take k).map
                (fun Γ : PolygonalArc => Γ.vertices.length - 1)).sum + m ∧
            (PolygonalArcEndpointGluedVertices pieces)[i] =
              (pieces[k]).vertices[m] ∧
            (PolygonalArcEndpointGluedVertices pieces)[i + 1] =
              (pieces[k]).vertices[m + 1] := by
-- BODY
  have endpointGluedVertices_tail_eq :
      ∀ (Γ : PolygonalArc) (rest : List PolygonalArc),
        (PolygonalArcEndpointGluedVertices (Γ :: rest)).tail =
          ((Γ :: rest).map (fun Δ => Δ.vertices.tail)).flatten := by
    intro Γ rest
    cases hverts : Γ.vertices with
    | nil =>
        have hlen := Γ.length_ge_two
        simp [hverts] at hlen
    | cons a vs =>
        simp [PolygonalArcEndpointGluedVertices, hverts]
  have endpointGluedVertices_cons_eq_append_tail :
      ∀ (Γ : PolygonalArc) (rest : List PolygonalArc),
        PolygonalArcEndpointGluedVertices (Γ :: rest) =
          Γ.vertices ++ (PolygonalArcEndpointGluedVertices rest).tail := by
    intro Γ rest
    cases rest with
    | nil =>
        simp [PolygonalArcEndpointGluedVertices]
    | cons Δ rest =>
        rw [PolygonalArcEndpointGluedVertices,
          endpointGluedVertices_tail_eq]
  have polygonalArc_first_vertex :
      ∀ Γ : PolygonalArc,
        Γ.vertices[0]'(by
          have hlen := Γ.length_ge_two
          omega) = Γ.source := by
    intro Γ
    have hidx : 0 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hhead := Γ.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hidx] at hhead
    exact Option.some.inj hhead
  have polygonalArc_last_vertex :
      ∀ Γ : PolygonalArc,
        Γ.vertices[Γ.vertices.length - 1]'(by
          have hlen := Γ.length_ge_two
          omega) = Γ.target := by
    intro Γ
    have hidx : Γ.vertices.length - 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hlast := Γ.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem hidx] at hlast
    exact Option.some.inj hlast
  induction pieces with
  | nil =>
      intro i hi
      simp [PolygonalArcEndpointGluedVertices] at hi
  | cons Δ rest ih =>
      intro i hi
      let W := PolygonalArcEndpointGluedVertices rest
      let Wbig := PolygonalArcEndpointGluedVertices (Δ :: rest)
      have hsucc_rest :
          ∀ n (hn : n + 1 < rest.length),
            (rest[n]).target = (rest[n + 1]).source := by
        intro n hn
        have hn_full : (n + 1) + 1 < (Δ :: rest).length := by
          simp
          omega
        have h := successive_attach (n + 1) hn_full
        simpa using h
      by_cases hleft : i + 1 < Δ.vertices.length
      · refine ⟨0, by simp, i, hleft, ?_, ?_, ?_⟩
        · simp
        · have hi_lt : i < Δ.vertices.length := by omega
          have hi_app :
              i < (Δ.vertices ++
                  (rest.map (fun Δ => Δ.vertices.tail)).flatten).length := by
            simp [List.length_append]
            omega
          simpa [PolygonalArcEndpointGluedVertices] using
            (List.getElem_append_left
              (as := Δ.vertices)
              (bs := (rest.map (fun Δ => Δ.vertices.tail)).flatten)
              (i := i) (h' := hi_app) hi_lt)
        · have hi1_app :
              i + 1 < (Δ.vertices ++
                  (rest.map (fun Δ => Δ.vertices.tail)).flatten).length := by
            simp [List.length_append]
            omega
          simpa [PolygonalArcEndpointGluedVertices] using
            (List.getElem_append_left
              (as := Δ.vertices)
              (bs := (rest.map (fun Δ => Δ.vertices.tail)).flatten)
              (i := i + 1) (h' := hi1_app) hleft)
      · by_cases histart : i < Δ.vertices.length
        · have hibound : i + 1 = Δ.vertices.length := by omega
          cases rest with
          | nil =>
              have hilen :
                  i + 1 < Δ.vertices.length := by
                simpa [PolygonalArcEndpointGluedVertices] using hi
              omega
          | cons E rs =>
              have hEseg : 0 + 1 < E.vertices.length := by
                have hlen := E.length_ge_two
                omega
              have hW1 :
                  1 < (PolygonalArcEndpointGluedVertices (E :: rs)).length := by
                have hlen := E.length_ge_two
                simp [PolygonalArcEndpointGluedVertices, List.length_append]
                omega
              refine ⟨1, by simp, 0, ?_, ?_, ?_, ?_⟩
              · simpa using hEseg
              · simp
                omega
              · have hattach : Δ.target = E.source := by
                  have hfull : 0 + 1 < (Δ :: E :: rs).length := by simp
                  simpa using successive_attach 0 hfull
                have hbig_left :
                    (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i] =
                      E.vertices[0] := by
                  have hΔlast :
                      Δ.vertices[i]'histart = Δ.target := by
                    have hi_eq : i = Δ.vertices.length - 1 := by omega
                    subst i
                    exact polygonalArc_last_vertex Δ
                  have hEfirst :
                      E.vertices[0]'(by
                        have hlen := E.length_ge_two
                        omega) = E.source :=
                    polygonalArc_first_vertex E
                  have hbig_i :
                      (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i] =
                        Δ.vertices[i] := by
                    have hi_app :
                        i < (Δ.vertices ++
                            ((E :: rs).map (fun Δ => Δ.vertices.tail)).flatten).length := by
                      simp [List.length_append]
                      omega
                    simpa [PolygonalArcEndpointGluedVertices] using
                      (List.getElem_append_left
                        (as := Δ.vertices)
                        (bs := ((E :: rs).map
                          (fun Δ => Δ.vertices.tail)).flatten)
                        (i := i) (h' := hi_app) histart)
                  rw [hbig_i, hΔlast, hattach, hEfirst]
                simpa using hbig_left
              · have htail_ne :
                    (PolygonalArcEndpointGluedVertices (E :: rs)).tail ≠ [] := by
                  intro hnil
                  have hlen_tail :
                      (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length = 0 := by
                    simp [hnil]
                  have hlen_tail_pos :
                      0 < (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                    have hlen := E.length_ge_two
                    simp [PolygonalArcEndpointGluedVertices, List.length_append,
                      List.length_tail]
                    omega
                  omega
                have hbig_right :
                    (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i + 1] =
                      (PolygonalArcEndpointGluedVertices (E :: rs)).tail[0]'(by
                        have htail_pos :
                            0 < (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                          cases h :
                              (PolygonalArcEndpointGluedVertices (E :: rs)).tail with
                          | nil => exact False.elim (htail_ne h)
                          | cons a as => simp
                        exact htail_pos) := by
                  have hle : Δ.vertices.length ≤ i + 1 := by omega
                  have hidx : i + 1 - Δ.vertices.length = 0 := by omega
                  have happ :
                      i + 1 <
                        (Δ.vertices ++
                          (PolygonalArcEndpointGluedVertices (E :: rs)).tail).length := by
                    have htail_pos :
                        0 <
                          (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                      cases h :
                          (PolygonalArcEndpointGluedVertices (E :: rs)).tail with
                      | nil => exact False.elim (htail_ne h)
                      | cons a as => simp
                    rw [hibound]
                    simp [List.length_append]
                    have htail_len :
                        (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length =
                          (PolygonalArcEndpointGluedVertices (E :: rs)).length - 1 :=
                      List.length_tail
                    omega
                  simpa [endpointGluedVertices_cons_eq_append_tail, hidx] using
                    (List.getElem_append_right
                      (as := Δ.vertices)
                      (bs := (PolygonalArcEndpointGluedVertices (E :: rs)).tail)
                      (i := i + 1) (h₂ := happ) hle)
                have htail0 :
                    (PolygonalArcEndpointGluedVertices (E :: rs)).tail[0]'(by
                      have htail_pos :
                          0 < (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                        cases h :
                            (PolygonalArcEndpointGluedVertices (E :: rs)).tail with
                        | nil => exact False.elim (htail_ne h)
                        | cons a as => simp
                      exact htail_pos) =
                      (PolygonalArcEndpointGluedVertices (E :: rs))[1]'hW1 := by
                  exact List.getElem_tail _
                have hEone :
                    (PolygonalArcEndpointGluedVertices (E :: rs))[1]'hW1 =
                      E.vertices[1]'(by
                        have hlen := E.length_ge_two
                        omega) := by
                  have h1E : 1 < E.vertices.length := by
                    have hlen := E.length_ge_two
                    omega
                  have h1app :
                      1 < (E.vertices ++
                          (rs.map (fun Δ => Δ.vertices.tail)).flatten).length := by
                    simp [List.length_append]
                    omega
                  simpa [PolygonalArcEndpointGluedVertices] using
                    (List.getElem_append_left
                      (as := E.vertices)
                      (bs := (rs.map (fun Δ => Δ.vertices.tail)).flatten)
                      (i := 1) (h' := h1app) h1E)
                rw [hbig_right, htail0]
                simpa using hEone
        · have hge : Δ.vertices.length ≤ i := by omega
          let q := i - Δ.vertices.length
          let r := q + 1
          have hrseg : r + 1 < W.length := by
            have hbig_len : Wbig.length = Δ.vertices.length + W.tail.length := by
              simp [Wbig, W, endpointGluedVertices_cons_eq_append_tail]
            have hiWbig : i + 1 < Wbig.length := by simpa [Wbig] using hi
            have htail_len : W.tail.length = W.length - 1 := List.length_tail
            dsimp [q, r]
            rw [hbig_len] at hiWbig
            omega
          rcases ih hsucc_rest r hrseg with
            ⟨k, hk, m, hm, hidx, hleft_eq, hright_eq⟩
          refine ⟨k + 1, by simpa [hk], m, ?_, ?_, ?_, ?_⟩
          · simpa using hm
          · have hr_eq : r =
                ((rest.take k).map
                  (fun Γ : PolygonalArc => Γ.vertices.length - 1)).sum + m := hidx
            rw [List.map_take] at hr_eq
            dsimp [q, r] at hr_eq ⊢
            simp [List.map_take]
            have hΔlen := Δ.length_ge_two
            omega
          · have hidx_left : i - Δ.vertices.length = q := by rfl
            have hq_tail : q < W.tail.length := by
              have htail_len : W.tail.length = W.length - 1 := List.length_tail
              dsimp [r] at hrseg
              omega
            have hglobal_left :
                Wbig[i] = W[r] := by
              have happ : i < (Δ.vertices ++ W.tail).length := by
                have hiWbig : i < Wbig.length := by
                  have hi' : i + 1 < Wbig.length := by simpa [Wbig] using hi
                  omega
                simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail]
                  using hiWbig
              have htail_idx :
                  W.tail[q]'hq_tail = W[r] := by
                simpa [r] using (List.getElem_tail (l := W) (i := q) hq_tail)
              have happget :
                  Wbig[i] = W.tail[q]'hq_tail := by
                simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail,
                  hidx_left] using
                  (List.getElem_append_right
                    (as := Δ.vertices) (bs := W.tail) (i := i)
                    (h₂ := happ) hge)
              rw [happget, htail_idx]
            rw [hglobal_left, hleft_eq]
            simp
          · have hle : Δ.vertices.length ≤ i + 1 := by omega
            have hidx_succ : i + 1 - Δ.vertices.length = q + 1 := by
              dsimp [q]
              omega
            have hq1_tail : q + 1 < W.tail.length := by
              have htail_len : W.tail.length = W.length - 1 := List.length_tail
              dsimp [r] at hrseg
              omega
            have hglobal_right :
                Wbig[i + 1] = W[r + 1] := by
              have happ : i + 1 < (Δ.vertices ++ W.tail).length := by
                have hiWbig : i + 1 < Wbig.length := by simpa [Wbig] using hi
                simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail]
                  using hiWbig
              have htail_idx :
                  W.tail[q + 1]'hq1_tail = W[r + 1] := by
                simpa [r] using
                  (List.getElem_tail (l := W) (i := q + 1) hq1_tail)
              have happget :
                  Wbig[i + 1] = W.tail[q + 1]'hq1_tail := by
                simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail,
                  hidx_succ] using
                  (List.getElem_append_right
                    (as := Δ.vertices) (bs := W.tail) (i := i + 1)
                    (h₂ := happ) hle)
              rw [happget, htail_idx]
            rw [hglobal_right, hright_eq]
            simp
