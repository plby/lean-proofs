import Util.IncidenceGeometry.PolygonalArcEndpointGluedTailSegmentLift

open Classical
noncomputable section

lemma PolygonalArcEndpointGluedSegmentTransfer
    (pieces : List PolygonalArc)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source) :
    (∀ Γ, Γ ∈ pieces →
      ∀ m (hm : m + 1 < Γ.vertices.length),
        ∃ i : ℕ,
          ∃ hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length,
            (((PolygonalArcEndpointGluedVertices pieces)[i] =
                  Γ.vertices[m] ∧
                (PolygonalArcEndpointGluedVertices pieces)[i + 1] =
                  Γ.vertices[m + 1]) ∨
              ((PolygonalArcEndpointGluedVertices pieces)[i] =
                  Γ.vertices[m + 1] ∧
                (PolygonalArcEndpointGluedVertices pieces)[i + 1] =
                  Γ.vertices[m]))) ∧
    (∀ i
      (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
      ∃ Γ : PolygonalArc, Γ ∈ pieces ∧
        ∃ m : ℕ, ∃ hm : m + 1 < Γ.vertices.length,
          (((PolygonalArcEndpointGluedVertices pieces)[i] =
                Γ.vertices[m] ∧
              (PolygonalArcEndpointGluedVertices pieces)[i + 1] =
                Γ.vertices[m + 1]) ∨
            ((PolygonalArcEndpointGluedVertices pieces)[i] =
                Γ.vertices[m + 1] ∧
              (PolygonalArcEndpointGluedVertices pieces)[i + 1] =
                Γ.vertices[m]))) := by
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
  constructor
  · induction pieces with
    | nil =>
        intro Γ hΓ
        cases hΓ
    | cons Δ rest ih =>
        intro Γ hΓ m hm
        simp only [List.mem_cons] at hΓ
        rcases hΓ with hΓ | hΓ
        · subst Γ
          refine ⟨m, ?_, Or.inl ?_⟩
          · simp [PolygonalArcEndpointGluedVertices, List.length_append]
            omega
          · constructor
            · have hm_lt : m < Δ.vertices.length := by omega
              have hm_app :
                  m < (Δ.vertices ++
                      (rest.map (fun Δ => Δ.vertices.tail)).flatten).length := by
                simp [List.length_append]
                omega
              simpa [PolygonalArcEndpointGluedVertices] using
                (List.getElem_append_left
                  (as := Δ.vertices)
                  (bs := (rest.map (fun Δ => Δ.vertices.tail)).flatten)
                  (i := m) (h' := hm_app) hm_lt)
            · have hm1_lt : m + 1 < Δ.vertices.length := by omega
              have hm1_app :
                  m + 1 < (Δ.vertices ++
                      (rest.map (fun Δ => Δ.vertices.tail)).flatten).length := by
                simp [List.length_append]
                omega
              simpa [PolygonalArcEndpointGluedVertices] using
                (List.getElem_append_left
                  (as := Δ.vertices)
                  (bs := (rest.map (fun Δ => Δ.vertices.tail)).flatten)
                  (i := m + 1) (h' := hm1_app) hm1_lt)
        · have hsucc_rest :
              ∀ n (hn : n + 1 < rest.length),
                (rest[n]).target = (rest[n + 1]).source := by
            intro n hn
            have hn_full : (n + 1) + 1 < (Δ :: rest).length := by
              simp
              omega
            have h := successive_attach (n + 1) hn_full
            simpa using h
          rcases ih hsucc_rest Γ hΓ m hm with
            ⟨i, hi, hseg⟩
          have hattach :
              ∀ Γ, rest.head? = some Γ → Δ.target = Γ.source := by
            intro E hhead
            cases rest with
            | nil => simp at hhead
            | cons Z zs =>
                have hfull : 0 + 1 < (Δ :: Z :: zs).length := by simp
                have h := successive_attach 0 hfull
                simp at hhead
                subst E
                simpa using h
          rcases PolygonalArcEndpointGluedTailSegmentLift Δ rest hattach i hi with
            ⟨j, hj, hlift⟩
          refine ⟨j, hj, ?_⟩
          rcases hseg with hseg | hseg
          · left
            exact ⟨by rw [hlift.1, hseg.1],
              by rw [hlift.2, hseg.2]⟩
          · right
            exact ⟨by rw [hlift.1, hseg.1],
              by rw [hlift.2, hseg.2]⟩
  · induction pieces with
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
        · refine ⟨Δ, by simp, i, hleft, Or.inl ?_⟩
          constructor
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
                have hWseg : 0 + 1 <
                    (PolygonalArcEndpointGluedVertices (E :: rs)).length := by
                  have htail_pos :
                      0 <
                        (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                    have hbig_len :
                        (PolygonalArcEndpointGluedVertices (Δ :: E :: rs)).length =
                          Δ.vertices.length +
                            (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                      simp [endpointGluedVertices_cons_eq_append_tail,
                        List.length_append]
                    have hi_big : i + 1 <
                        (PolygonalArcEndpointGluedVertices (Δ :: E :: rs)).length := hi
                    rw [hbig_len, hibound] at hi_big
                    omega
                  simpa [List.length_tail] using htail_pos
                rcases ih hsucc_rest 0 hWseg with
                  ⟨Γ, hΓ, m, hm, hseg⟩
                refine ⟨Γ, by simp [hΓ], m, hm, ?_⟩
                have hattach : Δ.target = E.source := by
                  have hfull : 0 + 1 < (Δ :: E :: rs).length := by simp
                  simpa using successive_attach 0 hfull
                have hbig_left :
                    (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i] =
                      (PolygonalArcEndpointGluedVertices (E :: rs))[0] := by
                  have hΔlast :
                      Δ.vertices[i]'histart = Δ.target := by
                    have hi_eq : i = Δ.vertices.length - 1 := by omega
                    subst i
                    exact polygonalArc_last_vertex Δ
                  have hEfirst :
                      (PolygonalArcEndpointGluedVertices (E :: rs))[0] =
                        E.source := by
                    have hE0 :
                        E.vertices[0]'(by
                          have hlen := E.length_ge_two
                          omega) = E.source :=
                      polygonalArc_first_vertex E
                    simpa [PolygonalArcEndpointGluedVertices, hE0] using
                      (List.getElem_append_left
                        (as := E.vertices)
                        (bs := (rs.map (fun Δ => Δ.vertices.tail)).flatten)
                        (i := 0)
                        (by
                          have hlen := E.length_ge_two
                          omega))
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
                have hbig_right :
                    (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i + 1] =
                      (PolygonalArcEndpointGluedVertices (E :: rs))[1] := by
                  have htail_ne :
                      (PolygonalArcEndpointGluedVertices (E :: rs)).tail ≠ [] := by
                    intro hnil
                    have hlen_tail :
                        (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length = 0 := by
                      simp [hnil]
                    have hlen_tail_pos :
                        0 < (PolygonalArcEndpointGluedVertices (E :: rs)).tail.length := by
                      simpa [List.length_tail] using hWseg
                    omega
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
                    simp only [List.length_append, List.length_tail, lt_add_iff_pos_right, tsub_pos_iff_lt, gt_iff_lt]
                    exact hWseg
                  have hbig_tail :
                      (PolygonalArcEndpointGluedVertices (Δ :: E :: rs))[i + 1] =
                        (PolygonalArcEndpointGluedVertices (E :: rs)).tail[0]'(by
                          simpa [List.length_tail] using hWseg) := by
                    simpa [endpointGluedVertices_cons_eq_append_tail, hidx] using
                      (List.getElem_append_right
                        (as := Δ.vertices)
                        (bs := (PolygonalArcEndpointGluedVertices (E :: rs)).tail)
                        (i := i + 1) (h₂ := happ) hle)
                  have htail0 :
                      (PolygonalArcEndpointGluedVertices (E :: rs)).tail[0]'(by
                        simpa [List.length_tail] using hWseg) =
                        (PolygonalArcEndpointGluedVertices (E :: rs))[1]'hWseg := by
                    exact List.getElem_tail _
                  rw [hbig_tail, htail0]
                rcases hseg with hseg | hseg
                · left
                  exact ⟨by rw [hbig_left, hseg.1],
                    by rw [hbig_right, hseg.2]⟩
                · right
                  exact ⟨by rw [hbig_left, hseg.1],
                    by rw [hbig_right, hseg.2]⟩
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
              ⟨Γ, hΓ, m, hm, hseg⟩
            refine ⟨Γ, by simp [hΓ], m, hm, ?_⟩
            have hidx_left : i - Δ.vertices.length = q := by rfl
            have hq_tail : q < W.tail.length := by
              have htail_len : W.tail.length = W.length - 1 := List.length_tail
              dsimp [r] at hrseg
              omega
            have hq1_tail : q + 1 < W.tail.length := by
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
            have hglobal_right :
                Wbig[i + 1] = W[r + 1] := by
              have hle : Δ.vertices.length ≤ i + 1 := by omega
              have hidx : i + 1 - Δ.vertices.length = q + 1 := by
                dsimp [q]
                omega
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
                  hidx] using
                  (List.getElem_append_right
                    (as := Δ.vertices) (bs := W.tail) (i := i + 1)
                    (h₂ := happ) hle)
              rw [happget, htail_idx]
            rcases hseg with hseg | hseg
            · left
              exact ⟨by rw [hglobal_left, hseg.1],
                by rw [hglobal_right, hseg.2]⟩
            · right
              exact ⟨by rw [hglobal_left, hseg.1],
                by rw [hglobal_right, hseg.2]⟩
