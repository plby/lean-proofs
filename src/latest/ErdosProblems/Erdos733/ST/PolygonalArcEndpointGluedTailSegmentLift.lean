import ErdosProblems.Erdos733.ST.PolygonalArcEndpointGluedVertices

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcEndpointGluedTailSegmentLift]
lemma PolygonalArcEndpointGluedTailSegmentLift
    (Δ : PolygonalArc) (rest : List PolygonalArc)
    (hattach :
      ∀ Γ, rest.head? = some Γ → Δ.target = Γ.source) :
    ∀ i
      (hi : i + 1 < (PolygonalArcEndpointGluedVertices rest).length),
      ∃ j : ℕ,
        ∃ hj : j + 1 < (PolygonalArcEndpointGluedVertices (Δ :: rest)).length,
          (PolygonalArcEndpointGluedVertices (Δ :: rest))[j] =
              (PolygonalArcEndpointGluedVertices rest)[i] ∧
            (PolygonalArcEndpointGluedVertices (Δ :: rest))[j + 1] =
              (PolygonalArcEndpointGluedVertices rest)[i + 1] := by
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
  intro i hi
  let W := PolygonalArcEndpointGluedVertices rest
  let Wbig := PolygonalArcEndpointGluedVertices (Δ :: rest)
  have hWbig : Wbig = Δ.vertices ++ W.tail := by
    dsimp [Wbig, W]
    exact endpointGluedVertices_cons_eq_append_tail Δ rest
  by_cases hi0 : i = 0
  · subst i
    cases rest with
    | nil =>
        simp [PolygonalArcEndpointGluedVertices] at hi
    | cons Γ rs =>
        let j := Δ.vertices.length - 1
        have hj : j + 1 < Wbig.length := by
          have hΔlen := Δ.length_ge_two
          have hWlen :
              1 < (PolygonalArcEndpointGluedVertices (Γ :: rs)).length := by
            simpa [W] using hi
          simp [PolygonalArcEndpointGluedVertices, List.length_append] at hWlen
          simp [Wbig, PolygonalArcEndpointGluedVertices, List.length_append]
          omega
        refine ⟨j, hj, ?_⟩
        constructor
        · have hj_left : j < Δ.vertices.length := by
            have hΔlen := Δ.length_ge_two
            dsimp [j]
            omega
          have hbigj :
              Wbig[j] = Δ.vertices[j] := by
            have hj_append : j < (Δ.vertices ++ W.tail).length := by
              simp [List.length_append]
              omega
            simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail] using
              (List.getElem_append_left (as := Δ.vertices) (bs := W.tail)
                (i := j) (h' := hj_append) hj_left)
          have hΔlast : Δ.vertices[j] = Δ.target := by
            dsimp [j]
            exact polygonalArc_last_vertex Δ
          have hΓfirst :
              (PolygonalArcEndpointGluedVertices (Γ :: rs))[0] = Γ.source := by
            have hΓ0 :
                Γ.vertices[0]'(by
                  have hlen := Γ.length_ge_two
                  omega) = Γ.source :=
              polygonalArc_first_vertex Γ
            simpa [PolygonalArcEndpointGluedVertices, hΓ0] using
              (List.getElem_append_left
                (as := Γ.vertices)
                (bs := (rs.map (fun Δ => Δ.vertices.tail)).flatten)
                (i := 0)
                (by
                  have hlen := Γ.length_ge_two
                  omega))
          have hatt : Δ.target = Γ.source := hattach Γ rfl
          rw [hbigj, hΔlast, hatt, hΓfirst]
        · have htail_ne : W.tail ≠ [] := by
            intro hnil
            have hlen_tail : W.tail.length = 0 := by simp [hnil]
            have hWlen : 1 < W.length := by simpa [W] using hi
            have htail_len : W.tail.length = W.length - 1 := List.length_tail
            omega
          have hbig_next :
              Wbig[j + 1] = W.tail[0]'(by
                have hlen_tail : 0 < W.tail.length := by
                  cases h : W.tail with
                  | nil => exact False.elim (htail_ne h)
                  | cons a as => simp
                exact hlen_tail) := by
            have hle : Δ.vertices.length ≤ j + 1 := by dsimp [j]; omega
            have hidx : j + 1 - Δ.vertices.length = 0 := by
              have hΔlen := Δ.length_ge_two
              dsimp [j]
              omega
            have hj_append :
                j + 1 < (Δ.vertices ++ W.tail).length := by
              have htail_pos : 0 < W.tail.length := by
                cases h : W.tail with
                | nil => exact False.elim (htail_ne h)
                | cons a as => simp
              have hjsucc : j + 1 = Δ.vertices.length := by
                have hΔlen := Δ.length_ge_two
                dsimp [j]
                omega
              rw [hjsucc]
              simp [List.length_append]
              simpa [W] using hi
            simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail, hidx] using
              (List.getElem_append_right (as := Δ.vertices) (bs := W.tail)
                (i := j + 1) (h₂ := hj_append) hle)
          have htail0 :
              W.tail[0]'(by
                have hWlen : 1 < W.length := by simpa [W] using hi
                simpa [List.length_tail] using Nat.sub_pos_of_lt hWlen) =
                W[1]'(by simpa [W] using hi) := by
            exact List.getElem_tail _
          rw [hbig_next, htail0]
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    let q := i - 1
    let j := Δ.vertices.length + q
    have hq_succ : q + 1 = i := by
      dsimp [q]
      omega
    have hq_tail : q + 1 < W.tail.length := by
      have htail_len : W.tail.length = W.length - 1 := List.length_tail
      have hiW : i + 1 < W.length := by simpa [W] using hi
      omega
    have hj : j + 1 < Wbig.length := by
      have hbig_len : Wbig.length = Δ.vertices.length + W.tail.length := by
        simp [Wbig, W, endpointGluedVertices_cons_eq_append_tail]
      rw [hbig_len]
      dsimp [j]
      omega
    refine ⟨j, hj, ?_⟩
    constructor
    · have hle : Δ.vertices.length ≤ j := by
        dsimp [j]
        omega
      have hidx : j - Δ.vertices.length = q := by
        dsimp [j]
        omega
      have hbigj :
          Wbig[j] = W.tail[q] := by
        simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail, hidx] using
          (List.getElem_append_right (as := Δ.vertices) (bs := W.tail)
            (i := j) hle)
      have htailq :
          W.tail[q] = W[i] := by
        have hq_lt : q < W.tail.length := by omega
        have hiW : i + 1 < W.length := by simpa [W] using hi
        have hi_lt : i < W.length := by omega
        simpa [hq_succ] using (List.getElem_tail (l := W) (i := q) hq_lt)
      rw [hbigj, htailq]
    · have hle : Δ.vertices.length ≤ j + 1 := by
        dsimp [j]
        omega
      have hidx : j + 1 - Δ.vertices.length = q + 1 := by
        dsimp [j]
        omega
      have hbigj :
          Wbig[j + 1] = W.tail[q + 1] := by
        simpa [Wbig, W, endpointGluedVertices_cons_eq_append_tail, hidx] using
          (List.getElem_append_right (as := Δ.vertices) (bs := W.tail)
            (i := j + 1) hle)
      have htailq :
          W.tail[q + 1] = W[i + 1] := by
        have hi1_lt : i + 1 < W.length := by simpa [W] using hi
        simpa [hq_succ] using
          (List.getElem_tail (l := W) (i := q + 1) hq_tail)
      rw [hbigj, htailq]
