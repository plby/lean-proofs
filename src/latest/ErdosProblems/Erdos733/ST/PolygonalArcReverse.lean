import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcReverse]
def PolygonalArcReverse (Γ : PolygonalArc) : PolygonalArc :=
-- BODY
  { vertices := Γ.vertices.reverse
    length_ge_two := by
      simpa using Γ.length_ge_two
    source := Γ.target
    target := Γ.source
    source_eq_head := by
      simpa [List.head?_reverse] using Γ.target_eq_last
    target_eq_last := by
      simpa [List.getLast?_reverse] using Γ.source_eq_head
    carrier := Γ.carrier
    relativeInterior := Γ.relativeInterior
    carrier_eq := by
      rw [Γ.carrier_eq]
      ext p
      constructor
      · intro hp
        rcases hp with ⟨k, hk, hpseg⟩
        let i := Γ.vertices.length - 2 - k
        have hi : i + 1 < Γ.vertices.reverse.length := by
          simp [i, List.length_reverse] at *
          omega
        refine ⟨i, hi, ?_⟩
        have hleft :
            Γ.vertices.reverse[i] =
              Γ.vertices[k + 1] := by
          have hi_lt : i < Γ.vertices.reverse.length :=
            Nat.lt_trans (Nat.lt_succ_self i) hi
          have hidx : Γ.vertices.length - 1 - i = k + 1 := by
            dsimp [i]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i) (h := hi_lt))
        have hright :
            Γ.vertices.reverse[i + 1] =
              Γ.vertices[k] := by
          have hidx : Γ.vertices.length - 1 - (i + 1) = k := by
            dsimp [i]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i + 1) (h := hi))
        simpa [hleft, hright, segment_symm] using hpseg
      · intro hp
        rcases hp with ⟨i, hi, hpseg⟩
        let k := Γ.vertices.length - 2 - i
        have hi_orig : i + 1 < Γ.vertices.length := by
          simpa [List.length_reverse] using hi
        have hk : k + 1 < Γ.vertices.length := by
          simp [k] at *
          omega
        refine ⟨k, hk, ?_⟩
        have hleft :
            Γ.vertices.reverse[i] =
              Γ.vertices[k + 1] := by
          have hi_lt : i < Γ.vertices.reverse.length :=
            Nat.lt_trans (Nat.lt_succ_self i) hi
          have hidx : Γ.vertices.length - 1 - i = k + 1 := by
            dsimp [k]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i) (h := hi_lt))
        have hright :
            Γ.vertices.reverse[i + 1] =
              Γ.vertices[k] := by
          have hidx : Γ.vertices.length - 1 - (i + 1) = k := by
            dsimp [k]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i + 1) (h := hi))
        simpa [hleft, hright, segment_symm] using hpseg
    relativeInterior_eq := by
      rw [Γ.relativeInterior_eq]
      ext p
      simp [Set.mem_diff, and_assoc, and_comm]
    simple_vertices := by
      exact List.nodup_reverse.2 Γ.simple_vertices
    segment_intersections := by
      intro i j hi hj hij
      let ri := Γ.vertices.length - 2 - i
      let rj := Γ.vertices.length - 2 - j
      have hi_orig : i + 1 < Γ.vertices.length := by
        simpa [List.length_reverse] using hi
      have hj_orig : j + 1 < Γ.vertices.length := by
        simpa [List.length_reverse] using hj
      have hri : ri + 1 < Γ.vertices.length := by
        dsimp [ri]
        omega
      have hrj : rj + 1 < Γ.vertices.length := by
        dsimp [rj]
        omega
      have hrj_lt_ri : rj < ri := by
        dsimp [ri, rj]
        omega
      have hrev_segment :
          ∀ a (ha : a + 1 < Γ.vertices.reverse.length),
            segment ℝ Γ.vertices.reverse[a] Γ.vertices.reverse[a + 1] =
              segment ℝ Γ.vertices[Γ.vertices.length - 2 - a]
                Γ.vertices[Γ.vertices.length - 2 - a + 1] := by
        intro a ha
        let r := Γ.vertices.length - 2 - a
        have ha_orig : a + 1 < Γ.vertices.length := by
          simpa [List.length_reverse] using ha
        have hleft :
            Γ.vertices.reverse[a] = Γ.vertices[r + 1] := by
          have ha_lt : a < Γ.vertices.reverse.length :=
            Nat.lt_trans (Nat.lt_succ_self a) ha
          have hidx : Γ.vertices.length - 1 - a = r + 1 := by
            dsimp [r]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := a) (h := ha_lt))
        have hright :
            Γ.vertices.reverse[a + 1] = Γ.vertices[r] := by
          have hidx : Γ.vertices.length - 1 - (a + 1) = r := by
            dsimp [r]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := a + 1) (h := ha))
        simpa [r, hleft, hright, segment_symm]
      calc
        segment ℝ Γ.vertices.reverse[i] Γ.vertices.reverse[i + 1] ∩
            segment ℝ Γ.vertices.reverse[j] Γ.vertices.reverse[j + 1]
            =
          segment ℝ Γ.vertices[ri] Γ.vertices[ri + 1] ∩
            segment ℝ Γ.vertices[rj] Γ.vertices[rj + 1] := by
            rw [hrev_segment i hi, hrev_segment j hj]
        _ =
          segment ℝ Γ.vertices[rj] Γ.vertices[rj + 1] ∩
            segment ℝ Γ.vertices[ri] Γ.vertices[ri + 1] := by
            rw [Set.inter_comm]
        _ = (if ri = rj + 1 then {Γ.vertices[ri]} else ∅) := by
            exact Γ.segment_intersections hrj hri hrj_lt_ri
        _ = (if j = i + 1 then {Γ.vertices.reverse[j]} else ∅) := by
            by_cases hAdj : j = i + 1
            · have hAdjOrig : ri = rj + 1 := by
                dsimp [ri, rj]
                omega
              have hj_lt : j < Γ.vertices.reverse.length :=
                Nat.lt_trans (Nat.lt_succ_self j) hj
              have hcommon : Γ.vertices[ri] = Γ.vertices.reverse[j] := by
                have hidx : Γ.vertices.length - 1 - j = ri := by
                  dsimp [ri]
                  omega
                symm
                simpa [hidx] using
                  (List.getElem_reverse (l := Γ.vertices) (i := j)
                    (h := hj_lt))
              have hcommon' :
                  Γ.vertices[rj + 1] = Γ.vertices.reverse[j] := by
                simpa [hAdjOrig] using hcommon
              simp [hAdj, hAdjOrig, hcommon']
            · have hAdjOrig : ri ≠ rj + 1 := by
                intro h
                apply hAdj
                dsimp [ri, rj] at h
                omega
              simp [hAdj, hAdjOrig]
    vertices_avoid_nonincident_interiors := by
      intro i k hi hk hki hkine
      let r := Γ.vertices.length - 2 - i
      let s := Γ.vertices.length - 1 - k
      have hi_orig : i + 1 < Γ.vertices.length := by
        simpa [List.length_reverse] using hi
      have hk_orig : k < Γ.vertices.length := by
        simpa [List.length_reverse] using hk
      have hr : r + 1 < Γ.vertices.length := by
        dsimp [r]
        omega
      have hs : s < Γ.vertices.length := by
        dsimp [s]
        omega
      have hvertex :
          Γ.vertices.reverse[k] = Γ.vertices[s] := by
        simpa [s] using
          (List.getElem_reverse (l := Γ.vertices) (i := k) (h := hk))
      have hseg :
          openSegment ℝ Γ.vertices.reverse[i] Γ.vertices.reverse[i + 1] =
            openSegment ℝ Γ.vertices[r] Γ.vertices[r + 1] := by
        have hi_lt : i < Γ.vertices.reverse.length :=
          Nat.lt_trans (Nat.lt_succ_self i) hi
        have hleft :
            Γ.vertices.reverse[i] = Γ.vertices[r + 1] := by
          have hidx : Γ.vertices.length - 1 - i = r + 1 := by
            dsimp [r]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i) (h := hi_lt))
        have hright :
            Γ.vertices.reverse[i + 1] = Γ.vertices[r] := by
          have hidx : Γ.vertices.length - 1 - (i + 1) = r := by
            dsimp [r]
            omega
          simpa [hidx] using
            (List.getElem_reverse (l := Γ.vertices) (i := i + 1) (h := hi))
        simpa [hleft, hright, openSegment_symm]
      have hs_ne_r : s ≠ r := by
        intro h
        apply hkine
        dsimp [s, r] at h
        omega
      have hs_ne_rsucc : s ≠ r + 1 := by
        intro h
        apply hki
        dsimp [s, r] at h
        omega
      have havoid :=
        Γ.vertices_avoid_nonincident_interiors (i := r) (k := s) hr hs
          hs_ne_r hs_ne_rsucc
      rw [hvertex, hseg]
      exact havoid }
