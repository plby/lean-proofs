import ErdosProblems.Erdos733.ST.PolygonalArc
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcContiguousVertexSubarc]
lemma PolygonalArcContiguousVertexSubarc
    (Q : PolygonalArc) (a b : ℕ)
    (ha : a < Q.vertices.length) (hb : b < Q.vertices.length)
    (hab : a < b) :
    ∃ R : PolygonalArc,
      R.vertices = (Q.vertices.drop a).take (b - a + 1) ∧
      R.source = Q.vertices[a] ∧
      R.target = Q.vertices[b] ∧
      R.carrier =
        {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
          a ≤ i ∧ i < b ∧
          z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} ∧
      ∀ z i (hi : i + 1 < Q.vertices.length),
        z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
        z ∈ R.carrier →
        ∃ j : ℕ, ∃ hj : j + 1 < R.vertices.length,
          z ∈ openSegment ℝ R.vertices[j] R.vertices[j + 1] ∧
            R.vertices[j + 1] - R.vertices[j] =
              Q.vertices[i + 1] - Q.vertices[i] := by
-- BODY
  let V := (Q.vertices.drop a).take (b - a + 1)
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | ∃ i : ℕ, ∃ hi : i + 1 < V.length,
      z ∈ segment ℝ V[i] V[i + 1]}
  have hVlen : V.length = b - a + 1 := by
    dsimp [V]
    rw [List.length_take, List.length_drop, min_eq_left]
    omega
  have hVtwo : 2 ≤ V.length := by omega
  have hVget : ∀ i (hi : i < V.length), V[i] = Q.vertices[a + i] := by
    intro i hi
    dsimp [V]
    rw [List.getElem_take]
    rw [List.getElem_drop]
  have hVhead : V.head? = some Q.vertices[a] := by
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem (by omega)]
    exact congrArg some (by simpa using hVget 0 (by omega))
  have hVlast : V.getLast? = some Q.vertices[b] := by
    have hVne : V ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [List.getLast?_eq_getLast_of_ne_nil hVne]
    rw [List.getLast_eq_getElem]
    have hidx : V.length - 1 < V.length := by omega
    have hget := hVget (V.length - 1) hidx
    have heq : a + (V.length - 1) = b := by omega
    exact congrArg some (by simpa [heq] using hget)
  have hVnodup : V.Nodup := by
    apply List.Sublist.nodup
    · exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
    · exact Q.simple_vertices
  have hVintersections :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < V.length) →
        (hj : j + 1 < V.length) →
        i < j →
        (segment ℝ V[i] V[i + 1] ∩ segment ℝ V[j] V[j + 1]) =
          if j = i + 1 then {V[j]} else ∅ := by
    intro i j hi hj hij
    have hiQ : a + i + 1 < Q.vertices.length := by omega
    have hjQ : a + j + 1 < Q.vertices.length := by omega
    have h := Q.segment_intersections (i := a + i) (j := a + j)
      (by omega) (by omega) (by omega)
    have hadj : a + j = a + i + 1 ↔ j = i + 1 := by omega
    simp only [hVget i (by omega), hVget (i + 1) (by omega),
      hVget j (by omega), hVget (j + 1) (by omega)]
    simpa [Nat.add_assoc, hadj] using h
  have hVavoid :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < V.length) →
        (hk : k < V.length) →
        k ≠ i → k ≠ i + 1 →
        V[k] ∉ openSegment ℝ V[i] V[i + 1] := by
    intro i k hi hk hki hki1
    have hiQ : a + i + 1 < Q.vertices.length := by omega
    have hkQ : a + k < Q.vertices.length := by omega
    have h := Q.vertices_avoid_nonincident_interiors
      (i := a + i) (k := a + k) (by omega) (by omega)
      (by omega) (by omega)
    simpa [Nat.add_assoc, hVget k hk, hVget i (by omega),
      hVget (i + 1) (by omega)] using h
  let R : PolygonalArc :=
    { vertices := V
      length_ge_two := hVtwo
      source := Q.vertices[a]
      target := Q.vertices[b]
      source_eq_head := hVhead
      target_eq_last := hVlast
      carrier := C
      relativeInterior := C \ ({Q.vertices[a], Q.vertices[b]} : Set _)
      carrier_eq := rfl
      relativeInterior_eq := rfl
      simple_vertices := hVnodup
      segment_intersections := hVintersections
      vertices_avoid_nonincident_interiors := hVavoid }
  have hRcarrier : R.carrier =
      {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
        a ≤ i ∧ i < b ∧
        z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨i, hi, hzi⟩
      refine ⟨a + i, by omega, by omega, by omega, ?_⟩
      simpa [Nat.add_assoc, hVget i (by omega), hVget (i + 1) (by omega)] using hzi
    · rintro ⟨i, hiQ, hai, hib, hzi⟩
      let j := i - a
      have hij : i = a + j := by dsimp [j]; omega
      have hj : j + 1 < V.length := by dsimp [j]; omega
      refine ⟨j, hj, ?_⟩
      simpa [R, C, Nat.add_assoc, hij, hVget j (by omega),
        hVget (j + 1) (by omega)] using hzi
  refine ⟨R, rfl, rfl, rfl, hRcarrier, ?_⟩
  intro z i hi hzopen hzR
  rw [hRcarrier] at hzR
  rcases hzR with ⟨m, hm, ham, hmb, hzclosed⟩
  have hseg_ne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
    intro heq
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
    omega
  have hz_ne_left : z ≠ Q.vertices[i] := by
    intro hz
    subst z
    exact hseg_ne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hzopen)
  have hz_ne_right : z ≠ Q.vertices[i + 1] := by
    intro hz
    subst z
    exact hseg_ne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hzopen)
  have him : i = m := by
    rcases lt_trichotomy i m with him | him | hmi
    · have hinter := Q.segment_intersections hi hm him
      have hzinter : z ∈
          segment ℝ Q.vertices[i] Q.vertices[i + 1] ∩
            segment ℝ Q.vertices[m] Q.vertices[m + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hzopen, hzclosed⟩
      by_cases hadj : m = i + 1
      · rw [hinter, if_pos hadj] at hzinter
        have hz : z = Q.vertices[i + 1] := by simpa [hadj] using hzinter
        exact False.elim (hz_ne_right hz)
      · rw [hinter, if_neg hadj] at hzinter
        exact False.elim hzinter
    · exact him
    · have hinter := Q.segment_intersections hm hi hmi
      have hzinter : z ∈
          segment ℝ Q.vertices[m] Q.vertices[m + 1] ∩
            segment ℝ Q.vertices[i] Q.vertices[i + 1] :=
        ⟨hzclosed, openSegment_subset_segment ℝ _ _ hzopen⟩
      by_cases hadj : i = m + 1
      · rw [hinter, if_pos hadj] at hzinter
        have hz : z = Q.vertices[i] := by simpa [hadj] using hzinter
        exact False.elim (hz_ne_left hz)
      · rw [hinter, if_neg hadj] at hzinter
        exact False.elim hzinter
  subst m
  let j := i - a
  have hij : i = a + j := by dsimp [j]; omega
  have hj : j + 1 < R.vertices.length := by
    change j + 1 < V.length
    dsimp [j]
    omega
  refine ⟨j, hj, ?_, ?_⟩
  · simpa [R, Nat.add_assoc, hij, hVget j (by omega),
      hVget (j + 1) (by omega)] using hzopen
  · change V[j + 1] - V[j] = Q.vertices[i + 1] - Q.vertices[i]
    rw [hVget j (by omega), hVget (j + 1) (by omega)]
    have h0 : a + j = i := hij.symm
    have h1 : a + (j + 1) = i + 1 := by omega
    simp only [h0, h1]
