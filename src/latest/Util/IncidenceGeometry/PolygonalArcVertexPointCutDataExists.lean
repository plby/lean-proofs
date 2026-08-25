import Util.IncidenceGeometry.PolygonalArcContiguousVertexSubarc
import Util.IncidenceGeometry.PolygonalArcPointCutData
import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcVertexPointCutDataExists
    (Q : PolygonalArc) (k : ℕ)
    (hkpos : 0 < k) (hk : k + 1 < Q.vertices.length) :
    Nonempty (PolygonalArcPointCutData Q Q.vertices[k]) := by
  let last := Q.vertices.length - 1
  have hlast : last < Q.vertices.length := by
    dsimp [last]
    omega
  have hklast : k < last := by
    dsimp [last]
    omega
  obtain ⟨P, hPvertices, hPsource, hPtarget, hPcarrier, hPtransfer⟩ :=
    PolygonalArcContiguousVertexSubarc Q 0 k (by omega) (by omega) hkpos
  obtain ⟨S, hSvertices, hSsource, hStarget, hScarrier, hStransfer⟩ :=
    PolygonalArcContiguousVertexSubarc Q k last (by omega) hlast hklast
  have hsource0 : Q.vertices[0] = Q.source := by
    have hhead := Q.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  have htargetLast : Q.vertices[last] = Q.target := by
    have hlast' := Q.target_eq_last
    rw [List.getLast?_eq_getLast_of_ne_nil (by
      exact List.ne_nil_of_length_pos (by omega))] at hlast'
    have hget : Q.vertices.getLast (by
        exact List.ne_nil_of_length_pos (by omega)) = Q.target :=
      Option.some.inj hlast'
    simpa [last, List.getLast_eq_getElem] using hget
  have hPsubset : P.carrier ⊆ Q.carrier := by
    intro z hz
    rw [hPcarrier] at hz
    rcases hz with ⟨i, hi, _hi0, hik, hzseg⟩
    rw [Q.carrier_eq]
    exact ⟨i, hi, hzseg⟩
  have hSsubset : S.carrier ⊆ Q.carrier := by
    intro z hz
    rw [hScarrier] at hz
    rcases hz with ⟨i, hi, _hki, _hilast, hzseg⟩
    rw [Q.carrier_eq]
    exact ⟨i, hi, hzseg⟩
  have hdecomp : Q.carrier = P.carrier ∪ S.carrier := by
    ext z
    constructor
    · intro hz
      rw [Q.carrier_eq] at hz
      rcases hz with ⟨i, hi, hzseg⟩
      by_cases hik : i < k
      · left
        rw [hPcarrier]
        exact ⟨i, hi, by omega, hik, hzseg⟩
      · right
        rw [hScarrier]
        exact ⟨i, hi, by omega, by
          dsimp [last]
          omega, hzseg⟩
    · rintro (hz | hz)
      · exact hPsubset hz
      · exact hSsubset hz
  have hinter : P.carrier ∩ S.carrier = {Q.vertices[k]} := by
    ext z
    constructor
    · rintro ⟨hzP, hzS⟩
      rw [hPcarrier] at hzP
      rw [hScarrier] at hzS
      rcases hzP with ⟨i, hi, _hi0, hik, hzPi⟩
      rcases hzS with ⟨j, hj, hkj, _hjlast, hzSj⟩
      have hij : i < j := by omega
      have hraw := Q.segment_intersections hi hj hij
      have hzinter : z ∈
          segment ℝ Q.vertices[i] Q.vertices[i + 1] ∩
            segment ℝ Q.vertices[j] Q.vertices[j + 1] := ⟨hzPi, hzSj⟩
      by_cases hadj : j = i + 1
      · rw [hraw, if_pos hadj] at hzinter
        have hjk : j = k := by omega
        simpa [hjk] using hzinter
      · rw [hraw, if_neg hadj] at hzinter
        exact False.elim hzinter
    · intro hz
      have hzEq : z = Q.vertices[k] := by simpa using hz
      subst z
      constructor
      · rw [hPcarrier]
        refine ⟨k - 1, by omega, by omega, by omega, ?_⟩
        have hidx : k - 1 + 1 = k := by omega
        simpa [hidx] using
          (right_mem_segment ℝ Q.vertices[k - 1] Q.vertices[k - 1 + 1])
      · rw [hScarrier]
        exact ⟨k, hk, by omega, hklast, left_mem_segment ℝ _ _⟩
  have hPregion : P.carrier =
      {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
        i < k - 1 ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} ∪
        segment ℝ Q.vertices[k - 1] Q.vertices[k] := by
    rw [hPcarrier]
    ext z
    constructor
    · rintro ⟨i, hi, _hi0, hik, hz⟩
      by_cases hbefore : i < k - 1
      · exact Or.inl ⟨i, hi, hbefore, hz⟩
      · right
        have hieq : i = k - 1 := by omega
        subst i
        simpa [Nat.sub_add_cancel hkpos] using hz
    · rintro (⟨i, hi, hbefore, hz⟩ | hz)
      · exact ⟨i, hi, by omega, by omega, hz⟩
      · refine ⟨k - 1, by omega, by omega, by omega, ?_⟩
        simpa [Nat.sub_add_cancel hkpos] using hz
  have hSregion : S.carrier =
      segment ℝ Q.vertices[k] Q.vertices[k - 1 + 1] ∪
        {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
          k - 1 < i ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} := by
    rw [hScarrier]
    ext z
    constructor
    · rintro ⟨i, hi, hki, hilast, hz⟩
      exact Or.inr ⟨i, hi, by omega, hz⟩
    · rintro (hz | ⟨i, hi, hki, hz⟩)
      · have hzEq : z = Q.vertices[k] := by
          simpa [Nat.sub_add_cancel hkpos] using hz
        subst z
        exact ⟨k, hk, le_rfl, hklast, left_mem_segment ℝ _ _⟩
      · exact ⟨i, hi, by omega, by
          dsimp [last]
          omega, hz⟩
  have hPverticesExact :
      P.vertices = Q.vertices.take (k - 1 + 1) ++ [Q.vertices[k]] := by
    calc
      P.vertices = Q.vertices.take (k + 1) := by simpa using hPvertices
      _ = Q.vertices.take k ++ [Q.vertices[k]] :=
        (List.take_concat_get' Q.vertices k (by omega)).symm
      _ = Q.vertices.take (k - 1 + 1) ++ [Q.vertices[k]] := by
        rw [Nat.sub_add_cancel hkpos]
  have hSverticesExact :
      S.vertices = Q.vertices[k] :: Q.vertices.drop (k + 1) := by
    calc
      S.vertices = Q.vertices.drop k := by
        rw [hSvertices]
        apply List.take_of_length_le
        simp [last, List.length_drop]
        omega
      _ = Q.vertices[k] :: Q.vertices.drop (k + 1) :=
        (List.cons_getElem_drop_succ (l := Q.vertices) (n := k) (h := by omega)).symm
  have hQgetEq (a b : ℕ) (ha : a < Q.vertices.length)
      (hb : b < Q.vertices.length) (hab : a = b) :
      Q.vertices[a]'ha = Q.vertices[b]'hb := by
    subst b
    rfl
  refine ⟨{
    prefixArc := P
    suffixArc := S
    cutIndex := k - 1
    cutIndex_valid := by omega
    cut_mem_segment := by
      simpa [Nat.sub_add_cancel hkpos] using
        (right_mem_segment ℝ Q.vertices[k - 1] Q.vertices[k])
    prefix_vertices_exact := hPverticesExact
    suffixDropIndex := k + 1
    suffix_vertices_exact := hSverticesExact
    suffix_drop_index_spec := Or.inr ⟨by omega, by
      exact hQgetEq k (k - 1 + 1) (by omega) (by omega)
        (Nat.sub_add_cancel hkpos).symm⟩
    prefix_source := hPsource.trans hsource0
    prefix_target := hPtarget
    suffix_source := hSsource
    suffix_target := hStarget.trans htargetLast
    prefix_carrier_subset := hPsubset
    suffix_carrier_subset := hSsubset
    carrier_decomposition := hdecomp
    carrier_intersection := hinter
    prefix_carrier_region := hPregion
    suffix_carrier_region := hSregion
    prefix_segment_transfer := ?_
    suffix_segment_transfer := ?_
    protected_first_vertices := ?_ }⟩
  · intro z i hi hzopen hzP _hzc
    obtain ⟨j, hj, hzj, hdir⟩ := hPtransfer z i hi hzopen hzP
    exact ⟨j, hj, hzj, 1, one_ne_zero, by simpa using hdir⟩
  · intro z i hi hzopen hzS _hzc
    obtain ⟨j, hj, hzj, hdir⟩ := hStransfer z i hi hzopen hzS
    exact ⟨j, hj, hzj, 1, one_ne_zero, by simpa using hdir⟩
  · intro hfirst hcut
    have hk2 : 2 ≤ k := by
      by_contra hnot
      have hk1 : k = 1 := by omega
      apply hcut
      simpa only [hk1] using
        (right_mem_segment ℝ Q.vertices[0] Q.vertices[1])
    have hPlen : 0 + 1 < P.vertices.length := by
      rw [hPvertices]
      simp [List.length_take, List.length_drop]
      omega
    refine ⟨hPlen, ?_, ?_⟩
    · have hopt := congrArg (fun xs => xs[0]?) hPvertices
      change P.vertices[0]? =
        ((Q.vertices.drop 0).take (k - 0 + 1))[0]? at hopt
      have hright : 0 < ((Q.vertices.drop 0).take (k - 0 + 1)).length := by
        simp [List.length_take]
        omega
      rw [List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hright] at hopt
      have hval := Option.some.inj hopt
      simpa using hval
    · have hopt := congrArg (fun xs => xs[1]?) hPvertices
      change P.vertices[1]? =
        ((Q.vertices.drop 0).take (k - 0 + 1))[1]? at hopt
      have hright : 1 < ((Q.vertices.drop 0).take (k - 0 + 1)).length := by
        simp [List.length_take]
        omega
      rw [List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hright] at hopt
      have hval := Option.some.inj hopt
      simpa using hval
