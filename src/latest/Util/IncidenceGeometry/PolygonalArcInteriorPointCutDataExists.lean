import Util.IncidenceGeometry.ArcCrossingOrderedTailArc
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcPointCutData
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier
import Util.IncidenceGeometry.PolygonalPathConstant
import Mathlib.Tactic

open Classical
noncomputable section

private lemma polygonalArc_suffix_carrier_region
    (Q S : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hSlen : S.vertices.length = Q.vertices.length - i)
    (hSzero : S.vertices[0] = c)
    (hSsucc : ∀ n (hn : n + 1 < S.vertices.length),
      S.vertices[n + 1] = Q.vertices[i + 1 + n])
    (hSpos : ∀ n (hnpos : 0 < n) (hn : n < S.vertices.length),
      S.vertices[n] = Q.vertices[i + n]) :
    S.carrier = segment ℝ c Q.vertices[i + 1] ∪
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
        i < m ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} := by
  rw [S.carrier_eq]
  ext z
  constructor
  · rintro ⟨m, hm, hzm⟩
    by_cases hm0 : m = 0
    · left
      subst m
      have hS1 : S.vertices[1] = Q.vertices[i + 1] := by
        simpa using hSsucc 0 hm
      simpa [hSzero, hS1] using hzm
    · right
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hleft : S.vertices[m] = Q.vertices[i + m] :=
        hSpos m hmpos (by omega)
      have hright : S.vertices[m + 1] = Q.vertices[i + m + 1] := by
        simpa [Nat.add_assoc, Nat.add_comm 1 m] using hSsucc m hm
      refine ⟨i + m, by rw [hSlen] at hm; omega, by omega, ?_⟩
      simpa [hleft, hright, Nat.add_assoc] using hzm
  · rintro (hz | ⟨m, hm, him, hzm⟩)
    · refine ⟨0, by rw [hSlen]; omega, ?_⟩
      have hS1 : S.vertices[1] = Q.vertices[i + 1] := by
        simpa using hSsucc 0 (by rw [hSlen]; omega)
      simpa [hSzero, hS1] using hz
    · let n := m - i
      have hnpos : 0 < n := by dsimp [n]; omega
      have hmn : m = i + n := by dsimp [n]; omega
      have hn : n + 1 < S.vertices.length := by rw [hSlen]; omega
      refine ⟨n, hn, ?_⟩
      have hleft : S.vertices[n] = Q.vertices[m] := by
        simpa [hmn] using hSpos n hnpos (by omega)
      have hright : S.vertices[n + 1] = Q.vertices[m + 1] := by
        simpa [hmn, Nat.add_assoc, Nat.add_comm 1 n] using hSsucc n hn
      simpa [hleft, hright] using hzm

private lemma polygonalArc_prefix_carrier_region
    (Q P : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hPlen : P.vertices.length = i + 2)
    (hPbefore : ∀ n (hn : n < i + 1), P.vertices[n] = Q.vertices[n])
    (hPcut : P.vertices[i + 1] = c) :
    P.carrier =
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          m < i ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} ∪
        segment ℝ Q.vertices[i] c := by
  rw [P.carrier_eq]
  ext z
  constructor
  · rintro ⟨m, hm, hzm⟩
    by_cases hmi : m < i
    · left
      have hleft : P.vertices[m] = Q.vertices[m] := hPbefore m (by omega)
      have hright : P.vertices[m + 1] = Q.vertices[m + 1] :=
        hPbefore (m + 1) (by omega)
      exact ⟨m, by omega, hmi, by simpa [hleft, hright] using hzm⟩
    · right
      have hmiEq : m = i := by rw [hPlen] at hm; omega
      subst m
      have hleft : P.vertices[i] = Q.vertices[i] := hPbefore i (by omega)
      simpa [hleft, hPcut] using hzm
  · rintro (⟨m, hm, hmi, hzm⟩ | hz)
    · refine ⟨m, by rw [hPlen]; omega, ?_⟩
      have hleft : P.vertices[m] = Q.vertices[m] := hPbefore m (by omega)
      have hright : P.vertices[m + 1] = Q.vertices[m + 1] :=
        hPbefore (m + 1) (by omega)
      simpa [hleft, hright] using hzm
    · refine ⟨i, by rw [hPlen]; omega, ?_⟩
      have hleft : P.vertices[i] = Q.vertices[i] := hPbefore i (by omega)
      simpa [hleft, hPcut] using hz

private lemma polygonalArc_carrier_decomposition_of_cut_regions
    (Q P S : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hPsubset : P.carrier ⊆ Q.carrier)
    (hSsubset : S.carrier ⊆ Q.carrier)
    (hPregion : P.carrier =
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          m < i ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} ∪
        segment ℝ Q.vertices[i] c)
    (hSregion : S.carrier =
      segment ℝ c Q.vertices[i + 1] ∪
        {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          i < m ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]})
    (hsplit : ∀ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1],
      z ∈ segment ℝ Q.vertices[i] c ∨
        z ∈ segment ℝ c Q.vertices[i + 1]) :
    Q.carrier = P.carrier ∪ S.carrier := by
  ext z
  constructor
  · intro hz
    rw [Q.carrier_eq] at hz
    rcases hz with ⟨m, hm, hzm⟩
    rcases lt_trichotomy m i with hmi | hmiEq | him
    · left
      rw [hPregion]
      exact Or.inl ⟨m, hm, hmi, hzm⟩
    · subst m
      rcases hsplit z hzm with hzLeft | hzRight
      · left
        rw [hPregion]
        exact Or.inr hzLeft
      · right
        rw [hSregion]
        exact Or.inl hzRight
    · right
      rw [hSregion]
      exact Or.inr ⟨m, hm, him, hzm⟩
  · rintro (hzP | hzS)
    · exact hPsubset hzP
    · exact hSsubset hzS

private lemma polygonalArc_cut_regions_intersection
    (Q P S : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hPregion : P.carrier =
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          m < i ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} ∪
        segment ℝ Q.vertices[i] c)
    (hSregion : S.carrier =
      segment ℝ c Q.vertices[i + 1] ∪
        {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          i < m ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]})
    (hpartialInter :
      segment ℝ Q.vertices[i] c ∩ segment ℝ c Q.vertices[i + 1] = {c})
    (hleft_not_right : Q.vertices[i] ∉ segment ℝ c Q.vertices[i + 1])
    (hright_not_left : Q.vertices[i + 1] ∉ segment ℝ Q.vertices[i] c) :
    P.carrier ∩ S.carrier = {c} := by
  ext z
  constructor
  · rintro ⟨hzP, hzS⟩
    rw [hPregion] at hzP
    rw [hSregion] at hzS
    rcases hzP with ⟨m, hm, hmi, hzm⟩ | hzLeft
    · rcases hzS with hzRight | ⟨n, hn, hin, hzn⟩
      · have hraw := Q.segment_intersections hm hi hmi
        have hzint : z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1] ∩
            segment ℝ Q.vertices[i] Q.vertices[i + 1] :=
          ⟨hzm, (convex_segment _ _).segment_subset
            (openSegment_subset_segment ℝ _ _ hc)
            (right_mem_segment ℝ _ _) hzRight⟩
        by_cases hadj : i = m + 1
        · rw [hraw, if_pos hadj] at hzint
          have hzi : z = Q.vertices[i] := by simpa [hadj] using hzint
          exact False.elim (hleft_not_right (hzi ▸ hzRight))
        · rw [hraw, if_neg hadj] at hzint
          exact False.elim hzint
      · have hmn : m < n := by omega
        have hraw := Q.segment_intersections hm hn hmn
        have hzint : z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1] ∩
            segment ℝ Q.vertices[n] Q.vertices[n + 1] := ⟨hzm, hzn⟩
        have hnot : n ≠ m + 1 := by omega
        rw [hraw, if_neg hnot] at hzint
        exact False.elim hzint
    · rcases hzS with hzRight | ⟨n, hn, hin, hzn⟩
      · have hzint : z ∈ segment ℝ Q.vertices[i] c ∩
            segment ℝ c Q.vertices[i + 1] := ⟨hzLeft, hzRight⟩
        rw [hpartialInter] at hzint
        exact hzint
      · have hraw := Q.segment_intersections hi hn hin
        have hzint : z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1] ∩
            segment ℝ Q.vertices[n] Q.vertices[n + 1] :=
          ⟨(convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
            (openSegment_subset_segment ℝ _ _ hc) hzLeft, hzn⟩
        by_cases hadj : n = i + 1
        · rw [hraw, if_pos hadj] at hzint
          have hzn' : z = Q.vertices[i + 1] := by simpa [hadj] using hzint
          exact False.elim (hright_not_left (hzn' ▸ hzLeft))
        · rw [hraw, if_neg hadj] at hzint
          exact False.elim hzint
  · intro hzc
    have hz : z = c := by simpa using hzc
    subst z
    constructor
    · rw [hPregion]
      exact Or.inr (right_mem_segment ℝ _ _)
    · rw [hSregion]
      exact Or.inl (left_mem_segment ℝ _ _)

private lemma polygonalArc_openSegment_index_unique
    (Q : PolygonalArc) (z : EuclideanSpace ℝ (Fin 2)) (a b : ℕ)
    (ha : a + 1 < Q.vertices.length) (hb : b + 1 < Q.vertices.length)
    (hza : z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1])
    (hzb : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1]) : a = b := by
  have habne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
    intro heq
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
    omega
  have hzleft : z ≠ Q.vertices[a] := by
    intro hz
    subst z
    exact habne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
  have hzright : z ≠ Q.vertices[a + 1] := by
    intro hz
    subst z
    exact habne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hraw := Q.segment_intersections ha hb hab
    have hzint : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
        segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hza, hzb⟩
    by_cases hadj : b = a + 1
    · rw [hraw, if_pos hadj] at hzint
      exact False.elim (hzright (by simpa [hadj] using hzint))
    · rw [hraw, if_neg hadj] at hzint
      exact False.elim hzint
  · rfl
  · have hraw := Q.segment_intersections hb ha hba
    have hzint : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
        segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
      ⟨hzb, openSegment_subset_segment ℝ _ _ hza⟩
    by_cases hadj : a = b + 1
    · rw [hraw, if_pos hadj] at hzint
      exact False.elim (hzleft (by simpa [hadj] using hzint))
    · rw [hraw, if_neg hadj] at hzint
      exact False.elim hzint

private lemma polygonalArc_getElem_eq_of_index_eq
    {α : Type*} (xs : List α) (a b : ℕ)
    (ha : a < xs.length) (hb : b < xs.length) (hab : a = b) :
    xs[a]'ha = xs[b]'hb := by
  subst b
  rfl

private lemma polygonalArc_segment_cut_geometry
    (p q c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ p q) (hpq : p ≠ q) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      (AffineMap.lineMap p q) t = c ∧
      segment ℝ p c ∩ segment ℝ c q = {c} ∧
      p ∉ segment ℝ c q ∧
      q ∉ segment ℝ p c ∧
      ∀ z ∈ segment ℝ p q,
        z ∈ segment ℝ p c ∨ z ∈ segment ℝ c q := by
  let E := EuclideanSpace ℝ (Fin 2)
  have hcParam := hc
  rw [openSegment_eq_image_lineMap] at hcParam
  obtain ⟨t, ht, htc⟩ := hcParam
  have hline_inj := AffineMap.lineMap_injective ℝ hpq
  have hleftParam : segment ℝ p c =
      (AffineMap.lineMap p q) '' Set.Icc 0 t := by
    let F : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p q
    calc
      segment ℝ p c = segment ℝ (F 0) (F t) := by simp [F, htc]
      _ = F '' segment ℝ (0 : ℝ) t := (image_segment ℝ F 0 t).symm
      _ = F '' Set.Icc 0 t := by rw [segment_eq_Icc ht.1.le]
  have hrightParam : segment ℝ c q =
      (AffineMap.lineMap p q) '' Set.Icc t 1 := by
    let F : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p q
    calc
      segment ℝ c q = segment ℝ (F t) (F 1) := by simp [F, htc]
      _ = F '' segment ℝ t (1 : ℝ) := (image_segment ℝ F t 1).symm
      _ = F '' Set.Icc t 1 := by rw [segment_eq_Icc ht.2.le]
  have hpartialInter : segment ℝ p c ∩ segment ℝ c q = {c} := by
    rw [hleftParam, hrightParam]
    ext z
    constructor
    · rintro ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩
      have huv : u = v := hline_inj (huz.trans hvz.symm)
      have hut : u = t := le_antisymm hu.2 (huv ▸ hv.1)
      subst u
      subst v
      simpa [htc] using huz.symm
    · intro hz
      have hzc : z = c := by simpa using hz
      subst z
      constructor
      · exact ⟨t, ⟨ht.1.le, le_rfl⟩, htc⟩
      · exact ⟨t, ⟨le_rfl, ht.2.le⟩, htc⟩
  have hleft_not_right : p ∉ segment ℝ c q := by
    rw [hrightParam]
    rintro ⟨u, hu, hueq⟩
    have hu0 : u = 0 := hline_inj (by simpa using hueq)
    subst u
    linarith [ht.1, hu.1]
  have hright_not_left : q ∉ segment ℝ p c := by
    rw [hleftParam]
    rintro ⟨u, hu, hueq⟩
    have hu1 : u = 1 := hline_inj (by simpa using hueq)
    subst u
    linarith [ht.2, hu.2]
  have hsegment_split : ∀ z ∈ segment ℝ p q,
      z ∈ segment ℝ p c ∨ z ∈ segment ℝ c q := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨u, hu, huz⟩
    by_cases hut : u ≤ t
    · left
      rw [hleftParam]
      exact ⟨u, ⟨hu.1, hut⟩, huz⟩
    · right
      rw [hrightParam]
      exact ⟨u, ⟨le_of_not_ge hut, hu.2⟩, huz⟩
  exact ⟨t, ht, htc, hpartialInter, hleft_not_right,
    hright_not_left, hsegment_split⟩

private lemma polygonalArc_prefix_segment_transfer
    (Q P : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hPregion : P.carrier =
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          m < i ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} ∪
        segment ℝ Q.vertices[i] c)
    (hPlen : P.vertices.length = i + 2)
    (hPbefore : ∀ n (hn : n < i + 1), P.vertices[n] = Q.vertices[n])
    (hPcut : P.vertices[i + 1] = c)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (htc : (AffineMap.lineMap Q.vertices[i] Q.vertices[i + 1]) t = c)
    (hseg_ne : Q.vertices[i] ≠ Q.vertices[i + 1]) :
    ∀ z a (ha : a + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
      z ∈ P.carrier → z ≠ c →
      ∃ j : ℕ, ∃ hj : j + 1 < P.vertices.length,
        z ∈ openSegment ℝ P.vertices[j] P.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            P.vertices[j + 1] - P.vertices[j] =
              scale • (Q.vertices[a + 1] - Q.vertices[a]) := by
  intro z a ha hza hzP hzc
  rw [hPregion] at hzP
  rcases hzP with ⟨m, hm, hmi, hzm⟩ | hzpartial
  · have ham : a = m :=
      polygonalArc_openSegment_index_unique Q z a m ha hm hza hzm
    subst m
    refine ⟨a, ?_, ?_, 1, one_ne_zero, ?_⟩
    · rw [hPlen]
      omega
    · have hleft : P.vertices[a] = Q.vertices[a] := hPbefore a (by omega)
      have hright : P.vertices[a + 1] = Q.vertices[a + 1] :=
        hPbefore (a + 1) (by omega)
      simpa [hleft, hright] using hza
    · have hleft : P.vertices[a] = Q.vertices[a] := hPbefore a (by omega)
      have hright : P.vertices[a + 1] = Q.vertices[a + 1] :=
        hPbefore (a + 1) (by omega)
      simp [hleft, hright]
  · have hai : a = i := polygonalArc_openSegment_index_unique Q z a i ha hi hza
      ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
        (openSegment_subset_segment ℝ _ _ hc) hzpartial)
    subst a
    refine ⟨i, ?_, ?_, t, ht.1.ne', ?_⟩
    · rw [hPlen]
      omega
    · have hleft : P.vertices[i] = Q.vertices[i] := hPbefore i (by omega)
      have hright : P.vertices[i + 1] = c := hPcut
      apply mem_openSegment_of_ne_left_right
      · intro hz
        have hzleft : Q.vertices[i] = z := hleft.symm.trans hz
        have hzendpoint : Q.vertices[i] ∈
            openSegment ℝ Q.vertices[i] Q.vertices[i + 1] := by
          simpa only [hzleft] using hza
        exact hseg_ne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hzendpoint)
      · simpa [hright] using hzc.symm
      · simpa [hleft, hright] using hzpartial
    · have hleft : P.vertices[i] = Q.vertices[i] := hPbefore i (by omega)
      have hright : P.vertices[i + 1] = c := hPcut
      rw [hleft, hright, ← htc]
      simp [AffineMap.lineMap_apply_module]
      module

private lemma polygonalArc_suffix_segment_transfer
    (Q S : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hSregion : S.carrier =
      segment ℝ c Q.vertices[i + 1] ∪
        {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          i < m ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]})
    (hSlen : S.vertices.length = Q.vertices.length - i)
    (hSzero : S.vertices[0] = c)
    (hSsucc : ∀ n (hn : n + 1 < S.vertices.length),
      S.vertices[n + 1] = Q.vertices[i + 1 + n])
    (hSpos : ∀ n (hnpos : 0 < n) (hn : n < S.vertices.length),
      S.vertices[n] = Q.vertices[i + n])
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (htc : (AffineMap.lineMap Q.vertices[i] Q.vertices[i + 1]) t = c)
    (hseg_ne : Q.vertices[i] ≠ Q.vertices[i + 1]) :
    ∀ z a (ha : a + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
      z ∈ S.carrier → z ≠ c →
      ∃ j : ℕ, ∃ hj : j + 1 < S.vertices.length,
        z ∈ openSegment ℝ S.vertices[j] S.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            S.vertices[j + 1] - S.vertices[j] =
              scale • (Q.vertices[a + 1] - Q.vertices[a]) := by
  intro z a ha hza hzS hzc
  rw [hSregion] at hzS
  rcases hzS with hzpartial | ⟨m, hm, him, hzm⟩
  · have hai : a = i := polygonalArc_openSegment_index_unique Q z a i ha hi hza
      ((convex_segment _ _).segment_subset
        (openSegment_subset_segment ℝ _ _ hc) (right_mem_segment ℝ _ _) hzpartial)
    subst a
    refine ⟨0, ?_, ?_, 1 - t, sub_ne_zero.mpr ht.2.ne', ?_⟩
    · rw [hSlen]
      omega
    · have hS1 : S.vertices[1] = Q.vertices[i + 1] := by
        simpa using hSsucc 0 (by rw [hSlen]; omega)
      apply mem_openSegment_of_ne_left_right
      · simpa only [hSzero] using hzc.symm
      · intro hz
        have hzright : Q.vertices[i + 1] = z := hS1.symm.trans hz
        have hzendpoint : Q.vertices[i + 1] ∈
            openSegment ℝ Q.vertices[i] Q.vertices[i + 1] := by
          simpa only [hzright] using hza
        exact hseg_ne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hzendpoint)
      · simpa [hSzero, hS1] using hzpartial
    · have hS1 : S.vertices[1] = Q.vertices[i + 1] := by
        simpa using hSsucc 0 (by rw [hSlen]; omega)
      rw [hSzero, hS1, ← htc]
      simp [AffineMap.lineMap_apply_module]
      module
  · have ham : a = m :=
      polygonalArc_openSegment_index_unique Q z a m ha hm hza hzm
    subst m
    let j := a - i
    have hjpos : 0 < j := by dsimp [j]; omega
    have hj : j + 1 < S.vertices.length := by rw [hSlen]; omega
    refine ⟨j, hj, ?_, 1, one_ne_zero, ?_⟩
    · have hleft : S.vertices[j] = Q.vertices[a] := by
        have hia : i + j = a := by dsimp [j]; omega
        exact (hSpos j hjpos (by omega)).trans
          (polygonalArc_getElem_eq_of_index_eq Q.vertices (i + j) a
            (by omega) (by omega) hia)
      have hright : S.vertices[j + 1] = Q.vertices[a + 1] := by
        have hia : i + 1 + j = a + 1 := by dsimp [j]; omega
        exact (hSsucc j hj).trans
          (polygonalArc_getElem_eq_of_index_eq Q.vertices (i + 1 + j) (a + 1)
            (by omega) (by omega) hia)
      simpa [hleft, hright] using hza
    · have hleft : S.vertices[j] = Q.vertices[a] := by
        have hia : i + j = a := by dsimp [j]; omega
        exact (hSpos j hjpos (by omega)).trans
          (polygonalArc_getElem_eq_of_index_eq Q.vertices (i + j) a
            (by omega) (by omega) hia)
      have hright : S.vertices[j + 1] = Q.vertices[a + 1] := by
        have hia : i + 1 + j = a + 1 := by dsimp [j]; omega
        exact (hSsucc j hj).trans
          (polygonalArc_getElem_eq_of_index_eq Q.vertices (i + 1 + j) (a + 1)
            (by omega) (by omega) hia)
      simp [hleft, hright]

private lemma polygonalArc_protected_first_vertices
    (Q P : PolygonalArc) (i : ℕ)
    (hi : i + 1 < Q.vertices.length)
    (hPlen : P.vertices.length = i + 2)
    (hPbefore : ∀ n (hn : n < i + 1), P.vertices[n] = Q.vertices[n])
    (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1]) :
    ∀ (_hfirst : 0 + 1 < Q.vertices.length),
      c ∉ segment ℝ Q.vertices[0] Q.vertices[1] →
      ∃ hprefix : 0 + 1 < P.vertices.length,
        P.vertices[0] = Q.vertices[0] ∧ P.vertices[1] = Q.vertices[1] := by
  intro _hfirst hcut
  have hiPos : 0 < i := by
    by_contra hnot
    have hi0 : i = 0 := by omega
    apply hcut
    simpa only [hi0] using openSegment_subset_segment ℝ _ _ hc
  have hPfirst : 0 + 1 < P.vertices.length := by
    rw [hPlen]
    omega
  exact ⟨hPfirst, hPbefore 0 (by omega), hPbefore 1 (by omega)⟩


lemma PolygonalArcInteriorPointCutDataExists
    (Q : PolygonalArc) (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1]) :
    Nonempty (PolygonalArcPointCutData Q c) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have hcarrier_ne : Q.carrier ≠ Set.univ :=
    (PolygonalArcCarrierCompact Q).ne_univ
  obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem Q.carrier).mp hcarrier_ne
  obtain ⟨dummy, _hdsource, _hdtarget, hdcarrier⟩ := PolygonalPathConstant w
  have hcQ : c ∈ Q.carrier := by
    rw [Q.carrier_eq]
    exact ⟨i, hi, openSegment_subset_segment ℝ _ _ hc⟩
  have hvertexQ : ∀ v, v ∈ Q.vertices → v ∈ Q.carrier := by
    intro v hv
    exact PolygonalArcVertexMemCarrier Q hv
  have hDummyDisjoint : Disjoint dummy.carrier Q.carrier := by
    rw [Set.disjoint_left]
    intro z hzDummy hzQ
    rw [hdcarrier] at hzDummy
    have hzw : z = w := by simpa using hzDummy
    exact hw (hzw ▸ hzQ)
  have hQsource_mem : Q.source ∈ Q.carrier := by
    apply hvertexQ Q.source
    cases hverts : Q.vertices with
    | nil => exact False.elim (by simpa [hverts] using Q.length_ge_two)
    | cons x xs =>
        have hx : x = Q.source := by simpa [hverts] using Q.source_eq_head
        simp [hx]
  have hQsingleton :
      Q.carrier ∩ ({Q.source} : Set E) = {Q.source} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · exact fun hz => hz.2
    · intro hz
      subst z
      exact ⟨hQsource_mem, rfl⟩
  obtain ⟨S, hSvertices, hSsource, hStarget, hSsubset,
      _hDummyInsideS, _hSsourceDisjoint⟩ :=
    ArcCrossingOrderedTailArc ({Q.source} : Set E) Q dummy i c hi hc
      (by
        intro hcd
        exact (Set.disjoint_left.mp hDummyDisjoint hcd) hcQ)
      (by
        intro m hm hmi
        exact hDummyDisjoint.mono_right (by
          intro z hz
          rw [Q.carrier_eq]
          exact ⟨m, hm, hz⟩))
      ((hDummyDisjoint.mono_right (by
        intro z hz
        rw [Q.carrier_eq]
        exact ⟨i, hi,
          (convex_segment Q.vertices[i] Q.vertices[i + 1]).segment_subset
            (left_mem_segment ℝ _ _)
            (openSegment_subset_segment ℝ _ _ hc) hz⟩)).symm)
      (by
        intro v hv hzDummy
        exact (Set.disjoint_left.mp hDummyDisjoint hzDummy) (hvertexQ v hv))
      hQsingleton
  let QR := PolygonalArcReverse Q
  let ri := Q.vertices.length - 2 - i
  have hri : ri + 1 < QR.vertices.length := by
    change (Q.vertices.length - 2 - i) + 1 < Q.vertices.reverse.length
    simp only [List.length_reverse]
    omega
  have hQRleft : QR.vertices[ri] = Q.vertices[i + 1] := by
    have hopt : QR.vertices[ri]? = Q.vertices[i + 1]? := by
      change Q.vertices.reverse[Q.vertices.length - 2 - i]? = Q.vertices[i + 1]?
      apply List.getElem?_reverse'
      omega
    rw [List.getElem?_eq_getElem (Nat.lt_trans (Nat.lt_succ_self ri) hri)] at hopt
    rw [List.getElem?_eq_getElem (by omega)] at hopt
    exact Option.some.inj hopt
  have hQRright : QR.vertices[ri + 1] = Q.vertices[i] := by
    have hopt : QR.vertices[ri + 1]? = Q.vertices[i]? := by
      change Q.vertices.reverse[Q.vertices.length - 2 - i + 1]? = Q.vertices[i]?
      apply List.getElem?_reverse'
      omega
    rw [List.getElem?_eq_getElem hri] at hopt
    rw [List.getElem?_eq_getElem (by omega)] at hopt
    exact Option.some.inj hopt
  have hcRev : c ∈ openSegment ℝ QR.vertices[ri] QR.vertices[ri + 1] := by
    simpa [hQRleft, hQRright, openSegment_symm ℝ] using hc
  have hDummyDisjointRev : Disjoint dummy.carrier QR.carrier := by
    simpa [QR, PolygonalArcReverse] using hDummyDisjoint
  have hQRsource_mem : QR.source ∈ QR.carrier := by
    dsimp [QR, PolygonalArcReverse]
    have htarget_mem : Q.target ∈ Q.carrier := by
      apply hvertexQ Q.target
      have hlast := Q.target_eq_last
      rw [List.getLast?_eq_getLast_of_ne_nil (by
        exact List.ne_nil_of_length_pos (by omega))] at hlast
      have heq : Q.vertices.getLast (by
          exact List.ne_nil_of_length_pos (by omega)) = Q.target :=
        Option.some.inj hlast
      rw [← heq]
      exact List.getLast_mem (by
        exact List.ne_nil_of_length_pos (by omega))
    exact htarget_mem
  have hQRsingleton :
      QR.carrier ∩ ({QR.source} : Set E) = {QR.source} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · exact fun hz => hz.2
    · intro hz
      subst z
      exact ⟨hQRsource_mem, rfl⟩
  obtain ⟨T, hTvertices, hTsource, hTtarget, hTsubset,
      _hDummyInsideT, _hTsourceDisjoint⟩ :=
    ArcCrossingOrderedTailArc ({QR.source} : Set E) QR dummy ri c hri hcRev
      (by
        intro hcd
        have hcQR : c ∈ QR.carrier := by
          dsimp [QR, PolygonalArcReverse]
          exact hcQ
        exact (Set.disjoint_left.mp hDummyDisjointRev hcd) hcQR)
      (by
        intro m hm hmri
        exact hDummyDisjointRev.mono_right (by
          intro z hz
          rw [QR.carrier_eq]
          exact ⟨m, hm, hz⟩))
      ((hDummyDisjointRev.mono_right (by
        intro z hz
        rw [QR.carrier_eq]
        exact ⟨ri, hri,
          (convex_segment QR.vertices[ri] QR.vertices[ri + 1]).segment_subset
            (left_mem_segment ℝ _ _)
            (openSegment_subset_segment ℝ _ _ hcRev) hz⟩)).symm)
      (by
        intro v hv hzDummy
        exact (Set.disjoint_left.mp hDummyDisjointRev hzDummy)
          (PolygonalArcVertexMemCarrier QR hv))
      hQRsingleton
  let P := PolygonalArcReverse T
  have hPsource : P.source = Q.source := by
    dsimp [P, PolygonalArcReverse]
    exact hTtarget.trans (by rfl)
  have hPtarget : P.target = c := by
    dsimp [P, PolygonalArcReverse]
    exact hTsource
  have hPsubset : P.carrier ⊆ Q.carrier := by
    intro z hz
    exact hTsubset hz
  have hPvertices : P.vertices = Q.vertices.take (i + 1) ++ [c] := by
    dsimp [P, PolygonalArcReverse]
    rw [hTvertices, List.reverse_cons, List.reverse_drop]
    have hindex : QR.vertices.length - (ri + 1) = i + 1 := by
      dsimp [QR, PolygonalArcReverse, ri]
      simp
      omega
    have hrev : QR.vertices.reverse = Q.vertices := by
      dsimp [QR, PolygonalArcReverse]
      simp
    rw [hindex, hrev]
  have hSlen : S.vertices.length = Q.vertices.length - i := by
    rw [hSvertices]
    simp [List.length_drop]
    omega
  have hPlen : P.vertices.length = i + 2 := by
    rw [hPvertices]
    simp [List.length_take]
    omega
  have hSzero : S.vertices[0] = c := by
    have hhead := S.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    exact (Option.some.inj hhead).trans hSsource
  have hSsucc : ∀ n (hn : n + 1 < S.vertices.length),
      S.vertices[n + 1] = Q.vertices[i + 1 + n]'(by
        rw [hSlen] at hn
        omega) := by
    intro n hn
    have hdrop : n < (Q.vertices.drop (i + 1)).length := by
      simp [List.length_drop]
      rw [hSlen] at hn
      omega
    have hopt := congrArg (fun xs => xs[n + 1]?) hSvertices
    change S.vertices[n + 1]? =
      (c :: Q.vertices.drop (i + 1))[n + 1]? at hopt
    rw [List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem (by simpa using hdrop)] at hopt
    have hval := Option.some.inj hopt
    simpa using hval
  have hSpos : ∀ n (hnpos : 0 < n) (hn : n < S.vertices.length),
      S.vertices[n] = Q.vertices[i + n]'(by
        rw [hSlen] at hn
        omega) := by
    intro n hnpos hn
    cases n with
    | zero => omega
    | succ q =>
        simpa [Nat.add_assoc, Nat.add_comm 1 q] using
          hSsucc q (by simpa using hn)
  have hPbefore : ∀ n (hn : n < i + 1), P.vertices[n] = Q.vertices[n] := by
    intro n hn
    have hopt := congrArg (fun xs => xs[n]?) hPvertices
    change P.vertices[n]? = (Q.vertices.take (i + 1) ++ [c])[n]? at hopt
    have hPbound : n < P.vertices.length := by
      rw [hPlen]
      omega
    have hRbound : n < (Q.vertices.take (i + 1) ++ [c]).length := by
      simp
      omega
    rw [List.getElem?_eq_getElem hPbound,
      List.getElem?_eq_getElem hRbound] at hopt
    have hval := Option.some.inj hopt
    have htake : n < (Q.vertices.take (i + 1)).length := by
      simp [List.length_take]
      omega
    calc
      P.vertices[n] = (Q.vertices.take (i + 1) ++ [c])[n] := hval
      _ = (Q.vertices.take (i + 1))[n] :=
        List.getElem_append_left htake
      _ = Q.vertices[n] := List.getElem_take
  have hPcut : P.vertices[i + 1] = c := by
    have hopt := congrArg (fun xs => xs[i + 1]?) hPvertices
    change P.vertices[i + 1]? = (Q.vertices.take (i + 1) ++ [c])[i + 1]? at hopt
    have hPbound : i + 1 < P.vertices.length := by
      rw [hPlen]
      omega
    have hRbound : i + 1 < (Q.vertices.take (i + 1) ++ [c]).length := by
      simp [List.length_take]
      omega
    rw [List.getElem?_eq_getElem hPbound,
      List.getElem?_eq_getElem hRbound] at hopt
    have hval := Option.some.inj hopt
    calc
      P.vertices[i + 1] = (Q.vertices.take (i + 1) ++ [c])[i + 1] := hval
      _ = c := by
        simpa using List.getElem_append_right
          (as := Q.vertices.take (i + 1)) (bs := [c])
          (i := i + 1)
  have hSregion : S.carrier =
      segment ℝ c Q.vertices[i + 1] ∪
        {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          i < m ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} :=
    polygonalArc_suffix_carrier_region Q S i hi c hSlen hSzero hSsucc hSpos
  have hPregion : P.carrier =
      {z | ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          m < i ∧ z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1]} ∪
        segment ℝ Q.vertices[i] c :=
    polygonalArc_prefix_carrier_region Q P i hi c hPlen hPbefore hPcut
  have hcOpen := hc
  have hseg_ne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
    intro heq
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
    omega
  obtain ⟨t, ht, htc, hpartialInter, hleft_not_right,
      hright_not_left, hsegment_split⟩ :=
    polygonalArc_segment_cut_geometry
      Q.vertices[i] Q.vertices[i + 1] c hcOpen hseg_ne
  have hdecomp : Q.carrier = P.carrier ∪ S.carrier :=
    polygonalArc_carrier_decomposition_of_cut_regions Q P S i hi c
      hPsubset hSsubset hPregion hSregion hsegment_split
  have hinter : P.carrier ∩ S.carrier = {c} :=
    polygonalArc_cut_regions_intersection Q P S i hi c hcOpen hPregion
      hSregion hpartialInter hleft_not_right hright_not_left
  have hprefixTransfer := polygonalArc_prefix_segment_transfer
    Q P i hi c hcOpen hPregion hPlen hPbefore hPcut t ht htc hseg_ne
  have hsuffixTransfer := polygonalArc_suffix_segment_transfer
    Q S i hi c hcOpen hSregion hSlen hSzero hSsucc hSpos t ht htc hseg_ne
  have hprotected := polygonalArc_protected_first_vertices
    Q P i hi hPlen hPbefore c hcOpen
  refine ⟨{
    prefixArc := P
    suffixArc := S
    cutIndex := i
    cutIndex_valid := hi
    cut_mem_segment := openSegment_subset_segment ℝ _ _ hcOpen
    prefix_vertices_exact := hPvertices
    suffixDropIndex := i + 1
    suffix_vertices_exact := hSvertices
    suffix_drop_index_spec := Or.inl ⟨rfl, by
      intro hEq
      exact hseg_ne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hEq ▸ hcOpen))⟩
    prefix_source := hPsource
    prefix_target := hPtarget
    suffix_source := hSsource
    suffix_target := hStarget
    prefix_carrier_subset := hPsubset
    suffix_carrier_subset := hSsubset
    carrier_decomposition := hdecomp
    carrier_intersection := hinter
    prefix_carrier_region := hPregion
    suffix_carrier_region := hSregion
    prefix_segment_transfer := hprefixTransfer
    suffix_segment_transfer := hsuffixTransfer
    protected_first_vertices := hprotected }⟩
