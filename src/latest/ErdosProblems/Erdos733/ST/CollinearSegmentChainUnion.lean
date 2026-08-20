import ErdosProblems.Erdos733.ST.RealSegmentChainUnion


open Classical
noncomputable section

open Set

-- [TABLET NODE: CollinearSegmentChainUnion]
lemma CollinearSegmentChainUnion
    (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B)
    (L : List (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hpos : 0 < L.length)
    (hcontained : ∀ n (hn : n < L.length),
      segment ℝ (L[n]).1 (L[n]).2 ⊆ segment ℝ A B)
    (hlink : ∀ n (hn : n + 1 < L.length),
      (L[n]).2 = (L[n + 1]).1)
    (hne : ∀ n (hn : n < L.length), (L[n]).1 ≠ (L[n]).2)
    (hinter : ∀ n (hn : n + 1 < L.length),
      segment ℝ (L[n]).1 (L[n]).2 ∩
          segment ℝ (L[n + 1]).1 (L[n + 1]).2 =
        ({(L[n]).2} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (⋃ k : Fin L.length, segment ℝ (L[k.1]).1 (L[k.1]).2) =
      segment ℝ (L[0]).1
        (L[L.length - 1]'(Nat.sub_one_lt_of_lt hpos)).2 := by
-- BODY
  let coordOf (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ segment ℝ A B) : ℝ :=
    Classical.choose (by
      rw [segment_eq_image_lineMap] at hx
      rcases hx with ⟨t, ht, htx⟩
      exact ⟨t, htx⟩)
  have coord_spec :
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ segment ℝ A B),
        AffineMap.lineMap A B (coordOf x hx) = x := by
    intro x hx
    exact Classical.choose_spec (by
      rw [segment_eq_image_lineMap] at hx
      rcases hx with ⟨t, ht, htx⟩
      exact ⟨t, htx⟩)
  let srcMem : (n : ℕ) → (hn : n < L.length) → (L[n]).1 ∈ segment ℝ A B :=
    fun n hn => hcontained n hn (left_mem_segment ℝ (L[n]).1 (L[n]).2)
  let tgtMem : (n : ℕ) → (hn : n < L.length) → (L[n]).2 ∈ segment ℝ A B :=
    fun n hn => hcontained n hn (right_mem_segment ℝ (L[n]).1 (L[n]).2)
  let C : List (ℝ × ℝ) :=
    List.ofFn (fun k : Fin L.length =>
      (coordOf (L[k.1]).1 (srcMem k.1 k.2),
        coordOf (L[k.1]).2 (tgtMem k.1 k.2)))
  have hClen : C.length = L.length := by
    simp [C]
  have hCpos : 0 < C.length := by
    simpa [hClen] using hpos
  have hCget :
      ∀ n (hnL : n < L.length) (hnC : n < C.length),
        C[n] =
          (coordOf (L[n]).1 (srcMem n hnL),
            coordOf (L[n]).2 (tgtMem n hnL)) := by
    intro n hnL hnC
    simp [C]
  have hCsrc :
      ∀ n (hnL : n < L.length) (hnC : n < C.length),
        AffineMap.lineMap A B (C[n].1) = (L[n]).1 := by
    intro n hnL hnC
    rw [hCget n hnL hnC]
    exact coord_spec (L[n]).1 (srcMem n hnL)
  have hCtgt :
      ∀ n (hnL : n < L.length) (hnC : n < C.length),
        AffineMap.lineMap A B (C[n].2) = (L[n]).2 := by
    intro n hnL hnC
    rw [hCget n hnL hnC]
    exact coord_spec (L[n]).2 (tgtMem n hnL)
  have hClink : ∀ n (hn : n + 1 < C.length),
      (C[n]).2 = (C[n + 1]).1 := by
    intro n hn
    have hnL : n < L.length := by omega
    have hnsL : n + 1 < L.length := by omega
    apply AffineMap.lineMap_injective ℝ hAB
    rw [hCtgt n hnL (by omega), hCsrc (n + 1) hnsL (by omega)]
    exact hlink n hnsL
  have hCne : ∀ n (hn : n < C.length), (C[n]).1 ≠ (C[n]).2 := by
    intro n hn h
    have hnL : n < L.length := by omega
    have heq : (L[n]).1 = (L[n]).2 := by
      have hmap := congrArg (AffineMap.lineMap A B) h
      simpa [hCsrc n hnL hn, hCtgt n hnL hn] using hmap
    exact hne n hnL heq
  have hCinter : ∀ n (hn : n + 1 < C.length),
      segment ℝ (C[n]).1 (C[n]).2 ∩
          segment ℝ (C[n + 1]).1 (C[n + 1]).2 =
        ({(C[n]).2} : Set ℝ) := by
    intro n hn
    have hnL : n < L.length := by omega
    have hnsL : n + 1 < L.length := by omega
    apply Set.ext
    intro t
    constructor
    · intro ht
      have hmap_mem :
          AffineMap.lineMap A B t ∈
            segment ℝ (L[n]).1 (L[n]).2 ∩
              segment ℝ (L[n + 1]).1 (L[n + 1]).2 := by
        constructor
        · rw [← hCsrc n hnL (by omega), ← hCtgt n hnL (by omega)]
          simpa using
            (show AffineMap.lineMap A B t ∈
              segment ℝ (AffineMap.lineMap A B (C[n]).1)
                (AffineMap.lineMap A B (C[n]).2) from
              by
                rw [← image_segment ℝ (AffineMap.lineMap A B)
                  (C[n]).1 (C[n]).2]
                exact ⟨t, ht.1, rfl⟩)
        · rw [← hCsrc (n + 1) hnsL (by omega),
            ← hCtgt (n + 1) hnsL (by omega)]
          simpa using
            (show AffineMap.lineMap A B t ∈
              segment ℝ (AffineMap.lineMap A B (C[n + 1]).1)
                (AffineMap.lineMap A B (C[n + 1]).2) from
              by
                rw [← image_segment ℝ (AffineMap.lineMap A B)
                  (C[n + 1]).1 (C[n + 1]).2]
                exact ⟨t, ht.2, rfl⟩)
      rw [hinter n hnsL] at hmap_mem
      have hmap_eq : AffineMap.lineMap A B t = (L[n]).2 := by
        simpa using hmap_mem
      have ht_eq : t = (C[n]).2 := by
        apply AffineMap.lineMap_injective ℝ hAB
        rw [hmap_eq, hCtgt n hnL (by omega)]
      simp [ht_eq]
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      constructor
      · exact right_mem_segment ℝ (C[n]).1 (C[n]).2
      · have hlnk := hClink n hn
        simpa [hlnk] using left_mem_segment ℝ (C[n + 1]).1 (C[n + 1]).2
  have hreal :=
    RealSegmentChainUnion C hCpos hClink hCne hCinter
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
    have hkC : k.1 < C.length := by omega
    rw [← hCsrc k.1 k.2 hkC, ← hCtgt k.1 k.2 hkC] at hxk
    rw [← image_segment ℝ (AffineMap.lineMap A B) (C[k.1]).1 (C[k.1]).2] at hxk
    rcases hxk with ⟨t, ht, rfl⟩
    have ht_union : t ∈ ⋃ k : Fin C.length, segment ℝ (C[k.1]).1 (C[k.1]).2 :=
      Set.mem_iUnion.2 ⟨⟨k.1, hkC⟩, by simpa using ht⟩
    rw [hreal] at ht_union
    have hfirstC : AffineMap.lineMap A B (C[0].1) = (L[0]).1 :=
      hCsrc 0 hpos (by omega)
    have hlastC :
        AffineMap.lineMap A B
            (C[C.length - 1]'(Nat.sub_one_lt_of_lt hCpos)).2 =
          (L[L.length - 1]'(Nat.sub_one_lt_of_lt hpos)).2 := by
      have hidx : C.length - 1 = L.length - 1 := by omega
      simpa [hidx] using
        hCtgt (C.length - 1) (by omega) (Nat.sub_one_lt_of_lt hCpos)
    rw [← hfirstC, ← hlastC]
    rw [← image_segment ℝ (AffineMap.lineMap A B)
      (C[0].1) (C[C.length - 1]'(Nat.sub_one_lt_of_lt hCpos)).2]
    exact ⟨t, ht_union, rfl⟩
  · intro hx
    have hfirstC : AffineMap.lineMap A B (C[0].1) = (L[0]).1 :=
      hCsrc 0 hpos (by omega)
    have hlastC :
        AffineMap.lineMap A B
            (C[C.length - 1]'(Nat.sub_one_lt_of_lt hCpos)).2 =
          (L[L.length - 1]'(Nat.sub_one_lt_of_lt hpos)).2 := by
      have hidx : C.length - 1 = L.length - 1 := by omega
      simpa [hidx] using
        hCtgt (C.length - 1) (by omega) (Nat.sub_one_lt_of_lt hCpos)
    rw [← hfirstC, ← hlastC] at hx
    rw [← image_segment ℝ (AffineMap.lineMap A B)
      (C[0].1) (C[C.length - 1]'(Nat.sub_one_lt_of_lt hCpos)).2] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rw [← hreal] at ht
    rcases Set.mem_iUnion.mp ht with ⟨k, htk⟩
    have hkL : k.1 < L.length := by omega
    have hmap_mem :
        AffineMap.lineMap A B t ∈ segment ℝ (L[k.1]).1 (L[k.1]).2 := by
      rw [← hCsrc k.1 hkL k.2, ← hCtgt k.1 hkL k.2]
      rw [← image_segment ℝ (AffineMap.lineMap A B) (C[k.1]).1 (C[k.1]).2]
      exact ⟨t, htk, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨k.1, hkL⟩, hmap_mem⟩
