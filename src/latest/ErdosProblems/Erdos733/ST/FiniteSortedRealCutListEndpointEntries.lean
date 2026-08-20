import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: FiniteSortedRealCutListEndpointEntries]
lemma FiniteSortedRealCutListEndpointEntries
    (L : List ℝ)
    (hSorted : L.SortedLT)
    (hzero : (0 : ℝ) ∈ L) (hone : (1 : ℝ) ∈ L)
    (hbounds : ∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) :
    2 ≤ L.length ∧
      (∀ h : 0 < L.length, L[0]'h = 0) ∧
        (∀ h : L.length - 1 < L.length, L[L.length - 1]'h = 1) := by
-- BODY
  have hlen_two : 2 ≤ L.length := by
    rcases List.mem_iff_get.mp hzero with ⟨z, hz⟩
    rcases List.mem_iff_get.mp hone with ⟨o, ho⟩
    have hne : z.1 ≠ o.1 := by
      intro hval
      have hzo : z = o := Fin.ext hval
      have h01 : (0 : ℝ) = 1 := by
        rw [← hz, ← ho, hzo]
      norm_num at h01
    omega
  refine ⟨hlen_two, ?_, ?_⟩
  · intro hpos
    rcases List.mem_iff_get.mp hzero with ⟨k, hk⟩
    by_cases hk0 : k.1 = 0
    · have hkfin : k = ⟨0, hpos⟩ := Fin.ext hk0
      simpa [hkfin] using hk
    · have h0lt : (⟨0, hpos⟩ : Fin L.length) < k := by
        exact Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hk0)
      have hlt : L[0] < L.get k := hSorted h0lt
      have hge : (0 : ℝ) ≤ L[0] :=
        (hbounds L[0] (List.get_mem L ⟨0, hpos⟩)).1
      nlinarith [hge, hlt, hk]
  · intro hlast
    rcases List.mem_iff_get.mp hone with ⟨k, hk⟩
    let last : Fin L.length := ⟨L.length - 1, hlast⟩
    by_cases hklast : k = last
    · simpa [last, hklast] using hk
    · have hklt : k < last := by
        apply Fin.mk_lt_mk.mpr
        have hle : k.1 ≤ L.length - 1 := by
          omega
        exact lt_of_le_of_ne hle (by
          intro hEq
          apply hklast
          exact Fin.ext hEq)
      have hlt : L.get k < L.get last := hSorted hklt
      have hle_last : L.get last ≤ 1 := (hbounds (L.get last) (List.get_mem L last)).2
      nlinarith [hle_last, hlt, hk]
