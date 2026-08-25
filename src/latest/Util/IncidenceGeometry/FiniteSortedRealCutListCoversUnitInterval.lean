import Util.IncidenceGeometry.FiniteSortedRealCutListEndpointEntries
import Mathlib.Tactic

open Classical
noncomputable section

lemma FiniteSortedRealCutListCoversUnitInterval
    (L : List ℝ)
    (hSorted : L.SortedLT)
    (hzero : (0 : ℝ) ∈ L) (hone : (1 : ℝ) ∈ L)
    (hbounds : ∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k, ∃ hk : k + 1 < L.length,
      t ∈ segment ℝ (L[k]'(Nat.lt_of_succ_lt hk)) (L[k + 1]'hk) := by
  classical
  rcases FiniteSortedRealCutListEndpointEntries L hSorted hzero hone hbounds with
    ⟨hlen_two, hfirst, hlast⟩
  have hpos : 0 < L.length := by omega
  have hlast_lt : L.length - 1 < L.length := Nat.sub_one_lt_of_lt hpos
  let P : ℕ → Prop := fun n => ∃ hn : n < L.length, t ≤ L[n]'hn
  have hP : ∃ n, P n := by
    refine ⟨L.length - 1, hlast_lt, ?_⟩
    simpa [hlast hlast_lt] using ht.2
  let m : ℕ := Nat.find hP
  have hmP : P m := Nat.find_spec hP
  rcases hmP with ⟨hm_len, htm⟩
  by_cases hm0 : m = 0
  · have hm_len0 : 0 < L.length := by
      simpa [m, hm0] using hm_len
    have h01 : 0 + 1 < L.length := by omega
    refine ⟨0, h01, ?_⟩
    have hlt01 :
        L[0]'(Nat.lt_of_succ_lt h01) < L[0 + 1]'h01 := by
      exact hSorted (Fin.mk_lt_mk.mpr (by omega))
    rw [segment_eq_Icc hlt01.le]
    constructor
    · simpa [hfirst (Nat.lt_of_succ_lt h01)] using ht.1
    · have ht0 : t ≤ (0 : ℝ) := by
        simpa [m, hm0, hfirst hm_len0] using htm
      have h0le1 : (0 : ℝ) ≤ L[0 + 1]'h01 := by
        have h0eq : L[0]'(Nat.lt_of_succ_lt h01) = (0 : ℝ) :=
          hfirst (Nat.lt_of_succ_lt h01)
        nlinarith
      exact le_trans ht0 h0le1
  · let k := m - 1
    have hkltm : k < m := by
      dsimp [k]
      omega
    have hkm : k + 1 = m := by
      dsimp [k]
      omega
    have hk_succ : k + 1 < L.length := by
      omega
    refine ⟨k, hk_succ, ?_⟩
    have hnotPk : ¬ P k := Nat.find_min hP hkltm
    have hLk_le_t : L[k]'(Nat.lt_of_succ_lt hk_succ) ≤ t := by
      by_contra hnot
      exact hnotPk ⟨Nat.lt_of_succ_lt hk_succ, le_of_not_ge hnot⟩
    have ht_le_next : t ≤ L[k + 1]'hk_succ := by
      simpa [hkm] using htm
    have hlt_next :
        L[k]'(Nat.lt_of_succ_lt hk_succ) < L[k + 1]'hk_succ := by
      exact hSorted (Fin.mk_lt_mk.mpr (by omega))
    rw [segment_eq_Icc hlt_next.le]
    exact ⟨hLk_le_t, ht_le_next⟩
