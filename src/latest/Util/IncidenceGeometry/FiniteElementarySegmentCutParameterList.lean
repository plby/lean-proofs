import Util.IncidenceGeometry.Basic
import Mathlib.Data.Finset.Sort

open Classical
noncomputable section

lemma FiniteElementarySegmentCutParameterList
    (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B)
    (T : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ, t ∈ L ↔
            t = 0 ∨ t = 1 ∨
              (0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap A B t ∈ T)) ∧
            (0 : ℝ) ∈ L ∧
              (1 : ℝ) ∈ L ∧
                (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                  (∀ n (hn : n + 1 < L.length), L[n] < L[n + 1]) ∧
                    (∀ n (hn : n + 1 < L.length) t,
                      0 ≤ t → t ≤ 1 →
                        AffineMap.lineMap A B t ∈ T →
                          ¬ (L[n] < t ∧ t < L[n + 1])) := by
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => AffineMap.lineMap A B t
  let pulled : Finset ℝ := T.preimage f (AffineMap.lineMap_injective ℝ hAB).injOn
  let cuts : Finset ℝ := insert 0 (insert 1 (pulled.filter fun t => 0 ≤ t ∧ t ≤ 1))
  let L : List ℝ := cuts.sort (· ≤ ·)
  have hmem : ∀ t : ℝ, t ∈ L ↔
      t = 0 ∨ t = 1 ∨
        (0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap A B t ∈ T) := by
    intro t
    constructor
    · intro ht
      have htcuts : t ∈ cuts := by
        simpa [L] using (Finset.mem_sort (s := cuts) (r := (· ≤ ·))).1 ht
      simp only [cuts, Finset.mem_insert, Finset.mem_filter] at htcuts
      rcases htcuts with h0 | h1 | hpull
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨hpull.2.1, hpull.2.2,
          by simpa [pulled, f] using (Finset.mem_preimage.mp hpull.1)⟩)
    · intro ht
      have htcuts : t ∈ cuts := by
        simp only [cuts, Finset.mem_insert, Finset.mem_filter]
        rcases ht with h0 | h1 | hmid
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨by
              exact Finset.mem_preimage.mpr (by simpa [f] using hmid.2.2),
            hmid.1, hmid.2.1⟩)
      simpa [L] using (Finset.mem_sort (s := cuts) (r := (· ≤ ·))).2 htcuts
  have hbounds : ∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    rcases (hmem t).1 ht with h0 | h1 | hmid
    · subst t
      norm_num
    · subst t
      norm_num
    · exact ⟨hmid.1, hmid.2.1⟩
  have hno_between :
      ∀ n (hn : n + 1 < L.length) t,
        t ∈ L → ¬ (L[n] < t ∧ t < L[n + 1]) := by
    intro n hn t ht hbetween
    rcases List.mem_iff_get.mp ht with ⟨k, hk⟩
    subst t
    have hmono : StrictMono L.get := Finset.sortedLT_sort cuts
    by_cases hkn : k ≤ n
    · have hle : L.get k ≤ L.get ⟨n, Nat.lt_of_succ_lt hn⟩ := by
        by_cases heq : k = ⟨n, Nat.lt_of_succ_lt hn⟩
        · simp [heq]
        · have hlt : k < ⟨n, Nat.lt_of_succ_lt hn⟩ := lt_of_le_of_ne hkn heq
          exact (hmono hlt).le
      exact not_lt_of_ge hle hbetween.1
    · have hle_k : ⟨n + 1, hn⟩ ≤ k :=
        Nat.succ_le_of_lt (lt_of_not_ge hkn)
      have hle : L.get ⟨n + 1, hn⟩ ≤ L.get k := by
        by_cases heq : ⟨n + 1, hn⟩ = k
        · simp [heq]
        · have hlt : ⟨n + 1, hn⟩ < k := lt_of_le_of_ne hle_k heq
          exact (hmono hlt).le
      exact not_lt_of_ge hle hbetween.2
  refine ⟨L, Finset.sort_nodup cuts (· ≤ ·), Finset.sortedLT_sort cuts,
    hmem, ?_, ?_, hbounds, ?_, ?_⟩
  · exact (hmem 0).2 (Or.inl rfl)
  · exact (hmem 1).2 (Or.inr (Or.inl rfl))
  · intro n hn
    have hmono : StrictMono L.get := Finset.sortedLT_sort cuts
    exact hmono (by simp [Fin.lt_def])
  · intro n hn t ht0 ht1 htT hbetween
    exact hno_between n hn t ((hmem t).2 (Or.inr (Or.inr ⟨ht0, ht1, htT⟩))) hbetween
