/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- A quantitative edge lower bound from a small independence number. -/

import ErdosProblems.Erdos717.SparseParameters

open Function Set
open SimpleGraph

namespace Erdos717

private theorem insert_independent_of_zero_pattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset V) (v : V) (hI : G.IsIndepSet I) (hvI : v ∉ I)
    (hv : (G.neighborFinset v ∩ I).card = 0) :
    G.IsIndepSet (↑(insert v I) : Set V) := by
  rw [G.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hxy rfl).elim
  · have hnot : ¬G.Adj x y := by
      intro hadj
      have : y ∈ G.neighborFinset x ∩ I := by
        simp only [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj, hy⟩
      have hpos : 0 < (G.neighborFinset x ∩ I).card :=
        Finset.card_pos.mpr ⟨y, this⟩
      omega
    exact hnot
  · have hnot : ¬G.Adj y x := by
      intro hadj
      have : x ∈ G.neighborFinset y ∩ I := by
        simp only [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj, hx⟩
      have hpos : 0 < (G.neighborFinset y ∩ I).card :=
        Finset.card_pos.mpr ⟨x, this⟩
      omega
    exact fun h => hnot h.symm
  · exact (G.isIndepSet_iff.mp hI) hx hy hxy

/-- A maximum independent set dominates every other vertex.  Counting one
incident edge per dominated vertex gives this slack, division-free form. -/
theorem card_le_indepBound_add_twice_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℕ)
    (hind : G.indepNum ≤ a) :
    Fintype.card V ≤ a + 2 * G.edgeFinset.card := by
  classical
  obtain ⟨I, _hIuniv, hIind, hImax⟩ :=
    exists_maximum_independent_subset G Finset.univ
  let X := highPatternFinset G Finset.univ I 0
  have hlowEmpty : lowPatternFinset G Finset.univ I 0 = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨v, hv⟩
    have hvI : v ∉ I := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    have hvzero : (G.neighborFinset v ∩ I).card = 0 :=
      Nat.eq_zero_of_le_zero
        (lowPattern_degree G Finset.univ I 0 v hv)
    have hinsert := insert_independent_of_zero_pattern G I v hIind hvI hvzero
    have hmax := hImax (insert v I) (by simp) hinsert
    simp [hvI] at hmax
  have hpart := low_high_pattern_partition G Finset.univ I (by simp) 0
  rw [hlowEmpty] at hpart
  have hXpart : X.card + I.card = Fintype.card V := by
    simpa [X] using hpart
  have hlower : X.card ≤ ∑ x ∈ X, (G.neighborFinset x ∩ I).card := by
    calc
      X.card = ∑ _x ∈ X, 1 := by simp
      _ ≤ ∑ x ∈ X, (G.neighborFinset x ∩ I).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hxpos : 0 < (G.neighborFinset x ∩ I).card := by
          have := (Finset.mem_filter.mp hx).2
          omega
        omega
  have hswap : ∑ x ∈ X, (G.neighborFinset x ∩ I).card =
      ∑ i ∈ I, (G.neighborFinset i ∩ X).card := by
    have hleft (x : V) : (G.neighborFinset x ∩ I).card =
        ∑ i ∈ I, if G.Adj x i then 1 else 0 := by
      rw [show G.neighborFinset x ∩ I = I.filter fun i => G.Adj x i by
        ext i
        simp [G.mem_neighborFinset, and_comm]]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hright (i : V) : (G.neighborFinset i ∩ X).card =
        ∑ x ∈ X, if G.Adj x i then 1 else 0 := by
      rw [show G.neighborFinset i ∩ X = X.filter fun x => G.Adj x i by
        ext x
        simp [G.mem_neighborFinset, G.adj_comm, and_comm]]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc
      ∑ x ∈ X, (G.neighborFinset x ∩ I).card =
          ∑ x ∈ X, ∑ i ∈ I, if G.Adj x i then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            exact hleft x
      _ = ∑ i ∈ I, ∑ x ∈ X, if G.Adj x i then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i ∈ I, (G.neighborFinset i ∩ X).card := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hright i).symm
  have hupper : ∑ i ∈ I, (G.neighborFinset i ∩ X).card ≤
      2 * G.edgeFinset.card := by
    calc
      ∑ i ∈ I, (G.neighborFinset i ∩ X).card ≤ ∑ i ∈ I, G.degree i := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.card_le_card Finset.inter_subset_left
      _ ≤ ∑ i : V, G.degree i := Finset.sum_le_sum_of_subset (by simp)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hIcard : I.card ≤ a := hIind.card_le_indepNum.trans hind
  rw [hswap] at hlower
  omega

/-- If every independent set has at most `a` vertices and `a ≤ n/16`, then
`e(G) ≥ n²/(32a)`.  This deliberately slack form follows from the same
low-degree/maximal-independent-set count used in the sparse reduction. -/
theorem card_sq_le_thirtytwo_mul_edges_mul_indepBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℕ)
    (hind : G.indepNum ≤ a) (ha : 16 * a ≤ Fintype.card V) :
    Fintype.card V * Fintype.card V ≤ 32 * G.edgeFinset.card * a := by
  classical
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let D := degreeCutParameter m n
  let P := lowDegreeFinset G D
  by_cases hn0 : n = 0
  · dsimp only [n, m] at hn0 ⊢
    simp [hn0]
  obtain ⟨I, hIP, hIind, hImax⟩ := exists_maximum_independent_subset G P
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hdegreeCut : 4 * m ≤ n * (D + 1) := by
    simpa [D] using degreeCutParameter_spec m n hn
  have hP : n / 2 ≤ P.card := by
    simpa [P, D, m, n] using half_card_le_lowDegreeFinset G D hdegreeCut
  have haPos : 1 ≤ a := by
    let v : V := Classical.choice (Fintype.card_pos_iff.mp (by simpa [n] using hn))
    have hsingle : G.IsIndepSet ({v} : Finset V) := by simp
    have := hsingle.card_le_indepNum.trans hind
    simpa using this
  have hIcard : I.card ≤ a := hIind.card_le_indepNum.trans hind
  have hlowEmpty : lowPatternFinset G P I 0 = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨v, hv⟩
    have hvP : v ∈ P := lowPattern_subset G P I 0 hv
    have hvI : v ∉ I := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    have hvzero : (G.neighborFinset v ∩ I).card = 0 :=
      Nat.eq_zero_of_le_zero (lowPattern_degree G P I 0 v hv)
    have hinsert := insert_independent_of_zero_pattern G I v hIind hvI hvzero
    have hsub : insert v I ⊆ P := Finset.insert_subset hvP hIP
    have hmax := hImax (insert v I) hsub hinsert
    simp [hvI] at hmax
  have hhigh := highPattern_card_mul_le G P I D 0 hIP
    (degree_le_of_mem_lowDegreeFinset G D)
  have hpart := low_high_pattern_partition G P I hIP 0
  rw [hlowEmpty] at hpart
  have hPD : P.card ≤ (D + 1) * I.card := by
    simp only [Finset.card_empty, zero_add, zero_add, one_mul] at hpart hhigh
    nlinarith
  have hnD : n * D ≤ 4 * m + n := by
    dsimp only [D, degreeCutParameter]
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc
      n * ((4 * m + n - 1) / n) ≤ 4 * m + n - 1 := Nat.mul_div_le _ _
      _ ≤ 4 * m + n := Nat.sub_le _ _
  have hIpos : 0 < I.card := by
    by_contra hzero
    have hIzero : I.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hPzero : P.card = 0 := by nlinarith [hPD]
    omega
  have hhalf : n ≤ 3 * P.card := by omega
  have hmain : n * n ≤ 12 * m * a + 6 * n * a := by
    calc
      n * n ≤ 3 * n * P.card := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left n hhalf
      _ ≤ 3 * n * ((D + 1) * I.card) :=
        Nat.mul_le_mul_left (3 * n) hPD
      _ ≤ 3 * n * ((D + 1) * a) := by
        exact Nat.mul_le_mul_left (3 * n)
          (Nat.mul_le_mul_left (D + 1) hIcard)
      _ ≤ 12 * m * a + 6 * n * a := by nlinarith
  dsimp only [n, m] at ha hmain ⊢
  nlinarith

end Erdos717
