/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic

/-!
# Erdős--Szekeres monochromatic pairs

This file proves the exact, floor-free form of the weighted
Erdős--Szekeres induction used in Sudakov's proof.  The estimate is written
with multiplication in `ℕ`; in particular, no choice of a real-valued
rounding convention is needed.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

private theorem choose_pascal (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Nat.choose (k + l) k =
      Nat.choose ((k - 1) + l) (k - 1) +
        Nat.choose (k + (l - 1)) k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  simp only [Nat.succ_sub_one, Nat.succ_add]
  rw [Nat.choose_succ_succ]
  congr 2

private theorem choose_left_lt (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Nat.choose ((k - 1) + l) (k - 1) < Nat.choose (k + l) k := by
  rw [choose_pascal k l hk hl]
  exact Nat.lt_add_of_pos_right (Nat.choose_pos (by omega))

private theorem choose_right_lt (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Nat.choose (k + (l - 1)) k < Nat.choose (k + l) k := by
  rw [choose_pascal k l hk hl]
  exact Nat.lt_add_of_pos_left (Nat.choose_pos (by omega))

/-- The elementary weighted pigeonhole step behind the denominator-free
Erdős--Szekeres induction. -/
private theorem weighted_neighbor_dichotomy
    (a b c d : ℕ) :
    (c + d) * a ≥ c * (a + b) ∨
      (c + d) * b ≥ d * (a + b) := by
  by_contra h
  push Not at h
  nlinarith

/-- If a weighted branch is selected and the whole set is at least the
Pascal sum, that branch contains enough vertices for the induction
hypothesis. -/
private theorem branch_large_enough
    {c d n a : ℕ} (hc : c < c + d) (hs : c + d ≤ n)
    (hweight : (c + d) * a ≥ c * (n - 1)) :
    c ≤ a := by
  by_contra hca
  have ha : a < c := Nat.lt_of_not_ge hca
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < c + d) hs
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  nlinarith

/-- The cancellation step which turns the weighted-neighbour inequality and
the recursive reservoir estimate into the next reservoir estimate. -/
private theorem branch_reservoir_bound
    {a b c d t : ℕ} (hc : 0 < c) (ha : a ≤ c * t)
    (hweight : c * (a + b) ≤ (c + d) * a) :
    a + b + 1 ≤ (c + d) * (t + 1) := by
  have hab_mul : c * (a + b) ≤ c * ((c + d) * t) := by
    calc
      c * (a + b) ≤ (c + d) * a := hweight
      _ ≤ (c + d) * (c * t) := Nat.mul_le_mul_left _ ha
      _ = c * ((c + d) * t) := by ring
  have hab : a + b ≤ (c + d) * t :=
    Nat.le_of_mul_le_mul_left hab_mul hc
  calc
    a + b + 1 ≤ (c + d) * t + 1 := Nat.add_le_add_right hab 1
    _ ≤ (c + d) * t + (c + d) := by omega
    _ = (c + d) * (t + 1) := by rw [Nat.mul_add]; simp

/-- Weighted Erdős--Szekeres on an arbitrary finite reservoir.  This is the
induction-strengthened form: all selected vertices remain inside `S`.

The conclusion says that the first member has red size `k` or blue size `l`,
and records the reservoir bound without division:
`|S| ≤ choose (k+l) k * (|Y| + k + l)`.
-/
theorem exists_monoPair_in_finset_choose_bound {N : ℕ}
    (R : SimpleGraph (Fin N)) (S : Finset (Fin N)) (k l : ℕ)
    (hsize : Nat.choose (k + l) k ≤ S.card) :
    ∃ X Y : Finset (Fin N), X ⊆ S ∧ Y ⊆ S ∧
      ((MonoPair R X Y ∧ X.card = k) ∨
        (MonoPair Rᶜ X Y ∧ X.card = l)) ∧
      S.card ≤ Nat.choose (k + l) k * (Y.card + k + l) := by
  classical
  induction hkl : k + l using Nat.strong_induction_on generalizing S k l with
  | h s ih =>
      subst s
      by_cases hk : k = 0
      · subst k
        refine ⟨∅, S, by simp, by simp, Or.inl ⟨?_, by simp⟩, ?_⟩
        · simp [MonoPair]
        · simpa only [Nat.zero_add, Nat.add_zero, Nat.choose_zero_right, one_mul] using
            Nat.le_add_right S.card l
      by_cases hl : l = 0
      · subst l
        refine ⟨∅, S, by simp, by simp, Or.inr ⟨?_, by simp⟩, ?_⟩
        · simp [MonoPair]
        · simpa only [Nat.add_zero, Nat.choose_self, one_mul] using
            Nat.le_add_right S.card k
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hlpos : 0 < l := Nat.pos_of_ne_zero hl
      have hSpos : S.Nonempty := by
        apply card_pos.mp
        exact lt_of_lt_of_le (Nat.choose_pos (by omega)) hsize
      have hScard : 1 ≤ S.card := card_pos.mpr hSpos
      obtain ⟨v, hv⟩ := hSpos
      let A : Finset (Fin N) := (S.erase v).filter (R.Adj v)
      let B : Finset (Fin N) := (S.erase v).filter (Rᶜ.Adj v)
      have hA_sub : A ⊆ S := by
        intro w hw
        exact (mem_erase.mp (mem_filter.mp hw).1).2
      have hB_sub : B ⊆ S := by
        intro w hw
        exact (mem_erase.mp (mem_filter.mp hw).1).2
      have hAB_disjoint : Disjoint A B := by
        refine Finset.disjoint_left.mpr ?_
        intro w hwA hwB
        have hr := (mem_filter.mp hwA).2
        have hb := (mem_filter.mp hwB).2
        exact ((SimpleGraph.compl_adj _ _ _).1 hb).2 hr
      have hAB_union : A ∪ B = S.erase v := by
        ext w
        simp only [mem_union, mem_erase, mem_filter, A, B]
        constructor
        · rintro (⟨hS, hr⟩ | ⟨hS, hb⟩)
          · exact hS
          · exact hS
        · intro hw
          by_cases hr : R.Adj v w
          · exact Or.inl ⟨hw, hr⟩
          · exact Or.inr ⟨hw, (SimpleGraph.compl_adj _ _ _).2 ⟨hw.1.symm, hr⟩⟩
      have hcards : A.card + B.card + 1 = S.card := by
        rw [← card_union_of_disjoint hAB_disjoint, hAB_union,
          card_erase_of_mem hv]
        exact Nat.sub_add_cancel hScard
      let c := Nat.choose ((k - 1) + l) (k - 1)
      let d := Nat.choose (k + (l - 1)) k
      have hcd : c + d = Nat.choose (k + l) k := by
        exact (choose_pascal k l hkpos hlpos).symm
      have hc_lt : c < c + d := by
        dsimp [c, d]
        exact Nat.lt_add_of_pos_right (Nat.choose_pos (by omega))
      have hd_lt : d < c + d := by
        dsimp [c, d]
        exact Nat.lt_add_of_pos_left (Nat.choose_pos (by omega))
      have hcpos : 0 < c := by
        dsimp [c]
        exact Nat.choose_pos (by omega)
      have hdpos : 0 < d := by
        dsimp [d]
        exact Nat.choose_pos (by omega)
      have hweighted :
          (c + d) * A.card ≥ c * (A.card + B.card) ∨
            (c + d) * B.card ≥ d * (A.card + B.card) := by
        exact weighted_neighbor_dichotomy A.card B.card c d
      rcases hweighted with hred | hblue
      · have hcA : c ≤ A.card := by
          apply branch_large_enough hc_lt
          · simpa [hcd] using hsize
          · have hABcard : A.card + B.card = S.card - 1 := by omega
            rw [← hABcard]
            exact hred
        have hsmaller : (k - 1) + l < k + l := by omega
        obtain ⟨X, Y, hXS, hYS, hcolour, hbound⟩ :=
          ih ((k - 1) + l) hsmaller A (k - 1) l (by simpa [c] using hcA) rfl
        rcases hcolour with hredpair | hbluepair
        · let X' := insert v X
          refine ⟨X', Y, ?_, hYS.trans hA_sub, Or.inl ⟨?_, ?_⟩, ?_⟩
          · intro w hw
            rcases mem_insert.mp hw with rfl | hw
            · exact hv
            · exact hA_sub (hXS hw)
          · refine ⟨?_, ?_, ?_⟩
            · rw [Finset.disjoint_insert_left]
              refine ⟨?_, hredpair.1.1⟩
              intro hvY
              have hvne : v ≠ v := (mem_erase.mp (mem_filter.mp (hYS hvY)).1).1
              exact hvne rfl
            · rw [coe_insert]
              apply hredpair.1.2.1.insert
              intro y hy _
              exact (mem_filter.mp (hXS hy)).2
            · intro x hx y hy
              rcases mem_insert.mp hx with rfl | hx
              · exact (mem_filter.mp (hYS hy)).2
              · exact hredpair.1.2.2 x hx y hy
          · rw [card_insert_of_notMem]
            · omega
            · intro hvX
              exact (mem_erase.mp (mem_filter.mp (hXS hvX)).1).1 rfl
          · have hA_bound : A.card ≤ c * (Y.card + (k - 1) + l) := by
              simpa [c] using hbound
            rw [← hcd]
            calc
              S.card = A.card + B.card + 1 := hcards.symm
              _ ≤ (c + d) * (Y.card + k + l) := by
                have hratio : c * (A.card + B.card) ≤ (c + d) * A.card := hred
                have hmain := branch_reservoir_bound hcpos hA_bound hratio
                have hinner : Y.card + (k - 1) + l + 1 = Y.card + k + l := by omega
                rw [hinner] at hmain
                exact hmain
        · refine ⟨X, Y, hXS.trans hA_sub, hYS.trans hA_sub,
              Or.inr hbluepair, ?_⟩
          rw [← hcd]
          have hA_bound : A.card ≤ c * (Y.card + (k - 1) + l) := by
            simpa [c] using hbound
          have hratio : c * (A.card + B.card) ≤ (c + d) * A.card := hred
          have hmain := branch_reservoir_bound hcpos hA_bound hratio
          rw [← hcards]
          have hinner : Y.card + (k - 1) + l + 1 = Y.card + k + l := by omega
          rw [hinner] at hmain
          simpa only [add_comm B.card A.card] using hmain
      · have hdB : d ≤ B.card := by
          apply branch_large_enough (c := d) (d := c) (n := S.card) (a := B.card)
          · omega
          · simpa [hcd, add_comm] using hsize
          · have hABcard : A.card + B.card = S.card - 1 := by omega
            rw [← hABcard]
            simpa [add_comm] using hblue
        have hsmaller : k + (l - 1) < k + l := by omega
        obtain ⟨X, Y, hXS, hYS, hcolour, hbound⟩ :=
          ih (k + (l - 1)) hsmaller B k (l - 1) (by simpa [d] using hdB) rfl
        rcases hcolour with hredpair | hbluepair
        · refine ⟨X, Y, hXS.trans hB_sub, hYS.trans hB_sub,
              Or.inl hredpair, ?_⟩
          rw [← hcd]
          have hB_bound : B.card ≤ d * (Y.card + k + (l - 1)) := by
            simpa [d] using hbound
          have hratio : d * (A.card + B.card) ≤ (c + d) * B.card := hblue
          have hmain := branch_reservoir_bound (c := d) (d := c) hdpos hB_bound (by
            simpa [add_comm] using hratio)
          rw [← hcards]
          have hinner : Y.card + k + (l - 1) + 1 = Y.card + k + l := by omega
          rw [add_comm d c, hinner] at hmain
          simpa only [add_comm B.card A.card] using hmain
        · let X' := insert v X
          refine ⟨X', Y, ?_, hYS.trans hB_sub, Or.inr ⟨?_, ?_⟩, ?_⟩
          · intro w hw
            rcases mem_insert.mp hw with rfl | hw
            · exact hv
            · exact hB_sub (hXS hw)
          · refine ⟨?_, ?_, ?_⟩
            · rw [Finset.disjoint_insert_left]
              refine ⟨?_, hbluepair.1.1⟩
              intro hvY
              have hvne : v ≠ v := (mem_erase.mp (mem_filter.mp (hYS hvY)).1).1
              exact hvne rfl
            · rw [coe_insert]
              apply hbluepair.1.2.1.insert
              intro y hy _
              exact (mem_filter.mp (hXS hy)).2
            · intro x hx y hy
              rcases mem_insert.mp hx with rfl | hx
              · exact (mem_filter.mp (hYS hy)).2
              · exact hbluepair.1.2.2 x hx y hy
          · rw [card_insert_of_notMem]
            · omega
            · intro hvX
              exact (mem_erase.mp (mem_filter.mp (hXS hvX)).1).1 rfl
          · rw [← hcd]
            have hB_bound : B.card ≤ d * (Y.card + k + (l - 1)) := by
              simpa [d] using hbound
            have hratio : d * (A.card + B.card) ≤ (c + d) * B.card := hblue
            have hmain := branch_reservoir_bound (c := d) (d := c) hdpos hB_bound (by
              simpa [add_comm] using hratio)
            rw [← hcards]
            have hinner : Y.card + k + (l - 1) + 1 = Y.card + k + l := by omega
            rw [add_comm d c, hinner] at hmain
            simpa only [add_comm B.card A.card] using hmain

/-- The denominator-free weighted Erdős--Szekeres monochromatic-pair lemma on
the complete host vertex set. -/
theorem exists_monoPair_choose_bound (k l N : ℕ)
    (R : SimpleGraph (Fin N)) (hsize : Nat.choose (k + l) k ≤ N) :
    ∃ X Y : Finset (Fin N),
      ((MonoPair R X Y ∧ X.card = k) ∨
        (MonoPair Rᶜ X Y ∧ X.card = l)) ∧
      N ≤ Nat.choose (k + l) k * (Y.card + k + l) := by
  simpa using exists_monoPair_in_finset_choose_bound R Finset.univ k l (by simpa using hsize)

/-- The central binomial coefficient is bounded by `4^k`. -/
theorem choose_two_mul_le_four_pow (k : ℕ) :
    Nat.choose (2 * k) k ≤ 4 ^ k := by
  calc
    Nat.choose (2 * k) k ≤ 2 ^ (2 * k) := Nat.choose_le_two_pow _ _
    _ = 4 ^ k := by rw [pow_mul]; norm_num

/-- Diagonal form used to start the Ramsey argument: one colour has a first
member of order `k`, and its reservoir satisfies the convenient `4^k` bound. -/
theorem exists_diagonal_monoPair_four_pow_bound (k N : ℕ)
    (R : SimpleGraph (Fin N)) (hsize : 4 ^ k ≤ N) :
    ∃ X Y : Finset (Fin N), HasMonoPair R X Y ∧ X.card = k ∧
      N ≤ 4 ^ k * (Y.card + 2 * k) := by
  have hchoose : Nat.choose (k + k) k ≤ N := by
    calc
      Nat.choose (k + k) k = Nat.choose (2 * k) k := by rw [two_mul]
      _ ≤ 4 ^ k := choose_two_mul_le_four_pow k
      _ ≤ N := hsize
  obtain ⟨X, Y, hcolour, hbound⟩ := exists_monoPair_choose_bound k k N R hchoose
  refine ⟨X, Y, ?_, ?_, ?_⟩
  · rcases hcolour with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rcases hcolour with h | h <;> exact h.2
  · calc
      N ≤ Nat.choose (k + k) k * (Y.card + k + k) := hbound
      _ ≤ 4 ^ k * (Y.card + 2 * k) := by
        apply Nat.mul_le_mul
        · simpa [two_mul] using choose_two_mul_le_four_pow k
        · omega

end Erdos546
