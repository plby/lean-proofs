import ErdosProblems.Erdos633b.CornerColumnTotals
import ErdosProblems.Erdos633b.SixAngleShapes
import Mathlib.Logic.Equiv.Fintype

/-! Two distinct matched angles determine the whole angle triple.
Consequently a tiling of a scalene outer triangle with at most four
outer tile corners is a reptiling. -/

namespace Erdos633b

theorem two_unit_rows_of_sum_le_four (r : Fin 3 → ℕ)
    (hp : ∀ i, 0 < r i) (hs : ∑ i, r i ≤ 4) :
    ∃ i j : Fin 3, i ≠ j ∧ r i = 1 ∧ r j = 1 := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hsum : r 0 + r 1 + r 2 ≤ 4 := by simpa only [Fin.sum_univ_three] using hs
  by_cases he0 : r 0 = 1
  · by_cases he1 : r 1 = 1
    · exact ⟨0, 1, by decide, he0, he1⟩
    · exact ⟨0, 2, by decide, he0, by omega⟩
  · exact ⟨1, 2, by decide, by omega, by omega⟩

theorem reptilingAngles_of_two_matched_angles (S T : Triangle)
    (i j a b : Fin 3) (hij : i ≠ j) (hab : a ≠ b)
    (hi : T.angle i = S.angle a) (hj : T.angle j = S.angle b) :
    ReptilingAngles S T := by
  have hf : Function.Injective (![i, j] : Fin 2 → Fin 3) := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  have hg : Function.Injective (![a, b] : Fin 2 → Fin 3) := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair ![i, j] ![a, b] hf hg
  have hei : e i = a := he 0
  have hej : e j = b := he 1
  have heSum : ∑ l : Fin 3, S.angle (e l) = ∑ l : Fin 3, S.angle l :=
    Fintype.sum_equiv e (fun l => S.angle (e l)) S.angle (by intro l; rfl)
  have hs : ∑ l : Fin 3, (T.angle l - S.angle (e l)) = 0 := by
    rw [Finset.sum_sub_distrib, heSum]
    simp only [Fin.sum_univ_three, T.angle_sum, S.angle_sum, sub_self]
  refine ⟨e, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    simpa only [hei] using hi
  by_cases hkj : k = j
  · subst k
    simpa only [hej] using hj
  have hsingle : ∑ l : Fin 3, (T.angle l - S.angle (e l)) =
      T.angle k - S.angle (e k) := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      have hl : l = i ∨ l = j := by omega
      rcases hl with rfl | rfl
      · rw [hei, hi, sub_self]
      · rw [hej, hj, sub_self]
    · intro h
      exact False.elim (h (Finset.mem_univ k))
  exact sub_eq_zero.mp (hsingle.symm.trans hs)

namespace Tiling

theorem angle_eq_tile_of_corner_row_one {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (h : ∑ j, d.cornerAngleCount i j = 1) :
    ∃ j, T.angle i = d.tile.angle j := by
  have hs : d.cornerAngleCount i 0 + d.cornerAngleCount i 1 + d.cornerAngleCount i 2 = 1 := by
    simpa only [Fin.sum_univ_three] using h
  have hc :
      (d.cornerAngleCount i 0 = 1 ∧ d.cornerAngleCount i 1 = 0 ∧ d.cornerAngleCount i 2 = 0) ∨
      (d.cornerAngleCount i 0 = 0 ∧ d.cornerAngleCount i 1 = 1 ∧ d.cornerAngleCount i 2 = 0) ∨
      (d.cornerAngleCount i 0 = 0 ∧ d.cornerAngleCount i 1 = 0 ∧ d.cornerAngleCount i 2 = 1) := by
    omega
  rcases hc with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨0, ?_⟩
    rw [d.angle_eq_three_counts i, h0, h1, h2]
    simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero]
  · refine ⟨1, ?_⟩
    rw [d.angle_eq_three_counts i, h0, h1, h2]
    simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]
  · refine ⟨2, ?_⟩
    rw [d.angle_eq_three_counts i, h0, h1, h2]
    simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add]

theorem reptiling_of_corner_total_le_four {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hscalene : Function.Injective T.angle) (hcount : ∑ j, d.cornerColumnCount j ≤ 4) :
    ReptilingAngles d.tile T := by
  let r : Fin 3 → ℕ := fun i => ∑ j, d.cornerAngleCount i j
  have hp : ∀ i, 0 < r i := by
    intro i
    obtain ⟨j, hj⟩ := d.corner_row_positive i
    exact lt_of_lt_of_le hj (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hs : ∑ i, r i ≤ 4 := by
    change (∑ i : Fin 3, ∑ j : Fin 3, d.cornerAngleCount i j) ≤ 4
    rw [Finset.sum_comm]
    exact hcount
  obtain ⟨i, j, hij, hi, hj⟩ := two_unit_rows_of_sum_le_four r hp hs
  obtain ⟨a, ha⟩ := d.angle_eq_tile_of_corner_row_one i hi
  obtain ⟨b, hb⟩ := d.angle_eq_tile_of_corner_row_one j hj
  have hab : a ≠ b := by
    intro h
    apply hij
    apply hscalene
    rw [ha, hb, h]
  exact reptilingAngles_of_two_matched_angles d.tile T i j a b hij hab ha hb

end Tiling
end Erdos633b
