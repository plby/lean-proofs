import ErdosProblems.Erdos633b.CornerColumnBounds
import ErdosProblems.Erdos633b.CornerPairEnumeration
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Sort the actual corner coefficients and apply the finite exhaustion.
The coefficients are extracted from genuine geometric corner incidences. -/

namespace Erdos633b

theorem three_corner_pairs_ordered (p q : Fin 3 → ℕ) (hq : ∀ i, q i ≤ 3)
    (hinj : Function.Injective (fun i => (p i, q i))) :
    ∃ e : Equiv.Perm (Fin 3),
      (p (e 0) < p (e 1) ∨ p (e 0) = p (e 1) ∧ q (e 0) < q (e 1)) ∧
      (p (e 1) < p (e 2) ∨ p (e 1) = p (e 2) ∧ q (e 1) < q (e 2)) := by
  let f : Fin 3 → ℝ := fun i => (4 * p i + q i : ℕ)
  have hf : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    have he' : 4 * p i + q i = 4 * p j + q j := by exact_mod_cast he
    apply hinj
    change (p i, q i) = (p j, q j)
    exact Prod.ext (by have hi := hq i; have hj := hq j; omega)
      (by have hi := hq i; have hj := hq j; omega)
  obtain ⟨e, h01, h12⟩ := three_values_ordered f
  have h01' : 4 * p (e 0) + q (e 0) < 4 * p (e 1) + q (e 1) := by
    have ht := lt_of_le_of_ne h01 (hf.ne (e.injective.ne (by decide : (0 : Fin 3) ≠ 1)))
    dsimp only [f] at ht
    exact_mod_cast ht
  have h12' : 4 * p (e 1) + q (e 1) < 4 * p (e 2) + q (e 2) := by
    have ht := lt_of_le_of_ne h12 (hf.ne (e.injective.ne (by decide : (1 : Fin 3) ≠ 2)))
    dsimp only [f] at ht
    exact_mod_cast ht
  refine ⟨e, ?_, ?_⟩
  · have h0 := hq (e 0)
    have h1 := hq (e 1)
    omega
  · have h1 := hq (e 1)
    have h2 := hq (e 2)
    omega

namespace Tiling

theorem corner_count_le_column {T : Triangle} {n : ℕ} (d : Tiling T n) (i j : Fin 3) :
    d.cornerAngleCount i j ≤ d.cornerColumnCount j := by
  unfold cornerColumnCount
  exact Finset.single_le_sum (f := fun k => d.cornerAngleCount k j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem corner_two_angle_row {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0) (i : Fin 3) :
    T.angle i = (d.cornerAngleCount i 0 : ℝ) * d.tile.angle 0 +
      (d.cornerAngleCount i 1 : ℝ) * d.tile.angle 1 := by
  rw [d.angle_eq_sum_counts, Fin.sum_univ_three,
    d.corner_count_zero_of_column_zero 2 h2 i, Nat.cast_zero, zero_mul, add_zero]

theorem corner_pair_nonzero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0) (i : Fin 3) :
    0 < d.cornerAngleCount i 0 + d.cornerAngleCount i 1 := by
  by_contra hn
  have h0 : d.cornerAngleCount i 0 = 0 := by omega
  have h1 : d.cornerAngleCount i 1 = 0 := by omega
  have he := d.corner_two_angle_row h2 i
  simp only [h0, h1, Nat.cast_zero, zero_mul, zero_add] at he
  exact (T.angle_pos i).ne' he

theorem corner_pair_injective {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0) (hscalene : Function.Injective T.angle) :
    Function.Injective (fun i => (d.cornerAngleCount i 0, d.cornerAngleCount i 1)) := by
  intro i j he
  have h0 := congrArg Prod.fst he
  have h1 := congrArg Prod.snd he
  apply hscalene
  change d.cornerAngleCount i 0 = d.cornerAngleCount j 0 at h0
  change d.cornerAngleCount i 1 = d.cornerAngleCount j 1 at h1
  rw [d.corner_two_angle_row h2 i, d.corner_two_angle_row h2 j, h0, h1]

theorem corner_column_reorder {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    d.cornerAngleCount (e 0) j + d.cornerAngleCount (e 1) j + d.cornerAngleCount (e 2) j =
      d.cornerColumnCount j := by
  have h := Fintype.sum_equiv e (fun i => d.cornerAngleCount (e i) j)
    (fun i => d.cornerAngleCount i j) (fun _ => rfl)
  simpa only [Fin.sum_univ_three, cornerColumnCount] using h

theorem actual_corner_pairs_exhaustive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hscalene : Function.Injective T.angle) :
    ∃ e : Equiv.Perm (Fin 3),
      ((d.cornerAngleCount (e 0) 0, d.cornerAngleCount (e 0) 1),
       (d.cornerAngleCount (e 1) 0, d.cornerAngleCount (e 1) 1),
       (d.cornerAngleCount (e 2) 0, d.cornerAngleCount (e 2) 1)) ∈ cornerPairPatterns := by
  have hb := d.corner_columns_le_three h2 hirr
  have hp := d.other_corner_columns_pos h2 hirr
  obtain ⟨e, he01, he12⟩ := three_corner_pairs_ordered
    (fun i => d.cornerAngleCount i 0) (fun i => d.cornerAngleCount i 1)
    (fun i => (d.corner_count_le_column i 1).trans hb.2) (d.corner_pair_injective h2 hscalene)
  refine ⟨e, sorted_corner_pairs_exhaustive _ _ _ _ _ _
    (d.corner_pair_nonzero h2 (e 0)) (d.corner_pair_nonzero h2 (e 1))
    (d.corner_pair_nonzero h2 (e 2)) he01 he12 ?_ ?_ ?_ ?_⟩
  · rw [d.corner_column_reorder]
    exact hp.1
  · rw [d.corner_column_reorder]
    exact hb.1
  · rw [d.corner_column_reorder]
    exact hp.2
  · rw [d.corner_column_reorder]
    exact hb.2

end Tiling
end Erdos633b
