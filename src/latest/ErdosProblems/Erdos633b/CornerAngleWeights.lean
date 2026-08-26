import ErdosProblems.Erdos633b.FewCornerAngles
import ErdosProblems.Erdos633b.ThreeAngleWeights
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Positive integer angle weights transported from actual corner counts,
with exact finite partitions for the two remaining right-tile candidates. -/

namespace Erdos633b

namespace Tiling

theorem integer_corner_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (D : ℕ) (hD : 0 < D) (w : Fin 3 → ℕ)
    (hangle : ∀ j, d.tile.angle j = (w j : ℝ) * (Real.pi / D)) :
    ∃ c : Fin 3 → ℕ, (∀ i, T.angle i = (c i : ℝ) * (Real.pi / D)) ∧
      (∀ i, 0 < c i) ∧ ∑ i, c i = D := by
  let c : Fin 3 → ℕ := fun i => ∑ j, d.cornerAngleCount i j * w j
  have hrow (i : Fin 3) : T.angle i = (c i : ℝ) * (Real.pi / D) := by
    rw [d.angle_eq_sum_counts i]
    dsimp only [c]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hangle]
    ring
  have hp (i : Fin 3) : 0 < c i := by
    by_contra hn
    have hz : c i = 0 := by omega
    have hh := hrow i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (T.angle_pos i).ne' hh
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hsReal : ((∑ i, c i : ℕ) : ℝ) = D := by
    apply mul_right_cancel₀ (div_ne_zero Real.pi_ne_zero hD'.ne')
    calc
      _ = ∑ i, (c i : ℝ) * (Real.pi / D) := by rw [Nat.cast_sum, Finset.sum_mul]
      _ = Real.pi := by simp_rw [← hrow]; simpa only [Fin.sum_univ_three] using T.angle_sum
      _ = (D : ℝ) * (Real.pi / D) := by field_simp
  exact ⟨c, hrow, hp, by exact_mod_cast hsReal⟩

end Tiling

theorem ordered_integer_weights (T : Triangle) (c : Fin 3 → ℕ) (δ : ℝ)
    (hrow : ∀ i, T.angle i = (c i : ℝ) * δ) (hscalene : Function.Injective T.angle) :
    ∃ e : Equiv.Perm (Fin 3), c (e 0) < c (e 1) ∧ c (e 1) < c (e 2) := by
  have hinj : Function.Injective c := by
    intro i j hij
    apply hscalene
    rw [hrow i, hrow j, hij]
  obtain ⟨e, h01r, h12r⟩ := three_values_ordered (fun i => (c i : ℝ))
  have h01 : c (e 0) ≤ c (e 1) := by exact_mod_cast h01r
  have h12 : c (e 1) ≤ c (e 2) := by exact_mod_cast h12r
  refine ⟨e, lt_of_le_of_ne h01 ?_, lt_of_le_of_ne h12 ?_⟩
  · intro he
    have hh := e.injective (hinj he)
    exact (by decide : (0 : Fin 3) ≠ 1) hh
  · intro he
    have hh := e.injective (hinj he)
    exact (by decide : (1 : Fin 3) ≠ 2) hh

theorem sorted_weights_sum (c : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3)) :
    c (e 0) + c (e 1) + c (e 2) = ∑ i, c i := by
  have h := Fintype.sum_equiv e (fun i => c (e i)) c (by intro i; rfl)
  simpa only [Fin.sum_univ_three] using h

theorem sorted_partition_eight (a b c : ℕ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hs : a + b + c = 8) :
    (a = 1 ∧ b = 2 ∧ c = 5) ∨ (a = 1 ∧ b = 3 ∧ c = 4) := by omega

theorem sorted_partition_ten (a b c : ℕ) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hs : a + b + c = 10) :
    (a = 1 ∧ b = 2 ∧ c = 7) ∨ (a = 1 ∧ b = 3 ∧ c = 6) ∨
      (a = 1 ∧ b = 4 ∧ c = 5) ∨ (a = 2 ∧ b = 3 ∧ c = 5) := by omega

end Erdos633b
