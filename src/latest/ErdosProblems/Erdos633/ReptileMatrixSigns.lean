import ErdosProblems.Erdos633.ReptileEigenvalues

/-!
# Extremal signs in a nonnegative reptile matrix

For a positive eigenvector at a positive eigenvalue and a nonzero eigenvector
at its negative, a maximal absolute coordinate ratio propagates across every
positive matrix entry and reverses sign. In dimension three this forces at
least two diagonal entries to vanish.
-/

namespace Erdos633

open scoped BigOperators

theorem exists_positive_maximum_ratio (v w : Fin 3 → ℝ)
    (hv : ∀ i, 0 < v i) (hw : w ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ i : Fin 3, |w i| = M * v i ∧ ∀ j, |w j| ≤ M * v j := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 3 => |w j| / v j) (by simp)
  let M := |w i| / v i
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hjpos : 0 < |w j| / v j := div_pos (abs_pos.mpr hj) (hv j)
  have hjle : |w j| / v j ≤ M := hi j (Finset.mem_univ j)
  refine ⟨M, lt_of_lt_of_le hjpos hjle, i, ?_, ?_⟩
  · dsimp [M]
    rw [div_mul_cancel₀ _ (ne_of_gt (hv i))]
  · intro k
    exact (div_le_iff₀ (hv k)).mp (hi k (Finset.mem_univ k))

theorem negative_eigenvector_positive_extreme_step
    (D : Fin 3 → Fin 3 → ℕ) (v w : Fin 3 → ℝ) (x M : ℝ)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hneg : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i)
    (hbound : ∀ j, |w j| ≤ M * v j) (i : Fin 3) (hi : w i = M * v i)
    (j : Fin 3) (hD : 0 < D i j) : w j = -M * v j := by
  have hn (k : Fin 3) : 0 ≤ (D i k : ℝ) * (M * v k + w k) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    linarith [(abs_le.mp (hbound k)).1]
  have hs : (∑ k : Fin 3, (D i k : ℝ) * (M * v k + w k)) = 0 := by
    calc
      _ = M * (∑ k : Fin 3, (D i k : ℝ) * v k) +
          (∑ k : Fin 3, (D i k : ℝ) * w k) := by
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
        ring
      _ = 0 := by rw [hpos i, hneg i, hi]; ring
  have hjle := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j)
  rw [hs] at hjle
  have hjzero : (D i j : ℝ) * (M * v j + w j) = 0 := le_antisymm hjle (hn j)
  have hDj : (D i j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hD)
  have hz := (mul_eq_zero.mp hjzero).resolve_left hDj
  linarith

theorem negative_eigenvector_neg
    (D : Fin 3 → Fin 3 → ℕ) (w : Fin 3 → ℝ) (x : ℝ)
    (h : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i) :
    ∀ i, ∑ j : Fin 3, (D i j : ℝ) * (-w j) = -x * (-w i) := by
  intro i
  simp only [mul_neg, Finset.sum_neg_distrib, h i]

theorem negative_eigenvector_extreme_step
    (D : Fin 3 → Fin 3 → ℕ) (v w : Fin 3 → ℝ) (x M : ℝ)
    (hv : ∀ i, 0 < v i) (hM : 0 < M)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hneg : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i)
    (hbound : ∀ j, |w j| ≤ M * v j) (i : Fin 3) (hi : |w i| = M * v i)
    (j : Fin 3) (hD : 0 < D i j) : |w j| = M * v j ∧ w i * w j < 0 := by
  by_cases hwi : 0 ≤ w i
  · have hi' : w i = M * v i := by rwa [abs_of_nonneg hwi] at hi
    have hj := negative_eigenvector_positive_extreme_step D v w x M hpos hneg hbound i hi' j hD
    have hjneg : w j < 0 := by rw [hj]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos hM) (hv j)
    refine ⟨?_, mul_neg_of_pos_of_neg (by rw [hi']; exact mul_pos hM (hv i)) hjneg⟩
    rw [abs_of_neg hjneg, hj]
    ring
  · have hwineg : w i < 0 := lt_of_not_ge hwi
    have hi' : -w i = M * v i := by rwa [abs_of_neg hwineg] at hi
    have hb : ∀ k, |-w k| ≤ M * v k := by simpa only [abs_neg] using hbound
    have hj := negative_eigenvector_positive_extreme_step D v (fun k => -w k) x M
      hpos (negative_eigenvector_neg D w x hneg) hb i hi' j hD
    have hj' : w j = M * v j := by linarith
    have hjpos : 0 < w j := by rw [hj']; exact mul_pos hM (hv j)
    exact ⟨by rw [abs_of_pos hjpos, hj'], mul_neg_of_neg_of_pos hwineg hjpos⟩

theorem negative_eigenvector_extreme_diagonal_zero
    (D : Fin 3 → Fin 3 → ℕ) (v w : Fin 3 → ℝ) (x M : ℝ)
    (hv : ∀ i, 0 < v i) (hM : 0 < M)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hneg : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i)
    (hbound : ∀ j, |w j| ≤ M * v j) (i : Fin 3) (hi : |w i| = M * v i) : D i i = 0 := by
  by_contra hD
  have h := (negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hbound i hi i
    (Nat.pos_of_ne_zero hD)).2
  nlinarith only [h, sq_nonneg (w i)]

theorem positive_negative_eigenvectors_two_zero_diagonals
    (D : Fin 3 → Fin 3 → ℕ) (v w : Fin 3 → ℝ) (x : ℝ)
    (hv : ∀ i, 0 < v i) (hw : w ≠ 0) (hx : 0 < x)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hneg : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i) :
    ∃ i j : Fin 3, i ≠ j ∧ D i i = 0 ∧ D j j = 0 := by
  obtain ⟨M, hM, i, hi, hb⟩ := exists_positive_maximum_ratio v w hv hw
  have hex : ∃ j : Fin 3, 0 < D i j := by
    by_contra h
    have hz : ∀ j, D i j = 0 := by
      intro j
      have hj := not_exists.mp h j
      omega
    have he := hpos i
    simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at he
    exact (ne_of_gt (mul_pos hx (hv i))) he.symm
  obtain ⟨j, hj⟩ := hex
  obtain ⟨hjmax, hsign⟩ := negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb i hi j hj
  have hne : i ≠ j := by
    intro he
    rw [he] at hsign
    nlinarith only [hsign, sq_nonneg (w j)]
  exact ⟨i, j, hne,
    negative_eigenvector_extreme_diagonal_zero D v w x M hv hM hpos hneg hb i hi,
    negative_eigenvector_extreme_diagonal_zero D v w x M hv hM hpos hneg hb j hjmax⟩

end Erdos633
