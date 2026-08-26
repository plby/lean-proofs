import ErdosProblems.Erdos633.ReptileMatrixSigns

/-!
# Side ratios belong to the field of the nonsquare similarity scale

The two zero diagonal entries supplied by the negative eigenvector allow
direct elimination in the three boundary equations. A zero principal minor
is handled using positivity, not by assuming the matrix is irreducible.
Thus no eigenspace-multiplicity or spectral theorem is needed here.
-/

namespace Erdos633

open scoped BigOperators

theorem two_zero_diagonal_normalized_ratios_mem
    (K : Subfield ℝ) (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (x : ℝ)
    (hv : ∀ i, 0 < v i) (hx : 0 < x) (hxK : x ∈ K) (hxirr : x ∉ rationalReals)
    (h0 : D 0 0 = 0) (h1 : D 1 1 = 0)
    (heigen : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i) :
    v 0 / v 2 ∈ K ∧ v 1 / v 2 ∈ K := by
  have he0 := heigen 0
  have he1 := heigen 1
  have he2 := heigen 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at he0 he1 he2
  change (D 0 0 : ℝ) * v 0 + ((D 0 1 : ℝ) * v 1 + (D 0 2 : ℝ) * v 2) =
    x * v 0 at he0
  change (D 1 0 : ℝ) * v 0 + ((D 1 1 : ℝ) * v 1 + (D 1 2 : ℝ) * v 2) =
    x * v 1 at he1
  change (D 2 0 : ℝ) * v 0 + ((D 2 1 : ℝ) * v 1 + (D 2 2 : ℝ) * v 2) =
    x * v 2 at he2
  rw [h0] at he0
  rw [h1] at he1
  simp only [Nat.cast_zero, zero_mul, zero_add] at he0 he1
  have hminor0 : (x ^ 2 - (D 0 1 : ℝ) * D 1 0) * v 0 =
      (x * D 0 2 + (D 0 1 : ℝ) * D 1 2) * v 2 := by
    linear_combination -x * he0 - (D 0 1 : ℝ) * he1
  have hminor1 : (x ^ 2 - (D 0 1 : ℝ) * D 1 0) * v 1 =
      (x * D 1 2 + (D 1 0 : ℝ) * D 0 2) * v 2 := by
    linear_combination -x * he1 - (D 1 0 : ℝ) * he0
  have hnK (i j : Fin 3) : (D i j : ℝ) ∈ K := natCast_mem K _
  have hv0 := ne_of_gt (hv 0)
  have hv2 := ne_of_gt (hv 2)
  have hx0 := ne_of_gt hx
  by_cases hminor : x ^ 2 - (D 0 1 : ℝ) * D 1 0 = 0
  · have hdpos : (0 : ℝ) < D 0 1 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (D 0 1), sq_pos_of_pos hx]
    have hsum : x * D 0 2 + (D 0 1 : ℝ) * D 1 2 = 0 := by
      rw [hminor, zero_mul] at hminor0
      exact (mul_eq_zero.mp hminor0.symm).resolve_right hv2
    have he02 : (D 0 2 : ℝ) = 0 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (D 0 2),
        Nat.cast_nonneg (α := ℝ) (D 1 2)]
    have he12 : (D 1 2 : ℝ) = 0 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (D 1 2)]
    rw [he12, zero_mul, add_zero] at he1
    have h10 : v 1 / v 0 = (D 1 0 : ℝ) / x := by
      apply (div_eq_div_iff hv0 hx0).mpr
      nlinarith only [he1]
    have h10K : v 1 / v 0 ∈ K := by
      rw [h10]
      exact K.div_mem (hnK 1 0) hxK
    have hx22 : x - (D 2 2 : ℝ) ≠ 0 := by
      intro h
      apply hxirr
      rw [sub_eq_zero.mp h]
      exact rationalReals_nat _
    have h20 : v 2 / v 0 =
        ((D 2 0 : ℝ) + (D 2 1 : ℝ) * (v 1 / v 0)) / (x - D 2 2) := by
      apply (div_eq_div_iff hv0 hx22).mpr
      field_simp [hv0]
      nlinarith only [he2]
    have h20K : v 2 / v 0 ∈ K := by
      rw [h20]
      exact K.div_mem (K.add_mem (hnK 2 0) (K.mul_mem (hnK 2 1) h10K))
        (K.sub_mem hxK (hnK 2 2))
    have h02K : v 0 / v 2 ∈ K := by
      simpa only [inv_div] using K.inv_mem h20K
    refine ⟨h02K, ?_⟩
    have h := K.mul_mem h10K h02K
    simpa only [div_mul_div_cancel₀ hv0] using h
  · have h0ratio : v 0 / v 2 =
        (x * D 0 2 + (D 0 1 : ℝ) * D 1 2) /
          (x ^ 2 - (D 0 1 : ℝ) * D 1 0) := by
      apply (div_eq_div_iff hv2 hminor).mpr
      nlinarith only [hminor0]
    have h1ratio : v 1 / v 2 =
        (x * D 1 2 + (D 1 0 : ℝ) * D 0 2) /
          (x ^ 2 - (D 0 1 : ℝ) * D 1 0) := by
      apply (div_eq_div_iff hv2 hminor).mpr
      nlinarith only [hminor1]
    have hdenK := K.sub_mem (K.pow_mem hxK 2) (K.mul_mem (hnK 0 1) (hnK 1 0))
    rw [h0ratio, h1ratio]
    exact ⟨K.div_mem (K.add_mem (K.mul_mem hxK (hnK 0 2))
      (K.mul_mem (hnK 0 1) (hnK 1 2))) hdenK,
      K.div_mem (K.add_mem (K.mul_mem hxK (hnK 1 2))
        (K.mul_mem (hnK 1 0) (hnK 0 2))) hdenK⟩

theorem fin_three_perm_first_two (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hij rfl)
    | exact ⟨Equiv.refl _, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 1 2, by decide, by decide⟩
    | exact ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide, by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), by decide, by decide⟩

theorem natural_matrix_nonsquare_ratios_mem_field
    (K : Subfield ℝ) (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (x : ℝ) (N : ℕ)
    (hv : ∀ i, 0 < v i) (hx : 0 < x) (hxK : x ∈ K)
    (hN : ¬ IsSquare N) (hsq : x ^ 2 = N)
    (heigen : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i) :
    ∀ i j : Fin 3, v i / v j ∈ K := by
  have hvne : v ≠ 0 := by intro h; exact (ne_of_gt (hv 0)) (congrFun h 0)
  obtain ⟨w, hw, hneg⟩ := natural_matrix_three_negative_eigenvector D N x hN hsq v hvne heigen
  obtain ⟨i, j, hij, hi, hj⟩ :=
    positive_negative_eigenvectors_two_zero_diagonals D v w x hv hw hx heigen hneg
  obtain ⟨e, he0, he1⟩ := fin_three_perm_first_two i j hij
  let E : Fin 3 → Fin 3 → ℕ := fun k l => D (e k) (e l)
  let z : Fin 3 → ℝ := fun k => v (e k)
  have hE (k : Fin 3) : ∑ l : Fin 3, (E k l : ℝ) * z l = x * z k := by
    change (∑ l : Fin 3, (D (e k) (e l) : ℝ) * v (e l)) = x * v (e k)
    rw [Equiv.sum_comp e (fun l => (D (e k) l : ℝ) * v l)]
    exact heigen (e k)
  obtain ⟨hz0, hz1⟩ := two_zero_diagonal_normalized_ratios_mem K E z x
    (fun k => hv (e k)) hx hxK (not_rational_of_sq_eq_nonsquare N x hN hsq)
    (by change D (e 0) (e 0) = 0; simpa only [he0] using hi)
    (by change D (e 1) (e 1) = 0; simpa only [he1] using hj) hE
  have hzK (k : Fin 3) : z k / z 2 ∈ K := by
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · exact hz0
    · exact hz1
    · rw [div_self (ne_of_gt (hv (e 2)))]
      exact K.one_mem
  intro k l
  have h := K.div_mem (hzK (e.symm k)) (hzK (e.symm l))
  dsimp [z] at h
  rw [e.apply_symm_apply, e.apply_symm_apply] at h
  have heq : (v k / v (e 2)) / (v l / v (e 2)) = v k / v l := by
    field_simp [ne_of_gt (hv (e 2)), ne_of_gt (hv l)]
  rwa [heq] at h

end Erdos633
