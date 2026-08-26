import ErdosProblems.Erdos633.RationalTilingData
import ErdosProblems.Erdos633.RationalResidueLifting

/-!
# Arithmetic constraints on genuine rational corner data

The bounds here are consequences of all geometric conjugate equations.
Relabelling only permutes the three reference angle labels.
-/

namespace Erdos633

open scoped BigOperators

theorem triple_permuted_apply {α : Type*} (f : Fin 3 → α)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    ![f (e 0), f (e 1), f (e 2)] j = f (e j) := by
  fin_cases j <;> rfl

theorem rational_angle_modulus_permuted (f : Fin 3 → ℚ) (e : Equiv.Perm (Fin 3)) :
    4 * (f (e 0)).den * (f (e 1)).den * (f (e 2)).den =
      4 * (f 0).den * (f 1).den * (f 2).den := by
  have h := Equiv.prod_comp e (fun j => (f j).den)
  have h' : (f (e 0)).den * (f (e 1)).den * (f (e 2)).den =
      (f 0).den * (f 1).den * (f 2).den := by
    simpa [Fin.prod_univ_succ, mul_assoc] using h
  nlinarith only [h']

theorem rationalConjugateAngle_permuted (f : Fin 3 → ℚ)
    (e : Equiv.Perm (Fin 3)) (k : ℕ) (θ : ℚ) :
    rationalConjugateAngle (f (e 0)) (f (e 1)) (f (e 2)) k θ =
      rationalConjugateAngle (f 0) (f 1) (f 2) k θ := by
  have h := Equiv.sum_comp e (fun j => Int.fract ((k : ℚ) * f j))
  have hs : Int.fract ((k : ℚ) * f (e 0)) + Int.fract ((k : ℚ) * f (e 1)) +
      Int.fract ((k : ℚ) * f (e 2)) =
      Int.fract ((k : ℚ) * f 0) + Int.fract ((k : ℚ) * f 1) +
        Int.fract ((k : ℚ) * f 2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using h
  simp only [rationalConjugateAngle, hs]

variable {ω : Fin 3 → ℝ} {α β γ : ℚ}

def RationalCornerData.total (D : RationalCornerData ω α β γ) (j : Fin 3) : ℕ := ∑ i, D.counts i j

theorem RationalCornerData.angle_pos (D : RationalCornerData ω α β γ) (j : Fin 3) :
    0 < ![α, β, γ] j := by
  fin_cases j
  · exact D.positive.1
  · exact D.positive.2.1
  · exact D.positive.2.2

theorem RationalCornerData.angle_lt_one (D : RationalCornerData ω α β γ) (j : Fin 3) :
    ![α, β, γ] j < 1 := by
  have hs := D.angle_sum
  obtain ⟨ha, hb, hc⟩ := D.positive
  fin_cases j <;> dsimp <;> linarith

def RationalCornerData.relabelReference (D : RationalCornerData ω α β γ) (e : Equiv.Perm (Fin 3)) :
    RationalCornerData ω (![α, β, γ] (e 0)) (![α, β, γ] (e 1)) (![α, β, γ] (e 2)) where
  counts i j := D.counts i (e j)
  positive := ⟨D.angle_pos (e 0), D.angle_pos (e 1), D.angle_pos (e 2)⟩
  angle_sum := by
    have h := sum_three_permuted (![α, β, γ] : Fin 3 → ℚ) e
    simpa [Fin.sum_univ_succ, ← add_assoc, D.angle_sum] using h
  row_pos i := by
    obtain ⟨j, hj⟩ := D.row_pos i
    exact ⟨e.symm j, by simpa using hj⟩
  angle_eq i := by
    simp only [triple_permuted_apply]
    exact (Equiv.sum_comp e (fun j => (D.counts i j : ℝ) *
      (Real.pi * (![α, β, γ] j : ℝ)))).trans (D.angle_eq i)
  conjugate_sum k hk := by
    have hm := rational_angle_modulus_permuted (![α, β, γ] : Fin 3 → ℚ) e
    change 4 * (![α, β, γ] (e 0)).den * (![α, β, γ] (e 1)).den *
      (![α, β, γ] (e 2)).den = 4 * α.den * β.den * γ.den at hm
    rw [hm] at hk
    simp only [triple_permuted_apply, rationalConjugateAngle_permuted]
    exact (Equiv.sum_comp e (fun j => ((∑ i, D.counts i j : ℕ) : ℚ) *
      rationalConjugateAngle α β γ k (![α, β, γ] j))).trans (D.conjugate_sum k hk)

@[simp] theorem RationalCornerData.total_relabelReference (D : RationalCornerData ω α β γ)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (D.relabelReference e).total j = D.total (e j) := rfl

theorem RationalCornerData.conjugate_pos (D : RationalCornerData ω α β γ) (k : ℕ)
    (hk : k.Coprime (4 * α.den * β.den * γ.den)) (j : Fin 3) :
    0 < rationalConjugateAngle α β γ k (![α, β, γ] j) := by
  have hd : (![α, β, γ] j).den ∣ 4 * α.den * β.den * γ.den := by
    fin_cases j
    · exact ⟨4 * β.den * γ.den, by dsimp; ring⟩
    · exact ⟨4 * α.den * γ.den, by dsimp; ring⟩
    · exact ⟨4 * α.den * β.den, by dsimp; ring⟩
  exact rationalConjugateAngle_pos α β γ k _
    (rational_fract_mul_pos_of_coprime _ k (D.angle_pos j) (D.angle_lt_one j)
      (hk.of_dvd_right hd))

theorem RationalCornerData.conjugate_one (D : RationalCornerData ω α β γ) (j : Fin 3) :
    rationalConjugateAngle α β γ 1 (![α, β, γ] j) = ![α, β, γ] j := by
  have hf (i : Fin 3) : Int.fract (![α, β, γ] i) = ![α, β, γ] i :=
    Int.fract_eq_self.mpr ⟨(D.angle_pos i).le, D.angle_lt_one i⟩
  have h0 : Int.fract α = α := hf 0
  have h1 : Int.fract β = β := hf 1
  have h2 : Int.fract γ = γ := hf 2
  simp only [rationalConjugateAngle, Nat.cast_one, one_mul, h0, h1, h2,
    D.angle_sum, if_true, hf]

theorem RationalCornerData.total_angle_eq (D : RationalCornerData ω α β γ) :
    (D.total 0 : ℚ) * α + (D.total 1 : ℚ) * β + (D.total 2 : ℚ) * γ = 1 := by
  have h := D.conjugate_sum 1 (by simp)
  simp only [D.conjugate_one] at h
  simpa [Fin.sum_univ_succ, add_assoc, RationalCornerData.total] using h

theorem RationalCornerData.total_conjugate_lt_one (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) (k : ℕ)
    (hk : k.Coprime (4 * α.den * β.den * γ.den)) :
    (D.total j : ℚ) * rationalConjugateAngle α β γ k (![α, β, γ] j) < 1 := by
  let f (i : Fin 3) : ℚ :=
    (D.total i : ℚ) * rationalConjugateAngle α β γ k (![α, β, γ] i)
  have hn (i : Fin 3) : 0 ≤ f i :=
    mul_nonneg (by positivity) (D.conjugate_pos k hk i).le
  have hp : 0 < f l := mul_pos (by exact_mod_cast hl) (D.conjugate_pos k hk l)
  have hpair : f j + f l ≤ ∑ i : Fin 3, f i :=
    Finset.add_le_sum (fun i _ => hn i) (Finset.mem_univ j) (Finset.mem_univ l) hjl
  have hs : (∑ i : Fin 3, f i) = 1 := D.conjugate_sum k hk
  change f j < 1
  linarith

theorem RationalCornerData.total_unit_bound (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) :
    ∀ k : ℕ, k.Coprime (4 * α.den * β.den * γ.den) →
      (D.total j : ℚ) * Int.fract ((k : ℚ) * ![α, β, γ] j) < 1 ∨
      (D.total j : ℚ) * (1 - Int.fract ((k : ℚ) * ![α, β, γ] j)) < 1 := by
  intro k hk
  have h := D.total_conjugate_lt_one j l hjl hl k hk
  unfold rationalConjugateAngle at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inr h

theorem RationalCornerData.modulus_pos (_D : RationalCornerData ω α β γ) :
    0 < 4 * α.den * β.den * γ.den := by
  have ha := α.den_pos
  have hb := β.den_pos
  have hc := γ.den_pos
  positivity

theorem RationalCornerData.angle_den_dvd_modulus (_D : RationalCornerData ω α β γ) (j : Fin 3) :
    (![α, β, γ] j).den ∣ 4 * α.den * β.den * γ.den := by
  fin_cases j
  · exact ⟨4 * β.den * γ.den, by dsimp; ring⟩
  · exact ⟨4 * α.den * γ.den, by dsimp; ring⟩
  · exact ⟨4 * α.den * β.den, by dsimp; ring⟩

theorem RationalCornerData.total_mul_angle_lt_one (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) :
    (D.total j : ℚ) * ![α, β, γ] j < 1 := by
  simpa only [D.conjugate_one] using D.total_conjugate_lt_one j l hjl hl 1 (by simp)

theorem RationalCornerData.repeated_angle_cases (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) (hj : 3 ≤ D.total j) :
    ![α, β, γ] j = 1 / 4 ∨ ![α, β, γ] j = 1 / 6 ∨
      ![α, β, γ] j = 1 / 10 ∨ ![α, β, γ] j = 3 / 10 := by
  exact rational_unit_bound_angle_cases _ _ _ (D.angle_pos j) D.modulus_pos
    (D.angle_den_dvd_modulus j) hj (D.total_mul_angle_lt_one j l hjl hl)
    (D.total_unit_bound j l hjl hl)

theorem RationalCornerData.repeated_total_le_five (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) : D.total j ≤ 5 := by
  by_cases hj : 3 ≤ D.total j
  · exact rational_unit_bound_multiplicity_le_five _ _ _ (D.angle_pos j) D.modulus_pos
      (D.angle_den_dvd_modulus j) hj (D.total_mul_angle_lt_one j l hjl hl)
      (D.total_unit_bound j l hjl hl)
  · omega

theorem RationalCornerData.repeated_angle_sixth (D : RationalCornerData ω α β γ)
    (j l : Fin 3) (hjl : j ≠ l) (hl : 0 < D.total l) (hj : 4 ≤ D.total j) :
    ![α, β, γ] j = 1 / 6 := by
  exact rational_unit_bound_angle_sixth _ _ _ (D.angle_pos j) D.modulus_pos
    (D.angle_den_dvd_modulus j) hj (D.total_mul_angle_lt_one j l hjl hl)
    (D.total_unit_bound j l hjl hl)

theorem RationalCornerData.two_type_conjugation_identity (D : RationalCornerData ω α β γ)
    (h2 : D.total 2 = 0) : RationalCornerConjugationIdentity α β γ (D.total 0) (D.total 1) := by
  intro k hk
  have h := D.conjugate_sum k hk
  change (∑ j : Fin 3, (D.total j : ℚ) *
    rationalConjugateAngle α β γ k (![α, β, γ] j)) = 1 at h
  simpa [Fin.sum_univ_succ, h2] using h

theorem RationalCornerData.two_type_three_two_impossible (D : RationalCornerData ω α β γ)
    (h0 : D.total 0 = 3) (h1 : D.total 1 = 2) (h2 : D.total 2 = 0) : False := by
  have ha : α = 1 / 4 ∨ α = 1 / 6 ∨ α = 1 / 10 ∨ α = 3 / 10 :=
    D.repeated_angle_cases 0 1 (by decide) (by omega) (by omega)
  have hs := D.total_angle_eq
  rw [h0, h1, h2] at hs
  norm_num at hs
  have hi := D.two_type_conjugation_identity h2
  rw [h0, h1] at hi
  exact rational_three_two_conjugation_impossible α β γ ha hs D.angle_sum hi

theorem RationalCornerData.two_type_five_two_impossible (D : RationalCornerData ω α β γ)
    (h0 : D.total 0 = 5) (h1 : D.total 1 = 2) (h2 : D.total 2 = 0) : False := by
  have ha : α = 1 / 6 := D.repeated_angle_sixth 0 1 (by decide) (by omega) (by omega)
  have hs := D.total_angle_eq
  rw [h0, h1, h2] at hs
  norm_num at hs
  have hi := D.two_type_conjugation_identity h2
  rw [h0, h1] at hi
  exact rational_five_two_conjugation_impossible α β γ ha hs D.angle_sum hi

theorem RationalCornerData.counts_eq_zero_of_total_zero (D : RationalCornerData ω α β γ)
    (j : Fin 3) (hj : D.total j = 0) (i : Fin 3) : D.counts i j = 0 := by
  have h : D.counts i j ≤ D.total j := by
    change D.counts i j ≤ ∑ x : Fin 3, D.counts x j
    exact Finset.single_le_sum (fun x _ => Nat.zero_le (D.counts x j)) (Finset.mem_univ i)
  omega

theorem RationalCornerData.outer_pos (D : RationalCornerData ω α β γ) (i : Fin 3) : 0 < ω i := by
  rw [← D.angle_eq i]
  obtain ⟨j, hj⟩ := D.row_pos i
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (by positivity) (mul_nonneg Real.pi_pos.le
      (by exact_mod_cast (D.angle_pos k).le))
  · exact ⟨j, Finset.mem_univ j, mul_pos (by exact_mod_cast hj)
      (mul_pos Real.pi_pos (by exact_mod_cast D.angle_pos j))⟩

theorem RationalCornerData.outer_sum (D : RationalCornerData ω α β γ) : ∑ i, ω i = Real.pi := by
  have hs : (D.total 0 : ℝ) * (α : ℝ) + (D.total 1 : ℝ) * (β : ℝ) +
      (D.total 2 : ℝ) * (γ : ℝ) = 1 := by exact_mod_cast D.total_angle_eq
  calc
    (∑ i, ω i) = ∑ i, ∑ j : Fin 3, (D.counts i j : ℝ) *
        (Real.pi * (![α, β, γ] j : ℝ)) :=
      Finset.sum_congr rfl (fun i _ => (D.angle_eq i).symm)
    _ = ∑ j : Fin 3, (D.total j : ℝ) * (Real.pi * (![α, β, γ] j : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [RationalCornerData.total, Nat.cast_sum, Finset.sum_mul]
    _ = Real.pi := by
      simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero]
      change (D.total 0 : ℝ) * (Real.pi * (α : ℝ)) +
        ((D.total 1 : ℝ) * (Real.pi * (β : ℝ)) +
          (D.total 2 : ℝ) * (Real.pi * (γ : ℝ))) = Real.pi
      linear_combination Real.pi * hs

theorem RationalCornerData.all_positive_totals_one (D : RationalCornerData ω α β γ)
    (hp : ∀ j : Fin 3, 0 < D.total j) : ∀ j : Fin 3, D.total j = 1 := by
  have hn (j : Fin 3) : 0 ≤ ((D.total j : ℚ) - 1) * ![α, β, γ] j := by
    apply mul_nonneg _ (D.angle_pos j).le
    have hj : (1 : ℚ) ≤ D.total j := by exact_mod_cast hp j
    linarith
  have hs : (∑ j : Fin 3, ((D.total j : ℚ) - 1) * ![α, β, γ] j) = 0 := by
    have he := D.total_angle_eq
    have ha := D.angle_sum
    simp [Fin.sum_univ_succ]
    linear_combination he - ha
  intro j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hs j
    (Finset.mem_univ j)
  have hzero : (D.total j : ℚ) - 1 = 0 :=
    (mul_eq_zero.mp hz).resolve_right (ne_of_gt (D.angle_pos j))
  have he : (D.total j : ℚ) = 1 := by linarith
  exact_mod_cast he

theorem RationalCornerData.permuted_angles_of_all_positive (D : RationalCornerData ω α β γ)
    (hp : ∀ j : Fin 3, 0 < D.total j) :
    PermutedTriple ω (fun j => Real.pi * (![α, β, γ] j : ℝ)) := by
  classical
  obtain ⟨e, he⟩ := corner_matrix_is_permutation D.counts
    (D.all_positive_totals_one hp) D.row_pos
  refine ⟨e.symm, fun j => ?_⟩
  have h := D.angle_eq (e.symm j)
  simp_rw [he] at h
  simpa using h.symm

theorem RationalCornerData.two_type_angle_eq (D : RationalCornerData ω α β γ) (h2 : D.total 2 = 0)
    (i : Fin 3) : ω i = (D.counts i 0 : ℝ) * (Real.pi * (α : ℝ)) +
      (D.counts i 1 : ℝ) * (Real.pi * (β : ℝ)) := by
  have hz := D.counts_eq_zero_of_total_zero 2 h2 i
  have h := D.angle_eq i
  simpa [Fin.sum_univ_succ, hz] using h.symm

theorem RationalCornerData.two_type_row_pos (D : RationalCornerData ω α β γ) (h2 : D.total 2 = 0)
    (i : Fin 3) : 0 < D.counts i 0 + D.counts i 1 := by
  obtain ⟨j, hj⟩ := D.row_pos i
  have hz := D.counts_eq_zero_of_total_zero 2 h2 i
  fin_cases j
  · change 0 < D.counts i 0 at hj
    omega
  · change 0 < D.counts i 1 at hj
    omega
  · change 0 < D.counts i 2 at hj
    omega

theorem RationalCornerData.two_type_total_eq (D : RationalCornerData ω α β γ) (h2 : D.total 2 = 0) :
    (D.total 0 : ℚ) * α + (D.total 1 : ℚ) * β = 1 := by
  simpa [h2] using D.total_angle_eq


end Erdos633
