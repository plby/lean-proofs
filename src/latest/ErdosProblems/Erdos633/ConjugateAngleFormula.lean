import ErdosProblems.Erdos633.FieldAngleSquares
import ErdosProblems.Erdos633.RationalConjugateObstructions

/-!
# Recovering conjugate angles from cosine squares

Squared cosines determine the three labelled angles of a nondegenerate
triangle once positivity and the angle sum are imposed. Fractional residues
are therefore used together or complemented together. The cyclotomic
embedding supplying the cosine-square identities remains separate.
-/

namespace Erdos633

open scoped BigOperators

theorem cos_sq_pi_fract (x : ℝ) :
    Real.cos (Real.pi * Int.fract x) ^ 2 = Real.cos (Real.pi * x) ^ 2 := by
  have heq : Real.pi * Int.fract x = Real.pi * x - (⌊x⌋ : ℝ) * Real.pi := by
    rw [Int.fract]
    ring
  rw [heq, Real.cos_sub_int_mul_pi, mul_pow]
  have hsign : ((-1 : ℝ) ^ (⌊x⌋ : ℤ)) ^ 2 = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  rw [hsign, one_mul]

theorem cos_sq_pi_rat_fract (x : ℚ) :
    Real.cos (Real.pi * ((Int.fract x : ℚ) : ℝ)) ^ 2 =
      Real.cos (Real.pi * (x : ℝ)) ^ 2 := by
  rw [Rat.cast_fract]
  exact cos_sq_pi_fract (x : ℝ)

theorem Triangle.cornerAngles_eq_of_residue_cos_sq (P : Triangle) (r : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < r k) (hlt : ∀ k, r k < 1)
    (hsum : (∑ k : Fin 3, r k) = 1 ∨ (∑ k : Fin 3, r k) = 2)
    (hcos : ∀ k, Real.cos (P.cornerAngle k) ^ 2 = Real.cos (Real.pi * r k) ^ 2) :
    P.cornerAngle = fun k =>
      Real.pi * (if (∑ j : Fin 3, r j) = 1 then r k else 1 - r k) := by
  apply P.cornerAngles_eq_of_cos_sq
  · intro k
    split_ifs <;> apply mul_pos Real.pi_pos
    · exact hpos k
    · linarith [hlt k]
  · intro k
    split_ifs <;> nlinarith [Real.pi_pos, hpos k, hlt k]
  · rcases hsum with hs | hs
    · simp [hs, ← Finset.mul_sum]
    · norm_num [hs, ← Finset.mul_sum, Finset.sum_sub_distrib]
  · intro k
    split_ifs
    · exact hcos k
    · rw [mul_sub, mul_one, Real.cos_pi_sub, neg_sq]
      exact hcos k

theorem rationalConjugateAngle_cos_sq (α β γ : ℚ) (k : ℕ) (θ : ℚ) :
    Real.cos (Real.pi * (rationalConjugateAngle α β γ k θ : ℝ)) ^ 2 =
      Real.cos (Real.pi * ((k : ℝ) * θ)) ^ 2 := by
  unfold rationalConjugateAngle
  split_ifs
  · simpa only [Rat.cast_mul, Rat.cast_natCast] using cos_sq_pi_rat_fract ((k : ℚ) * θ)
  · push_cast
    rw [mul_sub, mul_one, Real.cos_pi_sub, neg_sq]
    exact cos_sq_pi_fract ((k : ℝ) * θ)

theorem rationalConjugateAngle_pos (α β γ : ℚ) (k : ℕ) (θ : ℚ)
    (h : 0 < Int.fract ((k : ℚ) * θ)) : 0 < rationalConjugateAngle α β γ k θ := by
  unfold rationalConjugateAngle
  split_ifs
  · exact h
  · linarith [Int.fract_lt_one ((k : ℚ) * θ)]

theorem rationalConjugateAngle_lt_one (α β γ : ℚ) (k : ℕ) (θ : ℚ)
    (h : 0 < Int.fract ((k : ℚ) * θ)) : rationalConjugateAngle α β γ k θ < 1 := by
  unfold rationalConjugateAngle
  split_ifs
  · exact Int.fract_lt_one _
  · linarith

theorem rational_mul_nat_den_of_coprime (θ : ℚ) (k : ℕ) (hk : k.Coprime θ.den) :
    ((k : ℚ) * θ).den = θ.den := by
  have hc : (k * θ.num.natAbs).Coprime θ.den := hk.mul_left θ.reduced
  simp [Rat.mul_den, Int.natAbs_mul, hc.gcd_eq_one]

theorem rational_fract_mul_pos_of_coprime (θ : ℚ) (k : ℕ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hk : k.Coprime θ.den) :
    0 < Int.fract ((k : ℚ) * θ) := by
  have hden : θ.den ≠ 1 := by
    intro h
    have he := Rat.coe_int_num_of_den_eq_one h
    rw [← he] at hθ hθ1
    have hn0 : 0 < θ.num := by exact_mod_cast hθ
    have hn1 : θ.num < 1 := by exact_mod_cast hθ1
    omega
  have hne : Int.fract ((k : ℚ) * θ) ≠ 0 := by
    intro hz
    have he : (k : ℚ) * θ = (⌊(k : ℚ) * θ⌋ : ℚ) := by
      rw [Int.fract] at hz
      linarith
    have hd := congrArg Rat.den he
    rw [rational_mul_nat_den_of_coprime θ k hk, Rat.den_intCast] at hd
    exact hden hd
  exact lt_of_le_of_ne (Int.fract_nonneg _) hne.symm

theorem rational_fract_sum_one_or_two (α β γ : ℚ) (k : ℕ)
    (hsum : α + β + γ = 1)
    (ha : 0 < Int.fract ((k : ℚ) * α))
    (hb : 0 < Int.fract ((k : ℚ) * β))
    (hc : 0 < Int.fract ((k : ℚ) * γ)) :
    Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
      Int.fract ((k : ℚ) * γ) = 1 ∨
      Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
      Int.fract ((k : ℚ) * γ) = 2 := by
  let z : ℤ := (k : ℤ) - ⌊(k : ℚ) * α⌋ - ⌊(k : ℚ) * β⌋ - ⌊(k : ℚ) * γ⌋
  have hz : Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
      Int.fract ((k : ℚ) * γ) = (z : ℚ) := by
    simp only [Int.fract, z, Int.cast_sub, Int.cast_natCast]
    linear_combination (k : ℚ) * hsum
  have hz0 : (0 : ℚ) < z := by linarith
  have hz3 : (z : ℚ) < 3 := by
    linarith [Int.fract_lt_one ((k : ℚ) * α), Int.fract_lt_one ((k : ℚ) * β),
      Int.fract_lt_one ((k : ℚ) * γ)]
  have hz0' : 0 < z := by exact_mod_cast hz0
  have hz3' : z < 3 := by exact_mod_cast hz3
  have hcases : z = 1 ∨ z = 2 := by omega
  rcases hcases with h | h
  · left
    simpa only [h, Int.cast_one] using hz
  · right
    simpa only [h, Int.cast_ofNat] using hz

theorem rational_angle_unit_residue_data (α β γ : ℚ) (k : ℕ)
    (hpos : 0 < α ∧ 0 < β ∧ 0 < γ) (hsum : α + β + γ = 1)
    (hk : k.Coprime (4 * α.den * β.den * γ.den)) :
    (∀ θ ∈ ({α, β, γ} : Set ℚ), 0 < Int.fract ((k : ℚ) * θ)) ∧
      (Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
          Int.fract ((k : ℚ) * γ) = 1 ∨
        Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
          Int.fract ((k : ℚ) * γ) = 2) := by
  have hka : k.Coprime α.den := hk.of_dvd_right ⟨4 * β.den * γ.den, by ring⟩
  have hkb : k.Coprime β.den := hk.of_dvd_right ⟨4 * α.den * γ.den, by ring⟩
  have hkc : k.Coprime γ.den := hk.of_dvd_right ⟨4 * α.den * β.den, by ring⟩
  have ha := rational_fract_mul_pos_of_coprime α k hpos.1 (by linarith [hpos.2.1, hpos.2.2]) hka
  have hb := rational_fract_mul_pos_of_coprime β k hpos.2.1 (by linarith [hpos.1, hpos.2.2]) hkb
  have hc := rational_fract_mul_pos_of_coprime γ k hpos.2.2 (by linarith [hpos.1, hpos.2.1]) hkc
  refine ⟨?_, rational_fract_sum_one_or_two α β γ k hsum ha hb hc⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem Triangle.cornerAngles_eq_rationalConjugates (P : Triangle)
    (α β γ : ℚ) (k : ℕ)
    (hpos : ∀ θ ∈ ({α, β, γ} : Set ℚ), 0 < Int.fract ((k : ℚ) * θ))
    (hsum : Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
      Int.fract ((k : ℚ) * γ) = 1 ∨
      Int.fract ((k : ℚ) * α) + Int.fract ((k : ℚ) * β) +
      Int.fract ((k : ℚ) * γ) = 2)
    (hcos : ∀ j : Fin 3, Real.cos (P.cornerAngle j) ^ 2 =
      Real.cos (Real.pi * ((k : ℝ) * (![α, β, γ] j : ℝ))) ^ 2) :
    P.cornerAngle = fun j =>
      Real.pi * (rationalConjugateAngle α β γ k (![α, β, γ] j) : ℝ) := by
  apply P.cornerAngles_eq_of_cos_sq
  · intro j
    have hm : ![α, β, γ] j ∈ ({α, β, γ} : Set ℚ) := by fin_cases j <;> simp
    apply mul_pos Real.pi_pos
    exact_mod_cast rationalConjugateAngle_pos α β γ k _ (hpos _ hm)
  · intro j
    have hm : ![α, β, γ] j ∈ ({α, β, γ} : Set ℚ) := by fin_cases j <;> simp
    have hl : (rationalConjugateAngle α β γ k (![α, β, γ] j) : ℝ) < 1 := by
      exact_mod_cast rationalConjugateAngle_lt_one α β γ k _ (hpos _ hm)
    nlinarith [Real.pi_pos]
  · rw [← Finset.mul_sum]
    have hs := rationalConjugateAngle_sum α β γ k hsum
    have hsR : (rationalConjugateAngle α β γ k α : ℝ) +
        (rationalConjugateAngle α β γ k β : ℝ) +
        (rationalConjugateAngle α β γ k γ : ℝ) = 1 := by exact_mod_cast hs
    simp [Fin.sum_univ_succ, ← add_assoc, hsR]
  · intro j
    rw [rationalConjugateAngle_cos_sq]
    exact hcos j

theorem Triangle.rational_angle_triple_data (P : Triangle) (α β γ : ℚ)
    (hangle : ∀ j : Fin 3, P.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ)) :
    (0 < α ∧ 0 < β ∧ 0 < γ) ∧ α + β + γ = 1 := by
  have hpos (j : Fin 3) : 0 < ![α, β, γ] j := by
    have h := P.cornerAngle_pos j
    rw [hangle j] at h
    have hR : (0 : ℝ) < (![α, β, γ] j : ℝ) :=
      pos_of_mul_pos_right h Real.pi_pos.le
    exact_mod_cast hR
  refine ⟨⟨hpos 0, hpos 1, hpos 2⟩, ?_⟩
  have hs := P.sum_cornerAngle
  simp_rw [hangle] at hs
  norm_num [Fin.sum_univ_succ] at hs
  have hsR : (α : ℝ) + β + γ = 1 := by nlinarith [Real.pi_pos]
  exact_mod_cast hsR

theorem FieldTriangle.realize_rational_conjugate_angles {F : Type*} [Field F]
    (P : FieldTriangle F) (σ : F →+* ℝ) (α β γ : ℚ) (k : ℕ)
    (hpos : 0 < α ∧ 0 < β ∧ 0 < γ) (hsum : α + β + γ = 1)
    (hk : k.Coprime (4 * α.den * β.den * γ.den))
    (hcos : ∀ j : Fin 3, σ (P.cosineSquare j) =
      Real.cos (Real.pi * ((k : ℝ) * (![α, β, γ] j : ℝ))) ^ 2) :
    (P.realize σ).cornerAngle = fun j =>
      Real.pi * (rationalConjugateAngle α β γ k (![α, β, γ] j) : ℝ) := by
  obtain ⟨hp, hs⟩ := rational_angle_unit_residue_data α β γ k hpos hsum hk
  apply (P.realize σ).cornerAngles_eq_rationalConjugates α β γ k hp hs
  intro j
  rw [← P.map_cosineSquare σ j]
  exact hcos j

/-- The residue equation uses the counts of the original geometric tiling.
Only the algebraic action of the supplied embedding on cosine squares is
still an input; preservation of the tiling and of its labels is proved. -/
theorem CongruentTiling.rational_conjugate_outer_total
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (σ : F →+* ℝ)
    (hP : P.CoordinatesIn F) (hR : R.CoordinatesIn F)
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F)
    (α β γ : ℚ) (k : ℕ)
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ))
    (hk : k.Coprime (4 * α.den * β.den * γ.den))
    (hcos : ∀ j : Fin 3, σ ((R.toFieldTriangle F hR).cosineSquare j) =
      Real.cos (Real.pi * ((k : ℝ) * (![α, β, γ] j : ℝ))) ^ 2) :
    (∑ j : Fin 3, (T.outerCornerCount j : ℚ) *
      rationalConjugateAngle α β γ k (![α, β, γ] j)) = 1 := by
  obtain ⟨hp, hs⟩ := R.rational_angle_triple_data α β γ hangle
  have heq := (R.toFieldTriangle F hR).realize_rational_conjugate_angles σ
    α β γ k hp hs hk hcos
  have ht := T.conjugate_outer_angle_total F σ hP hR hQ
  rw [heq] at ht
  have hm : Real.pi * (∑ j : Fin 3, (T.outerCornerCount j : ℝ) *
      (rationalConjugateAngle α β γ k (![α, β, γ] j) : ℝ)) = Real.pi := by
    rw [Finset.mul_sum]
    convert ht using 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreal : (∑ j : Fin 3, (T.outerCornerCount j : ℝ) *
      (rationalConjugateAngle α β γ k (![α, β, γ] j) : ℝ)) = 1 := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hreal

theorem CongruentTiling.rational_corner_conjugation_identity
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (hP : P.CoordinatesIn F) (hR : R.CoordinatesIn F)
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F)
    (α β γ : ℚ)
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ))
    (hg : T.outerCornerCount 2 = 0)
    (hemb : ∀ k : ℕ, k.Coprime (4 * α.den * β.den * γ.den) →
      ∃ σ : F →+* ℝ, ∀ j : Fin 3, σ ((R.toFieldTriangle F hR).cosineSquare j) =
        Real.cos (Real.pi * ((k : ℝ) * (![α, β, γ] j : ℝ))) ^ 2) :
    RationalCornerConjugationIdentity α β γ (T.outerCornerCount 0) (T.outerCornerCount 1) := by
  intro k hk
  obtain ⟨σ, hσ⟩ := hemb k hk
  have h := T.rational_conjugate_outer_total F σ hP hR hQ α β γ k hangle hk hσ
  simpa [Fin.sum_univ_succ, hg] using h

end Erdos633
