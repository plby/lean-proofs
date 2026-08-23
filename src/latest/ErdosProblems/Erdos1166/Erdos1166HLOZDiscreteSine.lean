import ErdosProblems.Erdos1166.Erdos1166HLOZSquareSpectral

namespace Erdos1166.KilledGreen

open scoped BigOperators

noncomputable def dirichletCosineSum (L m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (L - 1),
    Real.cos ((Real.pi * (m : ℝ) / (L : ℝ)) * i +
      Real.pi * (m : ℝ) / (L : ℝ))

theorem dirichletCosineSum_even (L t : ℕ) (hL : 2 ≤ L)
    (ht0 : 0 < t) (htL : t < L) :
    dirichletCosineSum L (2 * t) = -1 := by
  let a : ℝ := Real.pi * ((2 * t : ℕ) : ℝ) / (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have ha : a = 2 * Real.pi * (t : ℝ) / (L : ℝ) := by
    dsimp [a]
    push_cast
    ring
  have haHalfPos : 0 < a / 2 := by
    rw [ha]
    positivity
  have haHalfLt : a / 2 < Real.pi := by
    rw [ha]
    have ht : (t : ℝ) < L := by exact_mod_cast htL
    rw [show 2 * Real.pi * (t : ℝ) / (L : ℝ) / 2 =
      Real.pi * (t : ℝ) / (L : ℝ) by ring]
    apply (div_lt_iff₀ hLreal).2
    exact mul_lt_mul_of_pos_left ht Real.pi_pos
  have hsin : Real.sin (a / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi haHalfPos haHalfLt)
  have hsum := Real.sin_mul_sum_cos (L - 1) a a
  have hphaseCos : (((L - 1 : ℕ) : ℝ) - 1) * a / 2 + a =
      (t : ℝ) * Real.pi := by
    norm_num only [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    rw [ha]
    field_simp
    ring
  have hphaseSin : ((L - 1 : ℕ) : ℝ) * a / 2 =
      (t : ℝ) * Real.pi - a / 2 := by
    norm_num only [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    rw [ha]
    field_simp
  change Real.sin (a / 2) * dirichletCosineSum L (2 * t) = _ at hsum
  rw [hphaseCos, hphaseSin, Real.sin_nat_mul_pi_sub,
    Real.cos_nat_mul_pi] at hsum
  have hpow : ((-1 : ℝ) ^ t) * ((-1 : ℝ) ^ t) = 1 := by
    rw [← pow_add]
    simp
  have : Real.sin (a / 2) * dirichletCosineSum L (2 * t) =
      Real.sin (a / 2) * (-1) := by
    calc
      Real.sin (a / 2) * dirichletCosineSum L (2 * t) =
          (-((-1 : ℝ) ^ t * Real.sin (a / 2))) * ((-1 : ℝ) ^ t) := hsum
      _ = -Real.sin (a / 2) * (((-1 : ℝ) ^ t) * ((-1 : ℝ) ^ t)) := by ring
      _ = Real.sin (a / 2) * (-1) := by rw [hpow]; ring
  exact (mul_left_cancel₀ hsin this)

theorem dirichletCosineSum_odd (L t : ℕ) (hL : 2 ≤ L)
    (ht : 2 * t + 1 < 2 * L) :
    dirichletCosineSum L (2 * t + 1) = 0 := by
  let a : ℝ := Real.pi * ((2 * t + 1 : ℕ) : ℝ) / (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have ha : a = Real.pi * (2 * (t : ℝ) + 1) / (L : ℝ) := by
    dsimp [a]
    push_cast
    ring
  have haHalfPos : 0 < a / 2 := by
    rw [ha]
    positivity
  have haHalfLt : a / 2 < Real.pi := by
    rw [ha]
    have hm : (2 * (t : ℝ) + 1) < 2 * (L : ℝ) := by
      exact_mod_cast ht
    rw [show Real.pi * (2 * (t : ℝ) + 1) / (L : ℝ) / 2 =
      Real.pi * (2 * (t : ℝ) + 1) / (2 * (L : ℝ)) by ring]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * L)).2
    exact mul_lt_mul_of_pos_left hm Real.pi_pos
  have hsin : Real.sin (a / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi haHalfPos haHalfLt)
  have hsum := Real.sin_mul_sum_cos (L - 1) a a
  have hphaseCos : (((L - 1 : ℕ) : ℝ) - 1) * a / 2 + a =
      Real.pi / 2 + (t : ℝ) * Real.pi := by
    norm_num only [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    rw [ha]
    field_simp
    ring
  change Real.sin (a / 2) * dirichletCosineSum L (2 * t + 1) = _ at hsum
  rw [hphaseCos, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two] at hsum
  simp only [mul_zero] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hsin

theorem dirichletCosineSum_zero (L : ℕ) :
    dirichletCosineSum L 0 = (L - 1 : ℕ) := by
  simp [dirichletCosineSum]

theorem dirichletCosineSum_of_pos_lt_two_mul
    (L m : ℕ) (hL : 2 ≤ L) (hm0 : 0 < m) (hm : m < 2 * L) :
    dirichletCosineSum L m = if Even m then -1 else 0 := by
  by_cases he : Even m
  · rw [if_pos he]
    rcases he with ⟨t, rfl⟩
    have ht0 : 0 < t := by omega
    have htL : t < L := by omega
    simpa [two_mul] using dirichletCosineSum_even L t hL ht0 htL
  · rw [if_neg he]
    have ho : Odd m := Nat.not_even_iff_odd.mp he
    rcases ho with ⟨t, rfl⟩
    apply dirichletCosineSum_odd L t hL
    omega

theorem dirichletCosineSum_eq_of_even_iff
    (L m n : ℕ) (hL : 2 ≤ L)
    (hm0 : 0 < m) (hm : m < 2 * L)
    (hn0 : 0 < n) (hn : n < 2 * L)
    (hparity : Even m ↔ Even n) :
    dirichletCosineSum L m = dirichletCosineSum L n := by
  rw [dirichletCosineSum_of_pos_lt_two_mul L m hL hm0 hm,
    dirichletCosineSum_of_pos_lt_two_mul L n hL hn0 hn]
  simp only [hparity]

noncomputable def dirichletSineValue (L k j : ℕ) : ℝ :=
  Real.sin (Real.pi * ((k + 1) * (j + 1) : ℕ) / (L : ℝ))

noncomputable def dirichletSineInner (L j q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (L - 1),
    dirichletSineValue L k j * dirichletSineValue L k q

private theorem two_mul_sin_mul_sin (a b : ℝ) :
    2 * (Real.sin a * Real.sin b) =
      Real.cos (a - b) - Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem two_mul_dirichletSineInner_self
    (L j : ℕ) (hL : 2 ≤ L) (hj : j < L - 1) :
    2 * dirichletSineInner L j j = L := by
  have hjL : j + 1 < L := by omega
  calc
    2 * dirichletSineInner L j j =
        ∑ k ∈ Finset.range (L - 1),
          2 * (dirichletSineValue L k j *
            dirichletSineValue L k j) := by
      unfold dirichletSineInner
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (L - 1),
        (Real.cos (0 : ℝ) -
          Real.cos ((Real.pi * ((2 * (j + 1) : ℕ) : ℝ) / (L : ℝ)) * k +
            Real.pi * ((2 * (j + 1) : ℕ) : ℝ) / (L : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold dirichletSineValue
      rw [two_mul_sin_mul_sin]
      have hzero :
          Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L -
              Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L = 0 := by ring
      have hsum :
          Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L +
              Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L =
            Real.pi * (↑(2 * (j + 1)) : ℝ) / ↑L * ↑k +
              Real.pi * (↑(2 * (j + 1)) : ℝ) / ↑L := by
        push_cast
        ring
      rw [hzero, hsum]
    _ = (L - 1 : ℕ) - dirichletCosineSum L (2 * (j + 1)) := by
      rw [Finset.sum_sub_distrib, dirichletCosineSum]
      simp
    _ = L := by
      rw [dirichletCosineSum_even L (j + 1) hL (by omega) hjL]
      norm_num only [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one,
        Nat.cast_ofNat]
      ring

theorem two_mul_dirichletSineInner_eq_zero_of_lt
    (L j q : ℕ) (hL : 2 ≤ L) (_hj : j < L - 1)
    (hq : q < L - 1) (hjq : j < q) :
    2 * dirichletSineInner L j q = 0 := by
  have hdiff0 : 0 < q - j := by omega
  have hdiff : q - j < 2 * L := by omega
  have hsum0 : 0 < j + q + 2 := by omega
  have hsum : j + q + 2 < 2 * L := by omega
  have hparity : Even (q - j) ↔ Even (j + q + 2) := by
    have heq : j + q + 2 = (q - j) + 2 * (j + 1) := by omega
    rw [heq, Nat.even_add]
    simp
  have hcos := dirichletCosineSum_eq_of_even_iff
    L (q - j) (j + q + 2) hL hdiff0 hdiff hsum0 hsum hparity
  calc
    2 * dirichletSineInner L j q =
        ∑ k ∈ Finset.range (L - 1),
          2 * (dirichletSineValue L k j *
            dirichletSineValue L k q) := by
      unfold dirichletSineInner
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (L - 1),
        (Real.cos
            ((Real.pi * ((q - j : ℕ) : ℝ) / (L : ℝ)) * k +
              Real.pi * ((q - j : ℕ) : ℝ) / (L : ℝ)) -
          Real.cos
            ((Real.pi * ((j + q + 2 : ℕ) : ℝ) / (L : ℝ)) * k +
              Real.pi * ((j + q + 2 : ℕ) : ℝ) / (L : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold dirichletSineValue
      rw [two_mul_sin_mul_sin]
      have hsub :
          Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L -
              Real.pi * (↑((k + 1) * (q + 1)) : ℝ) / ↑L =
            -(Real.pi * (↑(q - j) : ℝ) / ↑L * ↑k +
              Real.pi * (↑(q - j) : ℝ) / ↑L) := by
        norm_num only [Nat.cast_sub (by omega : j ≤ q), Nat.cast_add,
          Nat.cast_one, Nat.cast_mul]
        ring
      have hadd :
          Real.pi * (↑((k + 1) * (j + 1)) : ℝ) / ↑L +
              Real.pi * (↑((k + 1) * (q + 1)) : ℝ) / ↑L =
            Real.pi * (↑(j + q + 2) : ℝ) / ↑L * ↑k +
              Real.pi * (↑(j + q + 2) : ℝ) / ↑L := by
        push_cast
        ring
      rw [hsub, Real.cos_neg, hadd]
    _ = dirichletCosineSum L (q - j) -
        dirichletCosineSum L (j + q + 2) := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ = 0 := sub_eq_zero.mpr hcos

theorem dirichletSineInner_comm (L j q : ℕ) :
    dirichletSineInner L j q = dirichletSineInner L q j := by
  unfold dirichletSineInner
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem two_mul_dirichletSineInner
    (L j q : ℕ) (hL : 2 ≤ L) (hj : j < L - 1)
    (hq : q < L - 1) :
    2 * dirichletSineInner L j q = if j = q then L else 0 := by
  by_cases heq : j = q
  · subst q
    rw [if_pos rfl]
    exact two_mul_dirichletSineInner_self L j hL hj
  · rw [if_neg heq]
    rcases lt_or_gt_of_ne heq with hjq | hqj
    · simpa using two_mul_dirichletSineInner_eq_zero_of_lt L j q hL hj hq hjq
    · rw [dirichletSineInner_comm]
      simpa using two_mul_dirichletSineInner_eq_zero_of_lt L q j hL hq hj hqj

theorem normalized_dirichletSineInner
    (L j q : ℕ) (hL : 2 ≤ L) (hj : j < L - 1)
    (hq : q < L - 1) :
    (2 / (L : ℝ)) * dirichletSineInner L j q =
      if j = q then 1 else 0 := by
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have h := two_mul_dirichletSineInner L j q hL hj hq
  by_cases heq : j = q
  · rw [if_pos heq] at h ⊢
    calc
      (2 / (L : ℝ)) * dirichletSineInner L j q =
          (2 * dirichletSineInner L j q) / (L : ℝ) := by ring
      _ = (L : ℝ) / (L : ℝ) := by rw [h]
      _ = 1 := div_self hL0
  · rw [if_neg heq] at h ⊢
    norm_num at h
    have hz : dirichletSineInner L j q = 0 := by linarith
    rw [hz]
    ring

/-! ## Coordinate bridge to the square modes -/

def squareCoordinateIndex (R : ℕ) (a : ℤ) : ℕ :=
  Int.toNat (a + (R : ℤ))

noncomputable def squareCoordinateSine
    (R : ℕ) (k : Fin (2 * R + 1)) (a : ℤ) : ℝ :=
  Real.sin (squareSineAngle R k * (a : ℝ) +
    squareSineAngle R k * (R + 1 : ℝ))

theorem squareCoordinateIndex_lt
    {R : ℕ} {a : ℤ} (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ)) :
    squareCoordinateIndex R a < 2 * R + 1 := by
  unfold squareCoordinateIndex
  rw [Int.toNat_lt]
  · norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega
  · omega

theorem squareCoordinateIndex_add_one_cast
    {R : ℕ} {a : ℤ} (hal : -(R : ℤ) ≤ a) :
    ((squareCoordinateIndex R a + 1 : ℕ) : ℝ) =
      (a : ℝ) + (R + 1 : ℝ) := by
  have hnonneg : 0 ≤ a + (R : ℤ) := by omega
  have hInt : ((squareCoordinateIndex R a + 1 : ℕ) : ℤ) =
      a + (R : ℤ) + 1 := by
    unfold squareCoordinateIndex
    rw [Int.natCast_add, Int.natCast_one, Int.toNat_of_nonneg hnonneg]
  have hReal : ((squareCoordinateIndex R a + 1 : ℕ) : ℝ) =
      (a : ℝ) + (R : ℝ) + 1 := by exact_mod_cast hInt
  convert hReal using 1
  ring

theorem squareCoordinateSine_eq_dirichletSineValue
    {R : ℕ} {a : ℤ} (hal : -(R : ℤ) ≤ a)
    (k : Fin (2 * R + 1)) :
    squareCoordinateSine R k a =
      dirichletSineValue (2 * (R + 1)) k (squareCoordinateIndex R a) := by
  unfold squareCoordinateSine dirichletSineValue squareSineAngle
  push_cast
  have hi := squareCoordinateIndex_add_one_cast hal
  norm_num only [Nat.cast_add, Nat.cast_one] at hi
  rw [hi]
  congr 1
  ring

theorem squareCoordinateIndex_eq_iff
    {R : ℕ} {a b : ℤ} (hal : -(R : ℤ) ≤ a) (hbl : -(R : ℤ) ≤ b) :
    squareCoordinateIndex R a = squareCoordinateIndex R b ↔ a = b := by
  constructor
  · intro h
    have ha := squareCoordinateIndex_add_one_cast hal
    have hb := squareCoordinateIndex_add_one_cast hbl
    rw [h] at ha
    exact_mod_cast (by linarith [ha, hb] : (a : ℝ) = b)
  · exact congrArg _

theorem normalized_squareCoordinateSineInner
    {R : ℕ} {a b : ℤ}
    (hal : -(R : ℤ) ≤ a) (hau : a ≤ (R : ℤ))
    (hbl : -(R : ℤ) ≤ b) (hbu : b ≤ (R : ℤ)) :
    (2 / (2 * (R + 1 : ℝ))) *
        ∑ k : Fin (2 * R + 1),
          squareCoordinateSine R k a * squareCoordinateSine R k b =
      if a = b then 1 else 0 := by
  let ia := squareCoordinateIndex R a
  let ib := squareCoordinateIndex R b
  have hia : ia < 2 * (R + 1) - 1 := by
    dsimp only [ia]
    have := squareCoordinateIndex_lt hal hau
    omega
  have hib : ib < 2 * (R + 1) - 1 := by
    dsimp only [ib]
    have := squareCoordinateIndex_lt hbl hbu
    omega
  have horth := normalized_dirichletSineInner
    (2 * (R + 1)) ia ib (by omega) hia hib
  have hsum :
      (∑ k : Fin (2 * R + 1),
          squareCoordinateSine R k a * squareCoordinateSine R k b) =
        dirichletSineInner (2 * (R + 1)) ia ib := by
    unfold dirichletSineInner
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [squareCoordinateSine_eq_dirichletSineValue hal,
      squareCoordinateSine_eq_dirichletSineValue hbl]
  rw [hsum]
  convert horth using 1
  · norm_num
  · simp only [ia, ib, squareCoordinateIndex_eq_iff hal hbl]

theorem squareSineMode_eq_coordinate_product
    (R : ℕ) (k l : Fin (2 * R + 1)) (x : Site) :
    squareSineMode R k l x =
      squareCoordinateSine R k x.1 * squareCoordinateSine R l x.2 := by
  rfl

/-- The two-dimensional finite discrete-sine completeness relation on the
square. -/
theorem squareSineMode_completeness
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
            squareSineMode R k l z * squareSineMode R k l x =
      if z = x then 1 else 0 := by
  rcases z with ⟨z₁, z₂⟩
  rcases x with ⟨x₁, x₂⟩
  rcases Finset.mem_product.mp hz with ⟨hz₁, hz₂⟩
  rcases Finset.mem_product.mp hx with ⟨hx₁, hx₂⟩
  rcases Finset.mem_Icc.mp hz₁ with ⟨hz₁l, hz₁u⟩
  rcases Finset.mem_Icc.mp hz₂ with ⟨hz₂l, hz₂u⟩
  rcases Finset.mem_Icc.mp hx₁ with ⟨hx₁l, hx₁u⟩
  rcases Finset.mem_Icc.mp hx₂ with ⟨hx₂l, hx₂u⟩
  let A : ℝ := ∑ k : Fin (2 * R + 1),
    squareCoordinateSine R k z₁ * squareCoordinateSine R k x₁
  let B : ℝ := ∑ l : Fin (2 * R + 1),
    squareCoordinateSine R l z₂ * squareCoordinateSine R l x₂
  have hA : (2 / (2 * (R + 1 : ℝ))) * A =
      if z₁ = x₁ then 1 else 0 := by
    exact normalized_squareCoordinateSineInner hz₁l hz₁u hx₁l hx₁u
  have hB : (2 / (2 * (R + 1 : ℝ))) * B =
      if z₂ = x₂ then 1 else 0 := by
    exact normalized_squareCoordinateSineInner hz₂l hz₂u hx₂l hx₂u
  have hfactor :
      (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          squareSineMode R k l (z₁, z₂) *
            squareSineMode R k l (x₁, x₂)) = A * B := by
    simp_rw [squareSineMode_eq_coordinate_product]
    dsimp only [A, B]
    calc
      (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          (squareCoordinateSine R k z₁ * squareCoordinateSine R l z₂) *
            (squareCoordinateSine R k x₁ * squareCoordinateSine R l x₂)) =
          ∑ k : Fin (2 * R + 1),
            (squareCoordinateSine R k z₁ * squareCoordinateSine R k x₁) *
              ∑ l : Fin (2 * R + 1),
                squareCoordinateSine R l z₂ * squareCoordinateSine R l x₂ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = _ := by rw [Finset.sum_mul]
  rw [hfactor]
  have hscale :
      (4 / (2 * (R + 1 : ℝ)) ^ 2) * (A * B) =
        ((2 / (2 * (R + 1 : ℝ))) * A) *
          ((2 / (2 * (R + 1 : ℝ))) * B) := by
    field_simp
    ring
  rw [hscale, hA, hB]
  by_cases h₁ : z₁ = x₁ <;> by_cases h₂ : z₂ = x₂ <;>
    simp [h₁, h₂]

theorem squareSpectralGreenCandidate_eq_diskGreen_toReal
    (R : ℕ) {z : Site} (hz : z ∈ squareDisk R) :
    ∀ x ∈ squareDisk R,
      squareSpectralGreenCandidate R z x = (diskGreen R z x).toReal := by
  apply squareSpectralGreenCandidate_eq_diskGreen_toReal_of_completeness
  intro x hx
  exact squareSineMode_completeness R hz hx

/-- Exact cancellation-preserving Fourier formula for a target-variable
edge gradient of the killed Green kernel.  This is the finite signed sum to
which the remaining HLOZ corner-robust estimate must be applied. -/
theorem diskGreen_toReal_target_edge_sub_eq_signed_sine_sum
    {R : ℕ} {z x : Site} (hz : z ∈ squareDisk R)
    (e : Direction) (hx : x ∈ squareDisk R)
    (hxe : x + directionStep e ∈ squareDisk R) :
    (diskGreen R z (x + directionStep e)).toReal -
        (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          (squareSineMode R k l z / squareSineEigenvalue R k l) *
            (squareSineMode R k l (x + directionStep e) -
              squareSineMode R k l x) := by
  rw [← squareSpectralGreenCandidate_eq_diskGreen_toReal R hz _ hxe,
    ← squareSpectralGreenCandidate_eq_diskGreen_toReal R hz _ hx]
  exact squareSpectralGreenCandidate_edge_sub R z x e

/-- Exact signed sine expansion for the positive reference denominator in
the predecessor-column estimate. -/
theorem diskGreen_toReal_eq_signed_sine_sum
    {R : ℕ} {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          (squareSineMode R k l z / squareSineEigenvalue R k l) *
            squareSineMode R k l x := by
  rw [← squareSpectralGreenCandidate_eq_diskGreen_toReal R hz x hx]
  rfl

end Erdos1166.KilledGreen
