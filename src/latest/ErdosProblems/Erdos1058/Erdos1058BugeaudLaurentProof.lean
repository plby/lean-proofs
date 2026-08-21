import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentParameters

noncomputable section

namespace Erdos1058.BugeaudLaurent

theorem coprime_odd_exponent_modulus_lt_parameter_product
    {p q a b T : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hbodd : Odd b)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T])
    (hfit :
      let M := parameterMaximum p q a b
      let u := Real.log p / Real.log 2
      let v := Real.log q / Real.log 2
      let L := blParameterL M
      let K := blParameterK M u v
      let m₂ := (K - 1) * L
      boxR m₂ u v ≤ a ∨ boxS m₂ u v ≤ b) :
    T < 3 * (blParameterK (parameterMaximum p q a b)
      (Real.log p / Real.log 2) (Real.log q / Real.log 2) *
        blParameterL (parameterMaximum p q a b)) := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let R₁ := boxR L u v
  let R₂ := boxR m₂ u v
  let S₁ := boxS L u v
  let S₂ := boxS m₂ u v
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hK : 3 ≤ K := blParameterK_ge_three hM hu hv
  have hL : 2 ≤ L := (blParameterL_ge_fifteen hM).trans' (by norm_num)
  have hR₁ : 0 < R₁ := boxR_pos L u v
  have hR₂ : 0 < R₂ := boxR_pos m₂ u v
  have hS₁ : 0 < S₁ := boxS_pos L u v
  have hS₂ : 0 < S₂ := boxS_pos m₂ u v
  have hsize₁ : L ≤ R₁ * S₁ := by
    exact (box_product_gt (m := L) (lt_of_lt_of_le (by norm_num) hu)
      (lt_of_lt_of_le (by norm_num) hv)).le
  have hsize₂ : (K - 1) * L < R₂ * S₂ := by
    exact box_product_gt (m := m₂) (lt_of_lt_of_le (by norm_num) hu)
      (lt_of_lt_of_le (by norm_num) hv)
  have hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val) := by
    dsimp only at hfit
    rcases hfit with hRa | hSb
    · exact linear_box_injective_of_R_le ha hab hRa
    · exact linear_box_injective_of_S_le hb hab hSb
  by_contra hnot
  have hT : 3 * (K * L) ≤ T := by
    change ¬T < 3 * (K * L) at hnot
    omega
  obtain ⟨c, t, hbc⟩ := exists_odd_exponent_inverse b T hbodd
  have hcriterion := prime_parameter_simple_criterion hp hq hpq hpodd ha hb
  dsimp only at hcriterion
  change
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log (((b * (R₁ + R₂ - 1) +
            a * (S₁ + S₂ - 1) : ℕ)) : ℝ) -
            Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((R₁ + R₂ - 1 - 1 : ℕ) * Real.log p +
            (S₁ + S₂ - 1 : ℕ) * Real.log q) <
      3 * K * (L - 1 : ℕ) * Real.log 2 at hcriterion
  push_cast [Nat.cast_sub (by omega : 1 ≤ R₁ + R₂),
    Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)] at hcriterion
  apply interpolation_simple_criterion_boxes hK hL hR₁ hR₂ hS₁ hS₂
    hp hq hpq.ne hpodd hqodd ha hb hsize₁ hsize₂ hinj hT hbc hrel
  push_cast [Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)]
  exact hcriterion

theorem factorization_two_lt_parameterK_of_collision
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpodd : Odd p)
    (ha : 0 < a) (hb : 0 < b)
    (hlarge :
      let M := parameterMaximum p q a b
      let u := Real.log p / Real.log 2
      let v := Real.log q / Real.log 2
      let L := blParameterL M
      let K := blParameterK M u v
      let m₂ := (K - 1) * L
      a < boxR m₂ u v ∧ b < boxS m₂ u v) :
    (p ^ a * q ^ b - 1).factorization 2 <
      blParameterK (parameterMaximum p q a b)
        (Real.log p / Real.log 2) (Real.log q / Real.log 2) := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let R₁ := boxR L u v
  let R₂ := boxR m₂ u v
  let S₁ := boxS L u v
  let S₂ := boxS m₂ u v
  let R := R₁ + R₂ - 1
  let S := S₁ + S₂ - 1
  let N := p ^ a * q ^ b
  let z := N - 1
  let T := z.factorization 2
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hR₁pos : 0 < R₁ := boxR_pos L u v
  have hR₂pos : 0 < R₂ := boxR_pos m₂ u v
  have hS₁pos : 0 < S₁ := boxS_pos L u v
  have hS₂pos : 0 < S₂ := boxS_pos m₂ u v
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hSpos : 0 < S := by dsimp only [S]; omega
  have htotal := parameter_box_height_plus_u_lt_K hM hu hv
  dsimp only at htotal
  change (R : ℝ) * u + (S : ℝ) * v < K at htotal
  dsimp only at hlarge
  rcases hlarge with ⟨haR, hbS⟩
  have hR₂R : R₂ ≤ R := by dsimp only [R]; omega
  have hS₂S : S₂ ≤ S := by dsimp only [S]; omega
  have hexponents : (a : ℝ) * u + (b : ℝ) * v < K := by
    have haReal : (a : ℝ) < R₂ := by exact_mod_cast haR
    have hbReal : (b : ℝ) < S₂ := by exact_mod_cast hbS
    have h1 := mul_lt_mul_of_pos_right haReal hu0
    have h2 := mul_lt_mul_of_pos_right hbReal hv0
    have hRReal : (R₂ : ℝ) ≤ R := by exact_mod_cast hR₂R
    have hSReal : (S₂ : ℝ) ≤ S := by exact_mod_cast hS₂S
    have h3 := mul_le_mul_of_nonneg_right hRReal hu0.le
    have h4 := mul_le_mul_of_nonneg_right hSReal hv0.le
    linarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hdu : Real.log 2 * u = Real.log p := by
    dsimp only [u]
    field_simp
  have hdv : Real.log 2 * v = Real.log q := by
    dsimp only [v]
    field_simp
  have hlogNupper : (a : ℝ) * Real.log p + (b : ℝ) * Real.log q <
      (K : ℝ) * Real.log 2 := by
    rw [← hdu, ← hdv]
    nlinarith [mul_lt_mul_of_pos_left hexponents hd]
  have hNgt : 1 < N := by
    dsimp only [N]
    have hpPow : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hqPow : 0 < q ^ b := pow_pos hq.pos _
    nlinarith [Nat.mul_le_mul hpPow.le hqPow]
  have hzpos : 0 < z := by dsimp only [z]; omega
  have hdiv : 2 ^ T ∣ z := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hzpos.ne').2 le_rfl
  have hpowle : 2 ^ T ≤ z := Nat.le_of_dvd hzpos hdiv
  have hpowReal : ((2 : ℝ) ^ T) ≤ (z : ℝ) := by exact_mod_cast hpowle
  have hlogLower := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ T) hpowReal
  rw [Real.log_pow] at hlogLower
  have hzN : z < N := by dsimp only [z]; omega
  have hlogzN := Real.strictMonoOn_log (by positivity : (0 : ℝ) < (z : ℝ))
    (by positivity : (0 : ℝ) < (N : ℝ)) (by exact_mod_cast hzN)
  have hlogN : Real.log (N : ℝ) =
      (a : ℝ) * Real.log p + (b : ℝ) * Real.log q := by
    dsimp only [N]
    push_cast
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [Real.log_mul (pow_ne_zero _ hpR) (pow_ne_zero _ hqR),
      Real.log_pow, Real.log_pow]
  rw [hlogN] at hlogzN
  have hTK : (T : ℝ) < K := by
    nlinarith [mul_lt_mul_of_pos_right hlogzN hd]
  exact_mod_cast hTK

theorem factorization_two_add_one_le_parameterK_of_collision
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpodd : Odd p)
    (ha : 0 < a) (hb : 0 < b)
    (hlarge :
      let M := parameterMaximum p q a b
      let u := Real.log p / Real.log 2
      let v := Real.log q / Real.log 2
      let L := blParameterL M
      let K := blParameterK M u v
      let m₂ := (K - 1) * L
      a < boxR m₂ u v ∧ b < boxS m₂ u v) :
    (p ^ a * q ^ b + 1).factorization 2 ≤
      blParameterK (parameterMaximum p q a b)
        (Real.log p / Real.log 2) (Real.log q / Real.log 2) := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let R₁ := boxR L u v
  let R₂ := boxR m₂ u v
  let S₁ := boxS L u v
  let S₂ := boxS m₂ u v
  let R := R₁ + R₂ - 1
  let S := S₁ + S₂ - 1
  let N := p ^ a * q ^ b
  let z := N + 1
  let T := z.factorization 2
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hR₁pos : 0 < R₁ := boxR_pos L u v
  have hR₂pos : 0 < R₂ := boxR_pos m₂ u v
  have hS₁pos : 0 < S₁ := boxS_pos L u v
  have hS₂pos : 0 < S₂ := boxS_pos m₂ u v
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hSpos : 0 < S := by dsimp only [S]; omega
  have htotal := parameter_box_height_plus_u_lt_K hM hu hv
  dsimp only at htotal
  change (R : ℝ) * u + (S : ℝ) * v < K at htotal
  dsimp only at hlarge
  rcases hlarge with ⟨haR, hbS⟩
  have hR₂R : R₂ ≤ R := by dsimp only [R]; omega
  have hS₂S : S₂ ≤ S := by dsimp only [S]; omega
  have hexponents : (a : ℝ) * u + (b : ℝ) * v < K := by
    have haReal : (a : ℝ) < R₂ := by exact_mod_cast haR
    have hbReal : (b : ℝ) < S₂ := by exact_mod_cast hbS
    have h1 := mul_lt_mul_of_pos_right haReal hu0
    have h2 := mul_lt_mul_of_pos_right hbReal hv0
    have hRReal : (R₂ : ℝ) ≤ R := by exact_mod_cast hR₂R
    have hSReal : (S₂ : ℝ) ≤ S := by exact_mod_cast hS₂S
    have h3 := mul_le_mul_of_nonneg_right hRReal hu0.le
    have h4 := mul_le_mul_of_nonneg_right hSReal hv0.le
    linarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdu : Real.log 2 * u = Real.log p := by
    dsimp only [u]
    field_simp
  have hdv : Real.log 2 * v = Real.log q := by
    dsimp only [v]
    field_simp
  have hlogNupper : (a : ℝ) * Real.log p + (b : ℝ) * Real.log q <
      (K : ℝ) * Real.log 2 := by
    rw [← hdu, ← hdv]
    nlinarith [mul_lt_mul_of_pos_left hexponents hd]
  have hNgt : 1 < N := by
    dsimp only [N]
    have hpPow : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hqPow : 0 < q ^ b := pow_pos hq.pos _
    nlinarith [Nat.mul_le_mul hpPow.le hqPow]
  have hzpos : 0 < z := by dsimp only [z]; omega
  have hdiv : 2 ^ T ∣ z := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hzpos.ne').2 le_rfl
  have hpowle : 2 ^ T ≤ z := Nat.le_of_dvd hzpos hdiv
  have hpowReal : ((2 : ℝ) ^ T) ≤ (z : ℝ) := by exact_mod_cast hpowle
  have hlogLower := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ T) hpowReal
  rw [Real.log_pow] at hlogLower
  have hz2N : z ≤ 2 * N := by dsimp only [z]; omega
  have hz2NReal : (z : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hz2N
  have hlogz2N := Real.log_le_log (by positivity : (0 : ℝ) < (z : ℝ))
    hz2NReal
  have hlogN : Real.log (N : ℝ) =
      (a : ℝ) * Real.log p + (b : ℝ) * Real.log q := by
    dsimp only [N]
    push_cast
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [Real.log_mul (pow_ne_zero _ hpR) (pow_ne_zero _ hqR),
      Real.log_pow, Real.log_pow]
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity : (N : ℝ) ≠ 0)]
  rw [hlog2N, hlogN] at hlogz2N
  have hTK : (T : ℝ) < K + 1 := by
    nlinarith [mul_lt_mul_of_pos_right hlogNupper hd]
  have hTKNat : T < K + 1 := by exact_mod_cast hTK
  change T ≤ K
  omega

theorem coprime_odd_second_two_adic_bound
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hbodd : Odd b) :
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let T := (p ^ a * q ^ b - 1).factorization 2
  have hNpos : 0 < p ^ a * q ^ b - 1 := by
    have hpPow : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hqPow : 0 < q ^ b := pow_pos hq.pos _
    have hprod : 1 < p ^ a * q ^ b :=
      hpPow.trans_le (Nat.le_mul_of_pos_right (p ^ a) hqPow)
    omega
  have hdiv : 2 ^ T ∣ p ^ a * q ^ b - 1 := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hNpos.ne').2 le_rfl
  have hrel₀ : p ^ a * q ^ b ≡ 1 [MOD 2 ^ T] := by
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p ^ a * q ^ b)).2 hdiv).symm
  have hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T] := by
    simpa using hrel₀.pow 2
  have hparameter := prime_parameter_product_upper_thirty_five (a := a) (b := b)
    hp hq hpq hpodd
  dsimp only at hparameter
  change (((3 * (K * L) : ℕ) : ℝ)) ≤ _ at hparameter
  by_cases hfit : boxR m₂ u v ≤ a ∨ boxS m₂ u v ≤ b
  · have hT := coprime_odd_exponent_modulus_lt_parameter_product hp hq hpq
      hpodd hqodd ha hb hab hbodd hrel (by simpa only [M, u, v, L, K, m₂] using hfit)
    change T < 3 * (K * L) at hT
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hT.le
    exact hTreal.trans hparameter
  · have hlarge : a < boxR m₂ u v ∧ b < boxS m₂ u v := by omega
    have hT := factorization_two_lt_parameterK_of_collision hp hq hpq hpodd
      ha hb (by simpa only [M, u, v, L, K, m₂] using hlarge)
    change T < K at hT
    have hLpos : 0 < L := by
      have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
      have := blParameterL_ge_fifteen hM
      omega
    have hTKL : T ≤ 3 * (K * L) := by
      have hKle : K ≤ K * L := Nat.le_mul_of_pos_right K hLpos
      have hKLle : K * L ≤ 3 * (K * L) := by omega
      exact hT.le.trans (hKle.trans hKLle)
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hTKL
    exact hTreal.trans hparameter

theorem prime_parameter_simple_criterion_swapped
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (ha : 0 < a) (hb : 0 < b) :
    let M := parameterMaximum p q a b
    let u := Real.log p / Real.log 2
    let v := Real.log q / Real.log 2
    let L := blParameterL M
    let K := blParameterK M u v
    let m₂ := (K - 1) * L
    let R₁ := boxR L v u
    let R₂ := boxR m₂ v u
    let S₁ := boxS L v u
    let S₂ := boxS m₂ v u
    let R := R₁ + R₂ - 1
    let S := S₁ + S₂ - 1
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log ((a * R + b * S : ℕ) : ℝ) - Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((R - 1 : ℕ) * Real.log q + (S : ℕ) * Real.log p) <
      3 * K * (L - 1 : ℕ) * Real.log 2 := by
  dsimp only
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let A₁ := boxR L u v
  let A₂ := boxR m₂ u v
  let B₁ := boxS L u v
  let B₂ := boxS m₂ u v
  let A := A₁ + A₂ - 1
  let B := B₁ + B₂ - 1
  have h := prime_parameter_simple_criterion hp hq hpq hpodd ha hb
  change
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log ((b * A + a * B : ℕ) : ℝ) - Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((A - 1 : ℕ) * Real.log p + (B : ℕ) * Real.log q) <
      3 * K * (L - 1 : ℕ) * Real.log 2 at h
  change
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log ((a * B + b * A : ℕ) : ℝ) - Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((B - 1 : ℕ) * Real.log q + (A : ℕ) * Real.log p) <
      3 * K * (L - 1 : ℕ) * Real.log 2
  have hA₁ : 0 < A₁ := boxR_pos L u v
  have hA₂ : 0 < A₂ := boxR_pos m₂ u v
  have hB₁ : 0 < B₁ := boxS_pos L u v
  have hB₂ : 0 < B₂ := boxS_pos m₂ u v
  have hA : 1 ≤ A := by dsimp only [A]; omega
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hlog : Real.log p < Real.log q :=
    Real.strictMonoOn_log (show (0 : ℝ) < p by exact_mod_cast hp.pos)
      (show (0 : ℝ) < q by exact_mod_cast hq.pos)
      (by exact_mod_cast hpq)
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hL : 2 ≤ L :=
    (blParameterL_ge_fifteen hM).trans' (by norm_num)
  have hLm1 : 0 < L - 1 := by omega
  have hcoef : (0 : ℝ) < 2 * (L - 1 : ℕ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hLm1)
  have hheight :
      ((B - 1 : ℕ) : ℝ) * Real.log q + (A : ℝ) * Real.log p <
        ((A - 1 : ℕ) : ℝ) * Real.log p + (B : ℝ) * Real.log q := by
    rw [Nat.cast_sub hB, Nat.cast_sub hA]
    norm_num
    linarith
  have harg : a * B + b * A = b * A + a * B := by omega
  rw [harg]
  nlinarith [mul_lt_mul_of_pos_left hheight hcoef]

theorem coprime_odd_first_exponent_modulus_lt_parameter_product
    {p q a b T : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (haodd : Odd a)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T])
    (hfit :
      let M := parameterMaximum p q a b
      let u := Real.log p / Real.log 2
      let v := Real.log q / Real.log 2
      let L := blParameterL M
      let K := blParameterK M u v
      let m₂ := (K - 1) * L
      boxR m₂ u v ≤ a ∨ boxS m₂ u v ≤ b) :
    T < 3 * (blParameterK (parameterMaximum p q a b)
      (Real.log p / Real.log 2) (Real.log q / Real.log 2) *
        blParameterL (parameterMaximum p q a b)) := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let R₁ := boxR L v u
  let R₂ := boxR m₂ v u
  let S₁ := boxS L v u
  let S₂ := boxS m₂ v u
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hK : 3 ≤ K := blParameterK_ge_three hM hu hv
  have hL : 2 ≤ L := (blParameterL_ge_fifteen hM).trans' (by norm_num)
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hR₁ : 0 < R₁ := boxR_pos L v u
  have hR₂ : 0 < R₂ := boxR_pos m₂ v u
  have hS₁ : 0 < S₁ := boxS_pos L v u
  have hS₂ : 0 < S₂ := boxS_pos m₂ v u
  have hsize₁ : L ≤ R₁ * S₁ := (box_product_gt (m := L) hv0 hu0).le
  have hsize₂ : (K - 1) * L < R₂ * S₂ := box_product_gt (m := m₂) hv0 hu0
  have hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      a * rs.1.val + b * rs.2.val) := by
    dsimp only at hfit
    rcases hfit with hRa | hSb
    · have hSa : S₂ ≤ a := by simpa only [S₂, boxS, boxR] using hRa
      exact linear_box_injective_of_S_le ha hab.symm hSa
    · have hRb : R₂ ≤ b := by simpa only [R₂, boxR, boxS] using hSb
      exact linear_box_injective_of_R_le hb hab.symm hRb
  by_contra hnot
  have hT : 3 * (K * L) ≤ T := by
    change ¬T < 3 * (K * L) at hnot
    omega
  obtain ⟨c, t, hac⟩ := exists_odd_exponent_inverse a T haodd
  have hrel' : (q ^ b * p ^ a) ^ 2 ≡ 1 [MOD 2 ^ T] := by
    simpa [mul_comm] using hrel
  have hcriterion := prime_parameter_simple_criterion_swapped hp hq hpq hpodd ha hb
  dsimp only at hcriterion
  change
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log (((a * (R₁ + R₂ - 1) + b * (S₁ + S₂ - 1) : ℕ)) : ℝ) -
            Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((R₁ + R₂ - 1 - 1 : ℕ) * Real.log q +
            (S₁ + S₂ - 1 : ℕ) * Real.log p) <
      3 * K * (L - 1 : ℕ) * Real.log 2 at hcriterion
  push_cast [Nat.cast_sub (by omega : 1 ≤ R₁ + R₂),
    Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)] at hcriterion
  apply interpolation_simple_criterion_boxes hK hL hR₁ hR₂ hS₁ hS₂
    hq hp hpq.ne.symm hqodd hpodd hb ha hsize₁ hsize₂ hinj hT hac hrel'
  push_cast [Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)]
  exact hcriterion

theorem coprime_odd_first_two_adic_bound
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (haodd : Odd a) :
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let T := (p ^ a * q ^ b - 1).factorization 2
  have hNpos : 0 < p ^ a * q ^ b - 1 := by
    have hpPow : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hqPow : 0 < q ^ b := pow_pos hq.pos _
    have hprod : 1 < p ^ a * q ^ b :=
      hpPow.trans_le (Nat.le_mul_of_pos_right (p ^ a) hqPow)
    omega
  have hdiv : 2 ^ T ∣ p ^ a * q ^ b - 1 := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hNpos.ne').2 le_rfl
  have hrel₀ : p ^ a * q ^ b ≡ 1 [MOD 2 ^ T] := by
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p ^ a * q ^ b)).2 hdiv).symm
  have hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T] := by
    simpa using hrel₀.pow 2
  have hparameter := prime_parameter_product_upper_thirty_five (a := a) (b := b)
    hp hq hpq hpodd
  dsimp only at hparameter
  change (((3 * (K * L) : ℕ) : ℝ)) ≤ _ at hparameter
  by_cases hfit : boxR m₂ u v ≤ a ∨ boxS m₂ u v ≤ b
  · have hT := coprime_odd_first_exponent_modulus_lt_parameter_product hp hq hpq
      hpodd hqodd ha hb hab haodd hrel (by simpa only [M, u, v, L, K, m₂] using hfit)
    change T < 3 * (K * L) at hT
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hT.le
    exact hTreal.trans hparameter
  · have hlarge : a < boxR m₂ u v ∧ b < boxS m₂ u v := by omega
    have hT := factorization_two_lt_parameterK_of_collision hp hq hpq hpodd
      ha hb (by simpa only [M, u, v, L, K, m₂] using hlarge)
    change T < K at hT
    have hLpos : 0 < L := by
      have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
      have := blParameterL_ge_fifteen hM
      omega
    have hTKL : T ≤ 3 * (K * L) := by
      have hKle : K ≤ K * L := Nat.le_mul_of_pos_right K hLpos
      have hKLle : K * L ≤ 3 * (K * L) := by omega
      exact hT.le.trans (hKle.trans hKLle)
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hTKL
    exact hTreal.trans hparameter

theorem coprime_two_adic_bound
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  rcases b.even_or_odd with hbeven | hbodd
  · have haodd : Odd a := by
      rw [← Nat.coprime_two_right]
      exact hab.coprime_dvd_right hbeven.two_dvd
    exact coprime_odd_first_two_adic_bound hp hq hpq hpodd hqodd
      ha hb hab haodd
  · exact coprime_odd_second_two_adic_bound hp hq hpq hpodd hqodd
      ha hb hab hbodd

theorem coprime_add_one_two_adic_bound
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (((p ^ a * q ^ b + 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let N := p ^ a * q ^ b
  let T := (N + 1).factorization 2
  have hNgt : 1 < N := by
    dsimp only [N]
    have hpPow : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hqPow : 0 < q ^ b := pow_pos hq.pos _
    exact hpPow.trans_le (Nat.le_mul_of_pos_right (p ^ a) hqPow)
  have hpluspos : 0 < N + 1 := by omega
  have hdivplus : 2 ^ T ∣ N + 1 := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hpluspos.ne').2 le_rfl
  have hfactor : N ^ 2 - 1 = (N + 1) * (N - 1) := by
    simpa [pow_two] using (mul_self_tsub_one N)
  have hdivsquare : 2 ^ T ∣ N ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_left hdivplus _
  have hrel : N ^ 2 ≡ 1 [MOD 2 ^ T] := by
    exact ((Nat.modEq_iff_dvd' (one_le_pow₀ hNgt.le)).2 hdivsquare).symm
  have hparameter := prime_parameter_product_upper_thirty_five (a := a) (b := b)
    hp hq hpq hpodd
  dsimp only at hparameter
  change (((3 * (K * L) : ℕ) : ℝ)) ≤ _ at hparameter
  by_cases hfit : boxR m₂ u v ≤ a ∨ boxS m₂ u v ≤ b
  · have hT : T < 3 * (K * L) := by
      rcases b.even_or_odd with hbeven | hbodd
      · have haodd : Odd a := by
          rw [← Nat.coprime_two_right]
          exact hab.coprime_dvd_right hbeven.two_dvd
        exact coprime_odd_first_exponent_modulus_lt_parameter_product hp hq hpq
          hpodd hqodd ha hb hab haodd
          (by simpa only [N] using hrel)
          (by simpa only [M, u, v, L, K, m₂] using hfit)
      · exact coprime_odd_exponent_modulus_lt_parameter_product hp hq hpq
          hpodd hqodd ha hb hab hbodd
          (by simpa only [N] using hrel)
          (by simpa only [M, u, v, L, K, m₂] using hfit)
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hT.le
    exact hTreal.trans hparameter
  · have hlarge : a < boxR m₂ u v ∧ b < boxS m₂ u v := by omega
    have hT := factorization_two_add_one_le_parameterK_of_collision hp hq hpq hpodd
      ha hb (by simpa only [M, u, v, L, K, m₂, N, T] using hlarge)
    change T ≤ K at hT
    have hLpos : 0 < L := by
      have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
      have := blParameterL_ge_fifteen hM
      omega
    have hTKL : T ≤ 3 * (K * L) := by
      have hKle : K ≤ K * L := Nat.le_mul_of_pos_right K hLpos
      have hKLle : K * L ≤ 3 * (K * L) := by omega
      exact hT.trans (hKle.trans hKLle)
    have hTreal : (T : ℝ) ≤ ((3 * (K * L) : ℕ) : ℝ) := by exact_mod_cast hTKL
    exact hTreal.trans hparameter

theorem gcd_factorization_two_le_parameter_spare
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpodd : Odd p)
    (ha : 0 < a) (hb : 0 < b) :
    (((Nat.gcd a b).factorization 2 : ℕ) : ℝ) ≤
      1 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  let d := Nat.gcd a b
  let T := d.factorization 2
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let m := M / Real.log 2
  let Bp := parameterBPrime p q a b
  have hdNat : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have hpowdvd : 2 ^ T ∣ d := by
    dsimp only [T]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hdNat.ne').2 le_rfl
  have hpowa : 2 ^ T ≤ a :=
    (Nat.le_of_dvd hdNat hpowdvd).trans (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b))
  have hdlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hBp : 0 < Bp := by
    dsimp only [Bp, parameterBPrime]
    positivity
  have haBp : (a : ℝ) ≤ Bp * Real.log q := by
    have hfirst : (a : ℝ) = ((a : ℝ) / Real.log q) * Real.log q := by
      field_simp
    rw [hfirst]
    dsimp only [Bp, parameterBPrime]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hqLog.le
  have hpowReal : ((2 : ℝ) ^ T) ≤ Bp * Real.log q := by
    have hpowaReal : ((2 : ℝ) ^ T) ≤ (a : ℝ) := by exact_mod_cast hpowa
    exact hpowaReal.trans haBp
  have hlogPow := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ T)
    hpowReal
  rw [Real.log_pow, Real.log_mul hBp.ne' hqLog.ne'] at hlogPow
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hqEq : Real.log 2 * v = Real.log q := by
    dsimp only [v]
    field_simp
  have hlogLogq : Real.log (Real.log q) =
      Real.log (Real.log 2) + Real.log v := by
    rw [← hqEq, Real.log_mul hdlog.ne' hv0.ne']
  rw [hlogLogq] at hlogPow
  have hMlog : Real.log Bp + Real.log (Real.log 2) + 2 / 5 ≤ M :=
    le_max_left _ _
  have hmain : (T : ℝ) * Real.log 2 ≤ M + Real.log v - 2 / 5 := by
    linarith
  have hlogv := Real.log_le_sub_one_of_pos hv0
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [parameter_log_two_lower]
  have hlogvCoarse : Real.log v ≤ 2 * v * Real.log 2 := by
    have hvNonneg : 0 ≤ v := hv0.le
    nlinarith [mul_le_mul_of_nonneg_left hlogTwoHalf.le hvNonneg]
  have hmEq : m * Real.log 2 = M := by
    dsimp only [m]
    field_simp
  have hTm : (T : ℝ) ≤ m + 2 * v := by
    nlinarith [mul_pos hdlog (show 0 < m + 2 * v - T by
      nlinarith [hmain, hlogvCoarse])]
  have hMlower : 15 * Real.log 2 ≤ M := le_max_right _ _
  have hm : (15 : ℝ) ≤ m := by
    dsimp only [m]
    exact (le_div_iff₀ hdlog).2 hMlower
  have hm0 : 0 ≤ m := by positivity
  have hmSq : m + 2 ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
  have hmv : m + 2 * v ≤ (m + 2) * v := by
    have := mul_le_mul_of_nonneg_left hv hm0
    nlinarith
  have hsqv : (m + 2) * v ≤ m ^ 2 * v :=
    mul_le_mul_of_nonneg_right hmSq hv0.le
  have huvmul : m ^ 2 * v ≤ m ^ 2 * (u * v) := by
    have huv : v ≤ u * v := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu hv0.le
    exact mul_le_mul_of_nonneg_left huv (sq_nonneg m)
  have htarget : (T : ℝ) ≤ m ^ 2 * (u * v) :=
    hTm.trans (hmv.trans (hsqv.trans huvmul))
  have hrewrite : m ^ 2 * (u * v) =
      1 / (Real.log 2) ^ 4 * M ^ 2 * Real.log p * Real.log q := by
    dsimp only [m, u, v]
    field_simp
  rw [hrewrite] at htarget
  simpa only [d, T, M] using htarget

theorem parameterMaximum_div_gcd_le
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (ha : 0 < a) :
    parameterMaximum p q (a / Nat.gcd a b) (b / Nat.gcd a b) ≤
      parameterMaximum p q a b := by
  let d := Nat.gcd a b
  let A := a / d
  let B := b / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have haEq : d * A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbEq : d * B = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hBp₀ : 0 < parameterBPrime p q A B := by
    dsimp only [parameterBPrime]
    have hA : 0 < A := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hd
    positivity
  have hBpEq : parameterBPrime p q a b =
      (d : ℝ) * parameterBPrime p q A B := by
    have haCast := congrArg (fun n : ℕ => (n : ℝ)) haEq
    have hbCast := congrArg (fun n : ℕ => (n : ℝ)) hbEq
    push_cast at haCast hbCast
    dsimp only [parameterBPrime]
    rw [← haCast, ← hbCast]
    ring
  have hBpLe : parameterBPrime p q A B ≤ parameterBPrime p q a b := by
    rw [hBpEq]
    have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hlog := Real.log_le_log hBp₀ hBpLe
  dsimp only [parameterMaximum]
  apply max_le_max_right
  linarith

theorem odd_factorization_two_sub_or_add_eq_one
    {X : ℕ} (hX : 1 < X) (hodd : Odd X) :
    (X - 1).factorization 2 = 1 ∨ (X + 1).factorization 2 = 1 := by
  have hsub : 0 < X - 1 := by omega
  have hadd : 0 < X + 1 := by omega
  rcases hodd with ⟨k, hk⟩
  have htwoSub : 2 ^ 1 ∣ X - 1 := by
    norm_num
    use k
    omega
  have htwoAdd : 2 ^ 1 ∣ X + 1 := by
    norm_num
    use k + 1
    omega
  have hfacSub : 1 ≤ (X - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hsub.ne').1 htwoSub
  have hfacAdd : 1 ≤ (X + 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hadd.ne').1 htwoAdd
  by_contra hnot
  push_neg at hnot
  have htwoFacSub : 2 ≤ (X - 1).factorization 2 := by omega
  have htwoFacAdd : 2 ≤ (X + 1).factorization 2 := by omega
  have hfourSub : 2 ^ 2 ∣ X - 1 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hsub.ne').2 htwoFacSub
  have hfourAdd : 2 ^ 2 ∣ X + 1 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hadd.ne').2 htwoFacAdd
  norm_num at hfourSub hfourAdd
  obtain ⟨r, hr⟩ := hfourSub
  obtain ⟨s, hs⟩ := hfourAdd
  omega

theorem odd_prime_two_adic_bound
    {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b) :
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      36 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  let d := Nat.gcd a b
  let A := a / d
  let B := b / d
  let X := p ^ A * q ^ B
  let M₀ := parameterMaximum p q A B
  let M := parameterMaximum p q a b
  let C₀ := 1 / (Real.log 2) ^ 4 * M₀ ^ 2 * Real.log p * Real.log q
  let C := 1 / (Real.log 2) ^ 4 * M ^ 2 * Real.log p * Real.log q
  have hd : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have hdOne : 1 ≤ d := hd
  have haEq : d * A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbEq : d * B = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hA : 0 < A := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hd
  have hB : 0 < B := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hd
  have hAB : A.Coprime B := Nat.coprime_div_gcd_div_gcd hd
  have hpowEq : p ^ a * q ^ b = X ^ d := by
    dsimp only [X]
    rw [← haEq, ← hbEq, mul_comm d A, mul_comm d B, pow_mul, pow_mul, mul_pow]
  have hXodd : Odd X := hpodd.pow.mul hqodd.pow
  have hXgt : 1 < X := by
    dsimp only [X]
    have hpPow : 1 < p ^ A := Nat.one_lt_pow hA.ne' hp.one_lt
    have hqPow : 0 < q ^ B := pow_pos hq.pos _
    exact hpPow.trans_le (Nat.le_mul_of_pos_right (p ^ A) hqPow)
  have hminus := coprime_two_adic_bound hp hq hpq hpodd hqodd hA hB hAB
  have hplus := coprime_add_one_two_adic_bound hp hq hpq hpodd hqodd hA hB hAB
  have hMle : M₀ ≤ M := by
    simpa only [M₀, M, A, B, d] using parameterMaximum_div_gcd_le hp hq ha
  have hM₀nonneg : 0 ≤ M₀ := by
    dsimp only [M₀, parameterMaximum]
    exact (le_max_right _ _).trans' (by positivity)
  have hMnonneg : 0 ≤ M := by
    dsimp only [M, parameterMaximum]
    exact (le_max_right _ _).trans' (by positivity)
  have hMsq : M₀ ^ 2 ≤ M ^ 2 := by nlinarith [sq_nonneg (M - M₀)]
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hscale : 0 ≤ 1 / (Real.log 2) ^ 4 * Real.log p * Real.log q := by positivity
  have hC : C₀ ≤ C := by
    have hm := mul_le_mul_of_nonneg_left hMsq hscale
    dsimp only [C₀, C]
    ring_nf at hm ⊢
    exact hm
  have hminusC : (((X - 1).factorization 2 : ℕ) : ℝ) ≤ 35 * C := by
    change (((X - 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * M₀ ^ 2 * Real.log p * Real.log q at hminus
    have hminus₀ : (((X - 1).factorization 2 : ℕ) : ℝ) ≤ 35 * C₀ := by
      dsimp only [C₀]
      ring_nf at hminus ⊢
      exact hminus
    have hm := hminus₀.trans (mul_le_mul_of_nonneg_left hC (by norm_num))
    ring_nf at hm ⊢
    exact hm
  have hplusC : (((X + 1).factorization 2 : ℕ) : ℝ) ≤ 35 * C := by
    change (((X + 1).factorization 2 : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * M₀ ^ 2 * Real.log p * Real.log q at hplus
    have hplus₀ : (((X + 1).factorization 2 : ℕ) : ℝ) ≤ 35 * C₀ := by
      dsimp only [C₀]
      ring_nf at hplus ⊢
      exact hplus
    have hm := hplus₀.trans (mul_le_mul_of_nonneg_left hC (by norm_num))
    ring_nf at hm ⊢
    exact hm
  have hdC := gcd_factorization_two_le_parameter_spare hp hq hpq hpodd ha hb
  have hdC' : (((d.factorization 2 : ℕ) : ℝ)) ≤ C := by
    simpa only [d, C, M] using hdC
  rw [hpowEq]
  rcases d.even_or_odd with hdeven | hdodd
  · have hnotTwoX : ¬2 ∣ X := by
      simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hXodd
    have hLTE := padicValNat.pow_two_sub_one hXgt hnotTwoX hd.ne' hdeven
    change (X ^ d - 1).factorization 2 + 1 =
      (X + 1).factorization 2 + (X - 1).factorization 2 + d.factorization 2 at hLTE
    have hone := odd_factorization_two_sub_or_add_eq_one hXgt hXodd
    rcases hone with hone | hone
    · have hreal := congrArg (fun n : ℕ => (n : ℝ)) hLTE
      push_cast at hreal
      rw [hone] at hreal hminusC
      norm_num at hreal hminusC
      simp only [add_comm X 1] at hreal
      dsimp only [C] at hminusC hplusC hdC' ⊢
      ring_nf at hminusC hplusC hdC' ⊢
      nlinarith
    · have hreal := congrArg (fun n : ℕ => (n : ℝ)) hLTE
      push_cast at hreal
      rw [hone] at hreal hplusC
      norm_num at hreal hplusC
      dsimp only [C] at hminusC hplusC hdC' ⊢
      ring_nf at hminusC hplusC hdC' ⊢
      nlinarith
  · let T := (X ^ d - 1).factorization 2
    have hxdpos : 0 < X ^ d - 1 := by
      have hpowgt : 1 < X ^ d := Nat.one_lt_pow hd.ne' hXgt
      omega
    have hdiv : 2 ^ T ∣ X ^ d - 1 := by
      dsimp only [T]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hxdpos.ne').2 le_rfl
    have hrelD : X ^ d ≡ 1 [MOD 2 ^ T] := by
      exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ X ^ d)).2 hdiv).symm
    obtain ⟨c, t, hdc⟩ := exists_odd_exponent_inverse d T hdodd
    have hrelDC : X ^ (d * c) ≡ 1 [MOD 2 ^ T] := by
      have h := hrelD.pow c
      simpa only [one_pow, pow_mul] using h
    have hrelDCZ : (X : ZMod (2 ^ T)) ^ (d * c) = 1 := by
      have hcast : ((X ^ (d * c) : ℕ) : ZMod (2 ^ T)) = (1 : ℕ) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).2 hrelDC
      simpa only [Nat.cast_pow, Nat.cast_one] using hcast
    have hperiod := zmod_pow_mul_exponent_inverse hXodd hdc (r := 1)
    have hXZ : (X : ZMod (2 ^ T)) = 1 := by
      calc
        (X : ZMod (2 ^ T)) = (X : ZMod (2 ^ T)) ^ (d * c * 1) := by
          simpa using hperiod.symm
        _ = 1 := by simpa using hrelDCZ
    have hrelX : X ≡ 1 [MOD 2 ^ T] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa using hXZ
    have hdivX : 2 ^ T ∣ X - 1 :=
      (Nat.modEq_iff_dvd' hXgt.le).1 hrelX.symm
    have hTle : T ≤ (X - 1).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : X - 1 ≠ 0)).1 hdivX
    have hTreal : (T : ℝ) ≤ ((X - 1).factorization 2 : ℕ) := by exact_mod_cast hTle
    change (T : ℝ) ≤ _
    dsimp only [C] at hminusC ⊢
    ring_nf at hminusC ⊢
    nlinarith

theorem bugeaudLaurent_special
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (ha : 0 < a) (hb : 0 < b) :
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      36 / (Real.log 2) ^ 4 * (parameterMaximum p q a b) ^ 2 *
        Real.log p * Real.log q := by
  by_cases hpTwo : p = 2
  · subst p
    have htwoPow : 2 ∣ 2 ^ a := by
      exact dvd_pow_self 2 ha.ne'
    have htwoProd : 2 ∣ 2 ^ a * q ^ b := dvd_mul_of_dvd_left htwoPow _
    have hnot : ¬2 ∣ 2 ^ a * q ^ b - 1 := by
      intro hdiv
      obtain ⟨r, hr⟩ := htwoProd
      obtain ⟨s, hs⟩ := hdiv
      have hprod : 0 < 2 ^ a * q ^ b := mul_pos (pow_pos (by norm_num) _)
        (pow_pos hq.pos _)
      omega
    rw [Nat.factorization_eq_zero_of_not_dvd hnot]
    norm_num
    positivity
  · have hpodd : Odd p := hp.odd_of_ne_two hpTwo
    have hqTwo : q ≠ 2 := by
      have hpTwoLe := hp.two_le
      omega
    have hqodd : Odd q := hq.odd_of_ne_two hqTwo
    exact odd_prime_two_adic_bound hp hq hpq hpodd hqodd ha hb

end Erdos1058.BugeaudLaurent
