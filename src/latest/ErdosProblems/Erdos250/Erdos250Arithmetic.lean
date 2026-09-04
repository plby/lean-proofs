import Mathlib

namespace Erdos250Arithmetic

def gauss2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gauss2 n k + 2 ^ (k + 1) * gauss2 n (k + 1)

@[simp] lemma gauss2_zero_zero : gauss2 0 0 = 1 := rfl
@[simp] lemma gauss2_zero_succ (k : ℕ) : gauss2 0 (k + 1) = 0 := rfl
@[simp] lemma gauss2_succ_zero (n : ℕ) : gauss2 (n + 1) 0 = 1 := rfl
@[simp] lemma gauss2_zero_right (n : ℕ) : gauss2 n 0 = 1 := by cases n <;> rfl
@[simp] lemma gauss2_succ_succ (n k : ℕ) :
    gauss2 (n + 1) (k + 1) = gauss2 n k + 2 ^ (k + 1) * gauss2 n (k + 1) := rfl

@[simp] lemma gauss2_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → gauss2 n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      rw [gauss2_succ_succ, gauss2_eq_zero_of_lt (by omega),
        gauss2_eq_zero_of_lt (by omega)]
      simp

@[simp] lemma gauss2_self : ∀ n : ℕ, gauss2 n n = 1
  | 0 => rfl
  | n + 1 => by rw [gauss2_succ_succ, gauss2_self, gauss2_eq_zero_of_lt (by omega)]; simp

lemma gauss2_pos_of_le : ∀ {n k : ℕ}, k ≤ n → 0 < gauss2 n k
  | 0, 0, _ => by simp
  | 0, _ + 1, h => by omega
  | _ + 1, 0, _ => by simp
  | n + 1, k + 1, h => by
      rw [gauss2_succ_succ]
      exact Nat.add_pos_left (gauss2_pos_of_le (by omega)) _

lemma exponent_le_quarter (n k : ℕ) : k * (n - k) ≤ n ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
  by_cases hk : k ≤ n
  · simpa [Nat.add_sub_of_le hk, mul_assoc, mul_left_comm, mul_comm] using
      (four_mul_le_sq_add k (n - k))
  · simp [Nat.sub_eq_zero_of_le (le_of_not_ge hk)]

lemma rat_mul_div_eq_intCast_of_dvd {D d : ℕ} (z : ℤ)
    (hd : d ∣ D) (hd0 : d ≠ 0) :
    ∃ w : ℤ, (D : ℚ) * ((z : ℚ) / (d : ℚ)) = (w : ℚ) := by
  obtain ⟨c, rfl⟩ := hd
  refine ⟨(c : ℤ) * z, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  push_cast
  field_simp [hdq]

lemma sum_eq_intCast_of_each_eq_intCast {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ∃ z : ℤ, f i = (z : ℚ)) :
    ∃ z : ℤ, ∑ i ∈ s, f i = (z : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨za, hza⟩ := hf a (by simp)
      obtain ⟨zs, hzs⟩ := ih fun i hi ↦ hf i (by simp [hi])
      exact ⟨za + zs, by simp [ha, hza, hzs]⟩

def oddFactor (d : ℕ) : ℕ := 2 ^ d - 1

/-- The exact finite sum displayed in the writeup for `b_n^*`. -/
def bStar (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (((gauss2 n k) ^ 2 * gauss2 (n + k) k : ℕ) : ℚ) /
      ((2 : ℕ) ^ (k * (n - k)) : ℕ)

/-- `h₁(k)` after specializing `p = 2`. -/
def hOne (k : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ)

/-- `h₂(k)` after specializing `p = 2`. -/
def hTwo (k : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 1 k, ((2 ^ d : ℕ) : ℚ) / ((oddFactor d : ℕ) ^ 2 : ℕ)

/-- The logarithmic-derivative factor in the cancellation-aware simple-pole coefficient.
For pole `j=k+1`, one has `u_{n,j} = -v_{n,j} * logDerivCoeff n k`. -/
def logDerivCoeff (n k : ℕ) : ℚ :=
  n +
    ∑ d ∈ Finset.Icc (k + 1) (n + k),
      ((2 ^ d : ℕ) : ℚ) / (oddFactor d : ℕ) -
    2 * ∑ d ∈ Finset.Icc 1 k,
      ((2 ^ d : ℕ) : ℚ) / (oddFactor d : ℕ) +
    2 * ∑ d ∈ Finset.Icc 1 (n - k),
      (1 : ℚ) / (oddFactor d : ℕ)

/-- The common coefficient `λ_n 2^(k+1) v_{n,k+1}`. -/
def cCoeff (n k : ℕ) : ℚ :=
  (((gauss2 n k) ^ 2 * gauss2 (n + k) k : ℕ) : ℚ) /
    ((2 : ℕ) ^ (k * (n - k)) : ℕ)

/-- The finite, cancellation-aware expansion of `a_n^*`. -/
def aStarRegrouped (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    cCoeff n k * (hTwo k - logDerivCoeff n k * hOne k)

lemma bStar_eq_sum_cCoeff (n : ℕ) :
    bStar n = ∑ k ∈ Finset.range (n + 1), cCoeff n k := rfl

/-- The power of two `2^{⌊n²/4⌋}` clears the displayed `b_n^*` expansion. -/
lemma powTwo_mul_bStar_eq_intCast (n : ℕ) :
    ∃ z : ℤ, (((2 : ℕ) ^ (n ^ 2 / 4) : ℕ) : ℚ) * bStar n = (z : ℚ) := by
  classical
  rw [bStar, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro k hk
  rw [Finset.mem_range] at hk
  apply rat_mul_div_eq_intCast_of_dvd
  · exact Nat.pow_dvd_pow 2 (exponent_le_quarter n k)
  · positivity

def denProd (n : ℕ) : ℕ := ∏ d ∈ Finset.Icc 1 n, oddFactor d

lemma oddFactor_dvd_denProd {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    oddFactor d ∣ denProd n := by
  exact Finset.dvd_prod_of_mem oddFactor (Finset.mem_Icc.mpr ⟨hd, hdn⟩)

lemma denProd_dvd_denProd {k n : ℕ} (hkn : k ≤ n) : denProd k ∣ denProd n := by
  apply Finset.prod_dvd_prod_of_subset (Finset.Icc 1 k) (Finset.Icc 1 n) oddFactor
  intro d hd
  simp only [Finset.mem_Icc] at hd ⊢
  exact ⟨hd.1, hd.2.trans hkn⟩

def highProd (n k : ℕ) : ℕ := ∏ r ∈ Finset.Icc 1 k, oddFactor (n + r)

lemma denProd_succ (k : ℕ) :
    denProd (k + 1) = denProd k * oddFactor (k + 1) := by
  rw [denProd, denProd, Finset.prod_Icc_succ_top]
  omega

lemma highProd_succ_right (n k : ℕ) :
    highProd n (k + 1) = highProd n k * oddFactor (n + k + 1) := by
  rw [highProd, highProd, Finset.prod_Icc_succ_top]
  · congr 2
  · omega

lemma highProd_succ_left (n k : ℕ) :
    highProd n (k + 1) = oddFactor (n + 1) * highProd (n + 1) k := by
  induction k with
  | zero => simp [highProd, oddFactor]
  | succ k ih =>
      rw [highProd_succ_right n (k + 1), highProd_succ_right (n + 1) k, ih]
      have hlast : oddFactor (n + (k + 1) + 1) =
          oddFactor (n + 1 + k + 1) := by
        congr 1
        omega
      rw [hlast]
      ring

theorem gauss2_mul_denProd_eq_highProd (n k : ℕ) :
    gauss2 (n + k) k * denProd k = highProd n k := by
  induction k generalizing n with
  | zero => simp [denProd, highProd]
  | succ k ih =>
      induction n with
      | zero => simp [denProd, highProd]
      | succ n hn =>
          rw [show (n + 1) + (k + 1) = (n + k + 1) + 1 by omega,
            gauss2_succ_succ, denProd_succ]
          calc
            (gauss2 (n + k + 1) k + 2 ^ (k + 1) * gauss2 (n + k + 1) (k + 1)) *
                  (denProd k * oddFactor (k + 1)) =
                (gauss2 ((n + 1) + k) k * denProd k) * oddFactor (k + 1) +
                  2 ^ (k + 1) *
                    ((gauss2 (n + (k + 1)) (k + 1) * denProd (k + 1))) := by
                      rw [denProd_succ]
                      ring_nf
            _ = highProd (n + 1) k * oddFactor (k + 1) +
                  2 ^ (k + 1) * highProd n (k + 1) := by
                    rw [ih (n + 1), hn]
            _ = highProd (n + 1) k * oddFactor (k + 1) +
                  2 ^ (k + 1) *
                    (oddFactor (n + 1) * highProd (n + 1) k) := by
                      rw [highProd_succ_left]
            _ = highProd (n + 1) k * oddFactor (n + k + 2) := by
              have hp : 2 ^ (n + k + 2) = 2 ^ (k + 1) * 2 ^ (n + 1) := by
                rw [← pow_add]
                congr 1
                omega
              have hA : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by omega)
              have hB : 1 ≤ 2 ^ (n + 1) := one_le_pow₀ (by omega)
              have hAB : 1 ≤ 2 ^ (k + 1) * 2 ^ (n + 1) :=
                Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
                  (pow_ne_zero _ (by norm_num)))
              have hodd : oddFactor (k + 1) +
                    2 ^ (k + 1) * oddFactor (n + 1) = oddFactor (n + k + 2) := by
                simp only [oddFactor]
                rw [hp]
                nlinarith [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB,
                  Nat.sub_add_cancel hAB]
              rw [← hodd]
              ring
            _ = highProd (n + 1) (k + 1) := by
              rw [highProd_succ_right]
              congr 2
              omega

lemma oddFactor_dvd_highProd {n k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    oddFactor (n + r) ∣ highProd n k := by
  exact Finset.dvd_prod_of_mem (fun r ↦ oddFactor (n + r))
    (Finset.mem_Icc.mpr ⟨hr, hrk⟩)

/-- Once the Gaussian product identity is available, every apparent denominator
`2^(n+r)-1` in `L_{n,k}` is absorbed by the Gaussian coefficient and one copy of `D_n`. -/
lemma high_oddFactor_dvd_gauss2_mul_denProd {n k r : ℕ} (hkn : k ≤ n)
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    oddFactor (n + r) ∣ gauss2 (n + k) k * denProd n := by
  apply (oddFactor_dvd_highProd hr hrk).trans
  rw [← hprod]
  exact Nat.mul_dvd_mul_left _ (denProd_dvd_denProd hkn)

lemma mul_dvd_mul_denProd_sq_of_dvd_mul_denProd {a b g D : ℕ}
    (ha : a ∣ g * D) (hb : b ∣ D) : a * b ∣ g * D ^ 2 := by
  simpa [pow_two, mul_assoc] using Nat.mul_dvd_mul ha hb

/-- Divisibility needed for a high-index summand of `c_{n,k} L_{n,k} h1_k`.
The Gaussian coefficient absorbs `2^(n+r)-1`; the two copies of `D_n` absorb
the product-formula denominator and the factor from `h1_k`. -/
lemma high_mixed_denominator_dvd_scaled_gauss {n k r d e M : ℕ}
    (hkn : k ≤ n) (hr : 1 ≤ r) (hrk : r ≤ k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (he : e ≤ M)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    2 ^ e * (oddFactor (n + r) * oddFactor d) ∣
      (2 ^ M * denProd n ^ 2) * gauss2 (n + k) k := by
  have hhigh := high_oddFactor_dvd_gauss2_mul_denProd hkn hr hrk hprod
  have hlow := oddFactor_dvd_denProd hd (hdk.trans hkn)
  have hodd : oddFactor (n + r) * oddFactor d ∣
      denProd n ^ 2 * gauss2 (n + k) k := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_dvd_mul hhigh hlow
  simpa [mul_assoc] using Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 he) hodd

lemma rat_mul_mul_div_eq_intCast_of_dvd {E c d : ℕ} (z : ℤ)
    (hd : d ∣ E * c) (hd0 : d ≠ 0) :
    ∃ w : ℤ, (E : ℚ) * (((c : ℚ) * (z : ℚ)) / (d : ℚ)) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd z hd hd0
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  ring

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

lemma RatIntegral.add {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

lemma RatIntegral.sub {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

lemma RatIntegral.mul {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

lemma RatIntegral.intCast (z : ℤ) : RatIntegral (z : ℚ) := ⟨z, rfl⟩

lemma RatIntegral.natCast_mul (m : ℕ) {x : ℚ} (hx : RatIntegral x) :
    RatIntegral ((m : ℚ) * x) :=
  (RatIntegral.intCast (m : ℤ)).mul hx

lemma oddFactor_ne_zero {d : ℕ} (hd : 1 ≤ d) : oddFactor d ≠ 0 := by
  exact Nat.sub_ne_zero_of_lt (one_lt_pow' (by decide : (1 : ℕ) < 2) (by omega))

lemma two_oddFactors_dvd_denProd_sq {d₁ d₂ n : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₁n : d₁ ≤ n) (hd₂ : 1 ≤ d₂) (hd₂n : d₂ ≤ n) :
    oddFactor d₁ * oddFactor d₂ ∣ denProd n ^ 2 := by
  simpa [pow_two] using Nat.mul_dvd_mul
    (oddFactor_dvd_denProd hd₁ hd₁n) (oddFactor_dvd_denProd hd₂ hd₂n)

/-- The full `E_n = 2^{⌊n²/4⌋} D_n²` used in the writeup clears `b_n^*`.
The `D_n²` factor is not actually needed for this coefficient. -/
lemma E_mul_bStar_eq_intCast (n : ℕ) :
    ∃ z : ℤ,
      ((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) * bStar n = (z : ℚ) := by
  obtain ⟨z, hz⟩ := powTwo_mul_bStar_eq_intCast n
  refine ⟨(denProd n ^ 2 : ℕ) * z, ?_⟩
  push_cast at hz ⊢
  calc
    (2 : ℚ) ^ (n ^ 2 / 4) * (denProd n : ℚ) ^ 2 * bStar n =
        (denProd n : ℚ) ^ 2 * ((2 : ℚ) ^ (n ^ 2 / 4) * bStar n) := by ring
    _ = (denProd n : ℚ) ^ 2 * (z : ℚ) := by rw [hz]

lemma mixed_denominator_dvd {e M d₁ d₂ n : ℕ} (he : e ≤ M)
    (hd₁ : 1 ≤ d₁) (hd₁n : d₁ ≤ n) (hd₂ : 1 ≤ d₂) (hd₂n : d₂ ≤ n) :
    2 ^ e * (oddFactor d₁ * oddFactor d₂) ∣ 2 ^ M * denProd n ^ 2 := by
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 he)
    (two_oddFactors_dvd_denProd_sq hd₁ hd₁n hd₂ hd₂n)

/-- Uniform divisibility for the long interval `k+1 ≤ a ≤ n+k` occurring in
`logDerivCoeff`: low `a` is handled by `D_n`, while high `a=n+r` is absorbed
by `gauss2 (n+k) k` through the product identity. -/
lemma long_range_denominator_dvd {n k a d e M : ℕ}
    (hkn : k ≤ n) (haL : k + 1 ≤ a) (haU : a ≤ n + k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (he : e ≤ M)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    2 ^ e * (oddFactor a * oddFactor d) ∣
      (2 ^ M * denProd n ^ 2) *
        ((gauss2 n k) ^ 2 * gauss2 (n + k) k) := by
  by_cases han : a ≤ n
  · have hbase := mixed_denominator_dvd he (by omega : 1 ≤ a) han
        hd (hdk.trans hkn)
    exact dvd_mul_of_dvd_left hbase _
  · let r := a - n
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrk : r ≤ k := by dsimp [r]; omega
    have har : a = n + r := by dsimp [r]; omega
    have hbase := high_mixed_denominator_dvd_scaled_gauss hkn hr hrk hd hdk he hprod
    rw [har]
    convert (dvd_mul_of_dvd_left hbase ((gauss2 n k) ^ 2)) using 1 <;> ac_rfl

lemma long_odd_denominator_dvd {n k a d : ℕ}
    (hkn : k ≤ n) (haL : k + 1 ≤ a) (haU : a ≤ n + k)
    (hd : 1 ≤ d) (hdk : d ≤ k) :
    oddFactor a * oddFactor d ∣ denProd n ^ 2 * gauss2 (n + k) k := by
  by_cases han : a ≤ n
  · exact dvd_mul_of_dvd_left
      (two_oddFactors_dvd_denProd_sq (by omega : 1 ≤ a) han hd (hdk.trans hkn)) _
  · let r := a - n
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrk : r ≤ k := by dsimp [r]; omega
    have har : a = n + r := by dsimp [r]; omega
    rw [har]
    have hhigh := high_oddFactor_dvd_gauss2_mul_denProd hkn hr hrk
      (gauss2_mul_denProd_eq_highProd n k)
    have hlow := oddFactor_dvd_denProd hd (hdk.trans hkn)
    convert Nat.mul_dvd_mul hhigh hlow using 1
    all_goals
      simp [pow_two]
      ac_rfl

lemma oddScale_mul_hTwo_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) * hTwo k) := by
  classical
  rw [hTwo, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hdiv : oddFactor d ^ 2 ∣ denProd n ^ 2 * gauss2 (n + k) k := by
    have h0 := two_oddFactors_dvd_denProd_sq hd.1 (hd.2.trans hkn)
      hd.1 (hd.2.trans hkn)
    exact dvd_mul_of_dvd_left (by simpa [pow_two] using h0) _
  apply rat_mul_div_eq_intCast_of_dvd (z := (2 ^ d : ℕ)) hdiv
  exact pow_ne_zero 2 (oddFactor_ne_zero hd.1)

lemma oddScale_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) * hOne k) := by
  classical
  rw [hOne, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hdiv : oddFactor d ∣ denProd n ^ 2 * gauss2 (n + k) k := by
    exact (oddFactor_dvd_denProd hd.1 (hd.2.trans hkn)).trans
      (by exact dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  apply rat_mul_div_eq_intCast_of_dvd (z := (1 : ℤ)) hdiv
  exact oddFactor_ne_zero hd.1

lemma denProdSq_mul_two_ratSums_integral
    {ι κ : Type*} (n : ℕ) (s : Finset ι) (t : Finset κ)
    (z₁ : ι → ℤ) (z₂ : κ → ℤ) (d₁ : ι → ℕ) (d₂ : κ → ℕ)
    (hd₁ : ∀ i ∈ s, 1 ≤ d₁ i ∧ d₁ i ≤ n)
    (hd₂ : ∀ j ∈ t, 1 ≤ d₂ j ∧ d₂ j ≤ n) :
    RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ i ∈ s, (z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ)) *
        (∑ j ∈ t, (z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ))) := by
  classical
  rw [Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro j hj
  have hexpand :
      (((denProd n ^ 2 : ℕ) : ℚ) *
          (∑ i ∈ s, (z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ))) *
          ((z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ)) =
        ∑ i ∈ s,
          (((denProd n ^ 2 : ℕ) : ℚ) *
            ((z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ))) *
            ((z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand]
  apply sum_eq_intCast_of_each_eq_intCast
  intro i hi
  have hdiv := two_oddFactors_dvd_denProd_sq
    (hd₁ i hi).1 (hd₁ i hi).2 (hd₂ j hj).1 (hd₂ j hj).2
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd (z₁ i * z₂ j) hdiv
    (mul_ne_zero (oddFactor_ne_zero (hd₁ i hi).1) (oddFactor_ne_zero (hd₂ j hj).1))
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  field_simp [oddFactor_ne_zero (hd₁ i hi).1, oddFactor_ne_zero (hd₂ j hj).1]

lemma oddScale_mul_longSum_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
  classical
  rw [hOne, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hexpand :
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
          (∑ a ∈ Finset.Icc (k + 1) (n + k),
            ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ))) *
          ((1 : ℚ) / (oddFactor d : ℕ)) =
        ∑ a ∈ Finset.Icc (k + 1) (n + k),
          (((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
            (((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ))) *
            ((1 : ℚ) / (oddFactor d : ℕ))) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand]
  apply sum_eq_intCast_of_each_eq_intCast
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hdiv := long_odd_denominator_dvd hkn ha.1 ha.2 hd.1 hd.2
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd (2 ^ a : ℕ) hdiv
    (mul_ne_zero (oddFactor_ne_zero (by omega)) (oddFactor_ne_zero hd.1))
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  field_simp [oddFactor_ne_zero (by omega : 1 ≤ a), oddFactor_ne_zero hd.1]

lemma oddScale_mul_logDeriv_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        logDerivCoeff n k * hOne k) := by
  let G : ℕ := gauss2 (n + k) k
  let scale : ℕ := denProd n ^ 2 * G
  have hconst : RatIntegral (((n : ℚ) * ((scale : ℕ) : ℚ)) * hOne k) := by
    have h := oddScale_mul_hOne_integral hkn
    have hm := RatIntegral.natCast_mul n h
    convert hm using 1
    all_goals
      dsimp [scale, G]
      push_cast
      ring
  have hlong : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    exact oddScale_mul_longSum_mul_hOne_integral hkn
  have hlow₁base : RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 k, ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) *
        (∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ))) := by
    apply denProdSq_mul_two_ratSums_integral n
    · intro a ha
      rw [Finset.mem_Icc] at ha
      exact ⟨ha.1, ha.2.trans hkn⟩
    · intro d hd
      rw [Finset.mem_Icc] at hd
      exact ⟨hd.1, hd.2.trans hkn⟩
  have hlow₁ : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 k, ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    have hmul := (RatIntegral.intCast (G : ℤ)).mul hlow₁base
    convert hmul using 1
    all_goals
      simp only [scale, G, hOne]
      push_cast
      ring
  have hlow₂base : RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 (n - k), (1 : ℚ) / (oddFactor a : ℕ)) *
        (∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ))) := by
    apply denProdSq_mul_two_ratSums_integral n
    · intro a ha
      rw [Finset.mem_Icc] at ha
      exact ⟨ha.1, by omega⟩
    · intro d hd
      rw [Finset.mem_Icc] at hd
      exact ⟨hd.1, hd.2.trans hkn⟩
  have hlow₂ : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 (n - k), (1 : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    have hmul := (RatIntegral.intCast (G : ℤ)).mul hlow₂base
    convert hmul using 1
    all_goals
      simp only [scale, G, hOne]
      push_cast
      ring
  have hall := ((hconst.add hlong).sub (RatIntegral.natCast_mul 2 hlow₁)).add
    (RatIntegral.natCast_mul 2 hlow₂)
  convert hall using 1
  all_goals
    simp only [scale, G, logDerivCoeff]
    push_cast
    ring

lemma oddScale_mul_aBracket_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        (hTwo k - logDerivCoeff n k * hOne k)) := by
  have h₂ := oddScale_mul_hTwo_integral hkn
  have h₁ := oddScale_mul_logDeriv_mul_hOne_integral hkn
  convert h₂.sub h₁ using 1
  all_goals ring

lemma E_mul_cCoeff_aBracket_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      (((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) *
        (cCoeff n k * (hTwo k - logDerivCoeff n k * hOne k))) := by
  let M := n ^ 2 / 4
  let e := k * (n - k)
  let G₁ := gauss2 n k
  let G₂ := gauss2 (n + k) k
  let bracket := hTwo k - logDerivCoeff n k * hOne k
  have he : e ≤ M := exponent_le_quarter n k
  have hodd : RatIntegral ((((denProd n ^ 2) * G₂ : ℕ) : ℚ) * bracket) := by
    exact oddScale_mul_aBracket_integral hkn
  have hmul := RatIntegral.natCast_mul ((2 ^ (M - e)) * G₁ ^ 2) hodd
  convert hmul using 1
  simp only [M, e, G₁, G₂, bracket, cCoeff]
  push_cast
  have hpow : (2 : ℚ) ^ (n ^ 2 / 4) =
      (2 : ℚ) ^ (n ^ 2 / 4 - k * (n - k)) * (2 : ℚ) ^ (k * (n - k)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp

/-- Full denominator clearing for the cancellation-aware expansion of `a_n^*`. -/
lemma E_mul_aStarRegrouped_eq_intCast (n : ℕ) :
    ∃ z : ℤ,
      (((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) *
        aStarRegrouped n) = (z : ℚ) := by
  classical
  rw [aStarRegrouped, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro k hk
  exact E_mul_cCoeff_aBracket_integral (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- Generic termwise denominator clearing for a finite sum whose denominators have
one power of two and at most two odd factors `2^d-1`. -/
lemma mixed_denominator_sum_clearing {ι : Type*} (s : Finset ι) (n M : ℕ)
    (z : ι → ℤ) (e d₁ d₂ : ι → ℕ)
    (he : ∀ i ∈ s, e i ≤ M)
    (hd₁ : ∀ i ∈ s, 1 ≤ d₁ i ∧ d₁ i ≤ n)
    (hd₂ : ∀ i ∈ s, 1 ≤ d₂ i ∧ d₂ i ≤ n) :
    ∃ Z : ℤ,
      ((((2 ^ M : ℕ) * denProd n ^ 2 : ℕ) : ℚ) *
        ∑ i ∈ s, (z i : ℚ) /
          (((2 ^ e i : ℕ) * (oddFactor (d₁ i) * oddFactor (d₂ i)) : ℕ) : ℕ) =
        (Z : ℚ)) := by
  classical
  rw [Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro i hi
  apply rat_mul_div_eq_intCast_of_dvd
  · exact mixed_denominator_dvd (he i hi)
      (hd₁ i hi).1 (hd₁ i hi).2 (hd₂ i hi).1 (hd₂ i hi).2
  · have h1 := oddFactor_ne_zero (hd₁ i hi).1
    have h2 := oddFactor_ne_zero (hd₂ i hi).1
    positivity

end Erdos250Arithmetic
