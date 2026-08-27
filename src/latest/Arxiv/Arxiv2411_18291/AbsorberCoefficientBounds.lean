import Arxiv.Arxiv2411_18291.AbsorberWorkingParameters

/-! # The accumulated integer constant in the absorber construction -/

namespace Arxiv2411_18291

def absorberExchangeEdges (q r : ℕ) : ℕ := 3 * (2 * q) ^ r * (q.choose r) ^ 2

def absorberFirstMultiplicity (q r : ℕ) : ℕ :=
  2 * absorberCoefficientCap q r * absorberGeneratorMultiplicity q r + 2

def absorberSecondMultiplicity (q r : ℕ) : ℕ :=
  absorberFirstMultiplicity q r +
    4 * q.choose r * (absorberFirstMultiplicity q r) ^ 2 + 2

def absorberSplittingConstant (q r : ℕ) : ℕ :=
  absorberNormalizationFactor q r *
    (1 + 16 * absorberExchangeEdges q r * r.factorial * absorberCoefficientCap q r)

def absorberFirstConstant (q r : ℕ) : ℕ :=
  absorberFirstMultiplicity q r * absorberSplittingConstant q r *
    (1 + 8 * absorberExchangeEdges q r * r.factorial * q.choose r *
      absorberFirstMultiplicity q r)

def absorberFinalConstant (q r : ℕ) : ℕ :=
  absorberSecondMultiplicity q r * absorberFirstConstant q r *
    (1 + 8 * absorberExchangeEdges q r * r.factorial * q.choose r *
      absorberSecondMultiplicity q r)

theorem scaled_elimination_constant_le {a x e f k : ℕ}
    (ha : 1 ≤ a) (he : 1 ≤ e) (hf : 1 ≤ f) (hk : 1 ≤ k) :
    a * x * (1 + 8 * e * f * k * a) ≤ 9 * e * f * k * a ^ 2 * x := by
  have hp : 1 ≤ e * f * k * a :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he hf) hk) ha
  have hb : 1 + 8 * e * f * k * a ≤ 9 * e * f * k * a := by nlinarith only [hp]
  calc
    _ ≤ a * x * (9 * e * f * k * a) := Nat.mul_le_mul_left _ hb
    _ = _ := by ring

theorem absorber_final_constant_le_monomial {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    absorberFinalConstant q r ≤
      130331373405555972656250 * ((2 * q) ^ r) ^ 3 * r.factorial ^ 11 * (2 ^ q) ^ 26 := by
  let t := 2 ^ q
  let f := r.factorial
  let p := (2 * q) ^ r
  let E := absorberExchangeEdges q r
  let C := absorberCoefficientCap q r
  let M := absorberGeneratorMultiplicity q r
  let A := absorberNormalizationFactor q r
  let K₀ := absorberFirstMultiplicity q r
  let K₁ := absorberSecondMultiplicity q r
  have hq : 2 ≤ q := by omega
  have ht : 4 ≤ t := by
    simpa only [t] using (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  have hf : 1 ≤ f := Nat.factorial_pos r
  have hp : 1 ≤ p := one_le_pow₀ (by omega)
  have hk : 1 ≤ q.choose r := Nat.choose_pos hqr.le
  have hkt : q.choose r ≤ t := Nat.choose_le_two_pow q r
  have hE : 1 ≤ E := by
    dsimp only [E, absorberExchangeEdges]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by decide) hp) (one_le_pow₀ hk)
  have hEb : E ≤ 3 * p * t ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkt 2)
  have hC : C = 17 * t * f := rfl
  have hCpos : 1 ≤ C := absorberCoefficientCap_pos q r
  have hMpos : 2 ≤ M := by dsimp only [M, absorberGeneratorMultiplicity]; omega
  have hMb : M ≤ 5 * t := by dsimp only [M, absorberGeneratorMultiplicity]; omega
  have hA : A ≤ 30 * f * t ^ 3 := by
    have h := Nat.mul_le_mul hMb (decoder_normalization_factor_le hqr)
    change A ≤ (5 * t) * (6 * f * 2 ^ (2 * q)) at h
    calc
      _ ≤ (5 * t) * (6 * f * 2 ^ (2 * q)) := h
      _ = _ := by rw [show 2 * q = q * 2 by omega, pow_mul]; dsimp only [t]; ring
  have hK₀ : 2 ≤ K₀ := by dsimp only [K₀, absorberFirstMultiplicity]; omega
  have hK₀b : K₀ ≤ 255 * f * t ^ 2 := by
    have hCM : 2 ≤ C * M := by nlinarith only [hCpos, hMpos]
    calc
      _ ≤ 3 * C * M := by dsimp only [K₀, absorberFirstMultiplicity]; nlinarith only [hCM]
      _ ≤ 3 * C * (5 * t) := Nat.mul_le_mul_left _ hMb
      _ = _ := by rw [hC]; ring
  have hK₁ : 1 ≤ K₁ := by dsimp only [K₁, absorberSecondMultiplicity]; omega
  have hK₁b : K₁ ≤ 325125 * f ^ 2 * t ^ 5 := by
    have hsq : K₀ + 2 ≤ K₀ ^ 2 := by nlinarith only [hK₀]
    have hs : K₀ ^ 2 ≤ q.choose r * K₀ ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (K₀ ^ 2) hk
    calc
      _ ≤ 5 * q.choose r * K₀ ^ 2 := by
        change K₀ + 4 * q.choose r * K₀ ^ 2 + 2 ≤ _
        nlinarith only [hsq, hs]
      _ ≤ 5 * t * (255 * f * t ^ 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hkt) (Nat.pow_le_pow_left hK₀b 2)
      _ = _ := by ring
  have hsplit : absorberSplittingConstant q r ≤ 26010 * p * f ^ 3 * t ^ 6 := by
    have hprod : 1 ≤ E * f * C :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hE hf) hCpos
    have hb : 1 + 16 * E * f * C ≤ 17 * E * f * C := by nlinarith only [hprod]
    calc
      _ ≤ A * (17 * E * f * C) := Nat.mul_le_mul_left _ hb
      _ ≤ (30 * f * t ^ 3) * (17 * (3 * p * t ^ 2) * f * C) :=
        Nat.mul_le_mul hA (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hEb)))
      _ = _ := by rw [hC]; ring
  have hfirst : absorberFirstConstant q r ≤
      45665106750 * p ^ 2 * f ^ 6 * t ^ 13 := by
    calc
      _ ≤ 9 * E * f * q.choose r * K₀ ^ 2 * absorberSplittingConstant q r :=
        scaled_elimination_constant_le (by omega) hE hf hk
      _ ≤ 9 * (3 * p * t ^ 2) * f * t * (255 * f * t ^ 2) ^ 2 *
          (26010 * p * f ^ 3 * t ^ 6) :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hEb)) hkt)
          (Nat.pow_le_pow_left hK₀b 2)) hsplit
      _ = _ := by ring
  calc
    _ ≤ 9 * E * f * q.choose r * K₁ ^ 2 * absorberFirstConstant q r :=
      scaled_elimination_constant_le hK₁ hE hf hk
    _ ≤ 9 * (3 * p * t ^ 2) * f * t * (325125 * f ^ 2 * t ^ 5) ^ 2 *
        (45665106750 * p ^ 2 * f ^ 6 * t ^ 13) :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hEb)) hkt)
        (Nat.pow_le_pow_left hK₁b 2)) hfirst
    _ = _ := by dsimp only [p, f, t]; ring

theorem absorber_final_constant_le {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    absorberFinalConstant q r ≤ (4 * q) ^ (22 * q) := by
  have hq : 2 ≤ q := by omega
  by_cases hq2 : q = 2
  · have hr1 : r = 1 := by omega
    subst q r
    norm_num [absorberFinalConstant, absorberFirstConstant, absorberSplittingConstant,
      absorberSecondMultiplicity, absorberFirstMultiplicity, absorberExchangeEdges,
      absorberCoefficientCap, absorberGeneratorMultiplicity, absorberNormalizationFactor]
  have hq3 : 3 ≤ q := by omega
  have hf : r.factorial ≤ q ^ q :=
    (Nat.factorial_le hqr.le).trans (Nat.factorial_le_pow q)
  have hp : (2 * q) ^ r ≤ (2 * q) ^ q := Nat.pow_le_pow_right (by omega) hqr.le
  have hcoef : 130331373405555972656250 ≤ q ^ (8 * q) * 2 ^ (15 * q) := by
    calc
      _ ≤ 3 ^ 24 * 2 ^ 45 := by norm_num
      _ ≤ q ^ (8 * q) * 2 ^ (15 * q) := Nat.mul_le_mul
        ((Nat.pow_le_pow_left hq3 24).trans (Nat.pow_le_pow_right (by omega) (by omega)))
        (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ 130331373405555972656250 * ((2 * q) ^ r) ^ 3 * r.factorial ^ 11 * (2 ^ q) ^ 26 :=
      absorber_final_constant_le_monomial hr hqr
    _ ≤ (q ^ (8 * q) * 2 ^ (15 * q)) * ((2 * q) ^ q) ^ 3 * (q ^ q) ^ 11 * (2 ^ q) ^ 26 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul hcoef (Nat.pow_le_pow_left hp 3)) (Nat.pow_le_pow_left hf 11))
    _ = _ := by
      rw [mul_pow, show 8 * q = q * 8 by omega, show 15 * q = q * 15 by omega, pow_mul,
        pow_mul, show 22 * q = q * 22 by omega, pow_mul, mul_pow]
      have hfour : 4 ^ q = (2 ^ q) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm q 2, pow_mul]
        norm_num
      simp only [mul_pow]
      rw [hfour]
      ring

theorem elimination_root_constant_le {a x e f k : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    k * a ^ 2 * x ≤ a * x * (1 + 8 * e * f * k * a) := by
  have hp : 1 ≤ 8 * e * f :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by decide) he) hf
  have h := Nat.mul_le_mul_right (k * a) hp
  have hb : k * a ≤ 1 + 8 * e * f * k * a := by nlinarith only [h]
  calc
    _ = a * x * (k * a) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hb

theorem twice_absorber_final_constant_le {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    2 * absorberFinalConstant q r ≤ (4 * q) ^ (22 * q + 1) := by
  calc
    _ ≤ (4 * q) ^ 1 * (4 * q) ^ (22 * q) :=
      Nat.mul_le_mul (by simp only [pow_one]; omega) (absorber_final_constant_le hr hqr)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Both cancellation input densities fit, even after doubling the initial
normalization factor to accommodate a union of two sparse graphs. -/
theorem absorber_elimination_density_constants {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    2 * (q.choose r * (absorberFirstMultiplicity q r) ^ 2 *
      absorberSplittingConstant q r) ≤ (4 * q) ^ (24 * q) ∧
    2 * (q.choose r * (absorberSecondMultiplicity q r) ^ 2 *
      absorberFirstConstant q r) ≤ (4 * q) ^ (24 * q) := by
  have he : 1 ≤ absorberExchangeEdges q r := by
    have hq : 0 < q := by omega
    have hk : 0 < q.choose r := Nat.choose_pos hqr.le
    unfold absorberExchangeEdges
    exact Nat.succ_le_of_lt (by positivity)
  have hf : 1 ≤ r.factorial := Nat.factorial_pos r
  have hfirst : q.choose r * (absorberFirstMultiplicity q r) ^ 2 *
      absorberSplittingConstant q r ≤ absorberFirstConstant q r :=
    elimination_root_constant_le he hf
  have hsecond : q.choose r * (absorberSecondMultiplicity q r) ^ 2 *
      absorberFirstConstant q r ≤ absorberFinalConstant q r :=
    elimination_root_constant_le he hf
  have hfinal : absorberFirstConstant q r ≤ absorberFinalConstant q r := by
    have hK : 1 ≤ absorberSecondMultiplicity q r := by
      unfold absorberSecondMultiplicity
      omega
    calc
      _ ≤ absorberSecondMultiplicity q r * absorberFirstConstant q r :=
        le_mul_of_one_le_left (Nat.zero_le _) hK
      _ ≤ _ := le_mul_of_one_le_right (Nat.zero_le _) (by omega)
  have hbound : 2 * absorberFinalConstant q r ≤ (4 * q) ^ (24 * q) :=
    (twice_absorber_final_constant_le hr hqr).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact ⟨(Nat.mul_le_mul_left 2 (hfirst.trans hfinal)).trans hbound,
    (Nat.mul_le_mul_left 2 hsecond).trans hbound⟩

end Arxiv2411_18291
