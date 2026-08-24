import ErdosProblems.Erdos587.ReciprocalDivisor

/-!
# Harmonic aggregation for reciprocal Weyl sums

The pointwise majorant is uniform in the linear coefficient and the interval
length. Counting its integer superlevel sets replaces the informal dyadic
decomposition by a finite harmonic sum.
-/

open scoped BigOperators

namespace Erdos587

open External.Erdos438.QuadraticWeyl

/-- A nonnegative real number is at most one plus the number of positive
integers below it. The cutoff may be any larger integer. -/
lemma real_le_one_add_card_Icc_le {y : ℝ} {K : ℕ} (hy : 0 ≤ y) (hyK : y ≤ K) :
    y ≤ 1 + (((Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ y)).card : ℝ) := by
  have hf : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  have hfK : ⌊y⌋₊ ≤ K := by exact_mod_cast hf.trans hyK
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ (Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ y) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans hfK⟩, ?_⟩
    exact (by exact_mod_cast hi'.2 : (i : ℝ) ≤ ⌊y⌋₊).trans hf
  have hcard : ⌊y⌋₊ ≤ ((Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ y)).card := by
    simpa using Finset.card_le_card hsub
  have hcardR : (⌊y⌋₊ : ℝ) ≤
      (((Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ y)).card : ℝ) := by exact_mod_cast hcard
  have hlt := Nat.lt_floor_add_one y
  linarith

/-- A correlation is controlled by small-fractional-part counts at the
harmonic thresholds `1/i`. Zero distance is included, never discarded. -/
lemma correlationMajorant_le_one_add_card_near (θ : ℝ) {L K : ℕ}
    (hLK : L ≤ K) (h : ℕ) :
    correlationMajorant θ L h ≤
      1 + (((Finset.Icc 1 K).filter (fun i : ℕ =>
        nearestIntDist (2 * θ * h) ≤ 1 / (i : ℝ))).card : ℝ) := by
  have hy : 0 ≤ correlationMajorant θ L h := correlationMajorant_nonneg θ L h
  have hyK : correlationMajorant θ L h ≤ K := by
    unfold correlationMajorant
    split_ifs
    · exact_mod_cast (Nat.sub_le L h).trans hLK
    · exact min_le_left _ _ |>.trans (by exact_mod_cast (Nat.sub_le L h).trans hLK)
  have hbase := real_le_one_add_card_Icc_le hy hyK
  have hsub : (Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ correlationMajorant θ L h) ⊆
      (Finset.Icc 1 K).filter (fun i : ℕ => nearestIntDist (2 * θ * h) ≤ 1 / (i : ℝ)) := by
    intro i hi
    obtain ⟨hiK, hiy⟩ := Finset.mem_filter.mp hi
    have hiR : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hiK).1
    refine Finset.mem_filter.mpr ⟨hiK, ?_⟩
    by_cases hz : nearestIntDist (2 * θ * h) = 0
    · rw [hz]
      exact one_div_nonneg.mpr hiR.le
    · have hd : 0 < nearestIntDist (2 * θ * h) :=
        (nearestIntDist_nonneg _).lt_of_ne' hz
      have hib : (i : ℝ) ≤ 1 / (2 * nearestIntDist (2 * θ * h)) := by
        exact hiy.trans (by rw [correlationMajorant, if_neg hz]; exact min_le_right _ _)
      have hiprod := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hd)).mp hib
      apply (le_div_iff₀ hiR).mpr
      nlinarith [mul_nonneg hiR.le hd.le]
  have hcardR :
      (((Finset.Icc 1 K).filter (fun i : ℕ => (i : ℝ) ≤ correlationMajorant θ L h)).card : ℝ) ≤
        (((Finset.Icc 1 K).filter (fun i : ℕ =>
          nearestIntDist (2 * θ * h) ≤ 1 / (i : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hbase.trans (add_le_add le_rfl hcardR)

/-- Interchanging two finite superlevel counts. -/
lemma sum_card_filter_swap {α β : Type*} (S : Finset α) (T : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    (∑ a ∈ S, ((T.filter (P a)).card : ℝ)) =
      ∑ b ∈ T, ((S.filter (fun a => P a b)).card : ℝ) := by
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  exact Finset.sum_comm

/-- A `B/i` superlevel count gives a harmonic bound for the sum of the
correlation majorants. The interval length can vary across the family. -/
lemma sum_correlationMajorant_le_of_near_counts {α : Type*}
    (D : Finset α) (θ : α → ℝ) (L : α → ℕ) {K h : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hLK : ∀ r ∈ D, L r ≤ K)
    (hcount : ∀ i ∈ Finset.Icc 1 K,
      ((D.filter (fun r => nearestIntDist (2 * θ r * h) ≤ 1 / (i : ℝ))).card : ℝ) ≤
        B / i) :
    (∑ r ∈ D, correlationMajorant (θ r) (L r) h) ≤
      (D.card : ℝ) + B * (1 + Real.log (K : ℝ)) := by
  calc
    (∑ r ∈ D, correlationMajorant (θ r) (L r) h) ≤
        ∑ r ∈ D, (1 + (((Finset.Icc 1 K).filter (fun i : ℕ =>
          nearestIntDist (2 * θ r * h) ≤ 1 / (i : ℝ))).card : ℝ)) := by
      exact Finset.sum_le_sum (fun r hr =>
        correlationMajorant_le_one_add_card_near (θ r) (hLK r hr) h)
    _ = (D.card : ℝ) +
        ∑ i ∈ Finset.Icc 1 K,
          ((D.filter (fun r => nearestIntDist (2 * θ r * h) ≤ 1 / (i : ℝ))).card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      exact sum_card_filter_swap D (Finset.Icc 1 K) _
    _ ≤ (D.card : ℝ) + ∑ i ∈ Finset.Icc 1 K, B / i :=
      add_le_add le_rfl (Finset.sum_le_sum hcount)
    _ = (D.card : ℝ) + B * ∑ i ∈ Finset.Icc 1 K, (1 : ℝ) / i := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
    _ ≤ (D.card : ℝ) + B * (1 + Real.log (K : ℝ)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [one_div] using sum_Icc_inv_natCast_le_one_add_log K

/-- Use a common upper length in Weyl differencing without losing uniformity
in the original interval length or linear term. -/
lemma norm_quadraticSum_sq_le_common_length (θ β : ℝ) {L K : ℕ} (hLK : L ≤ K) :
    ‖quadraticSum θ β L‖ ^ 2 ≤
      K + 2 * ∑ h ∈ Finset.Icc 1 K, correlationMajorant θ L h := by
  have hweyl := norm_quadraticSum_sq_le θ β L
  have heq : (∑ h ∈ Finset.range L, correlationMajorant θ L (h + 1)) =
      ∑ h ∈ Finset.Icc 1 L, correlationMajorant θ L h := by
    apply Finset.sum_bij (fun h _ => h + 1)
    · intro h hh
      have := Finset.mem_range.mp hh
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro h₁ hh₁ h₂ hh₂ heq
      omega
    · intro h hh
      have := Finset.mem_Icc.mp hh
      exact ⟨h - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro h hh
      rfl
  rw [heq] at hweyl
  apply hweyl.trans
  apply add_le_add (by exact_mod_cast hLK)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1, (Finset.mem_Icc.mp hh).2.trans hLK⟩
  · intro h hh hnot
    exact correlationMajorant_nonneg θ L h

/-- Uniform quadratic mean from the small-fractional-part counts.
All linear coefficients and all lengths up to `K` may vary independently. -/
theorem sum_norm_quadraticSum_sq_le_of_near_counts {α : Type*}
    (D : Finset α) (θ β : α → ℝ) (L : α → ℕ) (K : ℕ) (B : ℕ → ℝ)
    (hB : ∀ h ∈ Finset.Icc 1 K, 0 ≤ B h)
    (hLK : ∀ r ∈ D, L r ≤ K)
    (hcount : ∀ h ∈ Finset.Icc 1 K, ∀ i ∈ Finset.Icc 1 K,
      ((D.filter (fun r => nearestIntDist (2 * θ r * h) ≤ 1 / (i : ℝ))).card : ℝ) ≤
        B h / i) :
    (∑ r ∈ D, ‖quadraticSum (θ r) (β r) (L r)‖ ^ 2) ≤
      3 * (D.card : ℝ) * K + 2 * (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h := by
  have hsum : (∑ r ∈ D, ∑ h ∈ Finset.Icc 1 K, correlationMajorant (θ r) (L r) h) ≤
      (K : ℝ) * D.card + (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h := by
    rw [Finset.sum_comm]
    calc
      (∑ h ∈ Finset.Icc 1 K, ∑ r ∈ D, correlationMajorant (θ r) (L r) h) ≤
          ∑ h ∈ Finset.Icc 1 K, ((D.card : ℝ) + B h * (1 + Real.log (K : ℝ))) :=
        Finset.sum_le_sum (fun h hh =>
          sum_correlationMajorant_le_of_near_counts D θ L (hB h hh) hLK (hcount h hh))
      _ = (K : ℝ) * D.card + (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  calc
    (∑ r ∈ D, ‖quadraticSum (θ r) (β r) (L r)‖ ^ 2) ≤
        ∑ r ∈ D, ((K : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 K, correlationMajorant (θ r) (L r) h) :=
      Finset.sum_le_sum (fun r hr => norm_quadraticSum_sq_le_common_length (θ r) (β r) (hLK r hr))
    _ = (D.card : ℝ) * K + 2 *
        ∑ r ∈ D, ∑ h ∈ Finset.Icc 1 K, correlationMajorant (θ r) (L r) h := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D.card : ℝ) * K + 2 *
        ((K : ℝ) * D.card + (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h) := by
      linarith
    _ = 3 * (D.card : ℝ) * K + 2 * (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h := by ring

/-- Rounding the reciprocal cutoff costs only an absolute factor. -/
lemma reciprocal_cutoff_bounds {i K R c : ℕ} (hi : i ∈ Finset.Icc 1 K)
    (hKR : K ≤ R) (hc : 0 < c) (hc8 : c ≤ 8) :
    let S := 2 * c * R / i + 1
    0 < S ∧ R / K ≤ 2 * S + 1 ∧ S ≤ 16 * R + 1 ∧
      ((2 * c * R : ℕ) : ℝ) / i ≤ S ∧
      ((2 * S + 1 : ℕ) : ℝ) ≤ 35 * (R : ℝ) / i ∧ 2 * S + 1 ≤ 35 * R := by
  dsimp only
  let S := 2 * c * R / i + 1
  have hi0 : 0 < i := (Finset.mem_Icc.mp hi).1
  have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
  have hiR : i ≤ R := hiK.trans hKR
  have hiReal : (0 : ℝ) < i := by exact_mod_cast hi0
  have hR : R ≤ 2 * c * R := by nlinarith
  have hRi : R / K * i ≤ 2 * c * R := by
    calc
      R / K * i ≤ R / K * K := Nat.mul_le_mul_left _ hiK
      _ ≤ R := Nat.div_mul_le_self R K
      _ ≤ 2 * c * R := hR
  have hsmall : R / K ≤ 2 * c * R / i := (Nat.le_div_iff_mul_le hi0).mpr hRi
  have hSbound : S ≤ 16 * R + 1 := by
    have hdiv := Nat.div_le_self (2 * c * R) i
    dsimp [S]
    nlinarith
  have hSi : S * i ≤ 2 * c * R + i := by
    have hdiv := Nat.div_mul_le_self (2 * c * R) i
    dsimp [S]
    nlinarith
  have hSi' : 2 * c * R ≤ S * i := by
    have hmod := Nat.mod_lt (2 * c * R) hi0
    have hrem := Nat.div_add_mod (2 * c * R) i
    dsimp [S]
    nlinarith
  have hYi : (2 * S + 1) * i ≤ 35 * R := by nlinarith
  refine ⟨Nat.zero_lt_succ _, ?_, hSbound, ?_, ?_, ?_⟩
  · exact hsmall.trans (by omega)
  · apply (div_le_iff₀ hiReal).mpr
    exact_mod_cast hSi'
  · apply (le_div_iff₀ hiReal).mpr
    exact_mod_cast hYi
  · exact (Nat.le_mul_of_pos_right _ hi0).trans hYi

/-- Harmonic superlevel counts for the reciprocal coefficients. A fixed
power-scale size hypothesis replaces all pointwise divisor maxima. -/
theorem exists_reciprocal_near_harmonic_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (a v q c R K : ℕ), 0 < a → a ≤ 4 → 0 < c → c ≤ 8 → 0 < K → K ≤ R →
        16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ h ∈ Finset.Icc 1 K, ∀ i ∈ Finset.Icc 1 K,
          ((D.filter (fun r => nearestIntDist
            (((((2 * a * h) * v : ℕ) : ℤ) * inv r : ℤ) / ((c * r : ℕ) : ℝ)) ≤
              1 / (i : ℝ))).card : ℝ) ≤
            ((2 * a * h).divisors.card : ℝ) * C * R * Real.log (35 * (R : ℝ)) ^ O / i := by
  obtain ⟨C, hC, O, hO, hnear⟩ := exists_near_reciprocal_count_bound j
  refine ⟨35 * C, by positivity, O, hO, ?_⟩
  intro a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv h hh i hi
  let S := 2 * c * R / i + 1
  have hcut := reciprocal_cutoff_bounds hi hKR hc hc8
  change 0 < S ∧ _ at hcut
  obtain ⟨hS, hsmall, hSbound, hδS, hYi, hYR⟩ := hcut
  have hR : 0 < R := hK.trans_le hKR
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hhK : h ≤ K := (Finset.mem_Icc.mp hh).2
  have hm : 0 < 2 * a * h := by positivity
  have hm8 : 2 * a * h ≤ 8 * K := by nlinarith
  have hmq : 2 * a * h < q := by omega
  have hsize : (2 * a * h) * v + q * S ≤ (2 * S + 1) ^ (4 ^ j) := by
    have hqR : q ≤ q * R := Nat.le_mul_of_pos_right _ hR
    calc
      (2 * a * h) * v + q * S ≤ (8 * K) * v + q * (16 * R + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hm8) (Nat.mul_le_mul_left _ hSbound)
      _ ≤ 64 * (q * R + v * K + 1) := by nlinarith
      _ ≤ (R / K) ^ (4 ^ j) := hroot
      _ ≤ (2 * S + 1) ^ (4 ^ j) := Nat.pow_le_pow_left hsmall _
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hδ : ((2 * c * R : ℕ) : ℝ) * (1 / (i : ℝ)) ≤ S := by
    simpa only [mul_one_div] using hδS
  have hb := hnear (2 * a * h) v q c R S hm hmq hcop hc hS hsize
    D inv hD hinv (1 / (i : ℝ)) (one_div_nonneg.mpr hi0.le) hδ
  have hY0 : (0 : ℝ) < (2 * S + 1 : ℕ) := by positivity
  have hYlog : 0 ≤ Real.log (2 * S + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * S + 1 by omega))
  have hlog : Real.log (2 * S + 1 : ℕ) ≤ Real.log (35 * (R : ℝ)) := by
    apply Real.log_le_log hY0
    exact_mod_cast hYR
  have hpow := pow_le_pow_left₀ hYlog hlog O
  have hlogR : 0 ≤ Real.log (35 * (R : ℝ)) ^ O := pow_nonneg (hYlog.trans hlog) _
  calc
    ((D.filter (fun r => nearestIntDist
        (((((2 * a * h) * v : ℕ) : ℤ) * inv r : ℤ) / ((c * r : ℕ) : ℝ)) ≤
          1 / (i : ℝ))).card : ℝ) ≤
        ((2 * a * h).divisors.card : ℝ) * C * (2 * S + 1 : ℕ) *
          Real.log (2 * S + 1 : ℕ) ^ O := hb
    _ ≤ ((2 * a * h).divisors.card : ℝ) * C *
        (35 * (R : ℝ) / i) * Real.log (35 * (R : ℝ)) ^ O := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hYi (mul_nonneg (Nat.cast_nonneg _) hC.le)
      · exact hpow
      · positivity
      · positivity
    _ = ((2 * a * h).divisors.card : ℝ) * (35 * C) * R *
        Real.log (35 * (R : ℝ)) ^ O / i := by ring

/-- The numerator divisor costs have an ordinary divisor mean. -/
lemma sum_small_numerator_divisors_le {a : ℕ} (ha : a ≤ 4) (K : ℕ) :
    (∑ h ∈ Finset.Icc 1 K, ((2 * a * h).divisors.card : ℝ)) ≤
      8 * ∑ h ∈ Finset.Icc 1 K, (h.divisors.card : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hsmall : (2 * a).divisors.card ≤ 8 := (Nat.card_divisors_le_self _).trans (by omega)
  have hcount := (card_divisors_mul_le_product (2 * a) h).trans
    (Nat.mul_le_mul_right h.divisors.card hsmall)
  exact_mod_cast hcount

/-- The rational coefficient obtained after quadratic reciprocity. The
chosen integer inverse may be signed. -/
noncomputable def reciprocalQuadraticFrequency (a v c : ℕ) (inv : ℕ → ℤ) (r : ℕ) : ℝ :=
  (a * v : ℕ) * (inv r : ℝ) / (c * r : ℕ)

lemma reciprocalQuadraticFrequency_double (a v c h : ℕ) (inv : ℕ → ℤ) (r : ℕ) :
    2 * reciprocalQuadraticFrequency a v c inv r * h =
      (((((2 * a * h) * v : ℕ) : ℤ) * inv r : ℤ) / ((c * r : ℕ) : ℝ)) := by
  unfold reciprocalQuadraticFrequency
  push_cast
  ring

/-- The reciprocal quadratic mean, uniformly for independently chosen
linear coefficients and interval lengths. All constants depend only on the
fixed power-scale parameter `j`. -/
theorem exists_reciprocal_quadratic_mean_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (a v q c R K : ℕ), 0 < a → a ≤ 4 → 0 < c → c ≤ 8 → 3 ≤ K → K ≤ R →
        16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ (β : ℕ → ℝ) (L : ℕ → ℕ), (∀ r ∈ D, L r ≤ K) →
          (∑ r ∈ D, ‖quadraticSum (reciprocalQuadraticFrequency a v c inv r) (β r) (L r)‖ ^ 2) ≤
            C * R * K * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hcounts⟩ := exists_reciprocal_near_harmonic_bound j
  obtain ⟨H, hH, E, hE, hdivmean⟩ := exists_divisorPower_mean_log_bound 1
  simp only [pow_one] at hdivmean
  refine ⟨6 + 32 * C * H, by positivity, O + E + 1, by omega, ?_⟩
  intro a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv β L hLK
  let F : ℝ := Real.log (35 * (R : ℝ))
  let B : ℕ → ℝ := fun h => ((2 * a * h).divisors.card : ℝ) * C * R * F ^ O
  have hKpos : 0 < K := by omega
  have hKlog : 1 ≤ Real.log (K : ℝ) := one_le_log_nat_of_three_le hK
  have hlog : Real.log (K : ℝ) ≤ F := by
    apply Real.log_le_log (by exact_mod_cast hKpos)
    have hKR' : (K : ℝ) ≤ R := by exact_mod_cast hKR
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  have hF : 1 ≤ F := hKlog.trans hlog
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hB : ∀ h ∈ Finset.Icc 1 K, 0 ≤ B h := by
    intro h hh
    dsimp [B]
    positivity
  have hcount : ∀ h ∈ Finset.Icc 1 K, ∀ i ∈ Finset.Icc 1 K,
      ((D.filter (fun r => nearestIntDist
        (2 * reciprocalQuadraticFrequency a v c inv r * h) ≤ 1 / (i : ℝ))).card : ℝ) ≤ B h / i := by
    intro h hh i hi
    simp_rw [reciprocalQuadraticFrequency_double]
    exact hcounts a v q c R K ha ha4 hc hc8 hKpos hKR hq hcop hroot D inv hD hinv h hh i hi
  have hweyl := sum_norm_quadraticSum_sq_le_of_near_counts D
    (reciprocalQuadraticFrequency a v c inv) β L K B hB hLK hcount
  have hdiv : (∑ h ∈ Finset.Icc 1 K, ((2 * a * h).divisors.card : ℝ)) ≤
      8 * H * K * F ^ E := by
    calc
      (∑ h ∈ Finset.Icc 1 K, ((2 * a * h).divisors.card : ℝ)) ≤
          8 * ∑ h ∈ Finset.Icc 1 K, (h.divisors.card : ℝ) := sum_small_numerator_divisors_le ha4 K
      _ ≤ 8 * (H * K * Real.log (K : ℝ) ^ E) :=
        mul_le_mul_of_nonneg_left (hdivmean K hK) (by norm_num)
      _ ≤ 8 * (H * K * F ^ E) := by
        gcongr
      _ = 8 * H * K * F ^ E := by ring
  have hsum : (∑ h ∈ Finset.Icc 1 K, B h) ≤ 8 * C * H * R * K * F ^ (O + E) := by
    calc
      (∑ h ∈ Finset.Icc 1 K, B h) = C * R * F ^ O *
          ∑ h ∈ Finset.Icc 1 K, ((2 * a * h).divisors.card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        dsimp [B]
        ring
      _ ≤ C * R * F ^ O * (8 * H * K * F ^ E) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 8 * C * H * R * K * F ^ (O + E) := by rw [pow_add]; ring
  have hcard : D.card ≤ 2 * R := by
    have hsub : D ⊆ Finset.Icc 1 (2 * R) := fun r hr => Finset.mem_Icc.mpr (hD r hr)
    simpa using Finset.card_le_card hsub
  have hcardR : (D.card : ℝ) ≤ 2 * R := by exact_mod_cast hcard
  have hfirst : 3 * (D.card : ℝ) * K ≤ 6 * (R : ℝ) * K := by
    calc
      3 * (D.card : ℝ) * K ≤ 3 * (2 * (R : ℝ)) * K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
          (Nat.cast_nonneg _)
      _ = 6 * (R : ℝ) * K := by ring
  have hlogfactor : 1 + Real.log (K : ℝ) ≤ 2 * F := by linarith
  have hterm : 2 * (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h ≤
      2 * (2 * F) * (8 * C * H * R * K * F ^ (O + E)) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hlogfactor (by norm_num)) hsum
      (Finset.sum_nonneg hB) (by positivity)
  apply hweyl.trans
  calc
    3 * (D.card : ℝ) * K + 2 * (1 + Real.log (K : ℝ)) * ∑ h ∈ Finset.Icc 1 K, B h ≤
        6 * (R : ℝ) * K + 2 * (2 * F) * (8 * C * H * R * K * F ^ (O + E)) :=
      add_le_add hfirst hterm
    _ = 6 * (R : ℝ) * K + 32 * C * H * R * K * F ^ (O + E + 1) := by
      rw [pow_succ]
      ring
    _ ≤ 6 * (R : ℝ) * K * F ^ (O + E + 1) + 32 * C * H * R * K * F ^ (O + E + 1) := by
      apply add_le_add _ le_rfl
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hF)
    _ = (6 + 32 * C * H) * R * K * Real.log (35 * (R : ℝ)) ^ (O + E + 1) := by
      dsimp [F]
      ring

/-- Translating a quadratic interval changes only the linear coefficient
and a unit-modulus constant. In particular the starting point may be negative. -/
lemma norm_shifted_quadraticSum (θ β : ℝ) (s : ℤ) (L : ℕ) :
    ‖∑ z ∈ Finset.range L, phase (θ * ((s : ℝ) + z) ^ 2 + β * ((s : ℝ) + z))‖ =
      ‖quadraticSum θ (β + 2 * θ * s) L‖ := by
  have heq (z : ℕ) : phase (θ * ((s : ℝ) + z) ^ 2 + β * ((s : ℝ) + z)) =
      phase (θ * (s : ℝ) ^ 2 + β * s) *
        phase (θ * (z : ℝ) ^ 2 + (β + 2 * θ * s) * z) := by
    rw [← phase_add]
    congr 1
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum, norm_mul, norm_phase, one_mul]
  rfl

/-- The reciprocal mean holds for arbitrary translated intervals, with
independent starting points, lengths, and linear coefficients for every `r`. -/
theorem exists_reciprocal_interval_mean_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (a v q c R K : ℕ), 0 < a → a ≤ 4 → 0 < c → c ≤ 8 → 3 ≤ K → K ≤ R →
        16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ (β : ℕ → ℝ) (s : ℕ → ℤ) (L : ℕ → ℕ), (∀ r ∈ D, L r ≤ K) →
          (∑ r ∈ D, ‖∑ z ∈ Finset.range (L r), phase
            (reciprocalQuadraticFrequency a v c inv r * ((s r : ℝ) + z) ^ 2 +
              β r * ((s r : ℝ) + z))‖ ^ 2) ≤
            C * R * K * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_reciprocal_quadratic_mean_bound j
  refine ⟨C, hC, O, hO, ?_⟩
  intro a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv β s L hLK
  simp_rw [norm_shifted_quadraticSum]
  exact hmean a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv _ L hLK

end Erdos587
