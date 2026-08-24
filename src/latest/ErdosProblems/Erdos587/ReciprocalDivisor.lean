import ErdosProblems.Erdos587.NVDevelopment

/-!
# Divisor estimates for reciprocal quadratic sums

Iterating the fourth-root small-divisor selection gives arbitrarily small
fixed root scales without a pointwise maximal-divisor loss. This is the
arithmetic input to the short-progression estimate in Section 5 of `tex/587.tex`.

The exponents are deliberately not optimized: root orders `4 ^ j` suffice
for each fixed power saving required by the reciprocity argument.
-/

open scoped BigOperators

namespace Erdos587

/-- The constant accumulated after `j` fourth-root selections. -/
def iteratedDivisorConstant : ℕ → ℕ
  | 0 => 1
  | j + 1 => iteratedDivisorConstant j * 64 ^ (12 ^ j)

lemma iteratedDivisorConstant_pos (j : ℕ) : 0 < iteratedDivisorConstant j := by
  induction j with
  | zero => exact Nat.zero_lt_one
  | succ j ih => exact Nat.mul_pos ih (pow_pos (by norm_num) _)

/-- A divisor at any fixed iterated fourth-root scale still controls the
divisor count by a fixed moment. -/
theorem exists_iterated_small_divisor (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∃ d : ℕ, d ∣ n ∧ d ≠ 0 ∧ d ^ (4 ^ j) ≤ n ∧
      n.divisors.card ≤ iteratedDivisorConstant j * d.divisors.card ^ (12 ^ j) := by
  induction j with
  | zero =>
    refine ⟨n, dvd_refl n, hn, ?_, ?_⟩ <;> simp [iteratedDivisorConstant]
  | succ j ih =>
    obtain ⟨d, hdn, hd, hdpow, hcount⟩ := ih
    let e := nvSmallDivisor d
    have hed : e ∣ d := nvSmallDivisor_dvd hd
    have he : e ≠ 0 := nvSmallDivisor_ne_zero hd
    have hepow : e ^ 4 ≤ d := nvSmallDivisor_pow_four_le hd
    have hecount : d.divisors.card ≤ 64 * e.divisors.card ^ 12 :=
      card_divisors_le_smallDivisor hd
    refine ⟨e, hed.trans hdn, he, ?_, ?_⟩
    · calc
        e ^ (4 ^ (j + 1)) = (e ^ 4) ^ (4 ^ j) := by
          rw [← pow_mul, pow_succ]
          congr 1
          exact Nat.mul_comm _ _
        _ ≤ d ^ (4 ^ j) := Nat.pow_le_pow_left hepow _
        _ ≤ n := hdpow
    · calc
        n.divisors.card ≤
            iteratedDivisorConstant j * d.divisors.card ^ (12 ^ j) := hcount
        _ ≤ iteratedDivisorConstant j * (64 * e.divisors.card ^ 12) ^ (12 ^ j) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hecount _)
        _ = iteratedDivisorConstant (j + 1) * e.divisors.card ^ (12 ^ (j + 1)) := by
          rw [iteratedDivisorConstant, mul_pow, ← pow_mul, pow_succ]
          rw [Nat.mul_comm 12 (12 ^ j)]
          exact (Nat.mul_assoc _ _ _).symm

/-- A single ambient cutoff suffices whenever all values are bounded by
its `4 ^ j`-th power. This avoids rounding real roots. -/
theorem card_divisors_le_iterated_small_divisor_sum
    (j : ℕ) {n D : ℕ} (hn : n ≠ 0) (hsize : n ≤ D ^ (4 ^ j)) :
    (n.divisors.card : ℝ) ≤
      (iteratedDivisorConstant j : ℝ) *
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
          (d.divisors.card : ℝ) ^ (12 ^ j) := by
  obtain ⟨d, hdn, hd, hdpow, hcount⟩ := exists_iterated_small_divisor j hn
  have hdD : d ≤ D :=
    (Nat.pow_le_pow_iff_left (pow_ne_zero j (by norm_num))).mp (hdpow.trans hsize)
  have hdmem : d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hd, hdD⟩, hdn⟩
  have hcountR : (n.divisors.card : ℝ) ≤
      (iteratedDivisorConstant j : ℝ) * (d.divisors.card : ℝ) ^ (12 ^ j) := by
    exact_mod_cast hcount
  exact hcountR.trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun e => (e.divisors.card : ℝ) ^ (12 ^ j))
      (fun e _ => by positivity) hdmem) (by positivity))

/-- A coprime integer progression occupies at most one residue class for
each divisor, including when some progression values are negative. -/
lemma card_filter_affine_dvd_le {A B : ℤ} (hcop : IsCoprime A B)
    {d : ℕ} (hd : 0 < d) (Y : ℕ) :
    ((Finset.Icc 1 Y).filter (fun s : ℕ => d ∣ (A + B * s).natAbs)).card ≤ Y / d + 1 := by
  apply card_le_div_add_one_of_pairwise_modEq
    (fun _ hs => Finset.filter_subset _ _ hs) hd
  intro s hs t ht
  have hsdiv : (d : ℤ) ∣ A + B * s := by
    exact Int.natCast_dvd.mpr (Finset.mem_filter.mp hs).2
  have htdiv : (d : ℤ) ∣ A + B * t := by
    exact Int.natCast_dvd.mpr (Finset.mem_filter.mp ht).2
  have hdcop : IsCoprime (d : ℤ) B :=
    (hcop.add_mul_left_left (s : ℤ)).of_isCoprime_of_dvd_left hsdiv
  have hmul : (d : ℤ) ∣ B * ((t : ℤ) - s) := by
    rw [show B * ((t : ℤ) - s) = (A + B * t) - (A + B * s) by ring]
    exact dvd_sub htdiv hsdiv
  have hmod : (s : ℤ) ≡ (t : ℤ) [ZMOD (d : ℤ)] :=
    Int.modEq_of_dvd (hdcop.dvd_of_dvd_mul_left hmul)
  exact Int.natCast_modEq_iff.mp hmod

/-- Interchange the short-divisor sum with an arbitrary finite family. -/
lemma sum_card_divisors_le_iterated_moments {α : Type*}
    (j : ℕ) (S : Finset α) (f : α → ℕ) {D : ℕ}
    (hn : ∀ s ∈ S, f s ≠ 0) (hsize : ∀ s ∈ S, f s ≤ D ^ (4 ^ j)) :
    (∑ s ∈ S, ((f s).divisors.card : ℝ)) ≤
      (iteratedDivisorConstant j : ℝ) *
        ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) *
          ((S.filter (fun s => d ∣ f s)).card : ℝ) := by
  classical
  calc
    (∑ s ∈ S, ((f s).divisors.card : ℝ)) ≤
        ∑ s ∈ S, (iteratedDivisorConstant j : ℝ) *
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ f s),
            (d.divisors.card : ℝ) ^ (12 ^ j) := by
      apply Finset.sum_le_sum
      intro s hs
      exact card_divisors_le_iterated_small_divisor_sum j (hn s hs) (hsize s hs)
    _ = (iteratedDivisorConstant j : ℝ) *
        ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) *
          ((S.filter (fun s => d ∣ f s)).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _

/-- Divisibility along a coprime progression, in the harmonic form needed
for averaging. -/
lemma card_filter_affine_dvd_le_harmonic {A B : ℤ} (hcop : IsCoprime A B)
    {d Y : ℕ} (hd : d ∈ Finset.Icc 1 Y) :
    (((Finset.Icc 1 Y).filter (fun s : ℕ => d ∣ (A + B * s).natAbs)).card : ℝ) ≤
      2 * (Y : ℝ) / d := by
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdY : (d : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hone : (1 : ℝ) ≤ (Y : ℝ) / d := (le_div_iff₀ hdR).mpr (by simpa using hdY)
  calc
    (((Finset.Icc 1 Y).filter (fun s : ℕ => d ∣ (A + B * s).natAbs)).card : ℝ) ≤
        (Y / d + 1 : ℕ) := by exact_mod_cast card_filter_affine_dvd_le hcop hdpos Y
    _ ≤ (Y : ℝ) / d + 1 := by
      push_cast
      have hdiv : ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) / d := Nat.cast_div_le
      linarith
    _ ≤ 2 * (Y : ℝ) / d := by rw [mul_div_assoc]; linarith

/-- The short-progression mean at every fixed iterated fourth-root scale.
Both constants depend only on the number of iterations, not on the integer
coefficients or on a pointwise bound for their divisors. -/
theorem exists_affine_divisor_mean_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (A B : ℤ), IsCoprime A B → ∀ Y : ℕ, 3 ≤ Y →
        (∀ s ∈ Finset.Icc 1 Y, A + B * s ≠ 0) →
        (∀ s ∈ Finset.Icc 1 Y, (A + B * s).natAbs ≤ Y ^ (4 ^ j)) →
        (∑ s ∈ Finset.Icc 1 Y, ((A + B * s).natAbs.divisors.card : ℝ)) ≤
          K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_weighted_divisorPower_log_bound (12 ^ j)
  let C : ℝ := iteratedDivisorConstant j
  have hC : 0 < C := by dsimp [C]; exact_mod_cast iteratedDivisorConstant_pos j
  refine ⟨C * 2 * K, by positivity, O, hO, ?_⟩
  intro A B hcop Y hY hn hsize
  have hstart := sum_card_divisors_le_iterated_moments j (Finset.Icc 1 Y)
    (fun s => (A + B * s).natAbs) (fun s hs => Int.natAbs_ne_zero.mpr (hn s hs)) hsize
  calc
    (∑ s ∈ Finset.Icc 1 Y, ((A + B * s).natAbs.divisors.card : ℝ)) ≤
        C * ∑ d ∈ Finset.Icc 1 Y, (d.divisors.card : ℝ) ^ (12 ^ j) *
          (((Finset.Icc 1 Y).filter (fun s : ℕ => d ∣ (A + B * s).natAbs)).card : ℝ) := hstart
    _ ≤ C * ∑ d ∈ Finset.Icc 1 Y,
        (d.divisors.card : ℝ) ^ (12 ^ j) * (2 * (Y : ℝ) / d) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (card_filter_affine_dvd_le_harmonic hcop hd)
        (by positivity)
    _ = C * (2 * (Y : ℝ)) *
        ∑ d ∈ Finset.Icc 1 Y, (d.divisors.card : ℝ) ^ (12 ^ j) / d := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ C * (2 * (Y : ℝ)) * (K * Real.log (Y : ℝ) ^ O) :=
      mul_le_mul_of_nonneg_left (hmean Y hY) (by positivity)
    _ = C * 2 * K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by ring

/-- Divisor counts are submultiplicative even without coprimality. -/
lemma card_divisors_mul_le_product (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  classical
  obtain rfl | hm := eq_or_ne m 0
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hsub : (m * n).divisors ⊆
      (m.divisors ×ˢ n.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    obtain ⟨a, b, ha, hb, hab⟩ := dvd_mul.mp (Nat.mem_divisors.mp hd).1
    exact Finset.mem_image.mpr ⟨(a, b),
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨ha, hm⟩,
        Nat.mem_divisors.mpr ⟨hb, hn⟩⟩, hab.symm⟩
  calc
    (m * n).divisors.card ≤
        ((m.divisors ×ˢ n.divisors).image (fun p => p.1 * p.2)).card :=
      Finset.card_le_card hsub
    _ ≤ (m.divisors ×ˢ n.divisors).card := Finset.card_image_le
    _ = m.divisors.card * n.divisors.card := Finset.card_product _ _

/-- Removing the common divisor of both coefficients costs only its divisor
count, not the worst divisor count among the progression values. -/
theorem exists_affine_divisor_mean_gcd_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (A B : ℤ), B ≠ 0 → ∀ Y : ℕ, 3 ≤ Y →
        (∀ s ∈ Finset.Icc 1 Y, A + B * s ≠ 0) →
        (∀ s ∈ Finset.Icc 1 Y, (A + B * s).natAbs ≤ Y ^ (4 ^ j)) →
        (∑ s ∈ Finset.Icc 1 Y, ((A + B * s).natAbs.divisors.card : ℝ)) ≤
          ((A.gcd B).divisors.card : ℝ) * K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_affine_divisor_mean_bound j
  refine ⟨K, hK, O, hO, ?_⟩
  intro A B hB Y hY hn hsize
  have hg : 0 < A.gcd B := Int.gcd_pos_of_ne_zero_right A hB
  obtain ⟨A', B', hcop, hA', hB'⟩ := Int.exists_gcd_one hg
  have hfactor (s : ℕ) : A + B * s = (A.gcd B : ℤ) * (A' + B' * s) := by
    calc
      A + B * s = A' * (A.gcd B : ℤ) + (B' * (A.gcd B : ℤ)) * s :=
        congrArg₂ (· + ·) hA' (congrArg (fun b : ℤ => b * s) hB')
      _ = (A.gcd B : ℤ) * (A' + B' * s) := by ring
  have habs (s : ℕ) : (A + B * s).natAbs = A.gcd B * (A' + B' * s).natAbs := by
    rw [hfactor s, Int.natAbs_mul, Int.natAbs_natCast]
  have hn' : ∀ s ∈ Finset.Icc 1 Y, A' + B' * s ≠ 0 := by
    intro s hs hz
    apply hn s hs
    rw [hfactor s, hz, mul_zero]
  have hsize' : ∀ s ∈ Finset.Icc 1 Y, (A' + B' * s).natAbs ≤ Y ^ (4 ^ j) := by
    intro s hs
    calc
      (A' + B' * s).natAbs ≤ A.gcd B * (A' + B' * s).natAbs :=
        Nat.le_mul_of_pos_left _ hg
      _ = (A + B * s).natAbs := (habs s).symm
      _ ≤ Y ^ (4 ^ j) := hsize s hs
  have hnormalized := hmean A' B' (Int.isCoprime_iff_gcd_eq_one.mpr hcop)
    Y hY hn' hsize'
  calc
    (∑ s ∈ Finset.Icc 1 Y, ((A + B * s).natAbs.divisors.card : ℝ)) ≤
        ∑ s ∈ Finset.Icc 1 Y, ((A.gcd B).divisors.card : ℝ) *
          ((A' + B' * s).natAbs.divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [habs s]
      exact_mod_cast card_divisors_mul_le_product (A.gcd B) (A' + B' * s).natAbs
    _ = ((A.gcd B).divisors.card : ℝ) *
        ∑ s ∈ Finset.Icc 1 Y, ((A' + B' * s).natAbs.divisors.card : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((A.gcd B).divisors.card : ℝ) *
        (K * (Y : ℝ) * Real.log (Y : ℝ) ^ O) :=
      mul_le_mul_of_nonneg_left hnormalized (Nat.cast_nonneg _)
    _ = ((A.gcd B).divisors.card : ℝ) * K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by ring

/-- Counting reciprocal denominators by the divisors of each nonzero
linear value. The ambient set of denominators need not itself be an interval. -/
lemma card_reciprocal_divisibility_le {α : Type*}
    (R : Finset ℕ) (S : Finset α) (f : α → ℕ) {c : ℕ} (hc : c ≠ 0)
    (hf : ∀ s ∈ S, f s ≠ 0) :
    (R.filter (fun r => ∃ s ∈ S, c * r ∣ f s)).card ≤
      ∑ s ∈ S, (f s).divisors.card := by
  classical
  have hset : R.filter (fun r => ∃ s ∈ S, c * r ∣ f s) =
      S.biUnion (fun s => R.filter (fun r => c * r ∣ f s)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hr, s, hs, hd⟩
      exact ⟨s, hs, hr, hd⟩
    · rintro ⟨s, hs, hr, hd⟩
      exact ⟨hr, s, hs, hd⟩
  rw [hset]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro s hs
  let T := R.filter (fun r => c * r ∣ f s)
  have hinj : Set.InjOn (fun r : ℕ => c * r) T := by
    intro r hr t ht heq
    exact mul_left_cancel₀ hc heq
  have hsub : T.image (fun r => c * r) ⊆ (f s).divisors := by
    intro n hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hr).2, hf s hs⟩
  calc
    T.card = (T.image (fun r => c * r)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (f s).divisors.card := Finset.card_le_card hsub

/-- A ready-to-use reciprocal-denominator count after reindexing the
possible remainders by `1,...,Y`. -/
theorem exists_reciprocal_divisibility_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (A B : ℤ), B ≠ 0 → ∀ (Y c : ℕ), 3 ≤ Y → c ≠ 0 →
        (∀ s ∈ Finset.Icc 1 Y, A + B * s ≠ 0) →
        (∀ s ∈ Finset.Icc 1 Y, (A + B * s).natAbs ≤ Y ^ (4 ^ j)) →
        ∀ R : Finset ℕ,
          ((R.filter (fun r => ∃ s ∈ Finset.Icc 1 Y,
            c * r ∣ (A + B * s).natAbs)).card : ℝ) ≤
            ((A.gcd B).divisors.card : ℝ) * K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_affine_divisor_mean_gcd_bound j
  refine ⟨K, hK, O, hO, ?_⟩
  intro A B hB Y c hY hc hn hsize R
  have hcount := card_reciprocal_divisibility_le R (Finset.Icc 1 Y)
    (fun s => (A + B * s).natAbs) hc (fun s hs => Int.natAbs_ne_zero.mpr (hn s hs))
  have hcountR : ((R.filter (fun r => ∃ s ∈ Finset.Icc 1 Y,
      c * r ∣ (A + B * s).natAbs)).card : ℝ) ≤
      ∑ s ∈ Finset.Icc 1 Y, ((A + B * s).natAbs.divisors.card : ℝ) := by
    exact_mod_cast hcount
  exact hcountR.trans (hmean A B hB Y hY hn hsize)

/-- A small fractional part for an inverse coefficient produces a small
integer remainder in a divisibility condition with varying denominator. -/
lemma exists_reciprocal_remainder {m q inv : ℤ} {d : ℕ} (hd : 0 < d)
    (hinv : (d : ℤ) ∣ q * inv - 1) {δ : ℝ}
    (hnear : nearestIntDist ((m * inv : ℤ) / (d : ℝ)) ≤ δ) :
    ∃ s : ℤ, |(s : ℝ)| ≤ (d : ℝ) * δ ∧ (d : ℤ) ∣ m - q * s := by
  let x : ℝ := (m * inv : ℤ) / (d : ℝ)
  let s : ℤ := m * inv - (d : ℤ) * round x
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsR : (s : ℝ) = (d : ℝ) * (x - round x) := by
    dsimp [s, x]
    push_cast
    field_simp
  refine ⟨s, ?_, ?_⟩
  · calc
      |(s : ℝ)| = (d : ℝ) * nearestIntDist x := by
        rw [hsR, abs_mul, abs_of_pos hdR]
        rfl
      _ ≤ (d : ℝ) * δ := mul_le_mul_of_nonneg_left hnear hdR.le
  · have h₁ : (d : ℤ) ∣ m * (q * inv - 1) := dvd_mul_of_dvd_right hinv m
    have h₂ : (d : ℤ) ∣ q * ((d : ℤ) * round x) :=
      dvd_mul_of_dvd_right (dvd_mul_right _ _) q
    rw [show m - q * s = q * ((d : ℤ) * round x) - m * (q * inv - 1) by
      dsimp [s]
      ring]
    exact dvd_sub h₂ h₁

/-- The reciprocal-divisor encoding never encounters zero if the original
numerator is smaller than the coprime modulus. -/
lemma reciprocal_linear_value_ne_zero {m v q : ℕ} (hm : 0 < m)
    (hmq : m < q) (hcop : q.Coprime v) (s : ℤ) :
    ((m * v : ℕ) : ℤ) - (q : ℤ) * s ≠ 0 := by
  intro hz
  have hdivZ : (q : ℤ) ∣ ((m * v : ℕ) : ℤ) := ⟨s, sub_eq_zero.mp hz⟩
  have hdivN : q ∣ m * v := Int.natCast_dvd_natCast.mp hdivZ
  have hqm : q ≤ m := Nat.le_of_dvd hm (hcop.dvd_of_dvd_mul_right hdivN)
  exact (not_le_of_gt hmq) hqm

/-- The gcd cost in the short-progression mean is a divisor of the small
numerator, after any integer shift of the remainder interval. -/
lemma reciprocal_shifted_gcd_dvd {m v q : ℕ} (hcop : q.Coprime v) (T : ℤ) :
    Int.gcd (((m * v : ℕ) : ℤ) + (q : ℤ) * T) (-(q : ℤ)) ∣ m := by
  let A : ℤ := ((m * v : ℕ) : ℤ) + (q : ℤ) * T
  let g : ℕ := Int.gcd A (-(q : ℤ))
  have hgqZ : (g : ℤ) ∣ (q : ℤ) := by
    have h := Int.gcd_dvd_right A (-(q : ℤ))
    exact dvd_neg.mp h
  have hgq : g ∣ q := Int.natCast_dvd_natCast.mp hgqZ
  have hgmvZ : (g : ℤ) ∣ ((m * v : ℕ) : ℤ) := by
    have h := dvd_sub (Int.gcd_dvd_left A (-(q : ℤ))) (dvd_mul_of_dvd_left hgqZ T)
    simpa only [A, add_sub_cancel_right] using h
  have hgmv : g ∣ m * v := Int.natCast_dvd_natCast.mp hgmvZ
  exact (Nat.Coprime.of_dvd_left hgq hcop).dvd_of_dvd_mul_right hgmv

/-- The reciprocal count with its exact small-numerator divisor cost.
The shift `T` is arbitrary, so this covers intervals crossing zero. -/
theorem exists_shifted_reciprocal_divisibility_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (m v q Y c : ℕ) (T : ℤ), 0 < m → m < q → q.Coprime v →
        3 ≤ Y → c ≠ 0 →
        (∀ s ∈ Finset.Icc 1 Y,
          (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - T)).natAbs ≤ Y ^ (4 ^ j)) →
        ∀ R : Finset ℕ,
          ((R.filter (fun r => ∃ s ∈ Finset.Icc 1 Y,
            c * r ∣ (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - T)).natAbs)).card : ℝ) ≤
            (m.divisors.card : ℝ) * K * (Y : ℝ) * Real.log (Y : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_reciprocal_divisibility_bound j
  refine ⟨K, hK, O, hO, ?_⟩
  intro m v q Y c T hm hmq hcop hY hc hsize R
  let A : ℤ := ((m * v : ℕ) : ℤ) + (q : ℤ) * T
  let B : ℤ := -(q : ℤ)
  have hB : B ≠ 0 := by dsimp [B]; exact neg_ne_zero.mpr (by exact_mod_cast (hm.trans hmq).ne')
  have heq (s : ℕ) : A + B * s = ((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - T) := by
    dsimp [A, B]
    ring
  have hn : ∀ s ∈ Finset.Icc 1 Y, A + B * s ≠ 0 := by
    intro s hs
    rw [heq]
    exact reciprocal_linear_value_ne_zero hm hmq hcop _
  have hsize' : ∀ s ∈ Finset.Icc 1 Y, (A + B * s).natAbs ≤ Y ^ (4 ^ j) := by
    intro s hs
    rw [heq]
    exact hsize s hs
  have hcount := hmean A B hB Y c hY hc hn hsize' R
  simp_rw [heq] at hcount
  have hgc : (A.gcd B).divisors.card ≤ m.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hm.ne' (reciprocal_shifted_gcd_dvd hcop T))
  have hgcR : ((A.gcd B).divisors.card : ℝ) ≤ (m.divisors.card : ℝ) := by exact_mod_cast hgc
  apply hcount.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right hgcR hK.le
    · exact Nat.cast_nonneg _
  · exact pow_nonneg ((one_le_log_nat_of_three_le hY).trans' zero_le_one) _

/-- Size of the linear values after indexing the integer interval `[-S,S]`
by the positive integers `1,...,2*S+1`. -/
lemma reciprocal_shifted_value_size (m v q : ℕ) {s S : ℕ}
    (hs : s ∈ Finset.Icc 1 (2 * S + 1)) :
    (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - ((S + 1 : ℕ) : ℤ))).natAbs ≤
      m * v + q * S := by
  have hs' := Finset.mem_Icc.mp hs
  have ht : ((s : ℤ) - ((S + 1 : ℕ) : ℤ)).natAbs ≤ S := by omega
  calc
    (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - ((S + 1 : ℕ) : ℤ))).natAbs ≤
        (((m * v : ℕ) : ℤ)).natAbs +
          ((q : ℤ) * ((s : ℤ) - ((S + 1 : ℕ) : ℤ))).natAbs := Int.natAbs_sub_le _ _
    _ = m * v + q * ((s : ℤ) - ((S + 1 : ℕ) : ℤ)).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    _ ≤ m * v + q * S := Nat.add_le_add_left (Nat.mul_le_mul_left q ht) _

/-- The small-fractional-part count at reciprocal denominators. This is the
counting input to the dyadic decomposition of the Weyl majorant. -/
theorem exists_near_reciprocal_count_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (m v q c R S : ℕ), 0 < m → m < q → q.Coprime v → 0 < c → 0 < S →
        m * v + q * S ≤ (2 * S + 1) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ δ : ℝ, 0 ≤ δ → ((2 * c * R : ℕ) : ℝ) * δ ≤ S →
          ((D.filter (fun r => nearestIntDist
            ((((m * v : ℕ) : ℤ) * inv r : ℤ) / ((c * r : ℕ) : ℝ)) ≤ δ)).card : ℝ) ≤
            (m.divisors.card : ℝ) * K * (2 * S + 1 : ℕ) *
              Real.log (2 * S + 1 : ℕ) ^ O := by
  obtain ⟨K, hK, O, hO, hcount⟩ := exists_shifted_reciprocal_divisibility_bound j
  refine ⟨K, hK, O, hO, ?_⟩
  intro m v q c R S hm hmq hcop hc hS hsize D inv hD hinv δ hδ hδS
  let Y := 2 * S + 1
  have hY : 3 ≤ Y := by dsimp [Y]; omega
  have hsize' : ∀ s ∈ Finset.Icc 1 Y,
      (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - ((S + 1 : ℕ) : ℤ))).natAbs ≤
        Y ^ (4 ^ j) := fun s hs => (reciprocal_shifted_value_size m v q hs).trans hsize
  have hbound := hcount m v q Y c (S + 1 : ℕ) hm hmq hcop hY hc.ne' hsize' D
  have hsub : D.filter (fun r => nearestIntDist
      ((((m * v : ℕ) : ℤ) * inv r : ℤ) / ((c * r : ℕ) : ℝ)) ≤ δ) ⊆
      D.filter (fun r => ∃ s ∈ Finset.Icc 1 Y,
        c * r ∣ (((m * v : ℕ) : ℤ) - (q : ℤ) * ((s : ℤ) - ((S + 1 : ℕ) : ℤ))).natAbs) := by
    intro r hr
    obtain ⟨hrD, hrnear⟩ := Finset.mem_filter.mp hr
    have hrpos := (hD r hrD).1
    have hcr : c * r ≤ 2 * c * R := by
      calc
        c * r ≤ c * (2 * R) := Nat.mul_le_mul_left c (hD r hrD).2
        _ = 2 * c * R := by ring
    obtain ⟨s, hs, hsdiv⟩ := exists_reciprocal_remainder
      (Nat.mul_pos hc hrpos) (hinv r hrD) hrnear
    have hsR : |(s : ℝ)| ≤ S := hs.trans ((mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcr : ((c * r : ℕ) : ℝ) ≤ (2 * c * R : ℕ)) hδ).trans hδS)
    have hslo : -(S : ℤ) ≤ s := by exact_mod_cast (abs_le.mp hsR).1
    have hshi : s ≤ (S : ℤ) := by exact_mod_cast (abs_le.mp hsR).2
    let i := (s + (S : ℤ) + 1).toNat
    have hi : (i : ℤ) = s + (S : ℤ) + 1 := Int.toNat_of_nonneg (by omega)
    have hiY : i ∈ Finset.Icc 1 Y := by
      apply Finset.mem_Icc.mpr
      dsimp [Y]
      omega
    have hsi : (i : ℤ) - ((S + 1 : ℕ) : ℤ) = s := by omega
    refine Finset.mem_filter.mpr ⟨hrD, i, hiY, ?_⟩
    rw [hsi]
    exact Int.natCast_dvd.mp hsdiv
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hbound

end Erdos587
