/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs

/-!
# Elementary bounds for Ford's logarithmic divisor set

This file formalizes Lemma 3.1 of Kevin Ford's short paper
*Integers with a divisor in (y, 2y]*.  We use the slightly more general
interval length `σ`; Ford's displayed lemma is the specialization
`σ = log 2`.
-/

namespace Erdos896.Ford

open MeasureTheory
open scoped ENNReal Pointwise

/-! ## Finiteness and elementary set identities -/

/-- Ford's real-valued `L` is Lebesgue measure viewed in `ℝ`. -/
theorem L_eq_volume_real (a : ℕ) (σ : ℝ) :
    L a σ = volume.real (logDivisorUnion a σ) := by
  rfl

/-- For positive `a`, all logarithmic divisor intervals lie between
`-σ` and `log a`. -/
theorem logDivisorUnion_subset_Ico {a : ℕ} (ha : a ≠ 0) (σ : ℝ) :
    logDivisorUnion a σ ⊆ Set.Ico (-σ) (Real.log a) := by
  intro x hx
  rw [mem_logDivisorUnion] at hx
  obtain ⟨d, hd, hleft, hright⟩ := hx
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  have hda : d ≤ a := Nat.divisor_le hd
  have hlogd_nonneg : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hlogda : Real.log d ≤ Real.log a :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hdpos))
      (Set.mem_Ioi.mpr (by exact_mod_cast hapos))
      (by exact_mod_cast hda)
  constructor
  · linarith
  · exact hright.trans_le hlogda

/-- The logarithmic divisor union of a positive integer has finite measure. -/
theorem divisorLogMeasure_ne_top {a : ℕ} (ha : a ≠ 0) (σ : ℝ) :
    divisorLogMeasure a σ ≠ ∞ := by
  unfold divisorLogMeasure
  exact ne_of_lt <| measure_lt_top_mono
    (logDivisorUnion_subset_Ico ha σ) (by simp)

/-- `L` is monotone under inclusion of logarithmic divisor unions. -/
theorem L_mono_of_subset {a b : ℕ} {σ : ℝ}
    (h : logDivisorUnion a σ ⊆ logDivisorUnion b σ)
    (hb : b ≠ 0) :
    L a σ ≤ L b σ := by
  rw [L_eq_volume_real, L_eq_volume_real]
  exact measureReal_mono h (divisorLogMeasure_ne_top hb σ)

/-! ## Ford Lemma 3.1(i) -/

/-- The union is no longer than the sum of its divisor intervals. -/
theorem L_le_card_divisors_mul {a : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    L a σ ≤ (a.divisors.card : ℝ) * σ := by
  rw [L_eq_volume_real]
  calc
    volume.real (logDivisorUnion a σ) ≤
        ∑ d : ↑a.divisors, volume.real (logDivisorInterval d σ) :=
      measureReal_iUnion_fintype_le _
    _ = (a.divisors.card : ℝ) * σ := by
      have hinterval (d : ↑a.divisors) :
          volume.real (logDivisorInterval d σ) = σ := by
        change volume.real
          (Set.Ico (-σ + Real.log (d : ℕ)) (Real.log (d : ℕ))) = σ
        rw [Real.volume_real_Ico_of_le]
        · ring
        ·
          linarith
      simp_rw [hinterval]
      simp

/-- All divisor intervals lie in one interval of length `σ + log a`. -/
theorem L_le_sigma_add_log {a : ℕ} (ha : a ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    L a σ ≤ σ + Real.log a := by
  rw [L_eq_volume_real]
  have hloga : 0 ≤ Real.log a := Real.log_natCast_nonneg a
  calc
    volume.real (logDivisorUnion a σ) ≤
        volume.real (Set.Ico (-σ) (Real.log a)) :=
      measureReal_mono (logDivisorUnion_subset_Ico ha σ) (by simp)
    _ = Real.log a - (-σ) :=
      Real.volume_real_Ico_of_le (by linarith)
    _ = σ + Real.log a := by ring

/-- Ford, Lemma 3.1(i), with an arbitrary nonnegative logarithmic length. -/
theorem ford_lemma_three_one_i {a : ℕ} (ha : a ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    L a σ ≤ min ((a.divisors.card : ℝ) * σ) (σ + Real.log a) := by
  exact le_min (L_le_card_divisors_mul hσ) (L_le_sigma_add_log ha hσ)

/-! ## Ford Lemma 3.1(ii) -/

/-- Every divisor interval for `a * b` lies in a translate, indexed by a
divisor of `b`, of the logarithmic divisor union for `a`. -/
theorem logDivisorUnion_mul_subset {a b : ℕ} (_ha : a ≠ 0) (_hb : b ≠ 0) (σ : ℝ) :
    logDivisorUnion (a * b) σ ⊆
      ⋃ d : ↑b.divisors,
        (fun x : ℝ ↦ -Real.log (d : ℕ) + x) ⁻¹' logDivisorUnion a σ := by
  intro x hx
  rw [mem_logDivisorUnion] at hx
  obtain ⟨e, he, hleft, hright⟩ := hx
  rw [Nat.divisors_mul] at he
  obtain ⟨da, hda, db, hdb, rfl⟩ := Finset.mem_mul.mp he
  refine Set.mem_iUnion.mpr ⟨⟨db, hdb⟩, ?_⟩
  change -Real.log db + x ∈ logDivisorUnion a σ
  rw [mem_logDivisorUnion]
  have hda0 : da ≠ 0 := (Nat.pos_of_mem_divisors hda).ne'
  have hdb0 : db ≠ 0 := (Nat.pos_of_mem_divisors hdb).ne'
  have hlogmul : Real.log (↑(da * db) : ℝ) = Real.log da + Real.log db := by
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast hda0
    · exact_mod_cast hdb0
  refine ⟨da, hda, ?_, ?_⟩
  · rw [hlogmul] at hleft
    linarith
  · rw [hlogmul] at hright
    linarith

/-- Multiplication by `b` creates at most one translate of `ℒ(a;σ)` for
each divisor of `b`.  The coprimality assumption in Ford's statement is not
needed for this upper bound. -/
theorem L_mul_le_card_divisors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (σ : ℝ) :
    L (a * b) σ ≤ (b.divisors.card : ℝ) * L a σ := by
  let T : ↑b.divisors → Set ℝ := fun d ↦
    (fun x : ℝ ↦ -Real.log (d : ℕ) + x) ⁻¹' logDivisorUnion a σ
  have hTmeasure (d : ↑b.divisors) :
      volume (T d) = volume (logDivisorUnion a σ) := by
    simpa [T] using
      (measure_preimage_add volume (-Real.log (d : ℕ)) (logDivisorUnion a σ))
  have hTfinite : volume (⋃ d, T d) ≠ ∞ := by
    refine ne_of_lt <| (measure_iUnion_fintype_le volume T).trans_lt ?_
    rw [ENNReal.sum_lt_top]
    intro d hd
    rw [hTmeasure]
    exact lt_top_iff_ne_top.mpr (by
      simpa [divisorLogMeasure] using divisorLogMeasure_ne_top ha σ)
  rw [L_eq_volume_real, L_eq_volume_real]
  calc
    volume.real (logDivisorUnion (a * b) σ) ≤ volume.real (⋃ d, T d) :=
      measureReal_mono (by simpa [T] using logDivisorUnion_mul_subset ha hb σ) hTfinite
    _ ≤ ∑ d : ↑b.divisors, volume.real (T d) :=
      measureReal_iUnion_fintype_le _
    _ = (b.divisors.card : ℝ) * volume.real (logDivisorUnion a σ) := by
      simp_rw [Measure.real, hTmeasure]
      simp

/-- Source-faithful coprime form of Ford, Lemma 3.1(ii). -/
theorem ford_lemma_three_one_ii {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (_hab : Nat.Coprime a b) (σ : ℝ) :
    L (a * b) σ ≤ (b.divisors.card : ℝ) * L a σ :=
  L_mul_le_card_divisors ha hb σ

/-- The growth condition used when applying Ford's Lemma 3.3 with `f = L`. -/
theorem L_prime_mul_le_two {p m : ℕ} (hp : Nat.Prime p) (hm : m ≠ 0) (σ : ℝ) :
    L (p * m) σ ≤ 2 * L m σ := by
  simpa [mul_comm, hp.divisors, hp.ne_one, Ne.symm hp.ne_one] using
    (L_mul_le_card_divisors hm hp.ne_zero σ :
      L (m * p) σ ≤ (p.divisors.card : ℝ) * L m σ)

/-! ## Products of distinct primes and Ford Lemma 3.1(iii) -/

/-- A list of primes has nonzero product. -/
theorem list_prod_ne_zero_of_prime (ps : List ℕ)
    (hprime : ∀ p ∈ ps, Nat.Prime p) :
    ps.prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  exact (hprime 0 hzero).ne_zero rfl

/-- A product of `k` distinct primes has exactly `2^k` divisors. -/
theorem card_divisors_list_prod_primes (ps : List ℕ)
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hnodup : ps.Nodup) :
    ps.prod.divisors.card = 2 ^ ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hpp : Nat.Prime p := hprime p (by simp)
      have hprimeTail : ∀ q ∈ ps, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpnot : p ∉ ps := (List.nodup_cons.mp hnodup).1
      have hnodupTail : ps.Nodup := (List.nodup_cons.mp hnodup).2
      have hcop : Nat.Coprime p ps.prod := by
        rw [Nat.coprime_list_prod_right_iff]
        intro q hq
        apply (Nat.coprime_primes hpp (hprimeTail q hq)).mpr
        intro hpq
        subst q
        exact hpnot hq
      rw [List.prod_cons, Nat.Coprime.card_divisors_mul hcop,
        ih hprimeTail hnodupTail, hpp.divisors]
      simp [Ne.symm hpp.ne_one, pow_succ, Nat.mul_comm]

/-- The pointwise form of Ford Lemma 3.1(iii).  `ps.take j` is the
initial block `p₁,…,pⱼ`; the remaining `k-j` distinct primes contribute at
most `2^(k-j)` translates. -/
theorem L_list_prod_le {ps : List ℕ}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hnodup : ps.Nodup)
    {σ : ℝ} (hσ : 0 ≤ σ) (j : ℕ) :
    L ps.prod σ ≤
      (2 : ℝ) ^ (ps.length - j) *
        (Real.log (ps.take j).prod + σ) := by
  have htakePrime : ∀ p ∈ ps.take j, Nat.Prime p := by
    intro p hp
    exact hprime p ((List.take_sublist j ps).subset hp)
  have hdropPrime : ∀ p ∈ ps.drop j, Nat.Prime p := by
    intro p hp
    exact hprime p ((List.drop_sublist j ps).subset hp)
  have htake0 : (ps.take j).prod ≠ 0 :=
    list_prod_ne_zero_of_prime (ps.take j) htakePrime
  have hdrop0 : (ps.drop j).prod ≠ 0 :=
    list_prod_ne_zero_of_prime (ps.drop j) hdropPrime
  have hdropNodup : (ps.drop j).Nodup :=
    (List.drop_sublist j ps).nodup hnodup
  have hsplit : (ps.take j).prod * (ps.drop j).prod = ps.prod := by
    rw [← List.prod_append, List.take_append_drop]
  calc
    L ps.prod σ = L ((ps.take j).prod * (ps.drop j).prod) σ := by rw [hsplit]
    _ ≤ ((ps.drop j).prod.divisors.card : ℝ) * L (ps.take j).prod σ :=
      L_mul_le_card_divisors htake0 hdrop0 σ
    _ ≤ ((ps.drop j).prod.divisors.card : ℝ) *
        (σ + Real.log (ps.take j).prod) := by
      exact mul_le_mul_of_nonneg_left
        (L_le_sigma_add_log htake0 hσ) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ (ps.length - j) *
        (Real.log (ps.take j).prod + σ) := by
      rw [card_divisors_list_prod_primes (ps.drop j) hdropPrime hdropNodup,
        Nat.cast_pow, Nat.cast_ofNat, List.length_drop]
      ring

/-- Ford, Lemma 3.1(iii), for a strictly increasing list of primes.  The
source writes the collection of these bounds as a minimum over
`0 ≤ j ≤ k`; the universally quantified pointwise statement is equivalent and
is more convenient for later estimates. -/
theorem ford_lemma_three_one_iii {ps : List ℕ}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hstrict : ps.Pairwise (fun p q ↦ p < q))
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ j : ℕ, L ps.prod σ ≤
      (2 : ℝ) ^ (ps.length - j) *
        (Real.log (ps.take j).prod + σ) := by
  intro j
  exact L_list_prod_le hprime hstrict.nodup hσ j

/-- The finite family occurring under the minimum in Ford Lemma 3.1(iii). -/
noncomputable def primeListMeasureBounds (ps : List ℕ) (σ : ℝ) : Finset ℝ :=
  (Finset.range (ps.length + 1)).image fun j ↦
    (2 : ℝ) ^ (ps.length - j) *
      (Real.log (ps.take j).prod + σ)

theorem primeListMeasureBounds_nonempty (ps : List ℕ) (σ : ℝ) :
    (primeListMeasureBounds ps σ).Nonempty := by
  simp [primeListMeasureBounds]

/-- The literal minimum form of Ford Lemma 3.1(iii). -/
theorem ford_lemma_three_one_iii_min {ps : List ℕ}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hstrict : ps.Pairwise (fun p q ↦ p < q))
    {σ : ℝ} (hσ : 0 ≤ σ) :
    L ps.prod σ ≤
      (primeListMeasureBounds ps σ).min' (primeListMeasureBounds_nonempty ps σ) := by
  apply Finset.le_min'
  intro bound hbound
  rw [primeListMeasureBounds, Finset.mem_image] at hbound
  obtain ⟨j, _hj, rfl⟩ := hbound
  exact ford_lemma_three_one_iii hprime hstrict hσ j

/-! ## The `σ = log 2` specialization printed in Ford's paper -/

/-- Ford's short-paper notation `L(a)` means `L a (log 2)`. -/
noncomputable abbrev Ldyadic (a : ℕ) : ℝ := L a (Real.log 2)

theorem ford_lemma_three_one_i_dyadic {a : ℕ} (ha : a ≠ 0) :
    Ldyadic a ≤
      min ((a.divisors.card : ℝ) * Real.log 2) (Real.log 2 + Real.log a) := by
  exact ford_lemma_three_one_i ha (Real.log_nonneg one_le_two)

theorem ford_lemma_three_one_ii_dyadic {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    Ldyadic (a * b) ≤ (b.divisors.card : ℝ) * Ldyadic a :=
  ford_lemma_three_one_ii ha hb hab (Real.log 2)

theorem ford_lemma_three_one_iii_dyadic {ps : List ℕ}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hstrict : ps.Pairwise (fun p q ↦ p < q)) :
    Ldyadic ps.prod ≤
      (primeListMeasureBounds ps (Real.log 2)).min'
        (primeListMeasureBounds_nonempty ps (Real.log 2)) := by
  exact ford_lemma_three_one_iii_min hprime hstrict (Real.log_nonneg one_le_two)

end Erdos896.Ford
