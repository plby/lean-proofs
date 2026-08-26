import ErdosProblems.Erdos380.Core
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Elementary lower bounds for sieve denominators

Deleting the multiples of `p` removes at most `1 / p` of a harmonic sum
that already avoids other divisors.  Iteration gives a lower bound uniform
in the modulus, without an error term depending on its size.
-/

open scoped BigOperators

namespace Erdos380

noncomputable def divisorAvoidingUpTo (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ p ∈ s, ¬ p ∣ n

noncomputable def divisorAvoidingHarmonic (s : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ divisorAvoidingUpTo s N, (1 : ℝ) / n

lemma divisorAvoidingHarmonic_nonneg (s : Finset ℕ) (N : ℕ) :
    0 ≤ divisorAvoidingHarmonic s N := by
  unfold divisorAvoidingHarmonic
  positivity

lemma divisible_divisorAvoidingHarmonic_le
    (s : Finset ℕ) (N p : ℕ) (hp : 0 < p) :
    (∑ n ∈ (divisorAvoidingUpTo s N).filter (p ∣ ·), (1 : ℝ) / n) ≤
      (1 / p : ℝ) * divisorAvoidingHarmonic s N := by
  classical
  let A := (divisorAvoidingUpTo s N).filter (p ∣ ·)
  have hmem {n : ℕ} (hn : n ∈ A) :
      n / p ∈ divisorAvoidingUpTo s N := by
    obtain ⟨hnS, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hav⟩ := Finset.mem_filter.mp hnS
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have hquot : n / p * p = n := Nat.div_mul_cancel hpn
      by_contra h
      have hz : n / p = 0 := Nat.eq_zero_of_not_pos (by
        simpa only [Nat.succ_le_iff] using h)
      rw [hz, zero_mul] at hquot
      omega
    · exact (Nat.div_le_self n p).trans hnN
    · intro q hq hqd
      exact hav q hq (hqd.trans (Nat.div_dvd_of_dvd hpn))
  have hinj : Set.InjOn (fun n : ℕ => n / p) A := by
    intro n hn m hm heq
    have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hm' := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    exact hn'.symm.trans ((congrArg (fun k : ℕ => k * p) heq).trans hm')
  have heq {n : ℕ} (hn : n ∈ A) :
      (1 : ℝ) / n = (1 / p : ℝ) * (1 / (n / p : ℕ) : ℝ) := by
    have hprod : n / p * p = n := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hcast : ((n / p : ℕ) : ℝ) * p = n := by exact_mod_cast hprod
    rw [← hcast]
    simp only [one_div, mul_inv_rev]
  calc
    (∑ n ∈ A, (1 : ℝ) / n) =
        (1 / p : ℝ) * ∑ n ∈ A, (1 / (n / p : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n hn => heq hn
    _ = (1 / p : ℝ) * ∑ n ∈ A.image (fun n => n / p), (1 / n : ℝ) := by
      rw [Finset.sum_image hinj]
    _ ≤ (1 / p : ℝ) * divisorAvoidingHarmonic s N := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
        exact hmem hm
      · intro n _ _
        positivity

lemma divisorAvoidingHarmonic_insert_le
    (s : Finset ℕ) (N p : ℕ) (hp : 0 < p) :
    (1 - 1 / p : ℝ) * divisorAvoidingHarmonic s N ≤
      divisorAvoidingHarmonic (insert p s) N := by
  classical
  have hsplit : divisorAvoidingHarmonic (insert p s) N +
      (∑ n ∈ (divisorAvoidingUpTo s N).filter (p ∣ ·), (1 : ℝ) / n) =
      divisorAvoidingHarmonic s N := by
    have hfilter : divisorAvoidingUpTo (insert p s) N =
        (divisorAvoidingUpTo s N).filter (fun n => ¬ p ∣ n) := by
      ext n
      simp [divisorAvoidingUpTo, and_left_comm, and_assoc, and_comm]
    rw [divisorAvoidingHarmonic, hfilter]
    exact Finset.sum_filter_not_add_sum_filter _ _ _
  have hremoved := divisible_divisorAvoidingHarmonic_le s N p hp
  nlinarith

theorem divisorAvoidingHarmonic_ge_euler_harmonic
    (s : Finset ℕ) (N : ℕ) (hs : ∀ p ∈ s, 1 ≤ p) :
    (∏ p ∈ s, (1 - 1 / p : ℝ)) * ((harmonic N : ℚ) : ℝ) ≤
      divisorAvoidingHarmonic s N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [divisorAvoidingHarmonic, divisorAvoidingUpTo, harmonic_eq_sum_Icc, one_div]
  | @insert p s hp ih =>
    have hp1 := hs p (Finset.mem_insert_self p s)
    have hs1 : ∀ q ∈ s, 1 ≤ q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    have hfactor : (0 : ℝ) ≤ 1 - 1 / p := by
      exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpR)
    rw [Finset.prod_insert hp, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih hs1) hfactor).trans
      (divisorAvoidingHarmonic_insert_le s N p (by omega))

theorem coprime_harmonic_ge_totient_ratio
    (q N : ℕ) (hq : 0 < q) :
    (Nat.totient q : ℝ) / q * ((harmonic N : ℚ) : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (1 : ℝ) / n := by
  classical
  have h := divisorAvoidingHarmonic_ge_euler_harmonic q.primeFactors N
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)
  have hfilter : divisorAvoidingUpTo q.primeFactors N =
      (Finset.Icc 1 N).filter (fun n => n.Coprime q) := by
    ext n
    simp only [divisorAvoidingUpTo, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hav
      by_contra hcop
      obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      exact hav p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩) hpn
    · intro hc p hp hpn
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact hp'.ne_one ((hc.coprime_dvd_left hpn).eq_one_of_dvd
        (Nat.dvd_of_mem_primeFactors hp))
  have htot : (Nat.totient q : ℝ) =
      q * ∏ p ∈ q.primeFactors, (1 - 1 / p : ℝ) := by
    have ht := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv, one_div] using ht
  have hratio : (Nat.totient q : ℝ) / q =
      ∏ p ∈ q.primeFactors, (1 - 1 / p : ℝ) := by
    rw [htot]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  rw [hratio]
  simpa only [divisorAvoidingHarmonic, hfilter] using h

noncomputable def squarefreeCoprimeUpTo (q N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => Squarefree n ∧ n.Coprime q

noncomputable def squarefreeCoprimeReciprocal (q N : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimeUpTo q N, (1 : ℝ) / n

noncomputable def sieveDenominator (q N : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimeUpTo q N, (1 : ℝ) / Nat.totient n

lemma sum_Icc_reciprocal_square_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2) ≤ 2 := by
  have hset : Finset.Icc 1 N = Finset.Ioo 0 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  simpa only [hset, one_div, Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- Decomposing an integer as a square times a squarefree integer costs
at most the elementary bound `sum 1 / b² ≤ 2`. -/
lemma coprime_harmonic_le_two_squarefreeReciprocal (q N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (1 : ℝ) / n) ≤
      2 * squarefreeCoprimeReciprocal q N := by
  classical
  let S := squarefreeCoprimeUpTo q N
  let T := S ×ˢ Finset.Icc 1 N
  let f : ℕ × ℕ → ℕ := fun ab => ab.2 ^ 2 * ab.1
  have hcover : (Finset.Icc 1 N).filter (fun n => n.Coprime q) ⊆ T.image f := by
    intro n hn
    obtain ⟨hnI, hcop⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
    have hadvd : a ∣ n := by rw [← hab]; exact dvd_mul_left _ _
    have hbdvd : b ∣ n := by rw [← hab, pow_two, mul_assoc]; exact dvd_mul_right _ _
    have haN : a ≤ N := (Nat.le_of_dvd (by omega) hadvd).trans hnN
    have hbN : b ≤ N := (Nat.le_of_dvd (by omega) hbdvd).trans hnN
    refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, hab⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, haN⟩,
        hsq, hcop.coprime_dvd_left hadvd⟩
    · exact Finset.mem_Icc.mpr ⟨hb, hbN⟩
  calc
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (1 : ℝ) / n) ≤
        ∑ n ∈ T.image f, (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
    _ ≤ ∑ ab ∈ T, (1 : ℝ) / f ab :=
      Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = squarefreeCoprimeReciprocal q N *
        ∑ b ∈ Finset.Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2 := by
      simp only [T, f, Finset.sum_product, Nat.cast_mul, Nat.cast_pow,
        one_div, mul_inv_rev, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [S, squarefreeCoprimeReciprocal, one_div]
    _ ≤ squarefreeCoprimeReciprocal q N * 2 :=
      mul_le_mul_of_nonneg_left (sum_Icc_reciprocal_square_le_two N)
        (by unfold squarefreeCoprimeReciprocal; positivity)
    _ = _ := mul_comm _ _

lemma squarefreeCoprimeReciprocal_le_sieveDenominator (q N : ℕ) :
    squarefreeCoprimeReciprocal q N ≤ sieveDenominator q N := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < n)
  exact one_div_le_one_div_of_le hphi (by exact_mod_cast Nat.totient_le n)

/-- A uniform elementary lower bound for the squarefree sieve sum. -/
theorem sieveDenominator_ge_log (q N : ℕ) (hq : 0 < q) :
    (Nat.totient q : ℝ) / q * Real.log (N + 1 : ℕ) ≤
      2 * sieveDenominator q N := by
  calc
    (Nat.totient q : ℝ) / q * Real.log (N + 1 : ℕ) ≤
        (Nat.totient q : ℝ) / q * ((harmonic N : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_add, Nat.cast_one] using (log_add_one_le_harmonic N))
        (by positivity)
    _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (1 : ℝ) / n :=
      coprime_harmonic_ge_totient_ratio q N hq
    _ ≤ 2 * squarefreeCoprimeReciprocal q N :=
      coprime_harmonic_le_two_squarefreeReciprocal q N
    _ ≤ 2 * sieveDenominator q N :=
      mul_le_mul_of_nonneg_left (squarefreeCoprimeReciprocal_le_sieveDenominator q N)
        (by norm_num)

end Erdos380
