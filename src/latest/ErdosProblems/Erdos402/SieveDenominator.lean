import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# An effective lower bound for the sieve denominator

Grouping integers by their squarefree prime support outside the modulus
gives the logarithmic lower bound without an asymptotic error term.
-/

namespace Erdos402.Sieve

noncomputable section

private def invNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by intros; simp [mul_inv_rev, mul_comm]

lemma hasSum_factored_inv {k : ℕ} (hk : 0 < k) :
    HasSum (fun n : Nat.factoredNumbers k.primeFactors ↦ (1 : ℝ) / (n : ℕ))
      ((k : ℝ) / k.totient) := by
  have hpbound : ∀ {p : ℕ}, p.Prime → ‖invNatHom p‖ < 1 := by
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < p)).mpr hpR
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hpbound k.primeFactors).2
  have hfilter : k.primeFactors.filter Nat.Prime = k.primeFactors :=
    Finset.filter_eq_self.mpr fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have hphi : (k.totient : ℝ) =
      (k : ℝ) * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htR : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hprod : (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) = (k : ℝ) / k.totient := by
    rw [Finset.prod_inv_distrib]
    have heq : (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)) = (k.totient : ℝ) / k := by
      apply (eq_div_iff hkR.ne').mpr
      nlinarith [hphi]
    rw [heq, inv_div]
  simpa only [hfilter, invNatHom, MonoidHom.coe_mk, OneHom.coe_mk, hprod, one_div]
    using hsum

lemma sum_factored_inv_le {k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ∈ Nat.factoredNumbers k.primeFactors) :
    (∑ n ∈ S, (1 : ℝ) / n) ≤ (k : ℝ) / k.totient := by
  classical
  let f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ)
  have hsum := hasSum_factored_inv hk
  have hIndicator : Summable ((Nat.factoredNumbers k.primeFactors).indicator f) :=
    summable_subtype_iff_indicator.mp hsum.summable
  calc
    _ = ∑ n ∈ S, (Nat.factoredNumbers k.primeFactors).indicator f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Set.indicator_of_mem (hS n hn)]
    _ ≤ ∑' n : ℕ, (Nat.factoredNumbers k.primeFactors).indicator f n := by
      apply hIndicator.sum_le_tsum
      intro n _
      exact Set.indicator_nonneg (fun n _ ↦ by dsimp [f]; positivity) n
    _ = ∑' n : Nat.factoredNumbers k.primeFactors, f n :=
      (tsum_subtype _ f).symm
    _ = _ := hsum.tsum_eq

/-- The squarefree part of `n` supported on primes not dividing `k`. -/
def roughRadical (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ k), p

lemma roughRadical_pos (k n : ℕ) : 0 < roughRadical k n :=
  Finset.prod_pos fun _ hp ↦ Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma roughRadical_dvd (k n : ℕ) : roughRadical k n ∣ n := by
  apply dvd_trans _ (Nat.prod_primeFactors_dvd n)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

lemma roughRadical_coprime (k n : ℕ) : (roughRadical k n).Coprime k := by
  apply Nat.Coprime.prod_left
  intro p hp
  obtain ⟨hpn, hpk⟩ := Finset.mem_filter.mp hp
  exact (Nat.prime_of_mem_primeFactors hpn).coprime_iff_not_dvd.mpr hpk

lemma roughRadical_squarefree (k n : ℕ) : Squarefree (roughRadical k n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpp hqp).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree

lemma div_roughRadical_factored {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    n / roughRadical k n ∈ Nat.factoredNumbers (k * roughRadical k n).primeFactors := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hpd
  have hpn : p ∣ n := hpd.trans (Nat.div_dvd_of_dvd (roughRadical_dvd k n))
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp, ?_, (Nat.mul_pos hk (roughRadical_pos k n)).ne'⟩
  by_cases hpk : p ∣ k
  · exact dvd_mul_of_dvd_left hpk _
  · apply dvd_mul_of_dvd_right
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩, hpk⟩

/-- The normalizing denominator in the one-dimensional upper-bound sieve. -/
def denominator (k Q : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 Q).filter (fun d ↦ Squarefree d ∧ d.Coprime k),
    (1 : ℝ) / d.totient

lemma denominator_nonneg (k Q : ℕ) : 0 ≤ denominator k Q := by
  unfold denominator
  positivity

/-- Assign each integer to its squarefree prime support outside `k`. The
remaining smooth-number fiber has total mass at most `k/φ(k)` times
the reciprocal totient of that support. -/
theorem harmonic_le_mul_denominator {k : ℕ} (hk : 0 < k) (Q : ℕ) :
    ((harmonic Q : ℚ) : ℝ) ≤ (k : ℝ) / k.totient * denominator k Q := by
  classical
  let A := (Finset.Icc 1 Q).filter (fun d ↦ Squarefree d ∧ d.Coprime k)
  let M := fun d ↦ (Finset.Icc 1 Q).filter
    (fun m ↦ m ∈ Nat.factoredNumbers (k * d).primeFactors)
  let U := A.sigma M
  let f : ℕ → (Σ _ : ℕ, ℕ) := fun n ↦ ⟨roughRadical k n, n / roughRadical k n⟩
  let g : (Σ _ : ℕ, ℕ) → ℝ := fun dm ↦ 1 / ((dm.1 : ℝ) * dm.2)
  have hprod (n : ℕ) : (f n).1 * (f n).2 = n :=
    Nat.mul_div_cancel' (roughRadical_dvd k n)
  have hinj : Function.Injective f := by
    intro n m hnm
    have h := congrArg (fun dm : Σ _ : ℕ, ℕ ↦ dm.1 * dm.2) hnm
    simpa only [hprod] using h
  have hmem : ∀ n ∈ Finset.Icc 1 Q, f n ∈ U := by
    intro n hn
    obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hn
    have hdle : roughRadical k n ≤ n := Nat.le_of_dvd hnpos (roughRadical_dvd k n)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨roughRadical_pos k n, hdle.trans hnle⟩,
        roughRadical_squarefree k n, roughRadical_coprime k n⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos hdle (roughRadical_pos k n), (Nat.div_le_self _ _).trans hnle⟩,
      div_roughRadical_factored hk hnpos⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 Q, g (f n) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [g]
      rw [← Nat.cast_mul, hprod, one_div]
    _ = ∑ dm ∈ (Finset.Icc 1 Q).image f, g dm := by
      rw [Finset.sum_image]
      exact hinj.injOn
    _ ≤ ∑ dm ∈ U, g dm := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro dm hdm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hdm
        exact hmem n hn
      · intro dm _ _
        dsimp only [g]
        positivity
    _ = ∑ d ∈ A, (1 : ℝ) / d * ∑ m ∈ M d, (1 : ℝ) / m := by
      dsimp only [U]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [g]
      ring
    _ ≤ ∑ d ∈ A, (1 : ℝ) / d * ((k * d : ℕ) : ℝ) / (k * d).totient := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hfiber := sum_factored_inv_le (Nat.mul_pos hk hdpos) (M d)
        (fun m hm ↦ (Finset.mem_filter.mp hm).2)
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hfiber (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))
    _ = _ := by
      unfold denominator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hcop := (Finset.mem_filter.mp hd).2.2
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      rw [Nat.totient_mul hcop.symm]
      push_cast
      field_simp

/-- A completely effective logarithmic lower bound, valid for every positive
modulus and every cutoff. No distribution theorem or unspecified threshold
occurs in this estimate. -/
theorem totient_div_mul_log_add_one_le_denominator {k : ℕ} (hk : 0 < k) (Q : ℕ) :
    (k.totient : ℝ) / k * Real.log (Q + 1 : ℕ) ≤ denominator k Q := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htR : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  calc
    _ ≤ (k.totient : ℝ) / k * ((harmonic Q : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left (log_add_one_le_harmonic Q) (by positivity)
    _ ≤ (k.totient : ℝ) / k * ((k : ℝ) / k.totient * denominator k Q) :=
      mul_le_mul_of_nonneg_left (harmonic_le_mul_denominator hk Q) (by positivity)
    _ = _ := by field_simp

theorem totient_div_mul_log_le_denominator {k : ℕ} (hk : 0 < k) (Q : ℕ) :
    (k.totient : ℝ) / k * Real.log Q ≤ denominator k Q := by
  by_cases hQ : Q = 0
  · simp only [hQ, Nat.cast_zero, Real.log_zero, mul_zero]
    exact denominator_nonneg k 0
  · apply le_trans _ (totient_div_mul_log_add_one_le_denominator hk Q)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hQ)
      (by exact_mod_cast Nat.le_succ Q)

end
end Erdos402.Sieve
