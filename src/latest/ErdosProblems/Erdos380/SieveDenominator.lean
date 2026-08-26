import ErdosProblems.Erdos380.CutoffSieve
import ErdosProblems.Erdos380.SieveHarmonic

/-! # Identifying the squarefree terms in the Fourier-sieve denominator -/

open scoped BigOperators Function

namespace Erdos380

noncomputable def primeIndexFactors (t : Finset ℕ) (d : ℕ) : Finset t :=
  Finset.univ.filter fun p => p.1 ∈ d.primeFactors

lemma prod_primeIndexFactors {t : Finset ℕ} {d : ℕ}
    (hd : d.primeFactors ⊆ t) (f : ℕ → ℝ) :
    (∏ p ∈ primeIndexFactors t d, f p.1) = ∏ p ∈ d.primeFactors, f p := by
  classical
  have hfilter : t.filter (· ∈ d.primeFactors) = d.primeFactors :=
    Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hd)
  calc
    (∏ p ∈ primeIndexFactors t d, f p.1) =
        ∏ p : t, if p.1 ∈ d.primeFactors then f p.1 else 1 := by
      rw [primeIndexFactors, Finset.prod_filter]
    _ = ∏ p ∈ t, if p ∈ d.primeFactors then f p else 1 :=
      Finset.prod_coe_sort t (fun p => if p ∈ d.primeFactors then f p else 1)
    _ = _ := by rw [← Finset.prod_filter, hfilter]

lemma nat_prod_primeIndexFactors {t : Finset ℕ} {d : ℕ}
    (hd : d.primeFactors ⊆ t) (hsq : Squarefree d) :
    (∏ p ∈ primeIndexFactors t d, p.1) = d := by
  have h := prod_primeIndexFactors hd (fun p => (p : ℝ))
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  have h' : (∏ p ∈ primeIndexFactors t d, p.1) = ∏ p ∈ d.primeFactors, p := by
    apply Nat.cast_injective (R := ℝ)
    simpa only [Nat.cast_prod] using h
  exact h'.trans hprod

lemma totient_eq_prod_pred_of_squarefree {d : ℕ} (hd : Squarefree d) :
    Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  exact mul_right_cancel₀ hd.ne_zero (by simpa only [mul_comm] using h)

lemma inv_totient_eq_prod_primeIndexFactors {t : Finset ℕ} {d : ℕ}
    (hdt : d.primeFactors ⊆ t) (hd : Squarefree d) :
    (1 : ℝ) / Nat.totient d =
      ∏ p ∈ primeIndexFactors t d, (1 : ℝ) / (p.1 - 1 : ℕ) := by
  rw [prod_primeIndexFactors hdt (fun p => (1 : ℝ) / (p - 1 : ℕ)),
    totient_eq_prod_pred_of_squarefree hd]
  simp only [Nat.cast_prod, one_div, Finset.prod_inv_distrib]

/-- Every squarefree integer coprime to `q` below `Q` gives a distinct
term of the cutoff-family sum. -/
theorem sieveDenominator_le_productCutoff
    {t : Finset ℕ} {q Q : ℕ}
    (ht : ∀ p, p.Prime → p ≤ Q → ¬ p ∣ q → p ∈ t) :
    sieveDenominator q Q ≤
      ∑ T ∈ productCutoffFamily (fun p : t => p.1) Q,
        ∏ p ∈ T, (1 : ℝ) / (p.1 - 1 : ℕ) := by
  classical
  let S := squarefreeCoprimeUpTo q Q
  let f := primeIndexFactors t
  have hfactors {d : ℕ} (hd : d ∈ S) : d.primeFactors ⊆ t := by
    intro p hp
    obtain ⟨hdI, _, hcop⟩ := Finset.mem_filter.mp hd
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    apply ht p hpPrime ((Nat.le_of_mem_primeFactors hp).trans (Finset.mem_Icc.mp hdI).2)
    intro hpq
    exact hpPrime.ne_one ((hcop.coprime_dvd_left
      (Nat.dvd_of_mem_primeFactors hp)).eq_one_of_dvd hpq)
  have hprod {d : ℕ} (hd : d ∈ S) : (∏ p ∈ f d, p.1) = d :=
    nat_prod_primeIndexFactors (hfactors hd) (Finset.mem_filter.mp hd).2.1
  have hinj : Set.InjOn f S := by
    intro d hd e he hde
    rw [← hprod hd, ← hprod he, hde]
  have hsubset : S.image f ⊆ productCutoffFamily (fun p : t => p.1) Q := by
    intro T hT
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hprod hd]
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  calc
    sieveDenominator q Q =
        ∑ d ∈ S, ∏ p ∈ f d, (1 : ℝ) / (p.1 - 1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact inv_totient_eq_prod_primeIndexFactors (hfactors hd)
        (Finset.mem_filter.mp hd).2.1
    _ = ∑ T ∈ S.image f, ∏ p ∈ T, (1 : ℝ) / (p.1 - 1 : ℕ) := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)

end Erdos380
