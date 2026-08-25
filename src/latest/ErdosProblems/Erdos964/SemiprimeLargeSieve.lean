import ErdosProblems.Erdos964.SemiprimeCounts
import BoundedGaps.BombieriVinogradov.Analytic.MaximalBilinearConclusion

/-!
# A large-sieve bound for blocks of semiprimes

Applying the bilinear character large sieve to two sets of primes gives an
unconditional averaged character-sum bound for their products. Unlike a sum
of separate prime-progression bounds, this treats both prime factors as
variables. The conductor decomposition and small-conductor estimates needed
for a full semiprime Bombieri--Vinogradov theorem are not asserted here.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

/-- Products from two prescribed factor sets, truncated at `X`. -/
def primeProductBlock (P Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  ((P ×ˢ Q).filter (fun pq => pq.1 * pq.2 ≤ X)).image (fun pq => pq.1 * pq.2)

theorem primeProductBlock_subset_E2 (C X : ℕ) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ C < p) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    ↑(primeProductBlock P Q X) ⊆ E2 C := by
  intro n hn
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hn
  have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hpq).1
  exact ⟨p, q, (hP p hmem.1).1, hQ q hmem.2,
    ne_of_lt (hsep p hmem.1 q hmem.2), (hP p hmem.1).2,
    lt_trans (hP p hmem.1).2 (hsep p hmem.1 q hmem.2), rfl⟩

theorem sum_primeProductBlock {A : Type*} [AddCommMonoid A]
    (P Q : Finset ℕ) (X : ℕ) (w : ℕ → A)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    ∑ n ∈ primeProductBlock P Q X, w n =
      ∑ p ∈ P, ∑ q ∈ Q.filter (fun q => p * q ≤ X), w (p * q) := by
  unfold primeProductBlock
  rw [Finset.sum_image]
  · rw [Finset.sum_filter, Finset.sum_product]
    simp only [Finset.sum_filter]
  · intro pq hpq rs hrs heq
    have hpq' := Finset.mem_product.mp (Finset.mem_filter.mp hpq).1
    have hrs' := Finset.mem_product.mp (Finset.mem_filter.mp hrs).1
    exact prime_pair_mul_injective
      ⟨hP _ hpq'.1, hQ _ hpq'.2, hsep _ hpq'.1 _ hpq'.2⟩
      ⟨hP _ hrs'.1, hQ _ hrs'.2, hsep _ hrs'.1 _ hrs'.2⟩ heq

/-- An unconditional large-sieve estimate for ordered prime products.
The prime supports may be arbitrary subsets of the displayed intervals. -/
theorem semiprimeBlock_character_largeSieve
    (R m₀ M n₀ N X : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hX : X ∈ Finset.Icc 1 ((m₀ + M) * (n₀ + N)))
    (P Q : Finset ℕ)
    (hPinterval : P ⊆ Finset.Ioc m₀ (m₀ + M))
    (hQinterval : Q ⊆ Finset.Ioc n₀ (n₀ + N))
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    (∑ d ∈ Finset.Ioc 0 R, (d : ℝ) / d.totient *
      ∑ χ : primitiveCharacters d, ‖∑ n ∈ primeProductBlock P Q X, χ.1 n‖) ≤
      akbaryHambrookC3 * Real.sqrt ((M : ℝ) + (R : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (R : ℝ) ^ 2) * Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by
  have hpoint (d : ℕ) (χ : primitiveCharacters d) :
      ‖∑ n ∈ primeProductBlock P Q X, χ.1 n‖ ≤
        bilinearProductCutoffMaximum ((m₀ + M) * (n₀ + N)) d χ.1
          P Q (fun _ => 1) (fun _ => 1) := by
    rw [sum_primeProductBlock P Q X (fun n => χ.1 n) hP hQ hsep]
    simpa only [bilinearProductCutoffSum, one_mul, Nat.cast_mul] using
      norm_bilinearProductCutoffSum_le_maximum ((m₀ + M) * (n₀ + N)) d χ.1
        P Q (fun _ => 1) (fun _ => 1) hX
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 R, (d : ℝ) / d.totient *
        ∑ χ : primitiveCharacters d,
          bilinearProductCutoffMaximum ((m₀ + M) * (n₀ + N)) d χ.1
            P Q (fun _ => 1) (fun _ => 1) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun χ _ => hpoint d χ)
    _ ≤ _ := by
      simpa only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
          R m₀ M n₀ N hM hN P Q hPinterval hQinterval (fun _ => 1) (fun _ => 1)

/-- Maximum over all positive product cutoffs up to `K`. This retains the
endpoint uniformity required in a Bombieri--Vinogradov argument. -/
noncomputable def primeProductBlockMaximum (P Q : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) : ℝ :=
  if hK : 1 ≤ K then
    (Finset.Icc 1 K).sup' (Finset.nonempty_Icc.mpr hK)
      (fun X => ‖∑ n ∈ primeProductBlock P Q X, χ n‖)
  else 0

theorem primeProductBlockMaximum_eq_bilinear (P Q : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    primeProductBlockMaximum P Q K d χ =
      bilinearProductCutoffMaximum K d χ P Q (fun _ => 1) (fun _ => 1) := by
  have hfun : (fun X => ‖∑ n ∈ primeProductBlock P Q X, χ n‖) =
      (fun X => ‖bilinearProductCutoffSum X d χ P Q (fun _ => 1) (fun _ => 1)‖) := by
    funext X
    rw [sum_primeProductBlock P Q X (fun n => χ n) hP hQ hsep]
    simp only [bilinearProductCutoffSum, one_mul, Nat.cast_mul]
  unfold primeProductBlockMaximum bilinearProductCutoffMaximum
  rw [hfun]

theorem primeProductBlockMaximum_nonneg (P Q : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) : 0 ≤ primeProductBlockMaximum P Q K d χ := by
  unfold primeProductBlockMaximum
  split_ifs with hK
  · exact (norm_nonneg (∑ n ∈ primeProductBlock P Q 1, χ n)).trans
      (Finset.le_sup' (fun X => ‖∑ n ∈ primeProductBlock P Q X, χ n‖)
        (Finset.mem_Icc.mpr ⟨le_rfl, hK⟩))
  · exact le_rfl

theorem norm_primeProductBlock_le_maximum (P Q : Finset ℕ) (K d X : ℕ)
    (χ : DirichletCharacter ℂ d) (hX : X ∈ Finset.Icc 1 K) :
    ‖∑ n ∈ primeProductBlock P Q X, χ n‖ ≤ primeProductBlockMaximum P Q K d χ := by
  have hK : 1 ≤ K := (Finset.mem_Icc.mp hX).1.trans (Finset.mem_Icc.mp hX).2
  rw [primeProductBlockMaximum, dif_pos hK]
  exact Finset.le_sup' (fun Y => ‖∑ n ∈ primeProductBlock P Q Y, χ n‖) hX

theorem semiprimeBlock_maximal_largeSieve
    (R m₀ M n₀ N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (P Q : Finset ℕ)
    (hPinterval : P ⊆ Finset.Ioc m₀ (m₀ + M))
    (hQinterval : Q ⊆ Finset.Ioc n₀ (n₀ + N))
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    (∑ d ∈ Finset.Ioc 0 R, (d : ℝ) / d.totient *
      ∑ χ : primitiveCharacters d,
        primeProductBlockMaximum P Q ((m₀ + M) * (n₀ + N)) d χ.1) ≤
      akbaryHambrookC3 * Real.sqrt ((M : ℝ) + (R : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (R : ℝ) ^ 2) * Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by
  simp_rw [primeProductBlockMaximum_eq_bilinear P Q _ _ _ hP hQ hsep]
  simpa only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
      R m₀ M n₀ N hM hN P Q hPinterval hQinterval (fun _ => 1) (fun _ => 1)

/-- Change the natural large-sieve weight to a reciprocal totient on a
dyadic conductor interval. -/
theorem dyadic_totient_mass_le (R : ℕ) (hR : 0 < R)
    (U : ℕ → ℝ) (hU : ∀ d, 0 ≤ U d) :
    (∑ d ∈ Finset.Ioc R (2 * R), U d / d.totient) ≤
      (1 / (R : ℝ)) * ∑ d ∈ Finset.Ioc 0 (2 * R), (d : ℝ) / d.totient * U d := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  calc
    _ ≤ (1 / (R : ℝ)) *
        ∑ d ∈ Finset.Ioc R (2 * R), (d : ℝ) / d.totient * U d := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hRd : (R : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1.le
      have hnonneg : 0 ≤ U d / (d.totient : ℝ) :=
        div_nonneg (hU d) (Nat.cast_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hRd hnonneg
      calc
        U d / d.totient ≤ ((d : ℝ) * (U d / d.totient)) / R := by
          apply (le_div_iff₀ hRreal).mpr
          simpa only [mul_comm] using hmul
        _ = _ := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_Ioc] at hd ⊢
        omega
      · intro d _ _
        exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hU d)

/-- A dyadic conductor interval gains a factor `1/R`. This is the form used
to sum the large-conductor part of semiprime distribution errors. -/
theorem semiprimeBlock_dyadic_maximal_largeSieve
    (R m₀ M n₀ N : ℕ) (hR : 0 < R) (hM : 0 < M) (hN : 0 < N)
    (P Q : Finset ℕ)
    (hPinterval : P ⊆ Finset.Ioc m₀ (m₀ + M))
    (hQinterval : Q ⊆ Finset.Ioc n₀ (n₀ + N))
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    (∑ d ∈ Finset.Ioc R (2 * R),
      (∑ χ : primitiveCharacters d,
        primeProductBlockMaximum P Q ((m₀ + M) * (n₀ + N)) d χ.1) / d.totient) ≤
      (1 / (R : ℝ)) * (akbaryHambrookC3 * Real.sqrt ((M : ℝ) + (2 * (R : ℝ)) ^ 2) *
        Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) * Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ))) := by
  apply (dyadic_totient_mass_le R hR _ ?_).trans
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      semiprimeBlock_maximal_largeSieve (2 * R) m₀ M n₀ N hM hN
        P Q hPinterval hQinterval hP hQ hsep
  · intro d
    exact Finset.sum_nonneg (fun χ _ => primeProductBlockMaximum_nonneg _ _ _ _ χ.1)

end Erdos964
