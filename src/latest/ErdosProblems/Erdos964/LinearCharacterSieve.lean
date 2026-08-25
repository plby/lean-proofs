import ErdosProblems.Erdos964.CharacterReduction

/-!
# Maximal linear character sums for the imprimitive correction

The excluded prime factors leave linear character sums in the other factor.
Their endpoint maxima inherit a large-sieve bound by taking one factor of
the verified bilinear theorem to be the singleton `{1}`.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def finiteCharacterCutoffMaximum (S : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) : ℝ :=
  if hK : 1 ≤ K then
    (Finset.Icc 1 K).sup' (Finset.nonempty_Icc.mpr hK)
      (fun X => ‖∑ n ∈ S with n ≤ X, χ n‖)
  else 0

theorem finiteCharacterCutoffMaximum_eq_bilinear (S : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) :
    finiteCharacterCutoffMaximum S K d χ =
      bilinearProductCutoffMaximum K d χ {1} S (fun _ => 1) (fun _ => 1) := by
  have heq (X : ℕ) :
      (∑ n ∈ S with n ≤ X, χ n) =
        bilinearProductCutoffSum X d χ {1} S (fun _ => 1) (fun _ => 1) := by
    simp [bilinearProductCutoffSum]
  unfold finiteCharacterCutoffMaximum bilinearProductCutoffMaximum
  simp only [heq]

theorem finiteCharacterCutoffMaximum_nonneg (S : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) : 0 ≤ finiteCharacterCutoffMaximum S K d χ := by
  rw [finiteCharacterCutoffMaximum_eq_bilinear]
  exact bilinearProductCutoffMaximum_nonneg _ _ _ _ _ _ _

theorem finiteCharacterCutoffMaximum_le_card (S : Finset ℕ) (K d : ℕ)
    (χ : DirichletCharacter ℂ d) : finiteCharacterCutoffMaximum S K d χ ≤ S.card := by
  unfold finiteCharacterCutoffMaximum
  split_ifs with hK
  · apply Finset.sup'_le
    intro X hX
    calc
      _ ≤ ∑ n ∈ S with n ≤ X, ‖χ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S with n ≤ X, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => χ.norm_le_one _)
      _ = ((S.filter (fun n => n ≤ X)).card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast Finset.card_filter_le S (fun n => n ≤ X)
  · exact Nat.cast_nonneg _

theorem norm_finiteCharacterCutoff_le_maximum (S : Finset ℕ) (K d X : ℕ)
    (χ : DirichletCharacter ℂ d) (hS : ∀ n ∈ S, 0 < n) (hX : X ≤ K) :
    ‖∑ n ∈ S with n ≤ X, χ n‖ ≤ finiteCharacterCutoffMaximum S K d χ := by
  by_cases hpos : 0 < X
  · have hK : 1 ≤ K := (Nat.succ_le_of_lt hpos).trans hX
    rw [finiteCharacterCutoffMaximum, dif_pos hK]
    exact Finset.le_sup' (fun Y => ‖∑ n ∈ S with n ≤ Y, χ n‖)
      (Finset.mem_Icc.mpr ⟨hpos, hX⟩)
  · have hzero : S.filter (fun n => n ≤ X) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have := hS n hn'.1
      omega
    rw [hzero, Finset.sum_empty, norm_zero]
    exact finiteCharacterCutoffMaximum_nonneg S K d χ

/-- The endpoint maximum also bounds a product slice, including cutoffs
outside the support interval and the empty cutoff. -/
theorem norm_productSlice_le_maximum (S : Finset ℕ) (K d p X : ℕ)
    (χ : DirichletCharacter ℂ d) (hp : 0 < p)
    (hS : S ⊆ Finset.Ioc 0 K) :
    ‖∑ n ∈ S with p * n ≤ X, χ n‖ ≤ finiteCharacterCutoffMaximum S K d χ := by
  have hfilter : S.filter (fun n => p * n ≤ X) =
      S.filter (fun n => n ≤ min (X / p) K) := by
    ext n
    simp only [Finset.mem_filter, le_min_iff]
    constructor
    · rintro ⟨hn, hprod⟩
      refine ⟨hn, ?_, (Finset.mem_Ioc.mp (hS hn)).2⟩
      exact (Nat.le_div_iff_mul_le hp).mpr (by simpa only [mul_comm] using hprod)
    · rintro ⟨hn, hdiv, _⟩
      exact ⟨hn, by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hdiv⟩
  rw [hfilter]
  exact norm_finiteCharacterCutoff_le_maximum S K d _ χ
    (fun n hn => (Finset.mem_Ioc.mp (hS hn)).1) (min_le_right _ _)

/-- For small conductors it suffices to use cancellation in just the larger
prime factor. This comparison is uniform over every product endpoint. -/
theorem primeProductBlockMaximum_le_card_mul_linearMaximum
    (P Q : Finset ℕ) (K N d : ℕ) (χ : DirichletCharacter ℂ d)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hQinterval : Q ⊆ Finset.Ioc 0 N) :
    primeProductBlockMaximum P Q K d χ ≤
      (P.card : ℝ) * finiteCharacterCutoffMaximum Q N d χ := by
  have hpoint (X : ℕ) : ‖∑ n ∈ primeProductBlock P Q X, χ n‖ ≤
      (P.card : ℝ) * finiteCharacterCutoffMaximum Q N d χ := by
    rw [sum_primeProductBlock P Q X (fun n => χ n) hP hQ hsep]
    calc
      _ ≤ ∑ p ∈ P, ‖∑ r ∈ Q with p * r ≤ X, χ ((p * r : ℕ) : ZMod d)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, finiteCharacterCutoffMaximum Q N d χ := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [Nat.cast_mul, map_mul, ← Finset.mul_sum, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
          (norm_productSlice_le_maximum Q N d p X χ (hP p hp).pos hQinterval)
      _ = _ := by simp
  unfold primeProductBlockMaximum
  split_ifs with hK
  · exact Finset.sup'_le _ _ (fun X _ => hpoint X)
  · exact mul_nonneg (Nat.cast_nonneg _) (finiteCharacterCutoffMaximum_nonneg Q N d χ)

/-- A maximal linear large-sieve bound, valid for arbitrary supports in a
translated interval. -/
theorem finiteCharacterCutoffMaximum_largeSieve (R n₀ N : ℕ) (hN : 0 < N)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc n₀ (n₀ + N)) :
    (∑ d ∈ Finset.Ioc 0 R, (d : ℝ) / d.totient *
      ∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum S (n₀ + N) d ψ.1) ≤
      akbaryHambrookC3 * Real.sqrt (1 + (R : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (R : ℝ) ^ 2) * Real.sqrt S.card *
          Real.log (2 * ((n₀ + N : ℕ) : ℝ)) := by
  simp_rw [finiteCharacterCutoffMaximum_eq_bilinear]
  simpa only [zero_add, one_mul, Nat.cast_one, norm_one, one_pow,
    Finset.sum_singleton, Finset.card_singleton, Real.sqrt_one, mul_one,
    Finset.sum_const, nsmul_eq_mul] using
    sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
      R 0 1 n₀ N (by norm_num) hN {1} S (by simp) hS (fun _ => 1) (fun _ => 1)

theorem finiteCharacterCutoffMaximum_dyadic_largeSieve (R n₀ N : ℕ)
    (hR : 0 < R) (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc n₀ (n₀ + N)) :
    (∑ d ∈ Finset.Ioc R (2 * R),
      (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum S (n₀ + N) d ψ.1) /
        d.totient) ≤
      (1 / (R : ℝ)) * (akbaryHambrookC3 * Real.sqrt (1 + (2 * (R : ℝ)) ^ 2) *
        Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) * Real.sqrt S.card *
          Real.log (2 * ((n₀ + N : ℕ) : ℝ))) := by
  apply (dyadic_totient_mass_le R hR _ ?_).trans
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      finiteCharacterCutoffMaximum_largeSieve (2 * R) n₀ N hN S hS
  · intro d
    exact Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg _ _ _ ψ.1)

/-- A prime dividing the inducing conductor contributes zero. Otherwise
its character coefficient has norm at most one. -/
theorem norm_character_mul_productSlice_le (S : Finset ℕ) (K d p X : ℕ)
    (ψ : DirichletCharacter ℂ d) (hp : p.Prime)
    (hS : S ⊆ Finset.Ioc 0 K) :
    ‖ψ p * ∑ n ∈ S with p * n ≤ X, ψ n‖ ≤
      if p ∣ d then 0 else finiteCharacterCutoffMaximum S K d ψ := by
  by_cases hpd : p ∣ d
  · have hnonunit : ¬IsUnit (p : ZMod d) := by
      simpa only [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd] using not_not.mpr hpd
    rw [MulChar.map_nonunit ψ hnonunit, zero_mul, norm_zero, if_pos hpd]
  · rw [if_neg hpd, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)).trans
      (norm_productSlice_le_maximum S K d p X ψ hp.pos hS)

/-- The imprimitive correction is controlled by linear maxima in the other
prime factor. Only prime divisors of the modulus absent from the conductor
remain, so later modulus reindexing retains the saving from the large prime. -/
theorem semiprimeBlock_changeLevel_correction_le (P Q : Finset ℕ) (M N X : ℕ)
    {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) (ψ : DirichletCharacter ℂ d)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hPinterval : P ⊆ Finset.Ioc 0 M) (hQinterval : Q ⊆ Finset.Ioc 0 N)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hsize : ∀ p ∈ P, ∀ r ∈ Q, q < p * r) :
    ‖finiteCharacterSum (primeProductBlock P Q X) d ψ -
      finiteCharacterSum (primeProductBlock P Q X) q
        (DirichletCharacter.changeLevel hd ψ)‖ ≤
      (∑ _p ∈ (P.filter (fun p => p ∣ q)).filter (fun p => ¬p ∣ d),
        finiteCharacterCutoffMaximum Q N d ψ) +
      ∑ _r ∈ (Q.filter (fun r => r ∣ q)).filter (fun r => ¬r ∣ d),
        finiteCharacterCutoffMaximum P M d ψ := by
  classical
  rw [semiprimeBlock_changeLevel_correction P Q X hq hd ψ hP hQ hsep hsize]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ p ∈ P with p ∣ q, ‖ψ p * ∑ r ∈ Q with p * r ≤ X, ψ r‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ P with p ∣ q,
          if p ∣ d then 0 else finiteCharacterCutoffMaximum Q N d ψ := by
        apply Finset.sum_le_sum
        intro p hp
        exact norm_character_mul_productSlice_le Q N d p X ψ
          (hP p (Finset.mem_filter.mp hp).1) hQinterval
      _ = _ := by simp only [Finset.sum_filter, ite_not]
  · calc
      _ ≤ ∑ r ∈ Q with r ∣ q, ‖ψ r * ∑ p ∈ P with p * r ≤ X, ψ p‖ :=
        norm_sum_le _ _
      _ ≤ ∑ r ∈ Q with r ∣ q,
          if r ∣ d then 0 else finiteCharacterCutoffMaximum P M d ψ := by
        apply Finset.sum_le_sum
        intro r hr
        simpa only [mul_comm] using norm_character_mul_productSlice_le P M d r X ψ
          (hQ r (Finset.mem_filter.mp hr).1) hPinterval
      _ = _ := by simp only [Finset.sum_filter, ite_not]

end Erdos964
