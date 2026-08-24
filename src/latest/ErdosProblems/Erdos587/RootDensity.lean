import ErdosProblems.Erdos587.NVDevelopment

/-!
# Quantitative unit-square density

The character expansion is retained as a count, not just as an existence
criterion. Its principal term uses the full Euler density rather than the
coarser lower bound `2^(-omega)` used by the earlier square-hitting theorem.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def primeSetUnitDensity (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, (1 - (p : ℝ)⁻¹)

lemma primeSetUnitDensity_lower (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / 2 : ℝ) ^ s.card ≤ primeSetUnitDensity s :=
  prod_one_sub_prime_inv_lower s hs

lemma primeSetUnitDensity_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < primeSetUnitDensity s :=
  (pow_pos (by norm_num) _).trans_le (primeSetUnitDensity_lower s hs)

lemma card_shiftedPrimeSetCoprimeIndices_density_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ) :
    (H : ℝ) * primeSetUnitDensity s - (2 : ℝ) ^ s.card ≤
      (shiftedPrimeSetCoprimeIndices s M H).card := by
  have hcount := congrArg (fun z : ℤ ↦ (z : ℝ))
    (card_shiftedPrimeSetCoprimeIndices_eq_alternating s hs M H)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one] at hcount
  have herror := shifted_prime_floor_sum_error s hs M H
  rw [← hcount, alternating_prime_reciprocal_eq] at herror
  have hh := (abs_le.mp herror).1
  change -(2 : ℝ) ^ s.card ≤
    ((shiftedPrimeSetCoprimeIndices s M H).card : ℝ) - H * primeSetUnitDensity s at hh
  linarith

lemma unitSquareExpansion_sum_lower {q H : ℕ} (hq : Squarefree q) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range H, restrictedQuadraticPrimeFactorProduct q ∅ (f i)) -
      (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
        |∑ i ∈ Finset.range H, restrictedQuadraticPrimeFactorProduct q t (f i)|) ≤
      ∑ i ∈ Finset.range H, unitSquareExpansionValue q (f i) := by
  classical
  let F : Finset ℕ → ℝ := fun t =>
    ∑ i ∈ Finset.range H, restrictedQuadraticPrimeFactorProduct q t (f i)
  have htotal : (∑ t ∈ q.primeFactors.powerset, F t) =
      ∑ i ∈ Finset.range H, unitSquareExpansionValue q (f i) := by
    dsimp only [F]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact sum_restrictedQuadraticPrimeFactorProduct_powerset hq
  have herase : q.primeFactors.powerset.erase ∅ =
      q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hsplit := Finset.sum_erase_add q.primeFactors.powerset F (by simp : ∅ ∈ q.primeFactors.powerset)
  rw [herase, htotal] at hsplit
  have herr : -(∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t|) ≤
      ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun t ht => neg_abs_le (F t))
  change F ∅ - (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t|) ≤ _
  linarith

lemma restricted_affine_error_le_of_interval_bounds
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) {D R M H : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (B : Finset ℕ → Finset ℕ → ℝ)
    (hB : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, 0 ≤ B t u)
    (hinterval : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H → L ≤ H / (∏ p ∈ u, p) + 1 →
        |∑ j ∈ Finset.range L, quadraticPrimeFactorProduct t (K + j)| ≤ B t u) :
    (∑ t ∈ s.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (D + R * i)|) ≤
      ∑ t ∈ s.powerset.filter Finset.Nonempty, ∑ u ∈ (s \ t).powerset, B t u := by
  apply Finset.sum_le_sum
  intro t ht
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  apply abs_sum_restrictedQuadraticPrimeFactorProduct_affine_le hs hts hRcop hDM
  apply abs_sum_restrictedQuadraticPrimeFactorProduct_le_divisor_bounds hs hts M H (B t)
  intro u hu
  have htu : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
  have hus : u ⊆ s := fun p hp ↦
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hu hp)).1
  have hupos : 0 < ∏ p ∈ u, p := Finset.prod_pos fun p hp ↦ (hs p (hus hp)).pos
  exact abs_divisible_quadraticPrimeFactorProduct_sum_le t htu M H
    (∏ p ∈ u, p) hupos (hB t ht u hu) (hinterval t ht u hu)

lemma unitSquareExpansion_affine_density_lower_of_interval_bounds
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) {D R M H : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (B : Finset ℕ → Finset ℕ → ℝ)
    (hB : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, 0 ≤ B t u)
    (hinterval : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H → L ≤ H / (∏ p ∈ u, p) + 1 →
        |∑ j ∈ Finset.range L, quadraticPrimeFactorProduct t (K + j)| ≤ B t u) :
    (H : ℝ) * primeSetUnitDensity s - (2 : ℝ) ^ s.card -
      (∑ t ∈ s.powerset.filter Finset.Nonempty, ∑ u ∈ (s \ t).powerset, B t u) ≤
      ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  have hprincipal : (H : ℝ) * primeSetUnitDensity s - (2 : ℝ) ^ s.card ≤
      ∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct (primeSetModulus s) ∅ (D + R * i) := by
    calc
      _ ≤ ((shiftedPrimeSetCoprimeIndices s M H).card : ℝ) :=
        card_shiftedPrimeSetCoprimeIndices_density_lower s hs M H
      _ = ∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct (primeSetModulus s) ∅ (M + i) :=
        (sum_restrictedQuadraticPrimeFactorProduct_empty s M H).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh := restrictedQuadraticPrimeFactorProduct_affine
          hs (Finset.empty_subset s) hRcop hDM (i := i)
        simpa only [quadraticPrimeFactorProduct, Finset.prod_empty, one_mul] using hh.symm
  have herr := restricted_affine_error_le_of_interval_bounds s hs hRcop hDM B hB hinterval
  have hexp := unitSquareExpansion_sum_lower (H := H)
    (primeSetModulus_squarefree s hs) (fun i => D + R * i)
  rw [primeFactors_primeSetModulus s hs] at hexp
  linarith

lemma unitSquareTermBudget_total_le (s : Finset ℕ) (H : ℕ) :
    (∑ t ∈ s.powerset.filter Finset.Nonempty,
      ∑ _u ∈ (s \ t).powerset, unitSquareTermBudget s.card H) ≤
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card / 16 := by
  have hcount : (∑ t ∈ s.powerset.filter Finset.Nonempty,
      ((s \ t).powerset.card : ℝ)) ≤ (4 : ℝ) ^ s.card := by
    exact_mod_cast squarefreeSievePairCount_le s
  calc
    _ ≤ (4 : ℝ) ^ s.card * unitSquareTermBudget s.card H := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hcount (unitSquareTermBudget_nonneg _ _)
    _ = _ := by
      rw [unitSquareTermBudget,
        show (8 : ℝ) ^ s.card = (4 : ℝ) ^ s.card * (2 : ℝ) ^ s.card by
          rw [← mul_pow]; norm_num,
        show (1 / 2 : ℝ) ^ s.card = 1 / (2 : ℝ) ^ s.card by simp [div_eq_mul_inv]]
      field_simp

lemma unitSquareExpansion_affine_density_lower_of_budget_cases
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hodd : ∀ p ∈ s, p ≠ 2)
    {D R M H : ℕ} (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hlarge : (4 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcases : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H → L ≤ H / (∏ p ∈ u, p) + 1 →
        (L : ℝ) ≤ unitSquareTermBudget s.card H ∨
        Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
          unitSquareTermBudget s.card H ∨
        (0 < L ∧ CoprimeBurgessCertificate t L (unitSquareTermBudget s.card H))) :
    (H : ℝ) * primeSetUnitDensity s / 2 ≤
      ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  have hinterval : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H → L ≤ H / (∏ p ∈ u, p) + 1 →
        |∑ j ∈ Finset.range L, quadraticPrimeFactorProduct t (K + j)| ≤
          unitSquareTermBudget s.card H := by
    intro t ht u hu K L hLH hL
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
    have htodd : ∀ p ∈ t, p ≠ 2 := fun p hp ↦ hodd p (hts hp)
    have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
    rcases hcases t ht u hu K L hLH hL with htriv | hcompletion | hburgess
    · exact (abs_sum_quadraticPrimeFactorProduct_le_length t htprime K L).trans htriv
    · exact (abs_sum_quadraticPrimeFactorProduct_le_completion_long
        t htprime htodd htne K L).trans hcompletion
    · exact abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
        t htprime htodd htne K L hburgess.1
        (unitSquareTermBudget_nonneg _ _) (Or.inr hburgess.2)
  have hraw := unitSquareExpansion_affine_density_lower_of_interval_bounds s hs hRcop hDM
    (fun _ _ => unitSquareTermBudget s.card H)
    (fun _ _ _ _ => unitSquareTermBudget_nonneg _ _) hinterval
  have hprod : (H : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ H * primeSetUnitDensity s :=
    mul_le_mul_of_nonneg_left (primeSetUnitDensity_lower s hs) (Nat.cast_nonneg H)
  have hendpoint : 4 * (2 : ℝ) ^ s.card ≤ (H : ℝ) * primeSetUnitDensity s := by
    have hh := mul_le_mul_of_nonneg_right hlarge
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) s.card)
    have hpow : (4 : ℝ) ^ s.card * (1 / 2 : ℝ) ^ s.card = (2 : ℝ) ^ s.card := by
      rw [← mul_pow]
      norm_num
    rw [mul_assoc, hpow] at hh
    exact hh.trans hprod
  have herr := unitSquareTermBudget_total_le s H
  have hmain0 : 0 ≤ (H : ℝ) * primeSetUnitDensity s :=
    mul_nonneg (Nat.cast_nonneg H) (primeSetUnitDensity_pos s hs).le
  linarith

lemma unitSquareExpansion_affine_density_lower_of_local_certificates
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hodd : ∀ p ∈ s, p ≠ 2)
    {D R M H : ℕ} (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s]) (hH : 0 < H)
    (hlarge : (4 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcert : ∀ t ∈ s.powerset.filter Finset.Nonempty, ∀ L : ℕ,
      L ≤ H → unitSquareTermBudget s.card H < L →
      ¬ Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
        unitSquareTermBudget s.card H →
      CoprimeBurgessCertificate t L
        ((L : ℝ) / (16 * (2 : ℝ) ^ t.card * unitSquareBurgessLoss s.card))) :
    (H : ℝ) * primeSetUnitDensity s / 2 ≤
      ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  apply unitSquareExpansion_affine_density_lower_of_budget_cases s hs hodd hRcop hDM hlarge
  intro t ht u hu K L hLH hL
  by_cases htriv : (L : ℝ) ≤ unitSquareTermBudget s.card H
  · exact Or.inl htriv
  right
  by_cases hcompletion : Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
      unitSquareTermBudget s.card H
  · exact Or.inl hcompletion
  right
  have hLpos : 0 < L := by
    have hbudget_nonneg := unitSquareTermBudget_nonneg s.card H
    exact_mod_cast lt_of_not_ge htriv |>.trans_le' hbudget_nonneg
  exact ⟨hLpos,
    (hcert t ht L hLH (lt_of_not_ge htriv) hcompletion).to_unitSquareTermBudget
      hH (hLH.trans (Nat.le_add_right H 1))⟩

/-- The existing local completion/Burgess certificates give a quantitative
affine unit-square expansion, uniformly for intervals above the square-root
scale of a sufficiently large odd squarefree conductor. -/
theorem exists_unitSquareAffineDensityThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      (∀ p ∈ s, p ≠ 2) → Q₀ ≤ primeSetModulus s →
      ∀ (D R M H : ℕ), R.Coprime (primeSetModulus s) →
        D ≡ R * M [MOD primeSetModulus s] → 0 < H →
        (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
        (H : ℝ) * primeSetUnitDensity s / 2 ≤
          ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  obtain ⟨Qcomp, hcomp⟩ := exists_unitSquareCompletionScaleThreshold
  obtain ⟨Qloss, hloss⟩ := exists_unitSquareGlobalLossThreshold
  obtain ⟨Qfit, hfit⟩ := exists_unitSquareFitScaleThreshold
  obtain ⟨Qwrap, hwrap⟩ := exists_unitSquareWrapScaleThreshold
  obtain ⟨Qbudget, hbudget⟩ := exists_unitSquareBudgetThreeThreshold
  obtain ⟨Qgrowth, hgrowth⟩ := exists_burgessFourthGrowthThreshold
  let T : ℕ := max 3 Qgrowth
  refine ⟨max Qcomp (max Qloss (max Qfit (max Qwrap (max Qbudget (T ^ 2))))), ?_⟩
  intro s hs hodd hQ D R M H hRcop hDM hH hroot
  let Q : ℕ := primeSetModulus s
  have hQcomp : Qcomp ≤ Q := by dsimp [Q]; omega
  have hQloss : Qloss ≤ Q := by dsimp [Q]; omega
  have hQfit : Qfit ≤ Q := by dsimp [Q]; omega
  have hQwrap : Qwrap ≤ Q := by dsimp [Q]; omega
  have hQbudget : Qbudget ≤ Q := by dsimp [Q]; omega
  have hT2Q : T ^ 2 ≤ Q := by dsimp [Q]; omega
  have hcompletionScale := hcomp s hs hQcomp
  have hglobalLoss := hloss s hs hQloss
  have hfitLoss := hfit s hs hQfit
  have hbudgetThree := hbudget s hs hQbudget hroot
  have hbudgetMul : (3 : ℝ) * (16 * (8 : ℝ) ^ s.card) ≤ H := by
    dsimp [unitSquareTermBudget] at hbudgetThree
    exact (le_div_iff₀ (show (0 : ℝ) < 16 * 8 ^ s.card by positivity)).mp hbudgetThree
  have hlarge : (4 : ℝ) * (4 : ℝ) ^ s.card ≤ H := by
    calc
      (4 : ℝ) * 4 ^ s.card ≤ 4 * 8 ^ s.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) s.card)
          (by norm_num)
      _ ≤ 3 * (16 * 8 ^ s.card) := by
        have hp : (0 : ℝ) ≤ 8 ^ s.card := by positivity
        linarith
      _ ≤ H := hbudgetMul
  apply unitSquareExpansion_affine_density_lower_of_local_certificates
    s hs hodd hRcop hDM hH hlarge
  intro t ht L hLH hbudgetLt hnotCompletion
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hfailure : unitSquareTermBudget s.card H <
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) := lt_of_not_ge hnotCompletion
  have hlocal := completion_failure_local_scale hs hts htne hroot hcompletionScale hfailure
  have hrel := hlocal.1
  have hQqSq : Q < (primeSetModulus t) ^ 2 := by
    exact_mod_cast (show (Q : ℝ) < (primeSetModulus t : ℝ) ^ 2 by simpa only [Q] using hrel)
  have hTlt : T < primeSetModulus t :=
    (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp (hT2Q.trans_lt hQqSq)
  have hq3 : 3 ≤ primeSetModulus t := by dsimp [T] at hTlt; omega
  have hqgrowth : Qgrowth ≤ primeSetModulus t := by dsimp [T] at hTlt; omega
  have hfitScale := unitSquare_fit_scale hs hts htne hfitLoss
  have hwrapScale := hwrap s hs hQwrap t hts htne hrel
  exact local_extraLoss_certificate_of_completion_failure
    s hs t hts htne hroot hcompletionScale hglobalLoss hq3
    (hgrowth _ hqgrowth) hbudgetThree hfitScale hwrapScale hLH hbudgetLt hfailure

end Erdos587
