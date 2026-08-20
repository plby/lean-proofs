import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealCounting
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A Mertens upper bound for prime ideals

This file proves the elementary part of the number-field Mertens estimate needed by the
Elliott-tail sieve.  We only need an upper bound for the direct Euler product.  The proof uses
the linear asymptotic for the number of integral ideals, partial summation, and unique
factorization of ideals; it does not use an effective prime-ideal theorem.
-/

noncomputable section

open Filter NumberField
open scoped Topology nonZeroDivisors BigOperators

namespace Erdos980.ElliottTail.PrimeIdealMertens

variable (K : Type*) [Field K] [NumberField K]

/-- Nonzero integral ideals of norm at most `N`. -/
private noncomputable def nonzeroIdealsUpTo (N : ℕ) :
    Finset (Chebotarev.NonzeroIdeal K) := by
  classical
  exact (Set.Finite.preimage
    (f := fun I : Chebotarev.NonzeroIdeal K ↦ I.1)
    (fun _ _ _ _ ↦ Subtype.ext)
    (Ideal.finite_setOfPred_absNorm_le (S := NumberField.RingOfIntegers K) N)).toFinset

private lemma mem_nonzeroIdealsUpTo {N : ℕ} {I : Chebotarev.NonzeroIdeal K} :
    I ∈ nonzeroIdealsUpTo K N ↔ Ideal.absNorm I.1 ≤ N := by
  classical
  simp [nonzeroIdealsUpTo]

/-- The ideal harmonic mass, grouped by absolute norm. -/
def idealHarmonicMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Chebotarev.idealNormMultiplicity K n : ℝ) / (n : ℝ)

private lemma idealHarmonicMass_eq_sum_ideals (N : ℕ) :
    idealHarmonicMass K N =
      ∑ I ∈ nonzeroIdealsUpTo K N, ((Ideal.absNorm I.1 : ℝ))⁻¹ := by
  classical
  rw [idealHarmonicMass]
  have hmaps : ∀ I ∈ nonzeroIdealsUpTo K N,
      Ideal.absNorm I.1 ∈ Finset.Icc 1 N := by
    intro I hI
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h ↦ I.2 (Ideal.absNorm_eq_zero_iff.mp h)),
      (mem_nonzeroIdealsUpTo K).mp hI⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun I : Chebotarev.NonzeroIdeal K ↦ ((Ideal.absNorm I.1 : ℝ))⁻¹)]
  apply Finset.sum_congr rfl
  intro n hn
  have hcard : Chebotarev.idealNormMultiplicity K n =
      ((nonzeroIdealsUpTo K N).filter (fun I ↦ Ideal.absNorm I.1 = n)).card := by
    have hf : {I : Chebotarev.NonzeroIdeal K |
        Ideal.absNorm I.1 = n}.Finite :=
      Set.Finite.preimage (fun _ _ _ _ ↦ Subtype.ext)
        (Ideal.finite_setOfPred_absNorm_eq (S := NumberField.RingOfIntegers K) n)
    unfold Chebotarev.idealNormMultiplicity
    change Nat.card {I : Chebotarev.NonzeroIdeal K //
      I ∈ {I : Chebotarev.NonzeroIdeal K | Ideal.absNorm I.1 = n}} = _
    rw [Nat.subtype_card hf.toFinset (fun I ↦ hf.mem_toFinset)]
    apply Finset.card_bij (fun I _ ↦ I)
    · intro I hI
      have hInorm : Ideal.absNorm I.1 = n := hf.mem_toFinset.mp hI
      simp only [Finset.mem_filter, mem_nonzeroIdealsUpTo]
      exact ⟨by simpa [hInorm] using (Finset.mem_Icc.mp hn).2, hInorm⟩
    · intro I _ J _ h
      exact h
    · intro I hI
      simp only [Finset.mem_filter] at hI
      exact ⟨I, hf.mem_toFinset.mpr hI.2, rfl⟩
  calc
    (Chebotarev.idealNormMultiplicity K n : ℝ) / (n : ℝ) =
        (Chebotarev.idealNormMultiplicity K n : ℝ) * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ = ∑ _I ∈ (nonzeroIdealsUpTo K N).filter
        (fun I ↦ Ideal.absNorm I.1 = n), (n : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = ∑ I ∈ (nonzeroIdealsUpTo K N).filter
        (fun I ↦ Ideal.absNorm I.1 = n), ((Ideal.absNorm I.1 : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro I hI
      simp only [Finset.mem_filter] at hI
      rw [hI.2]

/-- Discrete Abel summation in the closed-interval form used below. -/
private lemma weighted_sum_eq_partial_sums (a : ℕ → ℝ) (ha0 : a 0 = 0)
    {N : ℕ} (hN : 0 < N) :
    ∑ i ∈ Finset.Icc 1 N, a i / (i : ℝ) =
      (∑ i ∈ Finset.Icc 1 N, a i) / (N : ℝ) +
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, a j) / ((i : ℝ) * (i + 1)) := by
  have hbp := Finset.sum_Ioc_by_parts
    (fun i : ℕ ↦ ((i : ℝ)⁻¹)) a (m := 0) (n := N) hN
  simp only [smul_eq_mul] at hbp
  rw [show Finset.Ioc 0 N = Finset.Icc 1 N by ext i; simp; omega] at hbp
  have hrangeN : ∑ i ∈ Finset.range (N + 1), a i =
      ∑ i ∈ Finset.Icc 1 N, a i := by
    calc
      ∑ i ∈ Finset.range (N + 1), a i =
          (∑ i ∈ (Finset.range (N + 1)).erase 0, a i) + a 0 :=
        (Finset.sum_erase_add _ _ (by simp)).symm
      _ = ∑ i ∈ (Finset.range (N + 1)).erase 0, a i := by rw [ha0, add_zero]
      _ = ∑ i ∈ Finset.Icc 1 N, a i := by
        congr 1
        ext i
        simp
        omega
  have hrange0 : ∑ i ∈ Finset.range (0 + 1), a i = 0 := by simp [ha0]
  rw [hrangeN, hrange0] at hbp
  simp only [inv_one, mul_zero, sub_zero] at hbp
  rw [show Finset.Ioc 0 (N - 1) = Finset.Icc 1 (N - 1) by ext i; simp; omega] at hbp
  calc
    ∑ i ∈ Finset.Icc 1 N, a i / (i : ℝ) =
        ∑ i ∈ Finset.Icc 1 N, ((i : ℝ)⁻¹) * a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv, mul_comm]
    _ = (N : ℝ)⁻¹ * (∑ i ∈ Finset.Icc 1 N, a i) -
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) *
            (∑ j ∈ Finset.range (i + 1), a j) := hbp
    _ = (∑ i ∈ Finset.Icc 1 N, a i) / (N : ℝ) +
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, a j) / ((i : ℝ) * (i + 1)) := by
      rw [sub_eq_add_neg, div_eq_mul_inv,
        mul_comm (∑ i ∈ Finset.Icc 1 N, a i)]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hirange : ∑ j ∈ Finset.range (i + 1), a j =
          ∑ j ∈ Finset.Icc 1 i, a j := by
        calc
          ∑ j ∈ Finset.range (i + 1), a j =
              (∑ j ∈ (Finset.range (i + 1)).erase 0, a j) + a 0 :=
            (Finset.sum_erase_add _ _ (by simp)).symm
          _ = ∑ j ∈ (Finset.range (i + 1)).erase 0, a j := by rw [ha0, add_zero]
          _ = ∑ j ∈ Finset.Icc 1 i, a j := by
            congr 1
            ext j
            simp
            omega
      rw [hirange]
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hi0 : (i : ℝ) ≠ 0 := by positivity
      have his0 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num [Nat.cast_add, Nat.cast_one] at his0 ⊢
      field_simp
      ring

private lemma shifted_harmonic_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.Icc 1 (N - 1), (((i + 1 : ℕ) : ℝ))⁻¹) =
      (harmonic N : ℝ) - 1 := by
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [show Finset.Icc 1 (N - 1) = Finset.Ico 1 N by ext i; simp; omega]
  rw [Finset.sum_Ico_add' (fun i : ℕ ↦ ((i : ℝ))⁻¹) 1 N 1]
  rw [show Finset.Ico (1 + 1) (N + 1) = Finset.Ioc 1 N by ext i; simp; omega]
  rw [← Finset.Icc_erase_left]
  have he := Finset.sum_erase_add (Finset.Icc 1 N)
    (fun i : ℕ ↦ ((i : ℝ))⁻¹) (Finset.left_mem_Icc.mpr hN)
  norm_num at he ⊢
  linarith

/-- The reciprocal-norm mass of all nonzero integral ideals is eventually bounded below by a
positive multiple of `log N`.  This is the only analytic input in the Euler-product argument. -/
theorem eventually_log_le_idealHarmonicMass :
    ∀ᶠ N : ℕ in atTop,
      (NumberField.dedekindZeta_residue K / 4) * Real.log (N : ℝ) ≤
        idealHarmonicMass K N := by
  let κ : ℝ := NumberField.dedekindZeta_residue K
  have hκ : 0 < κ := NumberField.dedekindZeta_residue_pos K
  have hratio : ∀ᶠ N : ℕ in atTop,
      κ / 2 ≤
        (∑ n ∈ Finset.Icc 1 N,
          (Chebotarev.idealNormMultiplicity K n : ℝ)) / (N : ℝ) := by
    have hnhds : Set.Ioi (κ / 2) ∈ nhds κ := Ioi_mem_nhds (by linarith [hκ])
    filter_upwards [(Chebotarev.tendsto_sum_idealNormMultiplicity_div K).eventually hnhds]
      with N hN
    exact hN.le
  rw [eventually_atTop] at hratio
  obtain ⟨N₀, hN₀⟩ := hratio
  have hN₀pos : 1 ≤ N₀ := by
    by_contra h
    have hzero : N₀ = 0 := by omega
    have hbad := hN₀ 0 (by simp [hzero])
    simp [hzero] at hbad
    linarith
  let B : ℝ := 1 + ∑ i ∈ Finset.Icc 1 (N₀ - 1), (((i + 1 : ℕ) : ℝ))⁻¹
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hlog : ∀ᶠ N : ℕ in atTop, 2 * B ≤ Real.log (N : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * B)))
  filter_upwards [hlog, eventually_ge_atTop (max N₀ 1)] with N hlogN hNbig
  have hN₀N : N₀ ≤ N := le_trans (Nat.le_max_left _ _) hNbig
  have hN1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hNbig
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN1
  have hAbel := weighted_sum_eq_partial_sums
    (fun n ↦ (Chebotarev.idealNormMultiplicity K n : ℝ))
    (by simp [Chebotarev.idealNormMultiplicity_zero]) hNpos
  change (κ / 4) * Real.log (N : ℝ) ≤ idealHarmonicMass K N
  rw [idealHarmonicMass, hAbel]
  have hboundary : 0 ≤
      (∑ i ∈ Finset.Icc 1 N,
        (Chebotarev.idealNormMultiplicity K i : ℝ)) / (N : ℝ) := by positivity
  have hsubset : Finset.Icc N₀ (N - 1) ⊆ Finset.Icc 1 (N - 1) := by
    intro i hi
    rw [Finset.mem_Icc] at hi ⊢
    exact ⟨hN₀pos.trans hi.1, hi.2⟩
  have hterms_nonneg : ∀ i ∈ Finset.Icc 1 (N - 1),
      0 ≤ (∑ j ∈ Finset.Icc 1 i,
        (Chebotarev.idealNormMultiplicity K j : ℝ)) / ((i : ℝ) * (i + 1)) := by
    intro i hi
    positivity
  have htail : κ / 2 *
      (∑ i ∈ Finset.Icc N₀ (N - 1), (((i + 1 : ℕ) : ℝ))⁻¹) ≤
      ∑ i ∈ Finset.Icc 1 (N - 1),
        (∑ j ∈ Finset.Icc 1 i,
          (Chebotarev.idealNormMultiplicity K j : ℝ)) / ((i : ℝ) * (i + 1)) := by
    calc
      κ / 2 * (∑ i ∈ Finset.Icc N₀ (N - 1), (((i + 1 : ℕ) : ℝ))⁻¹) =
          ∑ i ∈ Finset.Icc N₀ (N - 1), κ / 2 / ((i + 1 : ℕ) : ℝ) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.Icc N₀ (N - 1),
          (∑ j ∈ Finset.Icc 1 i,
            (Chebotarev.idealNormMultiplicity K j : ℝ)) / ((i : ℝ) * (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN₀ : N₀ ≤ i := (Finset.mem_Icc.mp hi).1
        have hii : 1 ≤ i := by
          have : κ / 2 ≤
              (∑ j ∈ Finset.Icc 1 i,
                (Chebotarev.idealNormMultiplicity K j : ℝ)) / (i : ℝ) := hN₀ i hiN₀
          by_contra h
          have : i = 0 := by omega
          subst i
          simp at this
          linarith
        have hiRatio := hN₀ i hiN₀
        rw [show (∑ j ∈ Finset.Icc 1 i,
            (Chebotarev.idealNormMultiplicity K j : ℝ)) / ((i : ℝ) * (i + 1)) =
            ((∑ j ∈ Finset.Icc 1 i,
              (Chebotarev.idealNormMultiplicity K j : ℝ)) / (i : ℝ)) /
                ((i + 1 : ℕ) : ℝ) by
              have hi0 : (i : ℝ) ≠ 0 := by positivity
              norm_num [Nat.cast_add, Nat.cast_one]
              field_simp]
        exact div_le_div_of_nonneg_right hiRatio (by positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun i hi _ ↦ hterms_nonneg i hi)
  have htail_eq :
      (∑ i ∈ Finset.Icc N₀ (N - 1), (((i + 1 : ℕ) : ℝ))⁻¹) =
        (harmonic N : ℝ) - B := by
    have hpre : Finset.Icc 1 (N₀ - 1) ⊆ Finset.Icc 1 (N - 1) :=
      Finset.Icc_subset_Icc le_rfl (Nat.sub_le_sub_right hN₀N 1)
    have hset : Finset.Icc N₀ (N - 1) =
        Finset.Icc 1 (N - 1) \ Finset.Icc 1 (N₀ - 1) := by
      ext i
      simp
      omega
    rw [hset, Finset.sum_sdiff_eq_sub hpre, shifted_harmonic_sum N hN1]
    dsimp [B]
    ring
  rw [htail_eq] at htail
  have hharm : Real.log (N : ℝ) ≤ (harmonic N : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
        gcongr
        omega
      _ ≤ (harmonic N : ℝ) := log_add_one_le_harmonic N
  have hcore : (κ / 4) * Real.log (N : ℝ) ≤ κ / 2 * ((harmonic N : ℝ) - B) := by
    have hlogB : B ≤ Real.log (N : ℝ) / 2 := by linarith
    have : Real.log (N : ℝ) / 2 ≤ (harmonic N : ℝ) - B := by linarith
    nlinarith [hκ]
  linarith

/-! ## The finite Euler inequality -/

open UniqueFactorizationMonoid

private theorem pow_count_dvd_prod {A : Type*} [CommMonoid A] [DecidableEq A] (a : A)
    (s : Multiset A) : a ^ s.count a ∣ s.prod :=
  (Multiset.prod_replicate (s.count a) a) ▸
    Multiset.prod_dvd_prod_of_le (Multiset.le_count_iff_replicate_le.mp le_rfl)

private theorem prod_pow_count_normalizedFactors_eq
    (P : Finset (Ideal (NumberField.RingOfIntegers K)))
    {𝔠 : Ideal (NumberField.RingOfIntegers K)} (h₀ : 𝔠 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ normalizedFactors 𝔠, 𝔭 ∈ P) :
    𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (normalizedFactors 𝔠).count 𝔭 := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h₀]
  rw [Finset.prod_multiset_count]
  refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
  intro 𝔭 _ hnotin
  rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]

private theorem count_normalizedFactors_le_log
    {𝔭 𝔟 : Ideal (NumberField.RingOfIntegers K)}
    (h𝔭p : 𝔭.IsPrime) (h𝔭₀ : 𝔭 ≠ ⊥) (h𝔟₀ : 𝔟 ≠ ⊥) {N : ℕ}
    (h𝔟N : Ideal.absNorm 𝔟 ≤ N) :
    (normalizedFactors 𝔟).count 𝔭 ≤ Nat.log 2 N := by
  have hk : 𝔭 ^ (normalizedFactors 𝔟).count 𝔭 ∣ 𝔟 := by
    have hd := pow_count_dvd_prod 𝔭 (normalizedFactors 𝔟)
    rwa [Ideal.prod_normalizedFactors_eq_self h𝔟₀] at hd
  have hN𝔭₂ : 2 ≤ Ideal.absNorm 𝔭 := by
    have h₁ : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭p.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h₀ : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭₀ (Ideal.absNorm_eq_zero_iff.mp h)
    omega
  have h𝔟₀' : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ h𝔟₀ (Ideal.absNorm_eq_zero_iff.mp h)
  have hdvd : Ideal.absNorm 𝔭 ^ (normalizedFactors 𝔟).count 𝔭
      ∣ Ideal.absNorm 𝔟 := by
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hk)
    rwa [map_pow] at this
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hN𝔭₂ _)
    (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h𝔟₀') hdvd) h𝔟N))

private theorem absNorm_rpow_eq_prod_attach_count
    (P : Finset (Ideal (NumberField.RingOfIntegers K)))
    {𝔟 : Ideal (NumberField.RingOfIntegers K)} (h₀ : 𝔟 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ normalizedFactors 𝔟, 𝔭 ∈ P) (e : ℝ) :
    (Ideal.absNorm 𝔟 : ℝ) ^ e = ∏ 𝔭 ∈ P.attach,
      (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (normalizedFactors 𝔟).count 𝔭.1 := by
  have hNprod : Ideal.absNorm 𝔟 =
      ∏ 𝔭 ∈ P, (Ideal.absNorm 𝔭) ^ (normalizedFactors 𝔟).count 𝔭 := by
    conv_lhs => rw [prod_pow_count_normalizedFactors_eq K P h₀ hP, map_prod]
    exact Finset.prod_congr rfl fun 𝔭 _ ↦ by rw [map_pow]
  rw [Finset.prod_attach P
    (fun 𝔭 ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (normalizedFactors 𝔟).count 𝔭),
    hNprod]
  push_cast
  rw [← Real.finsetProd_rpow P _ (fun 𝔭 _ ↦ by positivity) e]
  refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
  rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭 : ℝ)) _,
    ← Real.rpow_natCast (((Ideal.absNorm 𝔭 : ℝ)) ^ e) _,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]

private theorem sum_rpow_le_euler_prod
    (P : Finset (Ideal (NumberField.RingOfIntegers K)))
    (hPprime : ∀ 𝔭 ∈ P, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥)
    (N : ℕ) (BF : Finset (Ideal (NumberField.RingOfIntegers K)))
    (hBF : ∀ 𝔟 ∈ BF, 𝔟 ≠ ⊥ ∧
      (∀ 𝔭 ∈ normalizedFactors 𝔟, 𝔭 ∈ P) ∧ Ideal.absNorm 𝔟 ≤ N)
    (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e ≤
      ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  classical
  set Kn := Nat.log 2 N
  have hx₀ : ∀ 𝔭 ∈ P, (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ)) ^ e :=
    fun 𝔭 _ ↦ Real.rpow_nonneg (by positivity) e
  set cnt : Ideal (NumberField.RingOfIntegers K) →
      ((𝔭 : Ideal (NumberField.RingOfIntegers K)) → 𝔭 ∈ P → ℕ) :=
    fun 𝔟 𝔭 _ ↦ (normalizedFactors 𝔟).count 𝔭
  set F : (((𝔭 : Ideal (NumberField.RingOfIntegers K)) → 𝔭 ∈ P → ℕ)) → ℝ :=
    fun g ↦ ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (g 𝔭.1 𝔭.2)
  have hterm : ∀ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e = F (cnt 𝔟) := by
    intro 𝔟 h𝔟
    obtain ⟨hb₀, hbP, _⟩ := hBF 𝔟 h𝔟
    simpa only [F, cnt] using absNorm_rpow_eq_prod_attach_count K P hb₀ hbP e
  have hmaps : ∀ 𝔟 ∈ BF, cnt 𝔟 ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)) := by
    intro 𝔟 h𝔟
    obtain ⟨hb₀, _hbP, hbN⟩ := hBF 𝔟 h𝔟
    rw [Finset.mem_pi]
    intro 𝔭 h𝔭
    change (normalizedFactors 𝔟).count 𝔭 ∈ Finset.range (Kn + 1)
    rw [Finset.mem_range, Nat.lt_succ_iff]
    obtain ⟨h𝔭p, h𝔭₀⟩ := hPprime 𝔭 h𝔭
    exact count_normalizedFactors_le_log K h𝔭p h𝔭₀ hb₀ hbN
  have hinj : Set.InjOn cnt BF := by
    intro 𝔞 ha 𝔟 hb hcnteq
    obtain ⟨ha₀, haP, _⟩ := hBF 𝔞 ha
    obtain ⟨hb₀, hbP, _⟩ := hBF 𝔟 hb
    have hcc : ∀ 𝔭 ∈ P, (normalizedFactors 𝔞).count 𝔭 =
        (normalizedFactors 𝔟).count 𝔭 :=
      fun 𝔭 h𝔭 ↦ congrFun (congrFun hcnteq 𝔭) h𝔭
    rw [prod_pow_count_normalizedFactors_eq K P ha₀ haP,
      prod_pow_count_normalizedFactors_eq K P hb₀ hbP]
    exact Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ by rw [hcc 𝔭 h𝔭]
  calc
    ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e =
        ∑ 𝔟 ∈ BF, F (cnt 𝔟) := Finset.sum_congr rfl hterm
    _ = ∑ g ∈ BF.image cnt, F g :=
      (Finset.sum_image (fun a ha b hb ↦ hinj ha hb)).symm
    _ ≤ ∑ g ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)), F g := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun g _ _ ↦ Finset.prod_nonneg fun 𝔭 _ ↦ pow_nonneg (hx₀ 𝔭.1 𝔭.2) _)
      intro g hg
      rw [Finset.mem_image] at hg
      obtain ⟨𝔟, h𝔟, rfl⟩ := hg
      exact hmaps 𝔟 h𝔟
    _ = ∏ 𝔭 ∈ P, ∑ k ∈ Finset.range (Kn + 1),
        (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k := by
      rw [Finset.prod_sum P (fun _ ↦ Finset.range (Kn + 1))
        (fun 𝔭 k ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)]
    _ ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
      refine Finset.prod_le_prod
        (fun 𝔭 h𝔭 ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hx₀ 𝔭 h𝔭) k)
        (fun 𝔭 h𝔭 ↦ ?_)
      have h₁x : 0 < 1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e := by
        have := hxlt 𝔭 h𝔭
        linarith
      have hkey := geom_sum_mul (((Ideal.absNorm 𝔭 : ℝ)) ^ e) (Kn + 1)
      have hxK : (0 : ℝ) ≤ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) :=
        pow_nonneg (hx₀ 𝔭 h𝔭) _
      have hmul : (∑ k ∈ Finset.range (Kn + 1),
          (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k) *
          (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e) =
          1 - (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := by
        nlinarith [hkey]
      have hle : (∑ k ∈ Finset.range (Kn + 1),
          (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k) *
          (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e) ≤ 1 := by
        rw [hmul]
        linarith
      rw [← le_div_iff₀ h₁x] at hle
      rwa [one_div] at hle

/-! ## Public Euler products -/

/-- The finite set of nonzero prime ideals of absolute norm at most `N`. -/
noncomputable def primeIdealsUpTo (N : ℕ) :
    Finset (Ideal (NumberField.RingOfIntegers K)) := by
  classical
  exact (Ideal.finite_setOfPred_absNorm_le (S := NumberField.RingOfIntegers K) N).toFinset.filter
    (fun 𝔭 ↦ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥)

@[simp] theorem mem_primeIdealsUpTo {N : ℕ}
    {𝔭 : Ideal (NumberField.RingOfIntegers K)} :
    𝔭 ∈ primeIdealsUpTo K N ↔ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ N := by
  classical
  simp only [primeIdealsUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  tauto

private noncomputable def nonzeroIdealsUpToAsIdeals (N : ℕ) :
    Finset (Ideal (NumberField.RingOfIntegers K)) :=
  (nonzeroIdealsUpTo K N).image Subtype.val

private lemma mem_nonzeroIdealsUpToAsIdeals {N : ℕ}
    {𝔞 : Ideal (NumberField.RingOfIntegers K)} :
    𝔞 ∈ nonzeroIdealsUpToAsIdeals K N ↔ 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N := by
  classical
  constructor
  · intro h
    rw [nonzeroIdealsUpToAsIdeals, Finset.mem_image] at h
    obtain ⟨I, hI, rfl⟩ := h
    exact ⟨I.2, (mem_nonzeroIdealsUpTo K).mp hI⟩
  · rintro ⟨h₀, hN⟩
    rw [nonzeroIdealsUpToAsIdeals, Finset.mem_image]
    exact ⟨⟨𝔞, h₀⟩, (mem_nonzeroIdealsUpTo K).mpr hN, rfl⟩

private lemma idealHarmonicMass_eq_sum_ideals' (N : ℕ) :
    idealHarmonicMass K N =
      ∑ 𝔞 ∈ nonzeroIdealsUpToAsIdeals K N, (Ideal.absNorm 𝔞 : ℝ)⁻¹ := by
  rw [idealHarmonicMass_eq_sum_ideals]
  classical
  rw [nonzeroIdealsUpToAsIdeals, Finset.sum_image]
  intro I _ J _ h
  exact Subtype.ext h

/-- The finite unique-factorization Euler inequality at `s = 1`. -/
theorem idealHarmonicMass_le_inverseEulerProduct (N : ℕ) :
    idealHarmonicMass K N ≤
      ∏ 𝔭 ∈ primeIdealsUpTo K N, (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)⁻¹ := by
  rw [idealHarmonicMass_eq_sum_ideals']
  have hEuler := sum_rpow_le_euler_prod K (primeIdealsUpTo K N)
    (fun 𝔭 h𝔭 ↦ ⟨(mem_primeIdealsUpTo K).mp h𝔭 |>.1,
      (mem_primeIdealsUpTo K).mp h𝔭 |>.2.1⟩)
    N (nonzeroIdealsUpToAsIdeals K N) (fun 𝔟 h𝔟 ↦ ?_) (-1) (fun 𝔭 h𝔭 ↦ ?_)
  · simpa only [Real.rpow_neg_one] using hEuler
  · have hb := (mem_nonzeroIdealsUpToAsIdeals K).mp h𝔟
    refine ⟨hb.1, ?_, hb.2⟩
    intro 𝔭 h𝔭
    have hp : Prime 𝔭 := prime_of_normalized_factor 𝔭 h𝔭
    have hdvd : Ideal.absNorm 𝔭 ∣ Ideal.absNorm 𝔟 :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors h𝔭))
    have hbNormPos : 0 < Ideal.absNorm 𝔟 :=
      Nat.pos_of_ne_zero (fun h ↦ hb.1 (Ideal.absNorm_eq_zero_iff.mp h))
    exact (mem_primeIdealsUpTo K).mpr
      ⟨Ideal.isPrime_of_prime hp, hp.ne_zero,
        (Nat.le_of_dvd hbNormPos hdvd).trans hb.2⟩
  · rw [Real.rpow_neg_one]
    have hp := (mem_primeIdealsUpTo K).mp h𝔭
    have hne₁ : Ideal.absNorm 𝔭 ≠ 1 :=
      fun h ↦ hp.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have hne₀ : Ideal.absNorm 𝔭 ≠ 0 :=
      fun h ↦ hp.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Nat.pos_of_ne_zero hne₀
    apply (inv_lt_one₀ hpos).mpr
    exact_mod_cast (show 1 < Ideal.absNorm 𝔭 by omega)

/-- The direct all-prime-ideal Euler product with inclusive norm cutoff. -/
def primeIdealMertensProductUpTo (N : ℕ) : ℝ :=
  ∏ 𝔭 ∈ primeIdealsUpTo K N, (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)

theorem primeIdealMertensProductUpTo_pos (N : ℕ) :
    0 < primeIdealMertensProductUpTo K N := by
  rw [primeIdealMertensProductUpTo]
  apply Finset.prod_pos
  intro 𝔭 h𝔭
  rw [sub_pos]
  have hp := (mem_primeIdealsUpTo K).mp h𝔭
  have hne₁ : Ideal.absNorm 𝔭 ≠ 1 :=
    fun h ↦ hp.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hne₀ : Ideal.absNorm 𝔭 ≠ 0 :=
    fun h ↦ hp.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
  have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Nat.pos_of_ne_zero hne₀
  apply (inv_lt_one₀ hpos).mpr
  exact_mod_cast (show 1 < Ideal.absNorm 𝔭 by omega)

private theorem inverse_primeIdealMertensProductUpTo (N : ℕ) :
    (primeIdealMertensProductUpTo K N)⁻¹ =
      ∏ 𝔭 ∈ primeIdealsUpTo K N, (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)⁻¹ := by
  rw [primeIdealMertensProductUpTo, Finset.prod_inv_distrib]

/-- Concrete eventual Mertens bound with inclusive norm cutoff. -/
theorem eventually_primeIdealMertensProductUpTo_le :
    ∀ᶠ N : ℕ in atTop,
      primeIdealMertensProductUpTo K N ≤
        (4 / NumberField.dedekindZeta_residue K) / Real.log (N : ℝ) := by
  let κ : ℝ := NumberField.dedekindZeta_residue K
  have hκ : 0 < κ := NumberField.dedekindZeta_residue_pos K
  filter_upwards [eventually_log_le_idealHarmonicMass K, eventually_ge_atTop 2]
    with N hmass hN
  change primeIdealMertensProductUpTo K N ≤ (4 / κ) / Real.log (N : ℝ)
  change (κ / 4) * Real.log (N : ℝ) ≤ idealHarmonicMass K N at hmass
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hc : 0 < κ / 4 := div_pos hκ (by norm_num)
  have hclog : 0 < (κ / 4) * Real.log (N : ℝ) := mul_pos hc hlog
  have hmasspos : 0 < idealHarmonicMass K N := hclog.trans_le hmass
  have hprodpos := primeIdealMertensProductUpTo_pos K N
  have hEuler := idealHarmonicMass_le_inverseEulerProduct K N
  rw [← inverse_primeIdealMertensProductUpTo] at hEuler
  have hprod_mass : primeIdealMertensProductUpTo K N ≤ (idealHarmonicMass K N)⁻¹ := by
    have := (inv_le_inv₀ (inv_pos.mpr hprodpos) hmasspos).mpr hEuler
    rwa [inv_inv] at this
  have hmass_clog : (idealHarmonicMass K N)⁻¹ ≤
      ((κ / 4) * Real.log (N : ℝ))⁻¹ :=
    (inv_le_inv₀ hmasspos hclog).mpr hmass
  calc
    primeIdealMertensProductUpTo K N ≤
        (idealHarmonicMass K N)⁻¹ := hprod_mass
    _ ≤ ((κ / 4) * Real.log (N : ℝ))⁻¹ := hmass_clog
    _ = (4 / κ) / Real.log (N : ℝ) := by
      field_simp

/-- The finite set of prime ideals with strict norm cutoff. -/
noncomputable def primeIdealsBelow (z : ℕ) :
    Finset (Ideal (NumberField.RingOfIntegers K)) :=
  primeIdealsUpTo K (z - 1)

@[simp] theorem mem_primeIdealsBelow {z : ℕ}
    {𝔭 : Ideal (NumberField.RingOfIntegers K)} :
    𝔭 ∈ primeIdealsBelow K z ↔
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 < z := by
  rw [primeIdealsBelow, mem_primeIdealsUpTo]
  constructor
  · rintro ⟨hp, h₀, hle⟩
    have hnpos : 0 < Ideal.absNorm 𝔭 :=
      Nat.pos_of_ne_zero (fun h ↦ h₀ (Ideal.absNorm_eq_zero_iff.mp h))
    exact ⟨hp, h₀, by omega⟩
  · rintro ⟨hp, h₀, hlt⟩
    exact ⟨hp, h₀, by omega⟩

/-- The direct all-prime-ideal Euler product with strict norm cutoff. -/
def primeIdealMertensProduct (z : ℕ) : ℝ :=
  ∏ 𝔭 ∈ primeIdealsBelow K z, (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)

theorem primeIdealMertensProduct_eq_upTo (z : ℕ) :
    primeIdealMertensProduct K z = primeIdealMertensProductUpTo K (z - 1) := rfl

private lemma eventually_two_log_sub_one_ge_log :
    ∀ᶠ z : ℕ in atTop,
      Real.log (z : ℝ) ≤ 2 * Real.log ((z - 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 3] with z hz
  have hz1 : 2 ≤ z - 1 := by omega
  have hzle : z ≤ 2 * (z - 1) := by omega
  have hlogmono : Real.log (z : ℝ) ≤ Real.log ((2 * (z - 1) : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show (0 : ℝ) < (z : ℕ)
      exact_mod_cast (show 0 < z by omega)
    · show (0 : ℝ) < (2 * (z - 1) : ℕ)
      exact_mod_cast (show 0 < 2 * (z - 1) by omega)
    · exact_mod_cast hzle
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log ((z - 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · show (0 : ℝ) < (z - 1 : ℕ)
      exact_mod_cast (show 0 < z - 1 by omega)
    · exact_mod_cast hz1
  rw [show ((2 * (z - 1) : ℕ) : ℝ) = 2 * ((z - 1 : ℕ) : ℝ) by norm_num,
    Real.log_mul (by norm_num) (by positivity)] at hlogmono
  linarith

/-- Concrete eventual Mertens bound with strict norm cutoff. -/
theorem eventually_primeIdealMertensProduct_le :
    ∀ᶠ z : ℕ in atTop,
      primeIdealMertensProduct K z ≤
        (8 / NumberField.dedekindZeta_residue K) / Real.log (z : ℝ) := by
  have hsub : Tendsto (fun z : ℕ ↦ z - 1) atTop atTop := by
    refine tendsto_atTop.mpr (fun b ↦ ?_)
    filter_upwards [eventually_ge_atTop (b + 1)] with z hz
    omega
  have hup := hsub.eventually (eventually_primeIdealMertensProductUpTo_le K)
  filter_upwards [hup, eventually_two_log_sub_one_ge_log,
    eventually_ge_atTop 3] with z hprod hlogs hz
  rw [primeIdealMertensProduct_eq_upTo]
  have hκ : 0 < NumberField.dedekindZeta_residue K :=
    NumberField.dedekindZeta_residue_pos K
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogsub : 0 < Real.log ((z - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z - 1 by omega))
  calc
    primeIdealMertensProductUpTo K (z - 1) ≤
        (4 / NumberField.dedekindZeta_residue K) /
          Real.log ((z - 1 : ℕ) : ℝ) := hprod
    _ ≤ (8 / NumberField.dedekindZeta_residue K) / Real.log (z : ℝ) := by
      apply (div_le_div_iff₀ hlogsub hlogz).mpr
      have hA : 0 ≤ 4 / NumberField.dedekindZeta_residue K :=
        (div_pos (by norm_num) hκ).le
      have hm := mul_le_mul_of_nonneg_left hlogs hA
      calc
        4 / NumberField.dedekindZeta_residue K * Real.log (z : ℝ) ≤
            4 / NumberField.dedekindZeta_residue K *
              (2 * Real.log ((z - 1 : ℕ) : ℝ)) := hm
        _ = 8 / NumberField.dedekindZeta_residue K *
              Real.log ((z - 1 : ℕ) : ℝ) := by ring

/-- Prime ideals in the half-open norm interval `[y, z)`. -/
noncomputable def primeIdealsInNormRange (y z : ℕ) :
    Finset (Ideal (NumberField.RingOfIntegers K)) :=
  (primeIdealsBelow K z).filter (fun 𝔭 ↦ y ≤ Ideal.absNorm 𝔭)

@[simp] theorem mem_primeIdealsInNormRange {y z : ℕ}
    {𝔭 : Ideal (NumberField.RingOfIntegers K)} :
    𝔭 ∈ primeIdealsInNormRange K y z ↔
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ y ≤ Ideal.absNorm 𝔭 ∧ Ideal.absNorm 𝔭 < z := by
  classical
  simp only [primeIdealsInNormRange, Finset.mem_filter, mem_primeIdealsBelow]
  tauto

/-- The direct Euler product over prime ideals in `[y, z)`. -/
def primeIdealMertensProductInNormRange (y z : ℕ) : ℝ :=
  ∏ 𝔭 ∈ primeIdealsInNormRange K y z, (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)

private lemma primeIdealsBelow_mono {y z : ℕ} (hyz : y ≤ z) :
    primeIdealsBelow K y ⊆ primeIdealsBelow K z := by
  intro 𝔭 h𝔭
  rw [mem_primeIdealsBelow] at h𝔭 ⊢
  exact ⟨h𝔭.1, h𝔭.2.1, h𝔭.2.2.trans_le hyz⟩

private lemma primeIdealMertensProductInNormRange_eq_div {y z : ℕ} (hyz : y ≤ z) :
    primeIdealMertensProductInNormRange K y z =
      primeIdealMertensProduct K z / primeIdealMertensProduct K y := by
  have hlow : primeIdealMertensProduct K y ≠ 0 := by
    rw [primeIdealMertensProduct_eq_upTo]
    exact (primeIdealMertensProductUpTo_pos K (y - 1)).ne'
  have hset : primeIdealsInNormRange K y z =
      primeIdealsBelow K z \ primeIdealsBelow K y := by
    ext 𝔭
    simp only [mem_primeIdealsInNormRange, Finset.mem_sdiff, mem_primeIdealsBelow]
    constructor
    · rintro ⟨hp, h₀, hlo, hhi⟩
      exact ⟨⟨hp, h₀, hhi⟩, fun hbad ↦ by omega⟩
    · rintro ⟨⟨hp, h₀, hhi⟩, hnotlow⟩
      refine ⟨hp, h₀, ?_, hhi⟩
      by_contra h
      exact hnotlow ⟨hp, h₀, by omega⟩
  rw [primeIdealMertensProductInNormRange, primeIdealMertensProduct,
    primeIdealMertensProduct, hset]
  apply (eq_div_iff hlow).mpr
  exact Finset.prod_sdiff (f := fun 𝔭 ↦
    (1 - (Ideal.absNorm 𝔭 : ℝ)⁻¹)) (primeIdealsBelow_mono K hyz)

theorem primeIdealMertensProduct_pos (z : ℕ) :
    0 < primeIdealMertensProduct K z := by
  rw [primeIdealMertensProduct_eq_upTo]
  exact primeIdealMertensProductUpTo_pos K (z - 1)

/-- Concrete form used by a sieve that discards the fixed prime ideals below `y`. -/
theorem eventually_primeIdealMertensProductInNormRange_le (y : ℕ) :
    ∀ᶠ z : ℕ in atTop,
      primeIdealMertensProductInNormRange K y z ≤
        ((8 / NumberField.dedekindZeta_residue K) /
          primeIdealMertensProduct K y) / Real.log (z : ℝ) := by
  filter_upwards [eventually_primeIdealMertensProduct_le K, eventually_ge_atTop y]
    with z hz hyz
  rw [primeIdealMertensProductInNormRange_eq_div K hyz]
  have hypos := primeIdealMertensProduct_pos K y
  calc
    primeIdealMertensProduct K z / primeIdealMertensProduct K y ≤
        ((8 / NumberField.dedekindZeta_residue K) / Real.log (z : ℝ)) /
          primeIdealMertensProduct K y :=
      div_le_div_of_nonneg_right hz hypos.le
    _ = ((8 / NumberField.dedekindZeta_residue K) /
          primeIdealMertensProduct K y) / Real.log (z : ℝ) := by ring

/-- Existential-constant packaging of the interval Mertens estimate. -/
theorem exists_primeIdealMertensProductInNormRange_bound (y : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z : ℕ in atTop,
      primeIdealMertensProductInNormRange K y z ≤ C / Real.log (z : ℝ) := by
  refine ⟨(8 / NumberField.dedekindZeta_residue K) /
      primeIdealMertensProduct K y, ?_,
    eventually_primeIdealMertensProductInNormRange_le K y⟩
  exact div_pos (div_pos (by norm_num) (NumberField.dedekindZeta_residue_pos K))
    (primeIdealMertensProduct_pos K y)

end Erdos980.ElliottTail.PrimeIdealMertens
