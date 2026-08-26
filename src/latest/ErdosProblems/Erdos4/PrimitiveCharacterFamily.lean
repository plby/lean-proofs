import ErdosProblems.Erdos4.WeightedCharacterSums
import ErdosProblems.Erdos4.GramBound
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Primitive character families without imprimitive duplicates

The index records the conductor and the primitive character itself. Both
equal-conductor and different-conductor pairs are handled explicitly.
-/

open scoped BigOperators

namespace Erdos4.PrimitiveCharacterFamily

open CharacterCorrelations WeightedCharacterSums SelbergCoefficients SieveMajorant

abbrev Entry := Σ d : ℕ, DirichletCharacter ℂ d

def Valid (c : Entry) : Prop := 0 < c.1 ∧ c.2.IsPrimitive

noncomputable def value (c : Entry) (n : ℕ) : ℂ := c.2 (n : ZMod c.1)

theorem value_norm_le_one (c : Entry) (n : ℕ) : ‖value c n‖ ≤ 1 :=
  c.2.norm_le_one _

abbrev BoundedEntries (Q : ℕ) := Σ d : (Finset.Icc 1 Q : Finset ℕ), DirichletCharacter ℂ d.1

theorem card_boundedEntries_le (Q : ℕ) : Fintype.card (BoundedEntries Q) ≤ Q ^ 2 := by
  classical
  rw [Fintype.card_sigma]
  have hcard : ∀ d : (Finset.Icc 1 Q : Finset ℕ),
      Fintype.card (DirichletCharacter ℂ d.1) ≤ Q := by
    intro d
    have hd := Finset.mem_Icc.mp d.2
    let : NeZero d.1 := ⟨(Nat.ne_of_gt hd.1)⟩
    have heq : Fintype.card (DirichletCharacter ℂ d.1) = Nat.totient d.1 := by
      simpa only [Nat.card_eq_fintype_card] using
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d.1
    exact heq.le.trans ((Nat.totient_le d.1).trans hd.2)
  calc
    (∑ d : (Finset.Icc 1 Q : Finset ℕ), Fintype.card (DirichletCharacter ℂ d.1)) ≤
        ∑ _d : (Finset.Icc 1 Q : Finset ℕ), Q := Finset.sum_le_sum (fun d _hd => hcard d)
    _ = Q ^ 2 := by simp [pow_two]

/-- A family indexed once by primitive conductor contains at most `Q²`
characters of conductor at most `Q`. -/
theorem card_family_le_square {I : Type*} [Fintype I]
    (family : I → Entry) (hvalid : ∀ i, Valid (family i)) (hinjective : Function.Injective family)
    {Q : ℕ} (hQ : ∀ i, (family i).1 ≤ Q) : Fintype.card I ≤ Q ^ 2 := by
  classical
  let encode : I → BoundedEntries Q := fun i =>
    ⟨⟨(family i).1, Finset.mem_Icc.mpr ⟨(hvalid i).1, hQ i⟩⟩, (family i).2⟩
  let forget : BoundedEntries Q → Entry := fun c => ⟨c.1.1, c.2⟩
  have hinj : Function.Injective encode := by
    intro i j hij
    apply hinjective
    exact congrArg forget hij
  exact (Fintype.card_le_of_injective encode hinj).trans (card_boundedEntries_le Q)

theorem distinct_sum_multiples_le (c b : Entry) (hc : Valid c) (hb : Valid b)
    (hne : c ≠ b) (r N : ℕ) (hr : 0 < r) :
    ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then star (value c n) * value b n else 0‖ ≤
      (c.1 : ℝ) * b.1 := by
  obtain ⟨d, chi⟩ := c
  obtain ⟨e, psi⟩ := b
  obtain ⟨hd, hchi⟩ := hc
  obtain ⟨he, hpsi⟩ := hb
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero e := ⟨he.ne'⟩
  change ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then
    star (chi (n : ZMod d)) * psi (n : ZMod e) else 0‖ ≤ (d : ℝ) * e
  by_cases hde : d = e
  · subst e
    have hchars : chi ≠ psi := by
      intro hh
      apply hne
      cases hh
      rfl
    have hcorr : ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then
        star (chi (n : ZMod d)) * psi (n : ZMod d) else 0‖ ≤ d := by
      rw [sum_multiples_Icc _ r N hr, sum_Icc_one_eq_range]
      simpa only [Nat.add_comm] using correlation_multiples_le chi psi r 1 (N / r) d
        (distinct_correlation_le chi psi hchars 1 (N / r))
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact hcorr.trans (by nlinarith)
  · have hcorr := primitive_sum_multiples_le chi psi hchi hpsi hde r N hr
    have hlcm : Nat.lcm d e ≤ d * e :=
      Nat.le_of_dvd (Nat.mul_pos hd he) (Nat.lcm_dvd_mul d e)
    exact hcorr.trans (by exact_mod_cast hlcm)

theorem distinct_sum_multiples_le_square (c b : Entry) (hc : Valid c) (hb : Valid b)
    (hne : c ≠ b) {Q : ℕ} (hcQ : c.1 ≤ Q) (hbQ : b.1 ≤ Q)
    (r N : ℕ) (hr : 0 < r) :
    ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then star (value c n) * value b n else 0‖ ≤
      (Q : ℝ) ^ 2 := by
  have hmul : (c.1 : ℝ) * b.1 ≤ (Q : ℝ) * Q := by
    exact_mod_cast Nat.mul_le_mul hcQ hbQ
  exact (distinct_sum_multiples_le c b hc hb hne r N hr).trans (by simpa only [pow_two] using hmul)

/-- The off-diagonal correlation loss for the concrete Selberg weights. -/
theorem weighted_distinct_correlation_le (c b : Entry) (hc : Valid c) (hb : Valid b)
    (hne : c ≠ b) {D Q : ℕ} (hD : 1 ≤ D) (hcQ : c.1 ≤ Q) (hbQ : b.1 ≤ Q) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
      (weight D (coefficient D) n : ℂ) * (star (value c n) * value b n)‖ ≤
        (Q : ℝ) ^ 2 * (D : ℝ) ^ 4 := by
  have hw := norm_weighted_sum_le D N (coefficient D)
    (fun n => star (value c n) * value b n) ((Q : ℝ) ^ 2)
    (fun r hr => distinct_sum_multiples_le_square c b hc hb hne hcQ hbQ r N hr)
  have habs := sum_abs_coefficient_le hD
  have hnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 D, |coefficient D d| :=
    Finset.sum_nonneg (fun d _hd => abs_nonneg _)
  have hsquare : (∑ d ∈ Finset.Icc 1 D, |coefficient D d|) ^ 2 ≤ (D : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((D : ℝ) ^ 2 - ∑ d ∈ Finset.Icc 1 D, |coefficient D d|)]
  exact hw.trans (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

theorem weighted_diagonal_le (c : Entry) {D : ℕ} (hD : 1 ≤ D) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
      (weight D (coefficient D) n : ℂ) * (star (value c n) * value c n)‖ ≤
        (N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 := by
  have hnorm : ‖∑ n ∈ Finset.Icc 1 N,
      (weight D (coefficient D) n : ℂ) * (star (value c n) * value c n)‖ ≤
        ∑ n ∈ Finset.Icc 1 N, weight D (coefficient D) n := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n _hn
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weight_nonneg D (coefficient D) n)]
    have hvalue := value_norm_le_one c n
    have hvalue0 := norm_nonneg (value c n)
    have hsquare : ‖value c n‖ * ‖value c n‖ ≤ 1 := by nlinarith
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsquare (weight_nonneg D (coefficient D) n)
  exact hnorm.trans (SelbergOptimization.sum_weight_coefficient_le hD N)

/-- A finite prime-supported mean-square bound, with all arithmetic inputs
proved above. The family is indexed once by its primitive conductor. -/
theorem prime_mean_square_le {I : Type*} [Fintype I]
    (family : I → Entry) (hvalid : ∀ i, Valid (family i)) (hinjective : Function.Injective family)
    {D Q : ℕ} (hD : 1 ≤ D) (hQ : ∀ i, (family i).1 ≤ Q)
    (N : ℕ) (primes : Finset ℕ)
    (hprimes : ∀ p ∈ primes, p.Prime ∧ D < p ∧ p ≤ N) (a : I → ℂ) :
    (∑ p ∈ primes, ‖∑ i, a i * value (family i) p‖ ^ 2) ≤
      ((N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 +
        (Fintype.card I : ℝ) * ((Q : ℝ) ^ 2 * (D : ℝ) ^ 4)) * ∑ i, ‖a i‖ ^ 2 := by
  classical
  let w : (Finset.Icc 1 N : Finset ℕ) → ℝ := fun n => weight D (coefficient D) n
  let f : I → (Finset.Icc 1 N : Finset ℕ) → ℂ := fun i n => value (family i) n
  let B : ℝ := (N : ℝ) / harmonicMass D + (D : ℝ) ^ 4
  let epsilon : ℝ := (Q : ℝ) ^ 2 * (D : ℝ) ^ 4
  have hepsilon : 0 ≤ epsilon := mul_nonneg (sq_nonneg _) (by positivity)
  have hdiag : ∀ i, ‖GramBound.weightedGram w f i i‖ ≤ B := by
    intro i
    simp only [GramBound.weightedGram, w, f, B, mul_assoc]
    rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      (weight D (coefficient D) n : ℂ) * (star (value (family i) n) * value (family i) n))]
    exact weighted_diagonal_le (family i) hD N
  have hoff : ∀ i j, i ≠ j → ‖GramBound.weightedGram w f i j‖ ≤ epsilon := by
    intro i j hij
    have hne : family i ≠ family j := fun h => hij (hinjective h)
    simp only [GramBound.weightedGram, w, f, epsilon, mul_assoc]
    rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      (weight D (coefficient D) n : ℂ) * (star (value (family i) n) * value (family j) n))]
    exact weighted_distinct_correlation_le (family i) (family j) (hvalid i) (hvalid j)
      hne hD (hQ i) (hQ j) N
  have hfull := GramBound.weighted_mean_square_le w f B epsilon hepsilon hdiag hoff a
  have hfull' : (∑ n ∈ Finset.Icc 1 N,
      weight D (coefficient D) n * ‖∑ i, a i * value (family i) n‖ ^ 2) ≤
      ((N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 +
        (Fintype.card I : ℝ) * ((Q : ℝ) ^ 2 * (D : ℝ) ^ 4)) * ∑ i, ‖a i‖ ^ 2 := by
    simpa only [w, f, B, epsilon,
      Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
        weight D (coefficient D) n * ‖∑ i, a i * value (family i) n‖ ^ 2)] using hfull
  have hsubset : primes ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpprime, _hpD, hpN⟩ := hprimes p hp
    exact Finset.mem_Icc.mpr ⟨hpprime.one_lt.le, hpN⟩
  calc
    (∑ p ∈ primes, ‖∑ i, a i * value (family i) p‖ ^ 2) =
        ∑ p ∈ primes, weight D (coefficient D) p * ‖∑ i, a i * value (family i) p‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [SelbergCoefficients.weight_prime hD (hprimes p hp).1 (hprimes p hp).2.1, one_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        weight D (coefficient D) n * ‖∑ i, a i * value (family i) n‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _hn _hnot => mul_nonneg (weight_nonneg D (coefficient D) n) (sq_nonneg _))
    _ ≤ _ := hfull'

/-- The dual prime-supported estimate, with the same constant and without
conjugating the primitive character family. -/
theorem prime_mean_square_dual_le {I : Type*} [Fintype I]
    (family : I → Entry) (hvalid : ∀ i, Valid (family i)) (hinjective : Function.Injective family)
    {D Q : ℕ} (hD : 1 ≤ D) (hQ : ∀ i, (family i).1 ≤ Q)
    (N : ℕ) (primes : Finset ℕ)
    (hprimes : ∀ p ∈ primes, p.Prime ∧ D < p ∧ p ≤ N) (a : primes → ℂ) :
    (∑ i, ‖∑ p : primes, a p * value (family i) p‖ ^ 2) ≤
      ((N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 +
        (Fintype.card I : ℝ) * ((Q : ℝ) ^ 2 * (D : ℝ) ^ 4)) * ∑ p : primes, ‖a p‖ ^ 2 := by
  classical
  let L : ℝ := (N : ℝ) / harmonicMass D + (D : ℝ) ^ 4 +
    (Fintype.card I : ℝ) * ((Q : ℝ) ^ 2 * (D : ℝ) ^ 4)
  have hH := harmonicMass_pos hD
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound : ∀ b : I → ℂ,
      (∑ p : primes, ‖∑ i, b i * value (family i) p‖ ^ 2) ≤ L * ∑ i, ‖b i‖ ^ 2 := by
    intro b
    rw [Finset.sum_coe_sort primes (fun p : ℕ => ‖∑ i, b i * value (family i) p‖ ^ 2)]
    exact prime_mean_square_le family hvalid hinjective hD hQ N primes hprimes b
  have hdual := GramBound.transform_duality
    (fun i (p : primes) => value (family i) p) L hL hbound (fun p => star (a p))
  have hinner : ∀ i,
      (∑ p : primes, star (a p) * star (value (family i) p)) =
        star (∑ p : primes, a p * value (family i) p) := by
    intro i
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [star_mul]
    ring
  simpa only [hinner, norm_star, L] using hdual

end Erdos4.PrimitiveCharacterFamily
