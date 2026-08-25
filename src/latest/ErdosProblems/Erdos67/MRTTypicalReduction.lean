import ErdosProblems.Erdos67.MRTDensity
import ErdosProblems.Erdos67.MRTMinorArc

/-!
# Removing the atypical integers from an MRT short sum

This file proves the elementary exceptional-set reduction used before the Ramaré expansion.
Every omitted summand is charged to an atypical integer.  After averaging over starting points,
each atypical integer is charged at most once for each of the `H` possible shifts.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- The modulated short sum restricted to integers having a prime factor in every selected
block. -/
def typicalModulatedShortSum (blocks : Finset (ℕ × ℕ)) (X : ℕ)
    (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H,
    if n + j ∈ typicalFactorizationSet blocks X then
      f (n + j) * additivePhase α j
    else 0

/-- The typical integers lying in the translated short interval `(n,n+H]`. -/
def typicalShortSupport (blocks : Finset (ℕ × ℕ)) (X n H : ℕ) : Finset ℕ :=
  (typicalFactorizationSet blocks X).filter (fun m ↦ m ∈ Finset.Ioc n (n + H))

@[simp]
theorem mem_typicalShortSupport
    {blocks : Finset (ℕ × ℕ)} {X n H m : ℕ} :
    m ∈ typicalShortSupport blocks X n H ↔
      m ∈ typicalFactorizationSet blocks X ∧ n < m ∧ m ≤ n + H := by
  simp [typicalShortSupport]

/-- Reindex the increment form of the typical short sum by the integer `m=n+j`. -/
theorem typicalModulatedShortSum_eq_support_sum
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    typicalModulatedShortSum blocks X f n H α =
      ∑ m ∈ typicalShortSupport blocks X n H,
        additivePhase α (m - n) * f m := by
  classical
  rw [typicalModulatedShortSum, ← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ ↦ n + j)
  · intro j hj
    rw [Finset.mem_filter] at hj
    rw [mem_typicalShortSupport]
    refine ⟨hj.2, ?_, ?_⟩
    · have := (Finset.mem_Icc.mp hj.1).1
      omega
    · have := (Finset.mem_Icc.mp hj.1).2
      omega
  · intro j₁ hj₁ j₂ hj₂ heq
    omega
  · intro m hm
    rw [mem_typicalShortSupport] at hm
    refine ⟨m - n, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        omega
      · simpa [Nat.add_sub_of_le hm.2.1.le] using hm.1
    · omega
  · intro j hj
    rw [Finset.mem_filter] at hj
    have := (Finset.mem_Icc.mp hj.1).1
    rw [show n + j - n = j by omega, mul_comm]

/-- Exact bilinear Ramaré expansion of the typical part of a translated modulated short sum. -/
theorem typicalModulatedShortSum_eq_ramare_bilinear
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ)
    (hf : IsCompletelyMultiplicativeOnPositive f) :
    typicalModulatedShortSum blocks X f n H α =
      ∑ p ∈ primesInBlock I,
        ∑ m ∈ typicalShortSupport blocks X n H,
          if hpm : p ∣ m then
            additivePhase α (m - n) * (f p * f (m / p)) /
              (ramareDenominator (primesInBlock I) p (m / p) : ℂ)
          else 0 := by
  rw [typicalModulatedShortSum_eq_support_sum]
  apply completelyMultiplicative_ramare_bilinear
  · intro p hp
    exact (mem_primesInBlock.mp hp).1
  · intro m hm
    have htyp := (mem_typicalShortSupport.mp hm).1
    exact (mem_typicalFactorizationSet.mp htyp).2.2 I hI
  · intro m hm
    have htyp := (mem_typicalShortSupport.mp hm).1
    exact (mem_typicalFactorizationSet.mp htyp).1
  · exact hf

/-- Cofactors obtained by dividing the elements of `S` which are divisible by `p`. -/
def divisorCofactorImage (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (S.filter (p ∣ ·)).image (fun m ↦ m / p)

@[simp]
theorem mem_divisorCofactorImage {S : Finset ℕ} {p k : ℕ} :
    k ∈ divisorCofactorImage S p ↔ ∃ m ∈ S, p ∣ m ∧ m / p = k := by
  classical
  rw [divisorCofactorImage, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, hmk⟩
    exact ⟨m, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, hmk⟩
  · rintro ⟨m, hmS, hdvd, hmk⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨hmS, hdvd⟩, hmk⟩

/-- Reindex a divisibility-restricted sum by its cofactor. -/
theorem sum_dvd_eq_sum_divisorCofactorImage
    {E : Type*} [AddCommMonoid E] (S : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (F : ℕ → ℕ → E) :
    (∑ m ∈ S, if p ∣ m then F m (m / p) else 0) =
      ∑ k ∈ divisorCofactorImage S p, F (p * k) k := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _ ↦ m / p)
  · intro m hm
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    have hdvd₁ := (Finset.mem_filter.mp hm₁).2
    have hdvd₂ := (Finset.mem_filter.mp hm₂).2
    calc
      m₁ = p * (m₁ / p) := (Nat.mul_div_cancel' hdvd₁).symm
      _ = p * (m₂ / p) := by rw [heq]
      _ = m₂ := Nat.mul_div_cancel' hdvd₂
  · intro k hk
    rw [mem_divisorCofactorImage] at hk
    obtain ⟨m, hmS, hdvd, hmk⟩ := hk
    refine ⟨m, Finset.mem_filter.mpr ⟨hmS, hdvd⟩, hmk⟩
  · intro m hm
    have hdvd := (Finset.mem_filter.mp hm).2
    rw [Nat.mul_div_cancel' hdvd]

/-- Cofactor-indexed form of the typical Ramaré expansion.  This is the exact algebraic form
to which the major/minor arc estimates are applied. -/
theorem typicalModulatedShortSum_eq_ramare_cofactors
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ)
    (hf : IsCompletelyMultiplicativeOnPositive f) :
    typicalModulatedShortSum blocks X f n H α =
      ∑ p ∈ primesInBlock I,
        ∑ k ∈ divisorCofactorImage (typicalShortSupport blocks X n H) p,
          additivePhase α (p * k - n) * (f p * f k) /
            (ramareDenominator (primesInBlock I) p k : ℂ) := by
  rw [typicalModulatedShortSum_eq_ramare_bilinear hI X f n H α hf]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : 0 < p := (mem_primesInBlock.mp hp).1.pos
  exact sum_dvd_eq_sum_divisorCofactorImage
    (typicalShortSupport blocks X n H) hp0
    (fun m k ↦ additivePhase α (m - n) * (f p * f k) /
      (ramareDenominator (primesInBlock I) p k : ℂ))

/-- Union of all cofactor supports arising from the selected prime block. -/
def ramareCofactorUnion (P S : Finset ℕ) : Finset ℕ :=
  P.biUnion (fun p ↦ divisorCofactorImage S p)

@[simp]
theorem mem_ramareCofactorUnion {P S : Finset ℕ} {k : ℕ} :
    k ∈ ramareCofactorUnion P S ↔
      ∃ p ∈ P, k ∈ divisorCofactorImage S p := by
  simp [ramareCofactorUnion]

/-- Extend every prime-dependent cofactor support to their common union and commute the sums. -/
theorem sum_divisorCofactorImage_commute
    {E : Type*} [AddCommMonoid E] (P S : Finset ℕ) (F : ℕ → ℕ → E) :
    (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p, F p k) =
      ∑ k ∈ ramareCofactorUnion P S,
        ∑ p ∈ P, if k ∈ divisorCofactorImage S p then F p k else 0 := by
  classical
  calc
    (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p, F p k) =
        ∑ p ∈ P, ∑ k ∈ ramareCofactorUnion P S,
          if k ∈ divisorCofactorImage S p then F p k else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        rw [Finset.mem_filter]
        constructor
        · intro hk
          exact ⟨mem_ramareCofactorUnion.mpr ⟨p, hp, hk⟩, hk⟩
        · exact fun hk ↦ hk.2
      · intro k hk
        rfl
    _ = ∑ k ∈ ramareCofactorUnion P S,
        ∑ p ∈ P, if k ∈ divisorCofactorImage S p then F p k else 0 := by
      rw [Finset.sum_comm]

/-- Cofactor-outer form of the typical Ramaré expansion. -/
theorem typicalModulatedShortSum_eq_ramare_cofactor_outer
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ)
    (hf : IsCompletelyMultiplicativeOnPositive f) :
    typicalModulatedShortSum blocks X f n H α =
      ∑ k ∈ ramareCofactorUnion (primesInBlock I)
          (typicalShortSupport blocks X n H),
        ∑ p ∈ primesInBlock I,
          if k ∈ divisorCofactorImage (typicalShortSupport blocks X n H) p then
            additivePhase α (p * k - n) * (f p * f k) /
              (ramareDenominator (primesInBlock I) p k : ℂ)
          else 0 := by
  rw [typicalModulatedShortSum_eq_ramare_cofactors hI X f n H α hf]
  exact sum_divisorCofactorImage_commute
    (primesInBlock I) (typicalShortSupport blocks X n H)
    (fun p k ↦ additivePhase α (p * k - n) * (f p * f k) /
      (ramareDenominator (primesInBlock I) p k : ℂ))

theorem additivePhase_natSub
    (α : ℝ) {n m : ℕ} (hnm : n ≤ m) :
    additivePhase α (m - n) =
      conj (additivePhase α n) * additivePhase α m := by
  have hadd := additivePhase_add α n (m - n)
  rw [Nat.add_sub_of_le hnm] at hadd
  calc
    additivePhase α (m - n) =
        1 * additivePhase α (m - n) := by rw [one_mul]
    _ = (conj (additivePhase α n) * additivePhase α n) *
          additivePhase α (m - n) := by
      rw [Complex.conj_mul', norm_additivePhase]
      norm_num
    _ = conj (additivePhase α n) * additivePhase α m := by
      rw [hadd]
      ring

/-- Prime coefficient in the cofactor-outer Ramaré polynomial. -/
def ramarePrimeCoefficient (P S : Finset ℕ) (f : ℕ → ℂ) (k p : ℕ) : ℂ :=
  if k ∈ divisorCofactorImage S p then
    f p / (ramareDenominator P p k : ℂ)
  else 0

/-- The Ramaré prime coefficient is bounded by one whenever the original prime coefficients
are bounded by one. -/
theorem norm_ramarePrimeCoefficient_le_one
    {P S : Finset ℕ} {f : ℕ → ℂ} {k p : ℕ}
    (hP : ∀ q ∈ P, q.Prime) (hp : p ∈ P)
    (hf : ∀ q ∈ P, ‖f q‖ ≤ 1) :
    ‖ramarePrimeCoefficient P S f k p‖ ≤ 1 := by
  classical
  unfold ramarePrimeCoefficient
  split_ifs with hk
  · have hdeneq := ramareDenominator_eq_primeDivisorCount_mul hP hp (m := k)
    have hcount : 0 < primeDivisorCount P (p * k) := by
      apply primeDivisorCount_pos
      exact ⟨p, hp, dvd_mul_right p k⟩
    have hden : (1 : ℝ) ≤ ramareDenominator P p k := by
      exact_mod_cast (show 1 ≤ ramareDenominator P p k by omega)
    rw [norm_div, Complex.norm_natCast]
    have hdenpos : (0 : ℝ) < ramareDenominator P p k :=
      lt_of_lt_of_le zero_lt_one hden
    exact (div_le_one hdenpos).2 ((hf p hp).trans hden)
  · simp

/-- Prime polynomial attached to one cofactor. -/
def ramarePrimePolynomial (P S : Finset ℕ) (f : ℕ → ℂ)
    (k : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ P, ramarePrimeCoefficient P S f k p * additivePhase α (k * p)

/-- Exact prime-polynomial form of the typical Ramaré expansion. -/
theorem typicalModulatedShortSum_eq_ramare_primePolynomials
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ)
    (hf : IsCompletelyMultiplicativeOnPositive f) :
    typicalModulatedShortSum blocks X f n H α =
      ∑ k ∈ ramareCofactorUnion (primesInBlock I)
          (typicalShortSupport blocks X n H),
        conj (additivePhase α n) * f k *
          ramarePrimePolynomial (primesInBlock I)
            (typicalShortSupport blocks X n H) f k α := by
  rw [typicalModulatedShortSum_eq_ramare_cofactor_outer hI X f n H α hf]
  apply Finset.sum_congr rfl
  intro k hkUnion
  unfold ramarePrimePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk :
      k ∈ divisorCofactorImage (typicalShortSupport blocks X n H) p
  · obtain ⟨m, hm, hpm, hmk⟩ := mem_divisorCofactorImage.mp hk
    have hpk : p * k = m := by
      rw [← hmk, Nat.mul_div_cancel' hpm]
    have hnm : n ≤ p * k := by
      rw [hpk]
      exact (mem_typicalShortSupport.mp hm).2.1.le
    rw [if_pos hk, ramarePrimeCoefficient, if_pos hk,
      additivePhase_natSub α hnm]
    rw [mul_comm k p]
    ring
  · simp [hk, ramarePrimeCoefficient]

/-- The exact prime-polynomial expansion gives a pointwise `ℓ¹` bound over its cofactor
support.  Under the unit-circle hypothesis the outer phase and the cofactor value both have
norm one, so the only nontrivial factors are the prime polynomials themselves. -/
theorem norm_typicalModulatedShortSum_le_sum_norm_ramarePrimePolynomial
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ)
    (hf : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ m : ℕ, 0 < m → ‖f m‖ = 1) :
    ‖typicalModulatedShortSum blocks X f n H α‖ ≤
      ∑ k ∈ ramareCofactorUnion (primesInBlock I)
          (typicalShortSupport blocks X n H),
        ‖ramarePrimePolynomial (primesInBlock I)
          (typicalShortSupport blocks X n H) f k α‖ := by
  classical
  rw [typicalModulatedShortSum_eq_ramare_primePolynomials hI X f n H α hf]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨p, hp, hkSupport⟩ := mem_ramareCofactorUnion.mp hk
  obtain ⟨m, hm, hpm, hmk⟩ := mem_divisorCofactorImage.mp hkSupport
  have hp0 : 0 < p := (mem_primesInBlock.mp hp).1.pos
  have hm0 : 0 < m :=
    (mem_typicalFactorizationSet.mp (mem_typicalShortSupport.mp hm).1).1
  have hk0 : 0 < k := by
    rw [← hmk]
    exact Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp0
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_additivePhase,
    hunit k hk0, one_mul, one_mul]

theorem mem_atypicalFactorizationSet_iff_not_mem_typical_of_bounds
    {blocks : Finset (ℕ × ℕ)} {X m : ℕ} (hm : 1 ≤ m) (hmX : m ≤ X) :
    m ∈ atypicalFactorizationSet blocks X ↔
      m ∉ typicalFactorizationSet blocks X := by
  rw [mem_atypicalFactorizationSet, mem_typicalFactorizationSet]
  simp [hm, hmX]

/-- Pointwise cost of removing all atypical summands from one short interval. -/
theorem norm_modulatedShortSum_sub_typical_le
    {blocks : Finset (ℕ × ℕ)} {X : ℕ} {f : ℕ → ℂ} {n H : ℕ} {α : ℝ}
    (hrange : ∀ j ∈ Finset.Icc 1 H, n + j ≤ X)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ‖modulatedShortSum f n H α -
        typicalModulatedShortSum blocks X f n H α‖ ≤
      ∑ j ∈ Finset.Icc 1 H,
        if n + j ∈ atypicalFactorizationSet blocks X then (1 : ℝ) else 0 := by
  classical
  have hrewrite :
      modulatedShortSum f n H α - typicalModulatedShortSum blocks X f n H α =
        ∑ j ∈ Finset.Icc 1 H,
          if n + j ∈ atypicalFactorizationSet blocks X then
            f (n + j) * additivePhase α j
          else 0 := by
    rw [modulatedShortSum, typicalModulatedShortSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos : 0 < n + j := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hatyp :
        n + j ∈ atypicalFactorizationSet blocks X ↔
          n + j ∉ typicalFactorizationSet blocks X :=
      mem_atypicalFactorizationSet_iff_not_mem_typical_of_bounds
        (by omega) (hrange j hj)
    by_cases htyp : n + j ∈ typicalFactorizationSet blocks X
    · simp [htyp, hatyp]
    · simp [htyp, hatyp.mpr htyp]
  rw [hrewrite]
  calc
    ‖∑ j ∈ Finset.Icc 1 H,
        if n + j ∈ atypicalFactorizationSet blocks X then
          f (n + j) * additivePhase α j
        else 0‖ ≤
        ∑ j ∈ Finset.Icc 1 H,
          ‖if n + j ∈ atypicalFactorizationSet blocks X then
            f (n + j) * additivePhase α j
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 H,
        if n + j ∈ atypicalFactorizationSet blocks X then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hatyp
      · rw [norm_mul, norm_additivePhase, mul_one]
        apply hf
        have := (Finset.mem_Icc.mp hj).1
        omega
      · simp

/-- For a fixed shift, translation injects the exceptional starting points into the atypical
set itself. -/
theorem card_filter_add_mem_atypical_le
    (blocks : Finset (ℕ × ℕ)) (X Y j : ℕ) :
    ((Finset.Icc Y (2 * Y)).filter
        (fun n ↦ n + j ∈ atypicalFactorizationSet blocks X)).card ≤
      (atypicalFactorizationSet blocks X).card := by
  classical
  let S := (Finset.Icc Y (2 * Y)).filter
    (fun n ↦ n + j ∈ atypicalFactorizationSet blocks X)
  have himage : S.image (fun n ↦ n + j) ⊆ atypicalFactorizationSet blocks X := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    exact (Finset.mem_filter.mp hn).2
  calc
    ((Finset.Icc Y (2 * Y)).filter
        (fun n ↦ n + j ∈ atypicalFactorizationSet blocks X)).card = S.card := rfl
    _ = (S.image (fun n ↦ n + j)).card := by
      rw [Finset.card_image_of_injective _ (fun _ _ h ↦ Nat.add_right_cancel h)]
    _ ≤ (atypicalFactorizationSet blocks X).card := Finset.card_le_card himage

/-- Averaged exceptional-set loss: at most `H` times the number of atypical integers. -/
theorem sum_norm_modulatedShortSum_sub_typical_le
    {blocks : Finset (ℕ × ℕ)} {X Y : ℕ} {f : ℕ → ℂ} {H : ℕ} {α : ℝ}
    (hrange : ∀ n ∈ Finset.Icc Y (2 * Y), ∀ j ∈ Finset.Icc 1 H, n + j ≤ X)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ∑ n ∈ Finset.Icc Y (2 * Y),
        ‖modulatedShortSum f n H α -
          typicalModulatedShortSum blocks X f n H α‖ ≤
      H * (atypicalFactorizationSet blocks X).card := by
  classical
  calc
    ∑ n ∈ Finset.Icc Y (2 * Y),
        ‖modulatedShortSum f n H α -
          typicalModulatedShortSum blocks X f n H α‖ ≤
        ∑ n ∈ Finset.Icc Y (2 * Y),
          ∑ j ∈ Finset.Icc 1 H,
            if n + j ∈ atypicalFactorizationSet blocks X then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_modulatedShortSum_sub_typical_le (hrange n hn) hf
    _ = ∑ j ∈ Finset.Icc 1 H,
          ∑ n ∈ Finset.Icc Y (2 * Y),
            if n + j ∈ atypicalFactorizationSet blocks X then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _j ∈ Finset.Icc 1 H,
          ((atypicalFactorizationSet blocks X).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hcard := card_filter_add_mem_atypical_le blocks X Y j
      have hcardR :
          (((Finset.Icc Y (2 * Y)).filter
            (fun n ↦ n + j ∈ atypicalFactorizationSet blocks X)).card : ℝ) ≤
            ((atypicalFactorizationSet blocks X).card : ℝ) := by
        exact_mod_cast hcard
      rw [Finset.sum_boole]
      exact hcardR
    _ = H * (atypicalFactorizationSet blocks X).card := by simp

/-- Triangle-inequality form of the exceptional-set reduction. -/
theorem sum_norm_modulatedShortSum_le_typical_add_atypical
    {blocks : Finset (ℕ × ℕ)} {X Y : ℕ} {f : ℕ → ℂ} {H : ℕ} {α : ℝ}
    (hrange : ∀ n ∈ Finset.Icc Y (2 * Y), ∀ j ∈ Finset.Icc 1 H, n + j ≤ X)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ∑ n ∈ Finset.Icc Y (2 * Y), ‖modulatedShortSum f n H α‖ ≤
      (∑ n ∈ Finset.Icc Y (2 * Y),
        ‖typicalModulatedShortSum blocks X f n H α‖) +
      H * (atypicalFactorizationSet blocks X).card := by
  calc
    ∑ n ∈ Finset.Icc Y (2 * Y), ‖modulatedShortSum f n H α‖ ≤
        ∑ n ∈ Finset.Icc Y (2 * Y),
          (‖typicalModulatedShortSum blocks X f n H α‖ +
            ‖modulatedShortSum f n H α -
              typicalModulatedShortSum blocks X f n H α‖) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖modulatedShortSum f n H α‖ =
            ‖(modulatedShortSum f n H α -
                typicalModulatedShortSum blocks X f n H α) +
              typicalModulatedShortSum blocks X f n H α‖ := by ring_nf
        _ ≤ ‖modulatedShortSum f n H α -
                typicalModulatedShortSum blocks X f n H α‖ +
              ‖typicalModulatedShortSum blocks X f n H α‖ := norm_add_le _ _
        _ = ‖typicalModulatedShortSum blocks X f n H α‖ +
              ‖modulatedShortSum f n H α -
                typicalModulatedShortSum blocks X f n H α‖ := add_comm _ _
    _ = (∑ n ∈ Finset.Icc Y (2 * Y),
          ‖typicalModulatedShortSum blocks X f n H α‖) +
        ∑ n ∈ Finset.Icc Y (2 * Y),
          ‖modulatedShortSum f n H α -
            typicalModulatedShortSum blocks X f n H α‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ n ∈ Finset.Icc Y (2 * Y),
          ‖typicalModulatedShortSum blocks X f n H α‖) +
        H * (atypicalFactorizationSet blocks X).card := by
      have herr := sum_norm_modulatedShortSum_sub_typical_le
        (blocks := blocks) (X := X) (Y := Y) (f := f) (H := H) (α := α)
        hrange hf
      exact add_le_add le_rfl herr

/-- Quantitative version: a `ρ`-density exceptional set costs at most `ρ H Y`. -/
theorem sum_norm_modulatedShortSum_le_of_typical_of_atypical_density
    {blocks : Finset (ℕ × ℕ)} {X Y : ℕ} {f : ℕ → ℂ} {H : ℕ} {α η ρ : ℝ}
    (hrange : ∀ n ∈ Finset.Icc Y (2 * Y), ∀ j ∈ Finset.Icc 1 H, n + j ≤ X)
    (hf : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (htypical :
      ∑ n ∈ Finset.Icc Y (2 * Y),
          ‖typicalModulatedShortSum blocks X f n H α‖ ≤ η * H * Y)
    (hbad : ((atypicalFactorizationSet blocks X).card : ℝ) ≤ ρ * Y) :
    ∑ n ∈ Finset.Icc Y (2 * Y), ‖modulatedShortSum f n H α‖ ≤
      (η + ρ) * H * Y := by
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have herr :
      (H : ℝ) * (atypicalFactorizationSet blocks X).card ≤ ρ * H * Y := by
    calc
      (H : ℝ) * (atypicalFactorizationSet blocks X).card ≤
          (H : ℝ) * (ρ * Y) := mul_le_mul_of_nonneg_left hbad hH
      _ = ρ * H * Y := by ring
  calc
    ∑ n ∈ Finset.Icc Y (2 * Y), ‖modulatedShortSum f n H α‖ ≤
        (∑ n ∈ Finset.Icc Y (2 * Y),
          ‖typicalModulatedShortSum blocks X f n H α‖) +
        H * (atypicalFactorizationSet blocks X).card :=
      sum_norm_modulatedShortSum_le_typical_add_atypical hrange hf
    _ ≤ η * H * Y + ρ * H * Y := add_le_add htypical herr
    _ = (η + ρ) * H * Y := by ring

end

end Erdos67
