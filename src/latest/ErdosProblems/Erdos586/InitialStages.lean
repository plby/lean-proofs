/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.Core
import ErdosProblems.Erdos586.PrimeStages
import ErdosProblems.Erdos586.Smooth
import ErdosProblems.Erdos586.Moments
import ErdosProblems.Erdos586.StageLaw

/-!
# The initial `2,3,5` stages for Erdős Problem 586

This file supplies the arithmetic bridge between occurrence-indexed moduli
and the exponent triples used by the sharp smooth-antichain estimates.  In
particular, it does not take the reciprocal estimate as a hypothesis:

* a positive 5-smooth modulus is recovered exactly from its three entries in
  `Nat.factorization`;
* divisibility becomes the coordinate order `TripleLe`;
* a divisibility antichain of moduli becomes a `TripleAntichain`;
* exclusion of prime-power moduli becomes exclusion of `PrimePowerExp`; and
* BBMST Lemma 9.2 gives the exact reciprocal bound `1 / 3`.

The last two lemmas package the immediate consequences for the remaining
mass `μ₃` and normalized seed `f₃`: `μ₃ ≥ 2/3` and `f₃ ≤ 51/20`.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

local instance initialPartialPeriodNeZero (Q r : ℕ) : NeZero (partialPeriod Q r) :=
  ⟨(partialPeriod_pos Q r).ne'⟩

local instance initialStageCoordinateNeZero (Q r : ℕ) :
    NeZero (stagePrime (r + 1) ^ stageExponent Q (r + 1)) :=
  ⟨(pow_pos (stagePrime_pos (by omega : 0 < r + 1)) _).ne'⟩

/-! ## The zero-distortion stages are uniform -/

lemma distortWeight_zero {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (μ : FiniteProbability X) (B : Set (X × Y)) (z : X × Y) :
    distortWeight μ B 0 z = uniformLiftWeight μ z := by
  classical
  let α := fiberFraction B z.1
  by_cases hzero : α = 0
  · simp [distortWeight, α, hzero]
  have hαpos : 0 < α := lt_of_le_of_ne (fiberFraction_nonneg B z.1) (Ne.symm hzero)
  have hsmall : ¬α ≤ 0 := not_le_of_gt hαpos
  by_cases hz : z ∈ B
  · simp only [distortWeight, α, hzero, ↓reduceDIte, hsmall, hz,
      ↓reduceIte, sub_zero]
    have hzero' : fiberFraction B z.1 ≠ 0 := by simpa [α] using hzero
    rw [mul_one, div_self hzero', one_mul]
  · simp [distortWeight, α, hzero, hsmall, hz]

/-- During the first three stages every point has the uniform weight on the
current partial period. -/
lemma stageDistribution_weight_of_le_three
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) :
    ∀ {r : ℕ}, r ≤ 3 → ∀ x : ZMod (partialPeriod Q r),
      (stageDistribution A s Q hQ r).weight x =
        1 / (partialPeriod Q r : ℝ) := by
  intro r
  induction r with
  | zero =>
      intro hr x
      simp [initialStageDistribution]
  | succ r ih =>
      intro hr x
      rw [stageDistribution_succ_weight,
        distortionDelta_of_le_three (by omega), distortWeight_zero]
      unfold uniformLiftWeight
      rw [ih (by omega) (stageCRTRingEquiv Q r x).1]
      simp only [StageCoordinate, ZMod.card]
      rw [partialPeriod_succ]
      push_cast
      rw [div_div]

lemma FiniteProbability.mass_of_constant_weight
    {Ω : Type*} [Fintype Ω] (μ : FiniteProbability Ω)
    (c : ℝ) (hweight : ∀ ω, μ.weight ω = c) (S : Set Ω) :
    μ.mass S = (S.ncard : ℝ) * c := by
  classical
  have hcard : (Finset.univ.filter fun ω : Ω => ω ∈ S).card = S.ncard := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext ω
    simp
  unfold FiniteProbability.mass
  rw [← Finset.sum_filter]
  simp_rw [hweight]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Exact class mass under the uniform initial-stage distribution. -/
lemma stageDistribution_mass_congruenceClass_of_le_three
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) {r m : ℕ} (hr : r ≤ 3)
    (hm : m ∣ partialPeriod Q r) (hm0 : 0 < m) (b : ℤ) :
    (stageDistribution A s Q hQ r).mass
        (congruenceClass (partialPeriod Q r) m hm b) = 1 / (m : ℝ) := by
  rw [FiniteProbability.mass_of_constant_weight _
    (1 / (partialPeriod Q r : ℝ))
    (stageDistribution_weight_of_le_three A s Q hQ hr)]
  rw [card_congruenceClass hm hm0 b]
  have hmul := Nat.div_mul_cancel hm
  have hperiod0 : (partialPeriod Q r : ℝ) ≠ 0 := by
    exact_mod_cast (partialPeriod_pos Q r).ne'
  have hm0' : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm0.ne'
  field_simp [hperiod0, hm0']
  exact_mod_cast hmul

lemma FiniteProbability.mass_finset_iUnion_le_sum
    {Ω ι : Type*} [Fintype Ω] (μ : FiniteProbability Ω)
    (I : Finset ι) (E : ι → Set Ω) :
    μ.mass {ω | ∃ i ∈ I, ω ∈ E i} ≤ ∑ i ∈ I, μ.mass (E i) := by
  classical
  unfold FiniteProbability.mass
  rw [← Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hu : ∃ i ∈ I, ω ∈ E i
  · have hmem : ω ∈ {ω | ∃ i ∈ I, ω ∈ E i} := hu
    rw [if_pos hmem]
    obtain ⟨i, hi, hEi⟩ := hu
    have hnonneg : ∀ j ∈ I,
        0 ≤ if ω ∈ E j then μ.weight ω else 0 := by
      intro j hj
      split_ifs
      · exact μ.weight_nonneg ω
      · exact le_rfl
    calc
      μ.weight ω = (if ω ∈ E i then μ.weight ω else 0) := by simp [hEi]
      _ ≤ ∑ j ∈ I, if ω ∈ E j then μ.weight ω else 0 :=
        Finset.single_le_sum hnonneg hi
  · have hmem : ω ∉ {ω | ∃ i ∈ I, ω ∈ E i} := hu
    rw [if_neg hmem]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact μ.weight_nonneg ω
      · exact le_rfl

/-- The individual cyclic congruence event attached to a stage index.  The
empty branch makes this a total function of the occurrence index, avoiding
any proof-dependent summand. -/
def initialStageClass (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0)
    (i : Fin A.length) : Set (ZMod (partialPeriod Q (r + 1))) :=
  if hi : i ∈ stageIndices A s Q r then
    congruenceClass (partialPeriod Q (r + 1)) (A.get i).modulus
      (newModulus_dvd_partialPeriod_succ hQ
        ((mem_stageIndices_iff.mp hi).2))
      (A.get i).residue
  else ∅

lemma mem_stageBadSet_iff {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} {hQ : Q ≠ 0}
    {x : ZMod (partialPeriod Q (r + 1))} :
    x ∈ stageBadSet A s Q r hQ ↔
      ∃ i ∈ stageIndices A s Q r,
        x ∈ initialStageClass A s Q r hQ i := by
  constructor
  · rintro ⟨z, ⟨i, hi, hz⟩, rfl⟩
    exact ⟨i, hi, by simpa [initialStageClass, hi] using hz⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨stageCRTRingEquiv Q r x, ?_, by simp⟩
    exact ⟨i, hi, by simpa [initialStageClass, hi] using hx⟩

/-- Each of the first three literal stage costs is at most the sum of the
reciprocal moduli assigned to that stage. -/
lemma stageCost_le_reciprocal_sum_of_succ_le_three
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (hr : r + 1 ≤ 3) :
    stageCost A s Q r hQ ≤
      ∑ i ∈ stageIndices A s Q r,
        1 / ((A.get i).modulus : ℝ) := by
  unfold stageCost
  have hset : stageBadSet A s Q r hQ =
      {x | ∃ i ∈ stageIndices A s Q r,
        x ∈ initialStageClass A s Q r hQ i} := by
    ext x
    exact mem_stageBadSet_iff
  rw [hset]
  calc
    (stageDistribution A s Q hQ (r + 1)).mass
        {x | ∃ i ∈ stageIndices A s Q r,
          x ∈ initialStageClass A s Q r hQ i} ≤
        ∑ i ∈ stageIndices A s Q r,
          (stageDistribution A s Q hQ (r + 1)).mass
            (initialStageClass A s Q r hQ i) :=
      FiniteProbability.mass_finset_iUnion_le_sum _ _
        (initialStageClass A s Q r hQ)
    _ = ∑ i ∈ stageIndices A s Q r,
          1 / ((A.get i).modulus : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [initialStageClass, dif_pos hi]
      exact stageDistribution_mass_congruenceClass_of_le_three
        A s Q hQ hr
        (newModulus_dvd_partialPeriod_succ hQ
          ((mem_stageIndices_iff.mp hi).2))
        (lt_trans Nat.zero_lt_one (A.get i).one_lt_modulus)
        (A.get i).residue

/-! ## Positive 5-smooth naturals and exponent triples -/

/-- A natural number all of whose prime factors belong to `{2,3,5}`. -/
def IsFiveSmooth (d : ℕ) : Prop := d.primeFactors ⊆ {2, 3, 5}

/-- The `2`, `3`, and `5` entries of the prime factorization of `d`. -/
def fiveSmoothExp (d : ℕ) : Exp3 :=
  (d.factorization 2, d.factorization 3, d.factorization 5)

/-- Every divisor already present after the `2,3,5` stages is 5-smooth. -/
lemma isFiveSmooth_of_dvd_partialPeriod_three {Q d : ℕ}
    (hd : d ∣ partialPeriod Q 3) : IsFiveSmooth d := by
  intro p hp
  have hpPeriod : p ∈ (partialPeriod Q 3).primeFactors :=
    Nat.primeFactors_mono hd (partialPeriod_pos Q 3).ne' hp
  have hpActive := primeFactors_partialPeriod_subset_active Q 3 hpPeriod
  have hpLe : p ≤ 5 := by
    have := (mem_activePrimeFactors_iff (Q := Q) (r := 3) (p := p)
      (by omega)).1 hpActive
    simpa using this.2
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpTwo : 2 ≤ p := hpPrime.two_le
  interval_cases p
  · simp
  · simp
  · norm_num at hpPrime
  · simp

lemma factorization_eq_zero_of_fiveSmooth {d p : ℕ} (hd : IsFiveSmooth d)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    d.factorization p = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  by_cases hd0 : d = 0
  · exact Or.inr (Or.inr hd0)
  by_cases hp : p.Prime
  · right
    left
    intro hpd
    have hmem : p ∈ d.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
    have hsmall := hd hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
    exact hsmall.elim hp2 fun h => h.elim hp3 hp5
  · exact Or.inl hp

/-- A nonzero 5-smooth natural is exactly the product of its three prime
power coordinates. -/
lemma decode5_fiveSmoothExp {d : ℕ} (hd0 : d ≠ 0) (hd : IsFiveSmooth d) :
    decode5 (fiveSmoothExp d) = d := by
  apply Nat.eq_of_factorization_eq (by unfold decode5 fiveSmoothExp; positivity) hd0
  intro p
  unfold decode5 fiveSmoothExp
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.Prime.factorization_pow Nat.prime_three,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
  by_cases hp2 : p = 2
  · subst p
    norm_num [Nat.Prime.factorization]
  by_cases hp3 : p = 3
  · subst p
    norm_num [Nat.Prime.factorization]
  by_cases hp5 : p = 5
  · subst p
    norm_num [Nat.Prime.factorization]
  rw [factorization_eq_zero_of_fiveSmooth hd hp2 hp3 hp5]
  simp [hp2, hp3, hp5]

/-- Divisibility of positive 5-smooth naturals is precisely coordinatewise
comparison of their factorization triples. -/
lemma fiveSmoothExp_le_iff_dvd {a b : ℕ}
    (ha0 : a ≠ 0) (ha : IsFiveSmooth a)
    (hb0 : b ≠ 0) (hb : IsFiveSmooth b) :
    TripleLe (fiveSmoothExp a) (fiveSmoothExp b) ↔ a ∣ b := by
  constructor
  · intro hle
    rw [← decode5_fiveSmoothExp ha0 ha,
      ← decode5_fiveSmoothExp hb0 hb]
    exact tripleLe_decode5_dvd hle
  · intro hab
    have hfac := (Nat.factorization_le_iff_dvd ha0 hb0).2 hab
    exact ⟨hfac 2, hfac 3, hfac 5⟩

/-- Reciprocal numerical weight agrees with the reciprocal of the decoded
positive 5-smooth integer. -/
lemma tripleWeight_fiveSmoothExp {d : ℕ} (hd0 : d ≠ 0)
    (hd : IsFiveSmooth d) :
    tripleWeight (fiveSmoothExp d) = 1 / (d : ℝ) := by
  rw [tripleWeight_eq_inv_decode5, decode5_fiveSmoothExp hd0 hd]
  simp [one_div]

/-- An exponent triple supported on one positive coordinate decodes to a
prime power. -/
lemma primePowerExp_isPrimePow_decode5 {x : Exp3} (hx : PrimePowerExp x) :
    IsPrimePow (decode5 x) := by
  rcases hx with hx | hx | hx
  · refine (isPrimePow_nat_iff _).2 ⟨2, x.1, Nat.prime_two, hx.1, ?_⟩
    simp [decode5, hx.2.1, hx.2.2]
  · refine (isPrimePow_nat_iff _).2 ⟨3, x.2.1, Nat.prime_three, hx.2.1, ?_⟩
    simp [decode5, hx.1, hx.2.2]
  · refine (isPrimePow_nat_iff _).2 ⟨5, x.2.2, by norm_num, hx.2.2, ?_⟩
    simp [decode5, hx.1, hx.2.1]

lemma primePowerExp_fiveSmoothExp_isPrimePow {d : ℕ}
    (hd0 : d ≠ 0) (hd : IsFiveSmooth d)
    (hpow : PrimePowerExp (fiveSmoothExp d)) : IsPrimePow d := by
  rw [← decode5_fiveSmoothExp hd0 hd]
  exact primePowerExp_isPrimePow_decode5 hpow

/-! ## The exponent set of the 5-smooth part of a subcover -/

/-- Occurrences in `s` whose moduli are 5-smooth. -/
def fiveSmoothIndices (A : CoveringFamily)
    (s : Finset (Fin A.length)) : Finset (Fin A.length) :=
  s.filter fun i => IsFiveSmooth (A.get i).modulus

lemma mem_fiveSmoothIndices_iff {A : CoveringFamily}
    {s : Finset (Fin A.length)} {i : Fin A.length} :
    i ∈ fiveSmoothIndices A s ↔
      i ∈ s ∧ IsFiveSmooth (A.get i).modulus := by
  classical
  simp [fiveSmoothIndices]

/-- The factorization triples belonging to the 5-smooth part of `s`. -/
def fiveSmoothExponentSet (A : CoveringFamily)
    (s : Finset (Fin A.length)) : Finset Exp3 :=
  (fiveSmoothIndices A s).image fun i => fiveSmoothExp (A.get i).modulus

lemma fiveSmoothExp_injective_on
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    Set.InjOn (fun i : Fin A.length => fiveSmoothExp (A.get i).modulus)
      (fiveSmoothIndices A s : Set (Fin A.length)) := by
  intro i hi j hj hexp
  change i ∈ fiveSmoothIndices A s at hi
  change j ∈ fiveSmoothIndices A s at hj
  rw [mem_fiveSmoothIndices_iff] at hi hj
  by_contra hij
  apply hanti i hi.1 j hj.1 hij
  have hi0 : (A.get i).modulus ≠ 0 :=
    (Nat.zero_lt_of_lt (A.get i).one_lt_modulus).ne'
  have hj0 : (A.get j).modulus ≠ 0 :=
    (Nat.zero_lt_of_lt (A.get j).one_lt_modulus).ne'
  rw [← decode5_fiveSmoothExp hi0 hi.2,
    ← decode5_fiveSmoothExp hj0 hj.2]
  refine ⟨1, ?_⟩
  simpa using (congrArg decode5 hexp).symm

lemma fiveSmoothExponentSet_antichain
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    TripleAntichain (fiveSmoothExponentSet A s) := by
  intro x hx y hy hxy hle
  change x ∈ fiveSmoothExponentSet A s at hx
  change y ∈ fiveSmoothExponentSet A s at hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_fiveSmoothIndices_iff] at hi hj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hxy rfl
  apply hanti i hi.1 j hj.1 hij
  exact (fiveSmoothExp_le_iff_dvd
    (Nat.zero_lt_of_lt (A.get i).one_lt_modulus).ne' hi.2
    (Nat.zero_lt_of_lt (A.get j).one_lt_modulus).ne' hj.2).1 hle

lemma fiveSmoothExponentSet_ne_zero
    (A : CoveringFamily) (s : Finset (Fin A.length)) :
    ∀ x ∈ fiveSmoothExponentSet A s, x ≠ (0, 0, 0) := by
  intro x hx hzero
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_fiveSmoothIndices_iff] at hi
  have hdecode := decode5_fiveSmoothExp
    (Nat.zero_lt_of_lt (A.get i).one_lt_modulus).ne' hi.2
  rw [hzero] at hdecode
  have hone : (A.get i).modulus = 1 := by
    simpa [decode5] using hdecode.symm
  exact (Nat.ne_of_gt (A.get i).one_lt_modulus) hone

lemma fiveSmoothExponentSet_not_primePower
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hnpp : ∀ i ∈ s, ¬ IsPrimePow (A.get i).modulus) :
    ∀ x ∈ fiveSmoothExponentSet A s, ¬ PrimePowerExp x := by
  intro x hx hpow
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_fiveSmoothIndices_iff] at hi
  exact hnpp i hi.1 <|
    primePowerExp_fiveSmoothExp_isPrimePow
      (Nat.zero_lt_of_lt (A.get i).one_lt_modulus).ne' hi.2 hpow

lemma sum_reciprocal_fiveSmoothIndices_eq
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    (∑ i ∈ fiveSmoothIndices A s, 1 / ((A.get i).modulus : ℝ)) =
      ∑ x ∈ fiveSmoothExponentSet A s, tripleWeight x := by
  classical
  unfold fiveSmoothExponentSet
  rw [Finset.sum_image (fiveSmoothExp_injective_on A s hanti)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mem_fiveSmoothIndices_iff] at hi
  exact (tripleWeight_fiveSmoothExp
    (Nat.zero_lt_of_lt (A.get i).one_lt_modulus).ne' hi.2).symm

/-! ## Sharp reciprocal, survival, and normalized-seed bounds -/

/-- The exact BBMST Lemma 9.2 bound, stated directly for the 5-smooth
occurrences of a minimal divisibility-antichain subcover. -/
theorem minimal_antichain_fiveSmooth_reciprocal_le
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    ∑ i ∈ fiveSmoothIndices A s,
      1 / ((A.get i).modulus : ℝ) ≤ 1 / 3 := by
  rw [sum_reciprocal_fiveSmoothIndices_eq A s hanti]
  apply five_smooth_reciprocal_le
  · exact fiveSmoothExponentSet_antichain A s hanti
  · exact fiveSmoothExponentSet_ne_zero A s
  · apply fiveSmoothExponentSet_not_primePower A s
    exact no_prime_power_modulus_of_minimal_antichain_cover
      A s hminimal hanti

/-- Every occurrence assigned to one of the first three prime stages belongs
to the 5-smooth part of the selected subcover. -/
lemma stageIndices_subset_fiveSmoothIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (hr : r + 1 ≤ 3) :
    stageIndices A s Q r ⊆ fiveSmoothIndices A s := by
  intro i hi
  have hi' := mem_stageIndices_iff.mp hi
  rw [mem_fiveSmoothIndices_iff]
  refine ⟨hi'.1, isFiveSmooth_of_dvd_partialPeriod_three (Q := Q) ?_⟩
  exact (newModulus_dvd_partialPeriod_succ hQ hi'.2).trans
    (partialPeriod_mono_dvd (by omega : 0 < r + 1) hr)

/-- Different prime stages have disjoint occurrence sets. -/
lemma stageIndices_disjoint_of_ne
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) {r t : ℕ} (hrt : r ≠ t) :
    Disjoint (stageIndices A s Q r) (stageIndices A s Q t) := by
  rw [Finset.disjoint_left]
  intro i hir hit
  have hrnew := (mem_stageIndices_iff.mp hir).2
  have htnew := (mem_stageIndices_iff.mp hit).2
  have hrstage := isNewModulus_stage_eq_primeStage_largest
    hQ (A.get i).one_lt_modulus hrnew
  have htstage := isNewModulus_stage_eq_primeStage_largest
    hQ (A.get i).one_lt_modulus htnew
  omega

/-- The complete first-three-stage bookkeeping inequality.  There are no
analytic hypotheses: it follows from the literal `StageLaw` costs, uniformity
at distortion parameter zero, the union bound, and uniqueness of the
largest-prime stage assignment. -/
theorem initial_stageCost_sum_le_fiveSmooth
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) :
    (∑ r ∈ Finset.range 3, stageCost A s Q r hQ) ≤
      ∑ i ∈ fiveSmoothIndices A s,
        1 / ((A.get i).modulus : ℝ) := by
  let w : Fin A.length → ℝ := fun i => 1 / ((A.get i).modulus : ℝ)
  let I0 := stageIndices A s Q 0
  let I1 := stageIndices A s Q 1
  let I2 := stageIndices A s Q 2
  have h0 : stageCost A s Q 0 hQ ≤ ∑ i ∈ I0, w i := by
    simpa [I0, w] using
      stageCost_le_reciprocal_sum_of_succ_le_three A s Q 0 hQ (by omega)
  have h1 : stageCost A s Q 1 hQ ≤ ∑ i ∈ I1, w i := by
    simpa [I1, w] using
      stageCost_le_reciprocal_sum_of_succ_le_three A s Q 1 hQ (by omega)
  have h2 : stageCost A s Q 2 hQ ≤ ∑ i ∈ I2, w i := by
    simpa [I2, w] using
      stageCost_le_reciprocal_sum_of_succ_le_three A s Q 2 hQ (by omega)
  have h01 : Disjoint I0 I1 := by
    simpa [I0, I1] using
      stageIndices_disjoint_of_ne A s Q hQ (by omega : (0 : ℕ) ≠ 1)
  have h02 : Disjoint I0 I2 := by
    simpa [I0, I2] using
      stageIndices_disjoint_of_ne A s Q hQ (by omega : (0 : ℕ) ≠ 2)
  have h12 : Disjoint I1 I2 := by
    simpa [I1, I2] using
      stageIndices_disjoint_of_ne A s Q hQ (by omega : (1 : ℕ) ≠ 2)
  have h012 : Disjoint (I0 ∪ I1) I2 := by
    rw [Finset.disjoint_left]
    intro i hi hi2
    rcases Finset.mem_union.mp hi with hi0 | hi1
    · exact (Finset.disjoint_left.mp h02) hi0 hi2
    · exact (Finset.disjoint_left.mp h12) hi1 hi2
  have hsubset : (I0 ∪ I1) ∪ I2 ⊆ fiveSmoothIndices A s := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi01 | hi2
    · rcases Finset.mem_union.mp hi01 with hi0 | hi1
      · exact stageIndices_subset_fiveSmoothIndices A s Q 0 hQ (by omega) hi0
      · exact stageIndices_subset_fiveSmoothIndices A s Q 1 hQ (by omega) hi1
    · exact stageIndices_subset_fiveSmoothIndices A s Q 2 hQ (by omega) hi2
  calc
    (∑ r ∈ Finset.range 3, stageCost A s Q r hQ) =
        (stageCost A s Q 0 hQ + stageCost A s Q 1 hQ) +
          stageCost A s Q 2 hQ := by norm_num [Finset.sum_range_succ]
    _ ≤ ((∑ i ∈ I0, w i) + ∑ i ∈ I1, w i) + ∑ i ∈ I2, w i :=
      add_le_add (add_le_add h0 h1) h2
    _ = ∑ i ∈ (I0 ∪ I1) ∪ I2, w i := by
      rw [Finset.sum_union h012, Finset.sum_union h01]
    _ ≤ ∑ i ∈ fiveSmoothIndices A s, w i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i hi hnot => by
        dsimp [w]
        positivity
    _ = ∑ i ∈ fiveSmoothIndices A s,
          1 / ((A.get i).modulus : ℝ) := rfl

/-- If the total cost of the first three stages is bounded by the reciprocal
sum of the 5-smooth moduli, their remaining budget is at least `2/3`.

The equality defining `μ₃` and the cost comparison are exactly the two
bookkeeping facts supplied by the concrete stage construction. -/
theorem initial_three_stage_survival_ge_two_thirds
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    {initialCost μ₃ : ℝ}
    (hcost : initialCost ≤ ∑ i ∈ fiveSmoothIndices A s,
      1 / ((A.get i).modulus : ℝ))
    (hμ₃ : μ₃ = 1 - initialCost) :
    2 / 3 ≤ μ₃ := by
  have hsmooth := minimal_antichain_fiveSmooth_reciprocal_le
    A s hminimal hanti
  rw [hμ₃]
  linarith

/-- The complete sharp initial seed: positive remaining mass and
`(17/10)/μ₃ ≤ 51/20`. -/
theorem initial_three_stage_seed_le_fifty_one_twentieth
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    {initialCost μ₃ : ℝ}
    (hcost : initialCost ≤ ∑ i ∈ fiveSmoothIndices A s,
      1 / ((A.get i).modulus : ℝ))
    (hμ₃ : μ₃ = 1 - initialCost) :
    0 < μ₃ ∧ fiveSmoothKappa / μ₃ ≤ 51 / 20 := by
  have hsurvival := initial_three_stage_survival_ge_two_thirds
    A s hminimal hanti hcost hμ₃
  exact ⟨lt_of_lt_of_le (by norm_num) hsurvival,
    fiveSmoothKappa_div_le_fifty_one_twentieth hsurvival⟩

/-- Concrete `StageLaw` form of the initial survival estimate. -/
theorem stageSurvival_three_ge_two_thirds
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0)
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    2 / 3 ≤ stageSurvival A s Q 3 hQ := by
  apply initial_three_stage_survival_ge_two_thirds
    A s hminimal hanti (initial_stageCost_sum_le_fiveSmooth A s Q hQ)
  rfl

/-- Concrete normalized starting bound for the recursive certificate. -/
theorem stageF_three_le_fifty_one_twentieth
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0)
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    0 < stageSurvival A s Q 3 hQ ∧
      stageF fiveSmoothKappa A s Q 3 3 hQ ≤ 51 / 20 := by
  have hsurvival := stageSurvival_three_ge_two_thirds
    A s Q hQ hminimal hanti
  refine ⟨lt_of_lt_of_le (by norm_num) hsurvival, ?_⟩
  simpa [stageF, stageGrowthProduct] using
    fiveSmoothKappa_div_le_fifty_one_twentieth hsurvival

end

end Erdos586
