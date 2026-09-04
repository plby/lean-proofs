import ErdosProblems.Erdos67.Section4Assembly
import ErdosProblems.Erdos67.BCCPrefix

/-!
# Reduction to the primitive character inducing an Elliott witness

The character supplied by the logarithmic Elliott theorem is allowed to be
imprimitive.  The Fourier-support statement used in the BCC argument is not:
it needs a primitive character at its actual conductor.  This file makes the
standard inducing-character reduction explicit.

There are two points which are easy to conflate.

* Replacing `chi` by `chi.primitiveCharacter` changes no prime value away
  from the *old* level.  At the finitely many primes dividing the old level it
  can increase the finite pretentious distance by at most their reciprocal
  harmonic mass.
* The modified character and its correction must then be rebuilt with the
  conductor, rather than merely relabelling the old level.  This gives exact
  agreement with the primitive character away from its conductor and keeps
  the factorization and conductor-prime normalization literal.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67

noncomputable section

/-! ## The finite loss at primes dividing the old level -/

/-- Reciprocal mass of the distinct prime divisors of a positive level. -/
def levelPrimeHarmonic (q : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, (p : ℝ)⁻¹

theorem levelPrimeHarmonic_nonneg (q : ℕ) :
    0 ≤ levelPrimeHarmonic q := by
  unfold levelPrimeHarmonic
  positivity

theorem levelPrimeHarmonic_le_card (q : ℕ) :
    levelPrimeHarmonic q ≤ q.primeFactors.card := by
  unfold levelPrimeHarmonic
  calc
    (∑ p ∈ q.primeFactors, (p : ℝ)⁻¹) ≤
        ∑ _p ∈ q.primeFactors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
      exact inv_le_one_of_one_le₀ hpR
    _ = q.primeFactors.card := by simp

theorem DirichletCharacter.primitiveCharacter_apply_nat_of_coprime
    {q n : ℕ} (chi : DirichletCharacter ℂ q) (hn : n.Coprime q) :
    chi.primitiveCharacter n = chi n := by
  simpa using chi.primitiveCharacter_apply_of_isCoprime hn.isCoprime

/-- Passing from a character to its inducing primitive character costs only
the reciprocal mass of primes dividing the original level.  This is the
precise finite estimate needed to reuse an Elliott witness after replacing
its level by the conductor. -/
theorem pretentiousDistSqToPrimitiveCharacter_le
    {q x : ℕ} [NeZero q] (f : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    pretentiousDistSqToTwist f chi.primitiveCharacter t x ≤
      pretentiousDistSqToTwist f chi t x + levelPrimeHarmonic q := by
  classical
  let exceptional : Finset ℕ :=
    (primesUpTo x).filter fun p ↦ p ∣ q
  have hterm (p : ℕ) (hp : p ∈ primesUpTo x) :
      pretentiousTerm f (dirichletArchimedeanTwist chi.primitiveCharacter t) p ≤
        pretentiousTerm f (dirichletArchimedeanTwist chi t) p +
          (if p ∣ q then (p : ℝ)⁻¹ else 0) := by
    have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
    by_cases hpq : p ∣ q
    · have hnotcop : ¬p.Coprime q := by
        intro hcop
        exact (hpPrime.coprime_iff_not_dvd.mp hcop) hpq
      have hchiZero : chi p = 0 := by
        have hnotcopInt : ¬IsCoprime (p : ℤ) (q : ℤ) := by
          simpa only [Nat.isCoprime_iff_coprime] using hnotcop
        simpa using
          (DirichletCharacter.apply_eq_zero_iff chi (p : ℤ)).2 hnotcopInt
      have hprimitive :
          pretentiousTerm f
              (dirichletArchimedeanTwist chi.primitiveCharacter t) p ≤
            2 / (p : ℝ) := by
        apply pretentiousTerm_le_two_div (hf p hpPrime)
        exact norm_dirichletArchimedeanTwist_le_one
          chi.primitiveCharacter t hpPrime.pos
      have hold :
          pretentiousTerm f (dirichletArchimedeanTwist chi t) p =
            1 / (p : ℝ) := by
        simp [pretentiousTerm, dirichletArchimedeanTwist, hchiZero]
      rw [if_pos hpq, hold]
      calc
        pretentiousTerm f
            (dirichletArchimedeanTwist chi.primitiveCharacter t) p ≤
            2 / (p : ℝ) := hprimitive
        _ = (p : ℝ)⁻¹ + (p : ℝ)⁻¹ := by ring
        _ ≤ 1 / (p : ℝ) + (p : ℝ)⁻¹ := by rw [one_div]
    · have hcop : p.Coprime q :=
        hpPrime.coprime_iff_not_dvd.mpr hpq
      have hchi : chi.primitiveCharacter p = chi p :=
        DirichletCharacter.primitiveCharacter_apply_nat_of_coprime chi hcop
      rw [if_neg hpq]
      simp only [add_zero]
      apply le_of_eq
      unfold pretentiousTerm dirichletArchimedeanTwist
      rw [hchi]
  have hexceptional_subset : exceptional ⊆ q.primeFactors := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact (mem_primesUpTo.mp hp'.1).1.mem_primeFactors hp'.2 (NeZero.ne q)
  have hexceptional_nonneg :
      ∀ p ∈ q.primeFactors, p ∉ exceptional → 0 ≤ (p : ℝ)⁻¹ := by
    intro p _hp _hpex
    positivity
  unfold pretentiousDistSqToTwist pretentiousDistSq
  calc
    (∑ p ∈ primesUpTo x,
        pretentiousTerm f
          (dirichletArchimedeanTwist chi.primitiveCharacter t) p) ≤
        ∑ p ∈ primesUpTo x,
          (pretentiousTerm f (dirichletArchimedeanTwist chi t) p +
            if p ∣ q then (p : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ = (∑ p ∈ primesUpTo x,
          pretentiousTerm f (dirichletArchimedeanTwist chi t) p) +
        ∑ p ∈ exceptional, (p : ℝ)⁻¹ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [exceptional, Finset.sum_filter]
    _ ≤ (∑ p ∈ primesUpTo x,
          pretentiousTerm f (dirichletArchimedeanTwist chi t) p) +
        levelPrimeHarmonic q := by
      gcongr
      unfold levelPrimeHarmonic
      exact Finset.sum_le_sum_of_subset_of_nonneg hexceptional_subset
        hexceptional_nonneg

/-! ## Canonical conductor data attached to a Section 4 witness -/

def Section4CharacterData.primitiveQ
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) : ℕ :=
  W.chi.conductor

def Section4CharacterData.primitiveChi
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    DirichletCharacter ℂ W.primitiveQ :=
  W.chi.primitiveCharacter

theorem Section4CharacterData.primitiveQ_pos
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    0 < W.primitiveQ := by
  let : NeZero W.q := ⟨W.q_pos.ne'⟩
  exact Nat.pos_of_ne_zero W.chi.conductor_ne_zero

instance Section4CharacterData.primitiveQ_neZero
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    NeZero W.primitiveQ :=
  ⟨W.primitiveQ_pos.ne'⟩

theorem Section4CharacterData.primitiveQ_dvd_q
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.primitiveQ ∣ W.q := by
  exact W.chi.conductor_dvd_level

theorem Section4CharacterData.primitiveQ_le_q
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.primitiveQ ≤ W.q :=
  Nat.le_of_dvd W.q_pos W.primitiveQ_dvd_q

theorem Section4CharacterData.primitiveQ_le_A
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.primitiveQ ≤ S.A :=
  W.primitiveQ_le_q.trans W.q_le

theorem Section4CharacterData.primitiveChi_isPrimitive
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.primitiveChi.IsPrimitive :=
  W.chi.primitiveCharacter_isPrimitive

theorem Section4CharacterData.primitiveQ_eq_one_iff
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.primitiveQ = 1 ↔ W.chi = 1 := by
  let : NeZero W.q := ⟨W.q_pos.ne'⟩
  exact (DirichletCharacter.eq_one_iff_conductor_eq_one).symm

/-- The complete assignment package rebuilt at the actual conductor. -/
def Section4CharacterData.primitiveAssignmentData
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    WitnessAssignmentData S.sample W.primitiveQ W.primitiveChi W.t :=
  witnessAssignmentData S.sample W.primitiveChi W.t

/-- The primitive modified character, with only the conductor primes patched. -/
def Section4CharacterData.primitiveModifiedAssignment
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    PrimeAssignment :=
  modifiedAssignment (compactCharacterPrimeAssignment S.sample)
    (patchedDirichletPrimeAssignment W.primitiveChi)
    (archimedeanPrimeAssignment W.t) (levelPrimeFinset W.primitiveQ)

/-- The correction corresponding to the conductor-level factorization. -/
def Section4CharacterData.primitiveCorrectionHom
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    ℕ →*₀ ℂ :=
  W.primitiveAssignmentData.correctionHom

theorem Section4CharacterData.primitiveModifiedAssignment_agrees
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    AgreesWithCharacterAway W.primitiveModifiedAssignment W.primitiveChi := by
  intro p hp
  have hpnotmem : p ∉ levelPrimeFinset W.primitiveQ := by
    intro hpmem
    exact hp ((mem_levelPrimeFinset_iff (NeZero.ne W.primitiveQ) p).1 hpmem)
  rw [Section4CharacterData.primitiveModifiedAssignment,
    modifiedAssignment_of_not_mem _ _ _ _ hpnotmem]
  exact patchedDirichletPrimeAssignment_coe_of_not_dvd W.primitiveChi p hp

theorem Section4CharacterData.primitiveCorrectionHom_hasUnitNorm
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    EulerResidue.HasUnitNorm W.primitiveCorrectionHom :=
  W.primitiveAssignmentData.correctionHom_hasUnitNorm

theorem Section4CharacterData.primitiveCorrectionHom_prime_dvd
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (p : ℕ) (hp : p.Prime) (hpq : p ∣ W.primitiveQ) :
    W.primitiveCorrectionHom p = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  let pp : PrimeNat := ⟨p, hp⟩
  have hmem : pp ∈ levelPrimeFinset W.primitiveQ :=
    (mem_levelPrimeFinset_iff W.primitiveQ_pos.ne' pp).2 hpq
  rw [Section4CharacterData.primitiveCorrectionHom,
    WitnessAssignmentData.correctionHom,
    zeroPreservingPrimeExtension_apply_of_ne_zero _ hp0]
  change (primeExtension W.primitiveAssignmentData.correction (pp : ℕ) : ℂ) = 1
  rw [primeExtension_prime]
  have hc : W.primitiveAssignmentData.correction pp = 1 := by
    unfold WitnessAssignmentData.correction
    apply correctionAssignment_of_mem
    simpa only [WitnessAssignmentData.exceptional_eq] using hmem
  simpa [pp] using congrArg Subtype.val hc

/-- Away from the conductor, the primitive correction is exactly the
pretentious quotient `g(p) * conj (chi*(p) p^(it))`. -/
theorem Section4CharacterData.primitiveCorrectionHom_apply_prime_of_not_dvd
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (p : PrimeNat) (hpq : ¬(p : ℕ) ∣ W.primitiveQ) :
    W.primitiveCorrectionHom p =
      compactCharacterNatValue S.sample p *
        conj (W.primitiveChi p * archimedeanTwist W.t p) := by
  have hpnotmem : p ∉ levelPrimeFinset W.primitiveQ := by
    intro hpmem
    exact hpq ((mem_levelPrimeFinset_iff (NeZero.ne W.primitiveQ) p).1 hpmem)
  rw [Section4CharacterData.primitiveCorrectionHom,
    WitnessAssignmentData.correctionHom,
    zeroPreservingPrimeExtension_apply_prime]
  change
    ((correctionAssignment (compactCharacterPrimeAssignment S.sample)
        (patchedDirichletPrimeAssignment W.primitiveChi)
        (archimedeanPrimeAssignment W.t) (levelPrimeFinset W.primitiveQ) p :
      Circle) : ℂ) = _
  rw [correctionAssignment, modifiedAssignment_of_not_mem _ _ _ _ hpnotmem]
  rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
  change
    (compactCharacterPrimeAssignment S.sample p : ℂ) *
        conj ((patchedDirichletPrimeAssignment W.primitiveChi p : ℂ) *
          (archimedeanPrimeAssignment W.t p : ℂ)) = _
  rw [patchedDirichletPrimeAssignment_coe_of_not_dvd W.primitiveChi p hpq,
    archimedeanPrimeAssignment_coe]
  rw [compactCharacterNatValue_of_pos S.sample p.2.pos]
  rfl

/-- The correction's finite pretentious mass is bounded by the primitive
character approximation distance.  At conductor primes the correction term
is zero; away from the conductor the two summands are exactly equal. -/
theorem Section4CharacterData.primitiveCorrection_pretentiousMass_le_distance
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) (X : ℕ) :
    EulerResidue.pretentiousMass W.primitiveCorrectionHom X ≤
      pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
        W.primitiveChi W.t X := by
  have hprimes : Nat.primesLE X = primesUpTo X := by
    ext p
    simp only [Nat.mem_primesLE, mem_primesUpTo]
    tauto
  unfold EulerResidue.pretentiousMass pretentiousDistSqToTwist pretentiousDistSq
  rw [hprimes]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
  let pp : PrimeNat := ⟨p, hpPrime⟩
  by_cases hpq : p ∣ W.primitiveQ
  · rw [W.primitiveCorrectionHom_prime_dvd p hpPrime hpq]
    simp only [Complex.one_re, sub_self, zero_div]
    apply pretentiousTerm_nonneg
    · exact (norm_compactCharacterNatValue S.sample hpPrime.pos).le
    · exact norm_dirichletArchimedeanTwist_le_one
        W.primitiveChi W.t hpPrime.pos
  · have hvalue :=
      W.primitiveCorrectionHom_apply_prime_of_not_dvd pp hpq
    rw [hvalue]
    rfl

/-- Exact conductor-level factorization of the original compact sample. -/
theorem Section4CharacterData.primitive_primeExtension_factorization
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) (n : ℕ) :
    primeExtension (compactCharacterPrimeAssignment S.sample) n =
      primeExtension W.primitiveModifiedAssignment n *
        primeExtension (archimedeanPrimeAssignment W.t) n *
          primeExtension
            (correctionAssignment (compactCharacterPrimeAssignment S.sample)
              (patchedDirichletPrimeAssignment W.primitiveChi)
              (archimedeanPrimeAssignment W.t)
              (levelPrimeFinset W.primitiveQ)) n := by
  simpa only [Section4CharacterData.primitiveModifiedAssignment] using
    primeExtension_compact_modified_factorization
      S.sample W.primitiveChi W.t n

/-- The selected Elliott approximation remains pretentious after passage to
the inducing primitive character, with the explicit finite level-prime loss. -/
theorem Section4CharacterData.primitive_distance_large_le
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) (X : ℕ) :
    pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
        W.primitiveChi W.t X ≤
      pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
        W.chi W.t X + levelPrimeHarmonic W.q := by
  let : NeZero W.q := ⟨W.q_pos.ne'⟩
  apply pretentiousDistSqToPrimitiveCharacter_le
  intro p hp
  exact (norm_compactCharacterNatValue S.sample hp.pos).le

theorem Section4CharacterData.primitive_distance_at_largeScale_lt
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
        W.primitiveChi W.t ((4 ^ S.K) ^ S.D) <
      S.A + levelPrimeHarmonic W.q := by
  apply lt_of_le_of_lt
    (W.primitive_distance_large_le ((4 ^ S.K) ^ S.D))
  have h := add_lt_add_right W.distance_large (levelPrimeHarmonic W.q)
  simpa only [add_comm] using h

theorem Section4CharacterData.primitive_distance_at_largeScale_lt_two_mul_A
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
        W.primitiveChi W.t ((4 ^ S.K) ^ S.D) < 2 * S.A := by
  have hcard : (W.q.primeFactors.card : ℝ) ≤ S.A := by
    have hsubset : W.q.primeFactors ⊆ Finset.Icc 1 W.q := by
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      exact Finset.mem_Icc.mpr
        ⟨hpPrime.one_le,
          Nat.le_of_dvd W.q_pos (Nat.dvd_of_mem_primeFactors hp)⟩
    have hcardNat : W.q.primeFactors.card ≤ S.A := by
      calc
        W.q.primeFactors.card ≤ (Finset.Icc 1 W.q).card :=
          Finset.card_le_card hsubset
        _ = W.q := by simp
        _ ≤ S.A := W.q_le
    exact_mod_cast hcardNat
  have herr : levelPrimeHarmonic W.q ≤ S.A :=
    (levelPrimeHarmonic_le_card W.q).trans hcard
  exact W.primitive_distance_at_largeScale_lt.trans_le (by linarith)

theorem Section4CharacterData.primitiveCorrection_pretentiousMass_at_largeScale_lt_two_mul_A
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    EulerResidue.pretentiousMass W.primitiveCorrectionHom
        ((4 ^ S.K) ^ S.D) < 2 * S.A := by
  exact lt_of_le_of_lt
    (W.primitiveCorrection_pretentiousMass_le_distance ((4 ^ S.K) ^ S.D))
    W.primitive_distance_at_largeScale_lt_two_mul_A

/-! ## Direct conductor-level BCC consumer -/

/-- Apply the full divisor-family BCC contradiction to the primitive modified
character canonically rebuilt from an arbitrary-level Section 4 witness.
The modulus bound is inherited from `conductor ∣ level` and `level ≤ A`; no
primitivity assumption on the Elliott character is present in this wrapper. -/
theorem Section4CharacterData.primitiveModified_selected_family_contradiction
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {k H : ℕ} (hk : 0 < k) (hH : 0 < H) (hq : 1 < W.primitiveQ)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (W.primitiveQ ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hactual :
      (1 / (((W.primitiveQ ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues W.primitiveQ k H,
              Complex.normSq
                (cyclicPrimeExtensionIccPrefix
                  W.primitiveModifiedAssignment L a) ≤ B)
    (hlarge :
      8 * (S.A : ℝ) *
          (B +
            (((2 * H * W.primitiveQ.primeFactors.card : ℕ) : ℝ) /
                ((2 ^ k : ℕ) : ℝ)) * (((2 * H : ℕ) : ℝ) ^ 2)) <
        (selected.card : ℝ)) : False := by
  exact modifiedCharacter_selected_family_contradiction
    hk hH W.primitiveModifiedAssignment W.primitiveChi
      W.primitiveChi_isPrimitive W.primitiveModifiedAssignment_agrees
      hq W.primitiveQ_le_A selected hselected hdH B hactual hlarge

/-! ## Nonlegacy shifted-convolution consumer at the conductor -/

/-- Values of the primitive modified character on the cyclic group used by
the stored Section 4 BCC parameters. -/
def Section4CharacterData.primitiveModifiedResidueValue
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    ZMod (W.primitiveQ ^ S.k) → ℂ :=
  fun a ↦ (primeExtension W.primitiveModifiedAssignment a.val : ℂ)

theorem Section4CharacterData.norm_primitiveModifiedResidueValue_le_one
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (a : ZMod (W.primitiveQ ^ S.k)) :
    ‖W.primitiveModifiedResidueValue a‖ ≤ 1 := by
  simpa only [Section4CharacterData.primitiveModifiedResidueValue] using
    (norm_primeExtension_coe W.primitiveModifiedAssignment a.val).le

@[simp] theorem Section4CharacterData.shiftedResiduePrefix_primitiveModified_eq
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (L : ℕ) (a : ZMod (W.primitiveQ ^ S.k)) :
    shiftedResiduePrefix W.primitiveModifiedResidueValue L a =
      cyclicPrimeExtensionIccPrefix W.primitiveModifiedAssignment L a := by
  rfl

/-- Equation-(15) transfer after replacing the Elliott character by its
inducing primitive character and rebuilding the correction at the conductor. -/
theorem Section4CharacterData.primitive_normalized_cyclicGoodEnergy_le
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {sigma Main : ℂ} {Err Kbound J : ℝ}
    (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod (W.primitiveQ ^ S.k),
      ‖EulerResidue.residueLSeries W.primitiveCorrectionHom b sigma - Main‖ ≤ Err)
    (hMain : 0 < ‖Main‖)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.primitiveCorrectionHom sigma
            W.primitiveModifiedResidueValue
            (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
        Kbound * ‖Main‖ ^ 2 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖Main‖ ^ 2) :
    (1 / (((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
            Complex.normSq
              (cyclicPrimeExtensionIccPrefix
                W.primitiveModifiedAssignment L a) ≤
      2 * Kbound + 2 * J := by
  simpa only [W.shiftedResiduePrefix_primitiveModified_eq] using
    normalized_medium_shiftedResiduePrefixEnergy_le hErr hresidue
      W.primitiveModifiedResidueValue
      W.norm_primitiveModifiedResidueValue_le_one
      (cyclicGoodResidues W.primitiveQ S.k S.H) S.H S.H_pos hMain
      hconvolution hsmall

/-- The stored BCC package contradicts a conductor-level primitive modified
prefix-energy bound.  The arbitrary Elliott level has disappeared from the
Fourier argument; it is used only through `conductor ≤ level ≤ A`. -/
theorem Section4CharacterData.primitive_bcc_contradiction_of_discrepancy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hq : 1 < W.primitiveQ)
    (hdiscrepancy :
      (1 / (((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)) *
          ∑ L ∈ Finset.Ioc S.H (2 * S.H),
            ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
              Complex.normSq
                (cyclicPrimeExtensionIccPrefix
                  W.primitiveModifiedAssignment L a) ≤ S.B) : False := by
  apply S.params.fullDivisor_bcc_contradiction (by omega)
    W.primitiveQ_le_A W.primitiveModifiedAssignment W.primitiveChi
    W.primitiveChi_isPrimitive W.primitiveModifiedAssignment_agrees
  change
    (1 / (((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ M ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
            Complex.normSq
              (∑ m ∈ Finset.Icc 1 M,
                (primeExtension W.primitiveModifiedAssignment
                  (a + (m : ZMod (W.primitiveQ ^ S.k))).val : ℂ)) ≤ S.B
  simpa only [cyclicPrimeExtensionIccPrefix] using hdiscrepancy

/-- Final nonlegacy primitive-character consumer: a shifted-convolution
estimate and uniform conductor-residue approximation feed the exact BCC
contradiction, with the analytic budget stored in `S.B`. -/
theorem Section4CharacterData.primitive_contradiction_of_shiftedConvolution
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hq : 1 < W.primitiveQ)
    {sigma Main : ℂ} {Err Kbound J : ℝ}
    (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod (W.primitiveQ ^ S.k),
      ‖EulerResidue.residueLSeries W.primitiveCorrectionHom b sigma - Main‖ ≤ Err)
    (hMain : 0 < ‖Main‖)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.primitiveCorrectionHom sigma
            W.primitiveModifiedResidueValue
            (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
        Kbound * ‖Main‖ ^ 2 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖Main‖ ^ 2)
    (hbudget : 2 * Kbound + 2 * J ≤ S.B) : False := by
  apply W.primitive_bcc_contradiction_of_discrepancy hq
  exact (W.primitive_normalized_cyclicGoodEnergy_le hErr hresidue hMain
    hconvolution hsmall).trans hbudget

/-! ## The conductor-one branch -/

theorem Section4CharacterData.primitiveModifiedAssignment_apply_eq_one
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hQ : W.primitiveQ = 1) (p : PrimeNat) :
    W.primitiveModifiedAssignment p = 1 := by
  have hpnot : ¬(p : ℕ) ∣ W.primitiveQ := by
    intro hpdiv
    have hpdivOne : (p : ℕ) ∣ 1 := by simpa only [hQ] using hpdiv
    have hple : (p : ℕ) ≤ 1 := Nat.le_of_dvd Nat.one_pos hpdivOne
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    omega
  have hchi : W.primitiveChi = 1 := by
    apply (DirichletCharacter.eq_one_iff_conductor_eq_one).2
    exact W.primitiveChi_isPrimitive.trans hQ
  apply Subtype.ext
  have hagree := W.primitiveModifiedAssignment_agrees p hpnot
  rw [hchi] at hagree
  have harg : ((p : ℕ) : ZMod W.primitiveQ) = 1 := by
    rw [hQ]
    exact Subsingleton.elim _ _
  rw [harg, map_one] at hagree
  exact hagree

theorem Section4CharacterData.primitiveModifiedAssignment_eq_one
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hQ : W.primitiveQ = 1) : W.primitiveModifiedAssignment = 1 := by
  funext p
  exact W.primitiveModifiedAssignment_apply_eq_one hQ p

theorem Section4CharacterData.primeExtension_primitiveModified_eq_one
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hQ : W.primitiveQ = 1) (n : ℕ) :
    primeExtension W.primitiveModifiedAssignment n = 1 := by
  rw [W.primitiveModifiedAssignment_eq_one hQ]
  simp [primeExtension, primeValue]

theorem Section4CharacterData.cyclicPrimeExtensionIccPrefix_primitive_eq_natCast
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hQ : W.primitiveQ = 1) (L : ℕ)
    (a : ZMod (W.primitiveQ ^ S.k)) :
    cyclicPrimeExtensionIccPrefix W.primitiveModifiedAssignment L a = L := by
  unfold cyclicPrimeExtensionIccPrefix
  simp_rw [W.primeExtension_primitiveModified_eq_one hQ]
  simp

theorem Section4Selection.B_lt_H {C : ℝ} (S : Section4Selection C) :
    S.B < S.H := by
  have hBL : S.B < (S.params.L : ℝ) := by
    have hQ : (2 : ℝ) ≤ S.A := by exact_mod_cast S.two_le_A
    have hB0 := S.params.B_nonneg
    have hlarge := S.params.layers_large
    nlinarith
  have hpow : S.params.L < 2 ^ S.params.L :=
    S.params.L.lt_two_pow_self
  have hpowH : 2 ^ S.params.L ≤ S.H := by
    have hLpos := S.params.L_pos
    have hsel := S.params.selected_pow_le 2 (S.params.L - 1)
      (by omega) S.two_le_A
      (by omega : S.params.L - 1 < S.params.L)
    rw [show S.params.L = (S.params.L - 1) + 1 by omega,
      pow_succ]
    simpa only [Section4Selection.H, mul_comm] using hsel
  exact hBL.trans (by exact_mod_cast hpow.trans_le hpowH)

/-- For conductor one the primitive modified character is identically one,
so its normalized medium prefix energy is strictly larger than the stored
budget `B`. -/
theorem Section4CharacterData.primitiveQ_one_prefixEnergy_gt_B
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hQ : W.primitiveQ = 1) :
    S.B <
      (1 / (((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
            Complex.normSq
              (cyclicPrimeExtensionIccPrefix
                W.primitiveModifiedAssignment L a) := by
  have hgood : cyclicGoodResidues W.primitiveQ S.k S.H = Finset.univ := by
    have hpf : W.primitiveQ.primeFactors = ∅ := by simp [hQ]
    rw [cyclicGoodResidues, cyclicBadResidues, hpf]
    simp
  rw [hgood]
  simp_rw [W.cyclicPrimeExtensionIccPrefix_primitive_eq_natCast hQ]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, hQ, one_pow,
    Nat.cast_one, one_mul, nsmul_eq_mul]
  have hHpos := S.H_pos
  have hHR : (0 : ℝ) < S.H := by exact_mod_cast hHpos
  have hmem : S.H + 1 ∈ Finset.Ioc S.H (2 * S.H) := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum :
      Complex.normSq ((S.H + 1 : ℕ) : ℂ) ≤
        ∑ x ∈ Finset.Ioc S.H (2 * S.H), Complex.normSq (x : ℂ) := by
    exact Finset.single_le_sum
      (s := Finset.Ioc S.H (2 * S.H))
      (f := fun x : ℕ ↦ Complex.normSq (x : ℂ))
      (fun x _hx ↦ Complex.normSq_nonneg (x : ℂ)) hmem
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ 1 / S.H by positivity)
  have hstrict :
      (S.H : ℝ) <
        (1 / (S.H : ℝ)) * Complex.normSq ((S.H + 1 : ℕ) : ℂ) := by
    rw [Complex.normSq_natCast, one_div, inv_mul_eq_div,
      lt_div_iff₀ hHR]
    push_cast
    nlinarith
  exact S.B_lt_H.trans (hstrict.trans_le hmul)

/-- One shifted-convolution endpoint covering both possible conductors.  For
`primitiveQ > 1` it invokes the primitive BCC argument; for `primitiveQ = 1`
the deterministic energy of the constant character already exceeds `S.B`. -/
theorem Section4CharacterData.primitive_contradiction_of_shiftedConvolution_all
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {sigma Main : ℂ} {Err Kbound J : ℝ}
    (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod (W.primitiveQ ^ S.k),
      ‖EulerResidue.residueLSeries W.primitiveCorrectionHom b sigma - Main‖ ≤ Err)
    (hMain : 0 < ‖Main‖)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.primitiveCorrectionHom sigma
            W.primitiveModifiedResidueValue
            (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
        Kbound * ‖Main‖ ^ 2 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖Main‖ ^ 2)
    (hbudget : 2 * Kbound + 2 * J ≤ S.B) : False := by
  by_cases hQ : W.primitiveQ = 1
  · have hupper :=
      (W.primitive_normalized_cyclicGoodEnergy_le hErr hresidue hMain
        hconvolution hsmall).trans hbudget
    exact (not_lt_of_ge hupper) (W.primitiveQ_one_prefixEnergy_gt_B hQ)
  · apply W.primitive_contradiction_of_shiftedConvolution
      (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne W.primitiveQ))
        (Ne.symm hQ))
      hErr hresidue hMain hconvolution hsmall hbudget

end

end Erdos67
