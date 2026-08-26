import ErdosProblems.Erdos67b.Section4Probability
import ErdosProblems.Erdos67b.Section3UnitCircle
import ErdosProblems.Erdos67b.TwistSeparation
import ErdosProblems.Erdos67b.WeightedTransfer
import ErdosProblems.Erdos67b.CorrectionTransport
import ErdosProblems.Erdos67b.BCCPrefix
import ErdosProblems.Erdos67b.CharacterPrimePatch
import ErdosProblems.Erdos67b.Section4ParameterHierarchy

/-!
# Assembly of Tao's Section 4 parameter hierarchy

This file performs the deterministic parameter choices and the final
probability-space sample selection which sit between the two-scale
pretentiousness theorem and the weighted BCC argument.  The analytic inputs
remain visible as theorem arguments: an eventual two-scale twist-separation
theorem is consumed here, while the output records the actual character and
frequency witnesses attached to one and the same compact character.
-/

open scoped ENNReal
open MeasureTheory

namespace Erdos67b

noncomputable section

/-! ## Explicit parameters -/

/-- The Markov cutoff.  Its factor `16` leaves a factor-two margin after the
two-scale union bound. -/
def section4B (C : ℝ) : ℝ := 16 * C ^ 2 + 1

/-- The first natural strictly above the Markov cutoff. -/
def section4H (C : ℝ) : ℕ := Nat.ceil (section4B C) + 1

/-- A correlation tolerance which works uniformly at every dyadic scale. -/
def section4Eta (C : ℝ) : ℝ :=
  ((section4H C : ℝ) - section4B C) /
    (4 * (section4H C : ℝ) ^ 2)

/-- A dyadic exponent large enough to absorb the `3H` boundary error in
the unit-circle reduction of translated correlations. -/
def section4TranslationK (C : ℝ) : ℕ :=
  Nat.ceil
      (12 * (section4H C : ℝ) ^ 3 /
        ((section4H C : ℝ) - section4B C)) + 1

/-- Eventual twist separation in the dyadic exponent.  This is the exact
shape in which a quantitative Vinogradov--Korobov theorem is consumed by the
assembly: no unproved analytic assertion is hidden in a definition. -/
def EventuallyTwoScaleTwistSeparation : Prop :=
  ∀ A D : ℕ, 2 ≤ A → 0 < D →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      TwoScaleTwistSeparationConclusion A (4 ^ K) D

/-- Parameters chosen only after the one-scale Elliott theorem has fixed its
conductor cutoff `A`.  In the intended application `H` is first made large
enough for the Euler/BCC constant, `k` is then made large enough to suppress
the bad residue classes, and finally `D` is made large enough for the Taylor
transfer.  The dyadic scale is deliberately absent and is chosen last. -/
structure Section4LateParameters (A : ℕ) where
  B : ℝ
  params : Section4BCCParameters A B

def Section4LateParameters.H {A : ℕ} (P : Section4LateParameters A) : ℕ :=
  P.params.H

def Section4LateParameters.k {A : ℕ} (P : Section4LateParameters A) : ℕ :=
  P.params.k

def Section4LateParameters.D {A : ℕ} (P : Section4LateParameters A) : ℕ :=
  P.params.D

theorem Section4LateParameters.H_pos {A : ℕ} (P : Section4LateParameters A) :
    0 < P.H := P.params.H_pos

theorem Section4LateParameters.k_pos {A : ℕ} (P : Section4LateParameters A) :
    0 < P.k := P.params.k_pos

theorem Section4LateParameters.D_pos {A : ℕ} (P : Section4LateParameters A) :
    0 < P.D := P.params.D_pos

theorem Section4LateParameters.taylorScale_le
    {A : ℕ} (P : Section4LateParameters A) : 32 * P.H ^ 2 ≤ P.D :=
  P.params.taylorScale_le

/-- Forget the quantitative BCC constant while retaining the late choices
needed by the probability-space selection.  The full parameter package is
kept by the caller for the eventual cardinal contradiction. -/
def Section4BCCParameters.toLate
    {A : ℕ} {B : ℝ} (P : Section4BCCParameters A B) :
    Section4LateParameters A where
  B := B
  params := P

/-- The data selected in Section 4.  In particular, `nearby` retains both
pretentious approximations and hence guarantees that all character,
frequency, and correction-factor data used later come from a single sample.
-/
structure Section4Selection (C : ℝ) where
  A : ℕ
  K : ℕ
  B : ℝ
  params : Section4BCCParameters A B
  sample : CompactCircleCharacter
  two_le_A : 2 ≤ A
  K_pos : 0 < K
  A_le_two_pow_K : A ≤ 2 ^ K
  nearby : HasNearbyTwoScalePretentiousPair A (4 ^ K) params.D sample

def Section4Selection.H {C : ℝ} (S : Section4Selection C) : ℕ := S.params.H

def Section4Selection.k {C : ℝ} (S : Section4Selection C) : ℕ := S.params.k

def Section4Selection.D {C : ℝ} (S : Section4Selection C) : ℕ := S.params.D

theorem Section4Selection.H_pos {C : ℝ} (S : Section4Selection C) : 0 < S.H :=
  S.params.H_pos

theorem Section4Selection.k_pos {C : ℝ} (S : Section4Selection C) : 0 < S.k :=
  S.params.k_pos

theorem Section4Selection.D_pos {C : ℝ} (S : Section4Selection C) : 0 < S.D :=
  S.params.D_pos

theorem Section4Selection.taylorScale_le {C : ℝ} (S : Section4Selection C) :
    32 * S.H ^ 2 ≤ S.D := S.params.taylorScale_le

/-- The two character approximations displayed as dependent data.  Keeping
these witnesses in one structure prevents a later transfer step from
silently choosing the large- and small-scale approximations from different
samples. -/
structure Section4CharacterData {C : ℝ} (S : Section4Selection C) where
  q : ℕ
  q_pos : 0 < q
  q_le : q ≤ S.A
  chi : DirichletCharacter ℂ q
  t : ℝ
  t_bound : |t| ≤ (S.A : ℝ) * ((4 ^ S.K) ^ S.D : ℕ)
  distance_large :
    pretentiousDistSqToTwist (compactCharacterNatValue S.sample) chi t
      ((4 ^ S.K) ^ S.D) < S.A
  qSmall : ℕ
  qSmall_pos : 0 < qSmall
  qSmall_le : qSmall ≤ S.A
  chiSmall : DirichletCharacter ℂ qSmall
  tSmall : ℝ
  tSmall_bound : |tSmall| ≤ (S.A : ℝ) * ((4 ^ S.K : ℕ) : ℝ)
  distance_small :
    pretentiousDistSqToTwist (compactCharacterNatValue S.sample)
      chiSmall tSmall (4 ^ S.K) < S.A
  frequencies_near : |tSmall - t| < ((4 ^ S.K : ℕ) : ℝ)

theorem Section4Selection.exists_characterData {C : ℝ}
    (S : Section4Selection C) : Nonempty (Section4CharacterData S) := by
  rcases S.nearby with
    ⟨q, hq, hqA, chi, t, ht, hdist,
      qSmall, hqSmall, hqSmallA, chiSmall, tSmall, htSmall,
      hdistSmall, hnear⟩
  exact ⟨{
    q := q
    q_pos := hq
    q_le := hqA
    chi := chi
    t := t
    t_bound := ht
    distance_large := hdist
    qSmall := qSmall
    qSmall_pos := hqSmall
    qSmall_le := hqSmallA
    chiSmall := chiSmall
    tSmall := tSmall
    tSmall_bound := htSmall
    distance_small := hdistSmall
    frequencies_near := hnear
  }⟩

/-! ## Prime-coordinate factorization data -/

/-- Prime coordinates of the selected compact character. -/
def compactCharacterPrimeAssignment
    (g : CompactCircleCharacter) : PrimeAssignment :=
  primeAssignmentOfCompactCircleCharacter g

@[simp] theorem compactCharacterPrimeAssignment_apply
    (g : CompactCircleCharacter) (p : PrimeNat) :
    compactCharacterPrimeAssignment g p = g.1 ⟨p, p.2.pos⟩ := rfl

/-- Circle-valued prime coordinates `p ↦ p^(it)`. -/
def archimedeanPrimeAssignment (t : ℝ) : PrimeAssignment :=
  fun p ↦ ⟨archimedeanTwist t p, by
    change archimedeanTwist t p ∈ Metric.sphere 0 1
    exact mem_sphere_zero_iff_norm.2 (norm_archimedeanTwist p.2.pos t)⟩

@[simp] theorem archimedeanPrimeAssignment_coe
    (t : ℝ) (p : PrimeNat) :
    (archimedeanPrimeAssignment t p : ℂ) = archimedeanTwist t p := rfl

/-- Exact factorization of a selected compact sample into the modified
character, the Archimedean phase, and the completely multiplicative
correction. -/
theorem primeExtension_compact_modified_factorization
    (g : CompactCircleCharacter) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    primeExtension (compactCharacterPrimeAssignment g) n =
      primeExtension
          (modifiedAssignment (compactCharacterPrimeAssignment g)
            (patchedDirichletPrimeAssignment chi)
            (archimedeanPrimeAssignment t) (levelPrimeFinset q)) n *
        primeExtension (archimedeanPrimeAssignment t) n *
          primeExtension
            (correctionAssignment (compactCharacterPrimeAssignment g)
              (patchedDirichletPrimeAssignment chi)
              (archimedeanPrimeAssignment t) (levelPrimeFinset q)) n := by
  exact primeExtension_modified_factorization
    (compactCharacterPrimeAssignment g)
    (patchedDirichletPrimeAssignment chi)
    (archimedeanPrimeAssignment t) (levelPrimeFinset q) n

/-- Canonically named assignment data for one selected character-frequency
witness. -/
structure WitnessAssignmentData (g : CompactCircleCharacter) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) where
  base : PrimeAssignment := compactCharacterPrimeAssignment g
  model : PrimeAssignment := patchedDirichletPrimeAssignment chi
  arch : PrimeAssignment := archimedeanPrimeAssignment t
  exceptional : Finset PrimeNat := levelPrimeFinset q
  base_eq : base = compactCharacterPrimeAssignment g := by rfl
  model_eq : model = patchedDirichletPrimeAssignment chi := by rfl
  arch_eq : arch = archimedeanPrimeAssignment t := by rfl
  exceptional_eq : exceptional = levelPrimeFinset q := by rfl
  factorization : ∀ n : ℕ,
    primeExtension base n =
      primeExtension (modifiedAssignment base model arch exceptional) n *
        primeExtension arch n *
          primeExtension (correctionAssignment base model arch exceptional) n

def WitnessAssignmentData.correction
    {g : CompactCircleCharacter} {q : ℕ}
    {chi : DirichletCharacter ℂ q} {t : ℝ}
    (W : WitnessAssignmentData g q chi t) : PrimeAssignment :=
  correctionAssignment W.base W.model W.arch W.exceptional

/-- The modified-character part of one exact witness factorization. -/
def WitnessAssignmentData.modified
    {g : CompactCircleCharacter} {q : ℕ}
    {chi : DirichletCharacter ℂ q} {t : ℝ}
    (W : WitnessAssignmentData g q chi t) : PrimeAssignment :=
  modifiedAssignment W.base W.model W.arch W.exceptional

/-- The modified assignment agrees with its Dirichlet-character model at
every prime away from the supplied level. -/
theorem WitnessAssignmentData.modified_agreesWithCharacterAway
    {g : CompactCircleCharacter} {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} {t : ℝ}
    (W : WitnessAssignmentData g q chi t) :
    AgreesWithCharacterAway W.modified chi := by
  intro p hpq
  rw [WitnessAssignmentData.modified, modifiedAssignment_of_not_mem]
  · rw [W.model_eq]
    exact patchedDirichletPrimeAssignment_coe_of_not_dvd chi p hpq
  · rw [W.exceptional_eq, mem_levelPrimeFinset_iff (NeZero.ne q)]
    exact hpq

/-- The correction in the exact zero-preserving form consumed by the Euler
residue and cyclic-good weighted-transfer theorem. -/
def WitnessAssignmentData.correctionHom
    {g : CompactCircleCharacter} {q : ℕ}
    {chi : DirichletCharacter ℂ q} {t : ℝ}
    (W : WitnessAssignmentData g q chi t) : ℕ →*₀ ℂ :=
  zeroPreservingPrimeExtension W.correction

theorem WitnessAssignmentData.correctionHom_hasUnitNorm
    {g : CompactCircleCharacter} {q : ℕ}
    {chi : DirichletCharacter ℂ q} {t : ℝ}
    (W : WitnessAssignmentData g q chi t) :
    EulerResidue.HasUnitNorm W.correctionHom :=
  zeroPreservingPrimeExtension_hasUnitNorm W.correction

def witnessAssignmentData
    (g : CompactCircleCharacter) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    WitnessAssignmentData g q chi t where
  factorization := primeExtension_compact_modified_factorization g chi t

def Section4CharacterData.largeAssignmentData
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    WitnessAssignmentData S.sample W.q W.chi W.t :=
  witnessAssignmentData S.sample W.chi W.t

def Section4CharacterData.smallAssignmentData
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    WitnessAssignmentData S.sample W.qSmall W.chiSmall W.tSmall :=
  witnessAssignmentData S.sample W.chiSmall W.tSmall

def Section4CharacterData.largeCorrectionHom
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) : ℕ →*₀ ℂ :=
  W.largeAssignmentData.correctionHom

def Section4CharacterData.largeModifiedAssignment
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    PrimeAssignment :=
  W.largeAssignmentData.modified

theorem Section4CharacterData.largeModifiedAssignment_agrees
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] :
    AgreesWithCharacterAway W.largeModifiedAssignment W.chi :=
  W.largeAssignmentData.modified_agreesWithCharacterAway

theorem Section4CharacterData.largeCorrectionHom_hasUnitNorm
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    EulerResidue.HasUnitNorm W.largeCorrectionHom :=
  W.largeAssignmentData.correctionHom_hasUnitNorm

/-- The correction is exactly one at every prime dividing the selected
Dirichlet-character level.  This is the normalization required by the
nonunit gcd-reduced weighted-transfer theorem. -/
theorem Section4CharacterData.largeCorrectionHom_prime_dvd
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (p : ℕ) (hp : p.Prime) (hpq : p ∣ W.q) :
    W.largeCorrectionHom p = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  let pp : PrimeNat := ⟨p, hp⟩
  have hmem : pp ∈ levelPrimeFinset W.q :=
    (mem_levelPrimeFinset_iff W.q_pos.ne' pp).2 hpq
  rw [Section4CharacterData.largeCorrectionHom,
    WitnessAssignmentData.correctionHom,
    zeroPreservingPrimeExtension_apply_of_ne_zero _ hp0]
  change (primeExtension W.largeAssignmentData.correction (pp : ℕ) : ℂ) = 1
  rw [primeExtension_prime]
  have hc : W.largeAssignmentData.correction pp = 1 := by
    unfold WitnessAssignmentData.correction
    apply correctionAssignment_of_mem
    simpa only [WitnessAssignmentData.exceptional_eq] using hmem
  simpa [pp] using congrArg Subtype.val hc

def Section4CharacterData.smallCorrectionHom
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) : ℕ →*₀ ℂ :=
  W.smallAssignmentData.correctionHom

theorem Section4CharacterData.smallCorrectionHom_hasUnitNorm
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    EulerResidue.HasUnitNorm W.smallCorrectionHom :=
  W.smallAssignmentData.correctionHom_hasUnitNorm

theorem Section4CharacterData.large_primeExtension_factorization
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) (n : ℕ) :
    primeExtension (compactCharacterPrimeAssignment S.sample) n =
      primeExtension
          (modifiedAssignment (compactCharacterPrimeAssignment S.sample)
            (patchedDirichletPrimeAssignment W.chi)
            (archimedeanPrimeAssignment W.t) (levelPrimeFinset W.q)) n *
        primeExtension (archimedeanPrimeAssignment W.t) n *
          primeExtension
            (correctionAssignment (compactCharacterPrimeAssignment S.sample)
              (patchedDirichletPrimeAssignment W.chi)
              (archimedeanPrimeAssignment W.t) (levelPrimeFinset W.q)) n :=
  primeExtension_compact_modified_factorization S.sample W.chi W.t n

theorem Section4CharacterData.small_primeExtension_factorization
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) (n : ℕ) :
    primeExtension (compactCharacterPrimeAssignment S.sample) n =
      primeExtension
          (modifiedAssignment (compactCharacterPrimeAssignment S.sample)
            (patchedDirichletPrimeAssignment W.chiSmall)
            (archimedeanPrimeAssignment W.tSmall) (levelPrimeFinset W.qSmall)) n *
        primeExtension (archimedeanPrimeAssignment W.tSmall) n *
          primeExtension
            (correctionAssignment (compactCharacterPrimeAssignment S.sample)
              (patchedDirichletPrimeAssignment W.chiSmall)
              (archimedeanPrimeAssignment W.tSmall) (levelPrimeFinset W.qSmall)) n :=
  primeExtension_compact_modified_factorization S.sample W.chiSmall W.tSmall n

theorem section4B_pos (C : ℝ) : 0 < section4B C := by
  unfold section4B
  positivity

theorem section4B_lt_section4H (C : ℝ) :
    section4B C < (section4H C : ℝ) := by
  unfold section4H
  have hB0 : 0 ≤ section4B C := (section4B_pos C).le
  have hceil : section4B C ≤ (Nat.ceil (section4B C) : ℝ) :=
    Nat.le_ceil _
  push_cast
  linarith

theorem section4H_pos (C : ℝ) : 0 < section4H C := by
  unfold section4H
  omega

theorem section4Eta_pos (C : ℝ) : 0 < section4Eta C := by
  unfold section4Eta
  have hH : (0 : ℝ) < section4H C := by
    exact_mod_cast section4H_pos C
  exact div_pos (sub_pos.mpr (section4B_lt_section4H C))
    (mul_pos (by norm_num) (sq_pos_of_pos hH))

/-- A proved polynomial-height prime-correlation theorem, uniformly in the
finite conductor cutoff, supplies the eventual separation input above. -/
theorem eventuallyTwoScaleTwistSeparation_of_polynomialHeight
    (hVK : ∀ A D : ℕ, 2 ≤ A → 0 < D →
      PolynomialHeightPrimeCorrelationBound A D (2 * A : ℕ)) :
    EventuallyTwoScaleTwistSeparation := by
  intro A D hA hD
  obtain ⟨Y₀, hY₀, hsep⟩ :=
    eventually_twoScaleTwistSeparationConclusion_of_polynomialHeightBound
      hD (hVK A D hA hD)
  refine ⟨Y₀, ?_⟩
  intro K hY₀K
  apply hsep (4 ^ K)
  calc
    Y₀ ≤ K := hY₀K
    _ ≤ 2 ^ K := K.lt_two_pow_self.le
    _ ≤ 4 ^ K := Nat.pow_le_pow_left (by norm_num) K

theorem Section4CharacterData.primeFactors_card_le_A
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    W.q.primeFactors.card ≤ S.A := by
  have hsubset : W.q.primeFactors ⊆ Finset.Icc 1 W.q := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_Icc.mpr
      ⟨hpPrime.one_le, Nat.le_of_dvd W.q_pos (Nat.dvd_of_mem_primeFactors hp)⟩
  calc
    W.q.primeFactors.card ≤ (Finset.Icc 1 W.q).card :=
      Finset.card_le_card hsubset
    _ = W.q := by simp
    _ ≤ S.A := W.q_le

/-- For the actually selected level, the omitted-residue coefficient in the
BCC bridge is strictly below one before multiplication by its pointwise
energy bound. -/
theorem Section4CharacterData.badResidueNumerator_lt_two_pow_k
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (hscale : 2 * S.H * S.A < 2 ^ S.k) :
    2 * S.H * W.q.primeFactors.card < 2 ^ S.k := by
  calc
    2 * S.H * W.q.primeFactors.card ≤ 2 * S.H * S.A := by
      exact Nat.mul_le_mul_left (2 * S.H) W.primeFactors_card_le_A
    _ < 2 ^ S.k := hscale

/-! ## Direct weighted-transfer consumer -/

/-- Apply the arbitrary-class, gcd-reduced Euler transfer directly to the
large-scale correction selected above.  The normalization at primes dividing
the level and the unit-norm hypothesis are discharged by the assignment
package; every genuinely analytic estimate remains an explicit argument. -/
theorem Section4CharacterData.normalized_cyclicGoodEnergy_le_legacy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q]
    {sigma : ℂ} (hsigma : 1 < sigma.re)
    (Singular : ℂ) (E₀ E delta : ℕ → ℝ) (Err Kbound : ℝ)
    (hprincipal : ∀ r, r ∣ W.q ^ S.k → r ≠ 0 →
      ‖(r.totient : ℂ)⁻¹ *
          EulerResidue.principalTwistSeries W.largeCorrectionHom r sigma -
          Singular / (r : ℂ)‖ ≤ E₀ r)
    (hnonprincipal : ∀ r, r ∣ W.q ^ S.k → r ≠ 0 →
      EulerResidue.NonprincipalTwistsBounded
        W.largeCorrectionHom r sigma (E r))
    (hfactor : ∀ d, d ∣ W.q ^ S.k → d ≠ 0 →
      ‖(d : ℂ) ^ (1 - sigma) - 1‖ ≤ delta d)
    (hbudget : ∀ d, d ∣ W.q ^ S.k → d ≠ 0 →
      ‖EulerResidue.residueScale W.largeCorrectionHom d sigma‖ *
          eulerResidueError (W.q ^ S.k / d)
            (E₀ (W.q ^ S.k / d)) (E (W.q ^ S.k / d)) +
        ‖Singular / ((W.q ^ S.k : ℕ) : ℂ)‖ * delta d ≤ Err)
    (classOf : ℕ → ZMod (W.q ^ S.k) → ZMod (W.q ^ S.k))
    (prefixFamily : ℕ → ZMod (W.q ^ S.k) → ℂ)
    (hMain : 0 < ‖Singular / ((W.q ^ S.k : ℕ) : ℂ)‖)
    (hhalf : 2 * Err ≤ ‖Singular / ((W.q ^ S.k : ℕ) : ℂ)‖)
    (hweighted : ∀ L ∈ Finset.Ioc S.H (2 * S.H),
      ‖eulerMappedResidueWeightedEnergy W.largeCorrectionHom sigma
          (cyclicGoodResidues W.q S.k S.H)
          (classOf L) (prefixFamily L)‖ ≤
        Kbound * ‖Singular / ((W.q ^ S.k : ℕ) : ℂ)‖ *
          ((W.q ^ S.k : ℕ) : ℝ)) :
    (1 / (((W.q ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.q S.k S.H,
            Complex.normSq (prefixFamily L a) ≤ 2 * Kbound := by
  exact normalized_medium_cyclicGoodResidueEnergy_pow_normalizedMain_le_two_mul
    S.k W.largeCorrectionHom_hasUnitNorm hsigma Singular E₀ E delta Err Kbound
    W.largeCorrectionHom_prime_dvd hprincipal hnonprincipal hfactor hbudget
    classOf prefixFamily S.H S.H_pos hMain hhalf hweighted

/-- The modified-character values on the actual cyclic group used by BCC. -/
def Section4CharacterData.largeModifiedResidueValue
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] : ZMod (W.q ^ S.k) → ℂ :=
  fun a ↦ (primeExtension W.largeModifiedAssignment a.val : ℂ)

theorem Section4CharacterData.norm_largeModifiedResidueValue_le_one
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] (a : ZMod (W.q ^ S.k)) :
    ‖W.largeModifiedResidueValue a‖ ≤ 1 := by
  simpa only [Section4CharacterData.largeModifiedResidueValue] using
    (norm_primeExtension_coe W.largeModifiedAssignment a.val).le

@[simp] theorem Section4CharacterData.shiftedResiduePrefix_largeModified_eq
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] (L : ℕ) (a : ZMod (W.q ^ S.k)) :
    shiftedResiduePrefix W.largeModifiedResidueValue L a =
      cyclicPrimeExtensionIccPrefix W.largeModifiedAssignment L a := by
  rfl

/-- Truthful equation-(15) transfer for the selected correction and modified
character.  The residue series remains inside the shifted sum until the
uniform common-main estimate is applied.  Consequently this statement feeds
the exact modified-character prefix energy consumed by BCC. -/
theorem Section4CharacterData.normalized_cyclicGoodEnergy_le
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q]
    {sigma Main : ℂ} {Err Kbound J : ℝ}
    (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod (W.q ^ S.k),
      ‖EulerResidue.residueLSeries W.largeCorrectionHom b sigma - Main‖ ≤ Err)
    (hMain : 0 < ‖Main‖)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.largeCorrectionHom sigma
            W.largeModifiedResidueValue
            (cyclicGoodResidues W.q S.k S.H) L ≤
        Kbound * ‖Main‖ ^ 2 * ((W.q ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖Main‖ ^ 2) :
    (1 / (((W.q ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.q S.k S.H,
            Complex.normSq
              (cyclicPrimeExtensionIccPrefix
                W.largeModifiedAssignment L a) ≤
      2 * Kbound + 2 * J := by
  simpa only [W.shiftedResiduePrefix_largeModified_eq] using
    normalized_medium_shiftedResiduePrefixEnergy_le hErr hresidue
      W.largeModifiedResidueValue W.norm_largeModifiedResidueValue_le_one
      (cyclicGoodResidues W.q S.k S.H) S.H S.H_pos hMain
      hconvolution hsmall

/-- The direct full-divisor BCC contradiction for the modified character
attached to a selected witness.  All divisor layers and their unit
coefficients are internal to `fullDivisor_bcc_contradiction_of_discrepancy`;
the only energy hypothesis is the normalized energy of the actual modified
multiplicative prefixes on the translated good residue classes. -/
theorem Section4CharacterData.bcc_contradiction_of_discrepancy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] (hchi : W.chi.IsPrimitive) (hq : 1 < W.q)
    (hdiscrepancy :
      (1 / (((W.q ^ S.k : ℕ) : ℝ) * S.H)) *
          ∑ L ∈ Finset.Ioc S.H (2 * S.H),
            ∑ a ∈ cyclicGoodResidues W.q S.k S.H,
              Complex.normSq
                (cyclicPrimeExtensionIccPrefix
                  W.largeModifiedAssignment L a) ≤ S.B) : False := by
  apply S.params.fullDivisor_bcc_contradiction (by omega) W.q_le
    W.largeModifiedAssignment W.chi hchi W.largeModifiedAssignment_agrees
  change
    (1 / (((W.q ^ S.k : ℕ) : ℝ) * S.H)) *
        ∑ M ∈ Finset.Ioc S.H (2 * S.H),
          ∑ a ∈ cyclicGoodResidues W.q S.k S.H,
            Complex.normSq
              (∑ m ∈ Finset.Icc 1 M,
                (primeExtension W.largeModifiedAssignment
                  (a + (m : ZMod (W.q ^ S.k))).val : ℂ)) ≤ S.B
  simpa only [cyclicPrimeExtensionIccPrefix] using hdiscrepancy

/-- Corrected transfer-to-BCC composition.  This is the non-legacy Section 4
consumer: the analytic side supplies Tao's shifted convolution energy and a
uniform residue-series approximation, while the stored BCC parameter package
supplies every layer-count and exceptional-residue inequality. -/
theorem Section4CharacterData.contradiction_of_shiftedConvolution
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    [NeZero W.q] (hchi : W.chi.IsPrimitive) (hq : 1 < W.q)
    {sigma Main : ℂ} {Err Kbound J : ℝ}
    (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod (W.q ^ S.k),
      ‖EulerResidue.residueLSeries W.largeCorrectionHom b sigma - Main‖ ≤ Err)
    (hMain : 0 < ‖Main‖)
    (hconvolution :
      ∑ L ∈ Finset.Ioc S.H (2 * S.H),
          shiftedResidueConvolutionEnergy W.largeCorrectionHom sigma
            W.largeModifiedResidueValue
            (cyclicGoodResidues W.q S.k S.H) L ≤
        Kbound * ‖Main‖ ^ 2 * ((W.q ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖Main‖ ^ 2)
    (hbudget : 2 * Kbound + 2 * J ≤ S.B) : False := by
  apply W.bcc_contradiction_of_discrepancy hchi hq
  exact (W.normalized_cyclicGoodEnergy_le hErr hresidue hMain
    hconvolution hsmall).trans hbudget

/-! ## Probability and correlation arithmetic -/

/-- The two-scale exceptional probability is strictly below one for the
explicit Markov cutoff. -/
theorem section4_exceptionalProbability_lt_one (C : ℝ) :
    2 * ENNReal.ofReal (4 * C ^ 2 / section4B C) < 1 := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_lt_one]
  have hB := section4B_pos C
  rw [show (2 : ℝ) * (4 * C ^ 2 / section4B C) =
      8 * C ^ 2 / section4B C by ring]
  rw [div_lt_one hB]
  unfold section4B
  nlinarith [sq_nonneg C]

/-- The elementary lower bound on the dyadic reciprocal mass makes the
Section 3 threshold valid at every positive scale. -/
theorem section4_threshold
    (C : ℝ) {K : ℕ} (hK : 0 < K) :
    section4Eta C * Real.log ((2 ^ K : ℕ) : ℝ) <
      (((section4H C : ℝ) - section4B C) *
          dyadicCorrelationWeight K) /
        (section4H C : ℝ) ^ 2 := by
  have hHB : 0 < (section4H C : ℝ) - section4B C :=
    sub_pos.mpr (section4B_lt_section4H C)
  have hHR : 0 < (section4H C : ℝ) := by
    exact_mod_cast section4H_pos C
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoLt : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hweight := half_mul_le_dyadicCorrelationWeight K
  rw [Nat.cast_pow, Real.log_pow]
  unfold section4Eta
  have hden : 0 < (section4H C : ℝ) ^ 2 := sq_pos_of_pos hHR
  calc
    (((section4H C : ℝ) - section4B C) /
          (4 * (section4H C : ℝ) ^ 2)) *
        ((K : ℝ) * Real.log (2 : ℝ)) <
        (((section4H C : ℝ) - section4B C) /
          (4 * (section4H C : ℝ) ^ 2)) * ((K : ℝ) * 2) := by
      apply mul_lt_mul_of_pos_left
      · apply mul_lt_mul_of_pos_left (hlogTwoLt.trans (by norm_num)) hKR
      · exact div_pos hHB (mul_pos (by norm_num) hden)
    _ = ((section4H C : ℝ) - section4B C) * ((K : ℝ) / 2) /
          (section4H C : ℝ) ^ 2 := by ring
    _ ≤ ((section4H C : ℝ) - section4B C) *
          dyadicCorrelationWeight K / (section4H C : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight hHB.le) hden.le

theorem section4TranslationK_pos (C : ℝ) : 0 < section4TranslationK C := by
  unfold section4TranslationK
  omega

/-- At every exponent above `section4TranslationK`, the spare half of the
dyadic reciprocal-mass lower bound absorbs the complete `3H` translation
error. -/
theorem section4_threshold_withTranslationError
    (C : ℝ) {K : ℕ} (hK : 0 < K)
    (hlarge : section4TranslationK C ≤ K) :
    section4Eta C * Real.log ((2 ^ K : ℕ) : ℝ) +
        3 * (section4H C : ℝ) <
      (((section4H C : ℝ) - section4B C) *
          dyadicCorrelationWeight K) /
        (section4H C : ℝ) ^ 2 := by
  let H : ℝ := section4H C
  let gap : ℝ := H - section4B C
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast section4H_pos C
  have hgap : 0 < gap := by
    dsimp [gap, H]
    exact sub_pos.mpr (section4B_lt_section4H C)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hlogTwoLt : Real.log (2 : ℝ) < 1 := by
    have hlog := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (by norm_num)
    norm_num at hlog ⊢
    exact hlog
  have hceil :
      12 * H ^ 3 / gap ≤
        (Nat.ceil (12 * H ^ 3 / gap) : ℝ) := Nat.le_ceil _
  have hceilSucc :
      (Nat.ceil (12 * H ^ 3 / gap) : ℝ) <
        (section4TranslationK C : ℕ) := by
    unfold section4TranslationK
    dsimp [H, gap]
    push_cast
    linarith
  have hTK : (section4TranslationK C : ℝ) ≤ K := by
    exact_mod_cast hlarge
  have hxK : 12 * H ^ 3 / gap < (K : ℝ) :=
    hceil.trans_lt (hceilSucc.trans_le hTK)
  have hxKmul : 12 * H ^ 3 < (K : ℝ) * gap := by
    exact (div_lt_iff₀ hgap).mp hxK
  have heta :
      section4Eta C * Real.log ((2 ^ K : ℕ) : ℝ) <
        gap * ((K : ℝ) / 4) / H ^ 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    unfold section4Eta
    change (gap / (4 * H ^ 2)) * ((K : ℝ) * Real.log 2) < _
    calc
      (gap / (4 * H ^ 2)) * ((K : ℝ) * Real.log 2) <
          (gap / (4 * H ^ 2)) * ((K : ℝ) * 1) := by
        apply mul_lt_mul_of_pos_left
        · exact mul_lt_mul_of_pos_left hlogTwoLt hKreal
        · positivity
      _ = gap * ((K : ℝ) / 4) / H ^ 2 := by ring
  have htranslation :
      3 * H < gap * ((K : ℝ) / 4) / H ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hH)).2
    nlinarith
  have hweight := half_mul_le_dyadicCorrelationWeight K
  change section4Eta C * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * H <
    gap * dyadicCorrelationWeight K / H ^ 2
  calc
    section4Eta C * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * H <
        gap * ((K : ℝ) / 4) / H ^ 2 +
          gap * ((K : ℝ) / 4) / H ^ 2 := add_lt_add heta htranslation
    _ = gap * ((K : ℝ) / 2) / H ^ 2 := by ring
    _ ≤ gap * dyadicCorrelationWeight K / H ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight hgap.le) (sq_nonneg H)

/-! ## Unit-circle Elliott at two scales -/

/-- Apply the proved unit-circle Section 3 endpoint at `4^K` and
`(4^K)^D`, retaining both witnesses on the same sample. -/
theorem UnitCircleLogElliott.exists_highProbability_twoScalePretentiousSet
    (helliott : UnitCircleLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H D : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hD : 0 < D)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        η * Real.log ((2 ^ (K * D) : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight (K * D) / (H : ℝ) ^ 2 →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            2 * ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G, HasTwoScalePretentiousPair A (4 ^ K) D g := by
  obtain ⟨A₀, hA₀, hgood⟩ :=
    helliott.exists_highProbability_pretentiousSet
      μ C B η H hBpos hH hBH hη hbound
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hsmall hlarge
  have hKD : 0 < K * D := Nat.mul_pos hK hD
  have hKleKD : K ≤ K * D := by
    have hDone : 1 ≤ D := hD
    nlinarith
  have hAKD : A ≤ 2 ^ (K * D) :=
    hAK.trans (Nat.pow_le_pow_right (by omega) hKleKD)
  obtain ⟨Glarge, hGlarge, hμlarge, hlargeWitness⟩ :=
    hgood A (K * D) hA hAKD hKD hlarge
  obtain ⟨Gsmall, hGsmall, hμsmall, hsmallWitness⟩ :=
    hgood A K hA hAK hK hsmall
  refine ⟨Glarge ∩ Gsmall, hGlarge.inter hGsmall,
    measure_compl_inter_le_two (μ : Measure CompactCircleCharacter)
      (ENNReal.ofReal (4 * C ^ 2 / B)) hμlarge hμsmall, ?_⟩
  intro g hg
  constructor
  · simpa only [pow_mul] using hlargeWitness g hg.1
  · exact hsmallWitness g hg.2

theorem UnitCircleLogElliott.exists_highProbability_nearbyTwoScaleSet
    (helliott : UnitCircleLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H D : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hD : 0 < D)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        η * Real.log ((2 ^ (K * D) : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight (K * D) / (H : ℝ) ^ 2 →
        TwoScaleTwistSeparationConclusion A (4 ^ K) D →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            2 * ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G, HasNearbyTwoScalePretentiousPair A (4 ^ K) D g := by
  obtain ⟨A₀, hA₀, hgood⟩ :=
    helliott.exists_highProbability_twoScalePretentiousSet
      μ C B η H D hBpos hH hBH hη hD hbound
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hsmall hlarge hsep
  obtain ⟨G, hG, hμG, hpair⟩ := hgood A K hA hAK hK hsmall hlarge
  exact ⟨G, hG, hμG, fun g hg ↦ (hpair g hg).nearby hsep⟩

/-! ## Selection of one common sample -/

/-- Correctly ordered Section 4 selection.  The one-scale Elliott theorem
first fixes `A`; only then does `late` choose the BCC prefix length, its
prime-power exponent, and the Taylor separation exponent.  The twist
threshold and the dyadic scale `K` are chosen afterward. -/
theorem exists_late_section4Selection_of_not_stochastic
    (helliott : UnitCircleLogElliott)
    (hseparation : EventuallyTwoScaleTwistSeparation)
    (late : ∀ (_C : ℝ) (A : ℕ), 2 ≤ A → Section4LateParameters A)
    (hnot : ¬ StochasticDiscrepancyStatement) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter, ∃ C : ℝ,
      (∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) ∧
      ∃ S : Section4Selection C,
        S.B = (late C S.A S.two_le_A).B ∧
        HEq S.params (late C S.A S.two_le_A).params := by
  rw [not_stochasticDiscrepancy_iff_exists_uniform_square_bound] at hnot
  obtain ⟨μ, C, hbound⟩ := hnot
  obtain ⟨A₀, hA₀, honeScale⟩ :=
    helliott.exists_highProbability_pretentiousSet
      μ C (section4B C) (section4Eta C) (section4H C)
      (section4B_pos C) (section4H_pos C) (section4B_lt_section4H C)
      (section4Eta_pos C) hbound
  let P : Section4LateParameters A₀ := late C A₀ hA₀
  obtain ⟨K₀, hK₀⟩ := hseparation A₀ P.D hA₀ P.D_pos
  let K : ℕ := max A₀ (max P.k (max K₀ (section4TranslationK C)))
  have hA₀K : A₀ ≤ K := le_max_left _ _
  have hkK : P.k ≤ K :=
    (le_max_left P.k (max K₀ (section4TranslationK C))).trans
      (le_max_right A₀ (max P.k (max K₀ (section4TranslationK C))))
  have hK₀K : K₀ ≤ K :=
    ((le_max_left K₀ (section4TranslationK C)).trans
      (le_max_right P.k (max K₀ (section4TranslationK C)))).trans
        (le_max_right A₀ (max P.k (max K₀ (section4TranslationK C))))
  have htranslationK : section4TranslationK C ≤ K :=
    ((le_max_right K₀ (section4TranslationK C)).trans
      (le_max_right P.k (max K₀ (section4TranslationK C)))).trans
        (le_max_right A₀ (max P.k (max K₀ (section4TranslationK C))))
  have hKpos : 0 < K := P.k_pos.trans_le hkK
  have hA₀pow : A₀ ≤ 2 ^ K := hA₀K.trans K.lt_two_pow_self.le
  have hKDpos : 0 < K * P.D := Nat.mul_pos hKpos P.D_pos
  have hKleKD : K ≤ K * P.D := by
    have hDone : 1 ≤ P.D := P.D_pos
    nlinarith
  have hA₀powKD : A₀ ≤ 2 ^ (K * P.D) :=
    hA₀pow.trans (Nat.pow_le_pow_right (by omega) hKleKD)
  obtain ⟨Glarge, hGlarge, hμlarge, hlargeWitness⟩ :=
    honeScale A₀ (K * P.D) le_rfl hA₀powKD hKDpos
      (section4_threshold C hKDpos)
  obtain ⟨Gsmall, hGsmall, hμsmall, hsmallWitness⟩ :=
    honeScale A₀ K le_rfl hA₀pow hKpos (section4_threshold C hKpos)
  let G : Set CompactCircleCharacter := Glarge ∩ Gsmall
  have hGcompl :
      (μ : Measure CompactCircleCharacter) Gᶜ ≤
        2 * ENNReal.ofReal (4 * C ^ 2 / section4B C) := by
    exact measure_compl_inter_le_two (μ : Measure CompactCircleCharacter)
      (ENNReal.ofReal (4 * C ^ 2 / section4B C)) hμlarge hμsmall
  obtain ⟨g, hg⟩ := set_nonempty_of_probability_compl_le μ hGcompl
    (section4_exceptionalProbability_lt_one C)
  have hgLarge : g ∈ Glarge := hg.1
  have hgSmall : g ∈ Gsmall := hg.2
  have hpair : HasTwoScalePretentiousPair A₀ (4 ^ K) P.D g := by
    constructor
    · simpa only [pow_mul] using hlargeWitness g hgLarge
    · exact hsmallWitness g hgSmall
  have hnearby : HasNearbyTwoScalePretentiousPair A₀ (4 ^ K) P.D g :=
    hpair.nearby (hK₀ K hK₀K)
  let S : Section4Selection C := {
    A := A₀
    K := K
    B := P.B
    params := P.params
    sample := g
    two_le_A := hA₀
    K_pos := hKpos
    A_le_two_pow_K := hA₀pow
    nearby := hnearby
  }
  refine ⟨μ, C, hbound, S, ?_, ?_⟩
  · rfl
  · exact HEq.rfl

/-- Legacy zero-budget specialization retained only for bookkeeping tests.
It is not a valid input to the final BCC contradiction; that proof must call
`exists_late_section4Selection_of_not_stochastic` with its actual positive
shifted-convolution energy budget. -/
theorem exists_section4Selection_zeroBudget_legacy
    (helliott : UnitCircleLogElliott)
    (hseparation : EventuallyTwoScaleTwistSeparation)
    (hnot : ¬ StochasticDiscrepancyStatement) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter, ∃ C : ℝ,
      (∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) ∧
      Nonempty (Section4Selection C) := by
  obtain ⟨μ, C, hbound, S, _hB, _hparams⟩ :=
    exists_late_section4Selection_of_not_stochastic
      helliott hseparation
        (fun _C A hA ↦
          (canonicalSection4BCCParameters A 0 hA (by norm_num)).toLate)
        hnot
  exact ⟨μ, C, hbound, ⟨S⟩⟩

end

end Erdos67b
