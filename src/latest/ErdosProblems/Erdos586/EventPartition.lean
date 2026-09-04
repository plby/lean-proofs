/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.StageAssembly
import ErdosProblems.Erdos586.StageLaw

/-!
# The occurrence partition for Erdős Problem 586

This file identifies the abstract bad set of a prime stage with the actual
congruence classes of the chosen subcover.  Occurrences (rather than distinct
moduli) are retained throughout.  Every occurrence is put at the unique stage
of the largest prime factor of its modulus, and all those stages occur before
the finite horizon attached to the common period.
-/

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

local instance eventPartialPeriodNeZero (Q r : ℕ) :
    NeZero (partialPeriod Q r) := ⟨(partialPeriod_pos Q r).ne'⟩

/-! ## A newly exposed modulus is already visible at its stage -/

theorem IsNewModulus.dvd_partialPeriod {Q r d : ℕ} (hQ : Q ≠ 0)
    (hnew : IsNewModulus Q r d) : d ∣ partialPeriod Q r := by
  obtain ⟨hd, hm, hj, hjE⟩ := newModulus_eq_oldPart_mul_pow hQ hnew
  rw [hd, partialPeriod_stage hnew.1]
  exact Nat.mul_dvd_mul hm (Nat.pow_dvd_pow _ hjE)

/-! ## Full-period classes and canonical stages -/

/-- The class belonging to an occurrence, represented in the common period. -/
def occurrenceClass (A : CoveringFamily) (i : Fin A.length) :
    Set (ZMod (commonPeriod A)) :=
  congruenceClass (commonPeriod A) (A.get i).modulus
    (modulus_dvd_commonPeriod A i) (A.get i).residue

/-- The canonical stage of an occurrence is the stage of its largest prime
factor.  Every modulus in a `CoveringFamily` is greater than one. -/
def occurrenceStage (A : CoveringFamily) (i : Fin A.length) : ℕ :=
  primeStage (largestPrimeFactor (A.get i).modulus)

lemma occurrenceStage_pos (A : CoveringFamily) (i : Fin A.length) :
    0 < occurrenceStage A i :=
  primeStage_pos _

lemma occurrence_isNewModulus (A : CoveringFamily) (i : Fin A.length) :
    IsNewModulus (commonPeriod A) (occurrenceStage A i)
      (A.get i).modulus := by
  exact divisor_isNewModulus_at_largestPrimeStage
    (commonPeriod_pos A).ne' (modulus_dvd_commonPeriod A i)
    (A.get i).one_lt_modulus

lemma occurrenceStage_le_horizon (A : CoveringFamily) (i : Fin A.length) :
    occurrenceStage A i ≤ stageHorizon (commonPeriod A) := by
  exact (divisor_processed_by_horizon_at_largestPrimeStage
    (commonPeriod_pos A).ne' (modulus_dvd_commonPeriod A i)
    (A.get i).one_lt_modulus).1

/-- The same occurrence class, represented at its canonical partial period. -/
def occurrenceClassAtStage (A : CoveringFamily) (i : Fin A.length) :
    Set (ZMod (partialPeriod (commonPeriod A) (occurrenceStage A i))) :=
  congruenceClass
    (partialPeriod (commonPeriod A) (occurrenceStage A i))
    (A.get i).modulus
    ((occurrence_isNewModulus A i).dvd_partialPeriod (commonPeriod_pos A).ne')
    (A.get i).residue

/-- Occurrences selected at a particular canonical stage. -/
abbrev CanonicalStageIndex (A : CoveringFamily)
    (s : Finset (Fin A.length)) (r : ℕ) :=
  {i : Fin A.length // i ∈ s ∧ occurrenceStage A i = r}

lemma canonicalStageIndex_isNewModulus
    {A : CoveringFamily} {s : Finset (Fin A.length)} {r : ℕ}
    (i : CanonicalStageIndex A s r) :
    IsNewModulus (commonPeriod A) r (A.get i.1).modulus := by
  rcases i with ⟨i, hi, hstage⟩
  subst r
  exact occurrence_isNewModulus A i

/-- An occurrence belongs to exactly one canonical stage. -/
lemma canonicalStage_unique {A : CoveringFamily} (i : Fin A.length)
    {r t : ℕ} (hr : occurrenceStage A i = r)
    (ht : occurrenceStage A i = t) : r = t :=
  hr.symm.trans ht

def canonicalStageDvd (A : CoveringFamily) (i : Fin A.length) (r : ℕ)
    (hi : occurrenceStage A i = r) :
    (A.get i).modulus ∣ partialPeriod (commonPeriod A) r := by
  subst r
  exact (occurrence_isNewModulus A i).dvd_partialPeriod
    (commonPeriod_pos A).ne'

/-- The concrete union of the selected congruence classes newly exposed at
stage `r`, in that stage's cyclic group. -/
def canonicalStageEvent (A : CoveringFamily)
    (s : Finset (Fin A.length)) (r : ℕ) :
    Set (ZMod (partialPeriod (commonPeriod A) r)) :=
  {x | ∃ i : CanonicalStageIndex A s r,
    x ∈ congruenceClass (partialPeriod (commonPeriod A) r)
      (A.get i.1).modulus
      (canonicalStageDvd A i.1 r i.2.2) (A.get i.1).residue}

/-- The same stage union represented in the fixed common-period group. -/
def fullCanonicalStageEvent (A : CoveringFamily)
    (s : Finset (Fin A.length)) (r : ℕ) :
    Set (ZMod (commonPeriod A)) :=
  {x | ∃ i : CanonicalStageIndex A s r, x ∈ occurrenceClass A i.1}

/-- The union of all selected occurrence classes in the fixed period. -/
def selectedCoveredResidues (A : CoveringFamily)
    (s : Finset (Fin A.length)) : Set (ZMod (commonPeriod A)) :=
  {x | ∃ i : Fin A.length, i ∈ s ∧ x ∈ occurrenceClass A i}

/-! ## Fixed-period pullback -/

theorem fullCanonicalStageEvent_eq_preimage (A : CoveringFamily)
    (s : Finset (Fin A.length)) (r : ℕ) :
    fullCanonicalStageEvent A s r =
      (ZMod.castHom
        (partialPeriod_dvd (commonPeriod A) r (commonPeriod_pos A).ne')
        (ZMod (partialPeriod (commonPeriod A) r))) ⁻¹'
        canonicalStageEvent A s r := by
  ext x
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change x ∈ congruenceClass (commonPeriod A) (A.get i.1).modulus
      (modulus_dvd_commonPeriod A i.1) (A.get i.1).residue at hi
    rw [congruenceClass_eq_preimage
      (partialPeriod_dvd (commonPeriod A) r (commonPeriod_pos A).ne')
      (canonicalStageDvd A i.1 r i.2.2) (A.get i.1).residue] at hi
    exact hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change x ∈ occurrenceClass A i.1
    change x ∈ congruenceClass (commonPeriod A) (A.get i.1).modulus
      (modulus_dvd_commonPeriod A i.1) (A.get i.1).residue
    rw [congruenceClass_eq_preimage
      (partialPeriod_dvd (commonPeriod A) r (commonPeriod_pos A).ne')
      (canonicalStageDvd A i.1 r i.2.2) (A.get i.1).residue]
    exact hi

/-! ## Identification with the CRT product event -/

/-- In CRT coordinates, an individual newly exposed congruence class is
exactly the product of its old-coordinate and new-coordinate classes. -/
theorem mem_momentStageClass_stageCRT_iff
    {A : CoveringFamily} {s : Finset (Fin A.length)} {Q r : ℕ}
    (hQ : Q ≠ 0) (hr : 0 < r) (i : MomentStageIndex A s Q r)
    (x : ZMod (partialPeriod Q r)) :
    stageCRT Q r hr x ∈ momentStageClass hQ i ↔
      x ∈ congruenceClass (partialPeriod Q r) (A.get i.1).modulus
        (i.2.2.dvd_partialPeriod hQ) (A.get i.1).residue := by
  change
    ((stageCRT Q r hr x).1 ∈ momentStageOldEvent i ∧
      (stageCRT Q r hr x).2 ∈ momentStageNewEvent hQ i) ↔ _
  rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast]
  have hOld :
      (x.val : ZMod (partialPeriod Q (r - 1))) ∈
          momentStageOldEvent i ↔
        (x.val : ℤ) ≡ (A.get i.1).residue
          [ZMOD momentStageOldPart i] := by
    simpa [momentStageOldEvent] using
      (intCast_mem_congruenceClass (momentStageOldPart_dvd i)
        (x.val : ℤ) (A.get i.1).residue)
  have hNew :
      (x.val : ZMod (stagePrime r ^ stageExponent Q r)) ∈
          momentStageNewEvent hQ i ↔
        (x.val : ℤ) ≡ (A.get i.1).residue
          [ZMOD stagePrime r ^ momentStageExponent i] := by
    simpa [momentStageNewEvent] using
      (intCast_mem_congruenceClass (momentStagePrimePower_dvd hQ i)
        (x.val : ℤ) (A.get i.1).residue)
  have hFull :
      (x.val : ZMod (partialPeriod Q r)) ∈
          congruenceClass (partialPeriod Q r) (A.get i.1).modulus
            (i.2.2.dvd_partialPeriod hQ) (A.get i.1).residue ↔
        (x.val : ℤ) ≡ (A.get i.1).residue
          [ZMOD (A.get i.1).modulus] := by
    simpa using
      (intCast_mem_congruenceClass (i.2.2.dvd_partialPeriod hQ)
        (x.val : ℤ) (A.get i.1).residue)
  rw [hOld, hNew, hFull]
  have hd0 : (A.get i.1).modulus ≠ 0 := by
    exact (Nat.zero_lt_one.trans (A.get i.1).one_lt_modulus).ne'
  have hcop : Nat.Coprime (momentStageOldPart i)
      (stagePrime r ^ momentStageExponent i) :=
    (stagePrime_prime hr).coprime_pow_of_not_dvd
      (oldPart_not_dvd_stagePrime hr hd0)
  rw [Int.modEq_and_modEq_iff_modEq_mul (by simpa using hcop)]
  have hmod :
      (momentStageOldPart i : ℤ) *
          (stagePrime r : ℤ) ^ momentStageExponent i =
        ((A.get i.1).modulus : ℤ) := by
    exact_mod_cast (momentStageModulus_eq hQ i).symm
  rw [hmod]

/-- Literal union of the congruence classes whose moduli satisfy
`IsNewModulus` at the one-indexed stage `r`. -/
def newlyExposedClassUnion (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0) :
    Set (ZMod (partialPeriod Q r)) :=
  {x | ∃ i : MomentStageIndex A s Q r,
    x ∈ congruenceClass (partialPeriod Q r) (A.get i.1).modulus
      (i.2.2.dvd_partialPeriod hQ) (A.get i.1).residue}

theorem stageCRT_preimage_momentStageBadSet
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r) :
    (stageCRT Q r hr) ⁻¹' momentStageBadSet A s Q r hQ =
      newlyExposedClassUnion A s Q r hQ := by
  ext x
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_momentStageClass_stageCRT_iff hQ hr i x).1 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_momentStageClass_stageCRT_iff hQ hr i x).2 hi⟩

theorem stageCRT_image_newlyExposedClassUnion
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r) :
    stageCRT Q r hr '' newlyExposedClassUnion A s Q r hQ =
      momentStageBadSet A s Q r hQ := by
  rw [← stageCRT_preimage_momentStageBadSet A s hQ hr]
  exact Equiv.image_preimage _ _

lemma stageCRT_succ_eq_stageCRTRingEquiv (Q r : ℕ) :
    stageCRT Q (r + 1) (by omega) = stageCRTRingEquiv Q r := by
  rfl

/-- The product bad event used by the recursive law is exactly the concrete
one-indexed product event used by the moment calculation. -/
theorem stageBadEvent_eq_momentStageBadSet
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) :
    stageBadEvent A s Q r hQ =
      momentStageBadSet A s Q (r + 1) hQ := by
  ext z
  constructor
  · rintro ⟨i, hi, hclass⟩
    let j : MomentStageIndex A s Q (r + 1) :=
      ⟨i, mem_stageIndices_iff.mp hi⟩
    refine ⟨j, ?_⟩
    have hj := (mem_momentStageClass_stageCRT_iff hQ (by omega) j
      ((stageCRTRingEquiv Q r).symm z)).2 (by simpa using hclass)
    simpa [stageCRT_succ_eq_stageCRTRingEquiv] using hj
  · rintro ⟨j, hj⟩
    have hclass := (mem_momentStageClass_stageCRT_iff hQ (by omega) j
      ((stageCRTRingEquiv Q r).symm z)).1 (by
        simpa [stageCRT_succ_eq_stageCRTRingEquiv] using hj)
    exact ⟨j.1, mem_stageIndices_iff.mpr j.2, by simpa using hclass⟩

/-- The cyclic bad set of the recursive law is literally the union of the
new congruence classes at the successor stage. -/
theorem stageBadSet_eq_newlyExposedClassUnion
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) :
    stageBadSet A s Q r hQ =
      newlyExposedClassUnion A s Q (r + 1) hQ := by
  rw [stageBadSet, stageBadEvent_eq_momentStageBadSet]
  rw [← stageCRT_image_newlyExposedClassUnion A s hQ (by omega)]
  simpa [stageCRT_succ_eq_stageCRTRingEquiv] using
    (Equiv.symm_image_image (stageCRTRingEquiv Q r).toEquiv
      (newlyExposedClassUnion A s Q (r + 1) hQ))

/-! ## Recursive cumulative event used by the distorted law -/

/-- Reduction to the old CRT coordinate preserves every congruence whose
modulus already divides the old partial period. -/
theorem mem_oldClass_stageCRTRingEquiv_iff
    {Q r d : ℕ} (hd : d ∣ partialPeriod Q r) (b : ℤ)
    (x : ZMod (partialPeriod Q (r + 1))) :
    (stageCRTRingEquiv Q r x).1 ∈
        congruenceClass (partialPeriod Q r) d hd b ↔
      x ∈ congruenceClass (partialPeriod Q (r + 1)) d
        (hd.trans (by
          rw [partialPeriod_succ Q r]
          exact Nat.dvd_mul_right _ _)) b := by
  have hdNext : d ∣ partialPeriod Q (r + 1) := by
    exact hd.trans (by
      rw [partialPeriod_succ Q r]
      exact Nat.dvd_mul_right _ _)
  rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast, Prod.fst_natCast]
  have hOld :
      (x.val : ZMod (partialPeriod Q r)) ∈
          congruenceClass (partialPeriod Q r) d hd b ↔
        (x.val : ℤ) ≡ b [ZMOD d] := by
    simpa using (intCast_mem_congruenceClass hd (x.val : ℤ) b)
  have hNew :
      (x.val : ZMod (partialPeriod Q (r + 1))) ∈
          congruenceClass (partialPeriod Q (r + 1)) d
            hdNext b ↔
        (x.val : ℤ) ≡ b [ZMOD d] := by
    simpa using
      (intCast_mem_congruenceClass hdNext (x.val : ℤ) b)
  rw [hOld, hNew]

/-- An occurrence has been assigned by stage `n` if one of its
`IsNewModulus` witnesses lies among stages `1,…,n`.  The terminal argument
uses the canonical largest-prime witness; uniqueness is not needed for the
set-theoretic recursion. -/
def HasAssignedStage (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (i : Fin A.length) : Prop :=
  i ∈ s ∧ ∃ r : ℕ, 0 < r ∧ r ≤ n ∧
    IsNewModulus Q r (A.get i).modulus

def assignedModulusDvdPartial {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q n : ℕ} (hQ : Q ≠ 0)
    (i : Fin A.length) (hi : HasAssignedStage A s Q n i) :
    (A.get i).modulus ∣ partialPeriod Q n := by
  obtain ⟨r, hr, hrn, hnew⟩ := hi.2
  exact (hnew.dvd_partialPeriod hQ).trans
    (partialPeriod_mono_dvd hr hrn)

/-- The literal cumulative union of selected classes assigned in the first
`n` one-indexed stages, represented in `ZMod (partialPeriod Q n)`. -/
def processedSelectedEvent (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q n : ℕ) (hQ : Q ≠ 0) :
    Set (ZMod (partialPeriod Q n)) :=
  {x | ∃ i : Fin A.length, ∃ hi : HasAssignedStage A s Q n i,
    x ∈ congruenceClass (partialPeriod Q n) (A.get i).modulus
      (assignedModulusDvdPartial hQ i hi) (A.get i).residue}

@[simp] theorem processedSelectedEvent_zero (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    processedSelectedEvent A s Q 0 hQ = ∅ := by
  ext x
  simp only [processedSelectedEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨i, hi, hxi⟩
  obtain ⟨r, hr, hr0, hnew⟩ := hi.2
  omega

/-- Exact recursive decomposition: old processed classes are pulled back
along the old CRT coordinate, and the current `stageBadSet` is then added. -/
theorem processedSelectedEvent_succ (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q n : ℕ) (hQ : Q ≠ 0) :
    processedSelectedEvent A s Q (n + 1) hQ =
      {x | (stageCRTRingEquiv Q n x).1 ∈
        processedSelectedEvent A s Q n hQ} ∪
      stageBadSet A s Q n hQ := by
  ext x
  constructor
  · rintro ⟨i, hi, hxi⟩
    obtain ⟨his, r, hr, hrn, hnew⟩ := hi
    by_cases hle : r ≤ n
    · left
      let hiOld : HasAssignedStage A s Q n i :=
        ⟨his, r, hr, hle, hnew⟩
      refine ⟨i, hiOld, ?_⟩
      exact (mem_oldClass_stageCRTRingEquiv_iff
        (assignedModulusDvdPartial hQ i hiOld) (A.get i).residue x).2
        (by simpa using hxi)
    · have hre : r = n + 1 := by omega
      subst r
      right
      refine ⟨stageCRTRingEquiv Q n x, ?_, by simp⟩
      refine ⟨i, (mem_stageIndices_iff.mpr ⟨his, hnew⟩), ?_⟩
      simpa using hxi
  · intro hx
    rcases hx with hxold | hxnew
    · obtain ⟨i, hi, hxi⟩ := hxold
      obtain ⟨his, r, hr, hrn, hnew⟩ := hi
      let hiOld : HasAssignedStage A s Q n i :=
        ⟨his, r, hr, hrn, hnew⟩
      let hiNew : HasAssignedStage A s Q (n + 1) i :=
        ⟨his, r, hr, hrn.trans (Nat.le_succ n), hnew⟩
      refine ⟨i, hiNew, ?_⟩
      exact (mem_oldClass_stageCRTRingEquiv_iff
        (assignedModulusDvdPartial hQ i hiOld) (A.get i).residue x).1
        (by simpa using hxi)
    · rcases hxnew with ⟨z, hz, rfl⟩
      obtain ⟨i, hiStage, hzi⟩ := hz
      have hiData := mem_stageIndices_iff.mp hiStage
      let hi : HasAssignedStage A s Q (n + 1) i :=
        ⟨hiData.1, n + 1, by omega, le_rfl, hiData.2⟩
      refine ⟨i, hi, ?_⟩
      simpa using hzi

/-- The recursively defined presentation of the cumulative event. -/
def cumulativeStageBadSet (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    (n : ℕ) → Set (ZMod (partialPeriod Q n))
  | 0 => ∅
  | n + 1 =>
      {x | (stageCRTRingEquiv Q n x).1 ∈
        cumulativeStageBadSet A s Q hQ n} ∪
      stageBadSet A s Q n hQ

/-- The recursive cumulative event is exactly the literal union of the
selected congruence classes assigned so far. -/
theorem cumulativeStageBadSet_eq_processedSelectedEvent
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) : ∀ n,
    cumulativeStageBadSet A s Q hQ n =
      processedSelectedEvent A s Q n hQ := by
  intro n
  induction n with
  | zero =>
      simp [cumulativeStageBadSet]
  | succ n ih =>
      rw [cumulativeStageBadSet, ih, processedSelectedEvent_succ]

/-- All selected classes, represented in the terminal partial period. -/
def selectedEventAtHorizon (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0)
    (hmod : ∀ i : Fin A.length, (A.get i).modulus ∣ Q) :
    Set (ZMod (partialPeriod Q (stageHorizon Q))) :=
  {x | ∃ i : Fin A.length, i ∈ s ∧
    x ∈ congruenceClass (partialPeriod Q (stageHorizon Q))
      (A.get i).modulus (dvd_partialPeriod_horizon hQ (hmod i))
      (A.get i).residue}

/-- At the horizon the cumulative bad event is exactly the union of all
selected congruence classes.  This is the nonvacuous terminal bridge from
the distorted recursion back to integer coverage. -/
theorem cumulativeStageBadSet_horizon_eq_selected
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0)
    (hmod : ∀ i : Fin A.length, (A.get i).modulus ∣ Q) :
    cumulativeStageBadSet A s Q hQ (stageHorizon Q) =
      selectedEventAtHorizon A s Q hQ hmod := by
  rw [cumulativeStageBadSet_eq_processedSelectedEvent]
  ext x
  constructor
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi.1, by simpa using hxi⟩
  · rintro ⟨i, his, hxi⟩
    let t := occurrenceStage A i
    have htnew : IsNewModulus Q t (A.get i).modulus := by
      exact divisor_isNewModulus_at_largestPrimeStage hQ (hmod i)
        (A.get i).one_lt_modulus
    have htle : t ≤ stageHorizon Q :=
      (divisor_processed_by_horizon_at_largestPrimeStage hQ (hmod i)
        (A.get i).one_lt_modulus).1
    let hi : HasAssignedStage A s Q (stageHorizon Q) i :=
      ⟨his, t, occurrenceStage_pos A i, htle, htnew⟩
    exact ⟨i, hi, by simpa using hxi⟩

theorem selectedEventAtHorizon_eq_univ_of_coversIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0)
    (hmod : ∀ i : Fin A.length, (A.get i).modulus ∣ Q)
    (hcover : CoversIndices A s) :
    selectedEventAtHorizon A s Q hQ hmod = Set.univ := by
  let : NeZero (partialPeriod Q (stageHorizon Q)) :=
    ⟨by simpa [partialPeriod_horizon hQ] using hQ⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, his, hi⟩ := hcover (x.val : ℤ)
  exact ⟨i, his, (mem_congruenceClass_iff_modEq_val
    (dvd_partialPeriod_horizon hQ (hmod i)) (A.get i).residue x).2 hi⟩

/-- A selected integer cover makes the terminal cumulative bad event the
whole terminal cyclic group. -/
theorem cumulativeStageBadSet_horizon_eq_univ_of_coversIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0)
    (hmod : ∀ i : Fin A.length, (A.get i).modulus ∣ Q)
    (hcover : CoversIndices A s) :
    cumulativeStageBadSet A s Q hQ (stageHorizon Q) = Set.univ := by
  rw [cumulativeStageBadSet_horizon_eq_selected A s Q hQ hmod,
    selectedEventAtHorizon_eq_univ_of_coversIndices A s Q hQ hmod hcover]

theorem cumulativeStageBadSet_commonPeriod_eq_selected
    (A : CoveringFamily) (s : Finset (Fin A.length)) :
    cumulativeStageBadSet A s (commonPeriod A) (commonPeriod_pos A).ne'
        (stageHorizon (commonPeriod A)) =
      selectedEventAtHorizon A s (commonPeriod A) (commonPeriod_pos A).ne'
        (modulus_dvd_commonPeriod A) :=
  cumulativeStageBadSet_horizon_eq_selected A s (commonPeriod A)
    (commonPeriod_pos A).ne' (modulus_dvd_commonPeriod A)

/-- The cumulative presentation in this file agrees with the identically
recursive event whose mass is bounded in `StageLaw`. -/
theorem processedStageBadSet_eq_cumulativeStageBadSet
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) : ∀ n,
    processedStageBadSet A s Q hQ n =
      cumulativeStageBadSet A s Q hQ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [processedStageBadSet_succ, cumulativeStageBadSet, ih]

/-! ## The finite partition -/

theorem mem_selectedCoveredResidues_iff_mem_stage
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (x : ZMod (commonPeriod A)) :
    x ∈ selectedCoveredResidues A s ↔
      ∃ r ∈ Finset.Icc 1 (stageHorizon (commonPeriod A)),
        x ∈ fullCanonicalStageEvent A s r := by
  constructor
  · rintro ⟨i, his, hxi⟩
    refine ⟨occurrenceStage A i, ?_, ⟨⟨i, his, rfl⟩, hxi⟩⟩
    simp only [Finset.mem_Icc]
    exact ⟨occurrenceStage_pos A i, occurrenceStage_le_horizon A i⟩
  · rintro ⟨r, hr, i, hxi⟩
    exact ⟨i.1, i.2.1, hxi⟩

theorem selectedCoveredResidues_eq_iUnion_stages
    (A : CoveringFamily) (s : Finset (Fin A.length)) :
    selectedCoveredResidues A s =
      ⋃ r ∈ Finset.Icc 1 (stageHorizon (commonPeriod A)),
        fullCanonicalStageEvent A s r := by
  ext x
  rw [mem_selectedCoveredResidues_iff_mem_stage]
  simp

theorem selectedCoveredResidues_eq_univ_of_coversIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hs : CoversIndices A s) :
    selectedCoveredResidues A s = Set.univ := by
  let : NeZero (commonPeriod A) := ⟨(commonPeriod_pos A).ne'⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, his, hi⟩ := hs (x.val : ℤ)
  exact ⟨i, his, (mem_congruenceClass_iff_modEq_val
    (modulus_dvd_commonPeriod A i) (A.get i).residue x).2 hi⟩

theorem iUnion_fullCanonicalStageEvent_eq_univ_of_coversIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hs : CoversIndices A s) :
    (⋃ r ∈ Finset.Icc 1 (stageHorizon (commonPeriod A)),
      fullCanonicalStageEvent A s r) = Set.univ := by
  rw [← selectedCoveredResidues_eq_iUnion_stages,
    selectedCoveredResidues_eq_univ_of_coversIndices A s hs]

end

end Erdos586
