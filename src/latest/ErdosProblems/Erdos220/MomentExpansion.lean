import ErdosProblems.Erdos220.Fourier
import ErdosProblems.Erdos220.CompatibleModel
import ErdosProblems.Erdos220.MomentEnergy
import ErdosProblems.Erdos220.ProductParseval
import ErdosProblems.Erdos220.SmallMoment
import ErdosProblems.Erdos220.SupportAssembly
import ErdosProblems.Erdos220.SupportFactor

/-!
# The smooth sixth-moment expansion for Erdős 220

This file assembles the exact Ramanujan expansion of the centered interval
count with the finite Cauchy--CRT estimate and the prime-support Euler
product.  The elementary consequences of the resulting moment estimate are
kept in `SmallMoment`.
-/

open scoped BigOperators

namespace Erdos220

noncomputable section

/-! ## The exact nonconstant amplitude -/

/-- The nonconstant part of the squarefree Ramanujan expansion, after
summing over the translated interval. -/
def centeredRamanujanAmplitude (s h u : ℕ) : ℂ :=
  ∑ T ∈ nonconstantRamanujanSubsets s,
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t)

/-- Pointwise, the centered unit count is the density times the nonconstant
Ramanujan amplitude. -/
theorem unitCount_centered_eq_density_mul_amplitude
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    (unitCount s h u : ℂ) - (h : ℂ) * (density s : ℂ) =
      (density s : ℂ) * centeredRamanujanAmplitude s h u := by
  have hexpansion :=
    unitCount_centered_eq_ramanujanSubsetSum s h u hsquare
  rw [fourierDensity_eq_density s hs] at hexpansion
  exact hexpansion

/-- The nonconstant amplitude is real.  This is important: the sixth moment
must be expanded as an exact complex sixth power before any triangle
inequality is used, so that summing over the translate retains character
orthogonality. -/
theorem centeredRamanujanAmplitude_im
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    (centeredRamanujanAmplitude s h u).im = 0 := by
  have hcenter :=
    unitCount_centered_eq_density_mul_amplitude s h u hs hsquare
  have him := congrArg Complex.im hcenter
  have hmul : density s * (centeredRamanujanAmplitude s h u).im = 0 := by
    simpa using him
  exact (mul_eq_zero.mp hmul).resolve_left (density_pos hs).ne'

/-- Consequently the sixth norm power of the amplitude is the real part of
its exact complex sixth power. -/
theorem norm_centeredRamanujanAmplitude_pow_six_eq_re
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
      (centeredRamanujanAmplitude s h u ^ 6).re := by
  have him := centeredRamanujanAmplitude_im s h u hs hsquare
  have hz : centeredRamanujanAmplitude s h u =
      ((centeredRamanujanAmplitude s h u).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [hz, Complex.norm_real, Real.norm_eq_abs]
  norm_cast
  norm_num [Even.pow_abs]

/-- Taking norms in the exact expansion gives the corresponding identity
for each sixth-power summand of the real centered moment. -/
theorem abs_unitCount_centered_pow_six
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    |(unitCount s h u : ℝ) - (h : ℝ) * density s| ^ 6 =
      density s ^ 6 * ‖centeredRamanujanAmplitude s h u‖ ^ 6 := by
  have hcenter :=
    unitCount_centered_eq_density_mul_amplitude s h u hs hsquare
  have hre : (unitCount s h u : ℝ) - (h : ℝ) * density s =
      density s * (centeredRamanujanAmplitude s h u).re := by
    simpa using congrArg Complex.re hcenter
  rw [hre, abs_mul, abs_of_nonneg (density_nonneg s), mul_pow,
    Even.pow_abs]
  rw [norm_pow_six_eq_re_pow_six_of_im_eq_zero
    (centeredRamanujanAmplitude_im s h u hs hsquare)]
  norm_num

/-- Exact reduction of the smooth sixth moment to the sixth norm moment of
the nonconstant Ramanujan amplitude. -/
theorem centeredSixthMoment_eq_density_pow_six_mul
    (s h : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    centeredSixthMoment s h =
      density s ^ 6 *
        ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 := by
  rw [centeredSixthMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact abs_unitCount_centered_pow_six s h u hs hsquare

/-! ## Sixth powers as six labelled copies -/

/-- Writing a sixth power as a product over `Fin 6` gives stable labels for
the six denominator supports in the moment expansion. -/
lemma norm_pow_six_eq_fin_prod (z : ℂ) :
    ‖z‖ ^ 6 = ∏ _i : Fin 6, ‖z‖ := by
  rw [Fin.prod_const]

/-- The same labelled form specialized to the centered amplitude. -/
lemma centeredRamanujanAmplitude_norm_pow_six (s h u : ℕ) :
    ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
      ∏ _i : Fin 6, ‖centeredRamanujanAmplitude s h u‖ :=
  norm_pow_six_eq_fin_prod _

/-! ## Transposing six divisor supports prime by prime -/

/-- Transpose a six-tuple of prime subsets into the prime-by-prime support
representation used by `SupportFactor`. -/
def familySupportTuple (P : Finset ℕ) (U : Fin 6 → Finset ℕ) :
    SixSubsetTuple P :=
  fun p ↦ Finset.univ.filter fun i ↦ p.1 ∈ U i

@[simp] lemma mem_familySupportTuple (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (p : P) (i : Fin 6) :
    i ∈ familySupportTuple P U p ↔ p.1 ∈ U i := by
  simp [familySupportTuple]

/-- Transposition is injective when all six subsets are contained in the
ambient prime set. -/
lemma familySupportTuple_injective_on (P : Finset ℕ)
    {U V : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ P) (hV : ∀ i, V i ⊆ P)
    (h : familySupportTuple P U = familySupportTuple P V) : U = V := by
  funext i
  ext p
  constructor
  · intro hp
    let pp : P := ⟨p, hU i hp⟩
    have hmem : i ∈ familySupportTuple P U pp :=
      (mem_familySupportTuple P U pp i).2 hp
    rw [h] at hmem
    exact (mem_familySupportTuple P V pp i).1 hmem
  · intro hp
    let pp : P := ⟨p, hV i hp⟩
    have hmem : i ∈ familySupportTuple P V pp :=
      (mem_familySupportTuple P V pp i).2 hp
    rw [← h] at hmem
    exact (mem_familySupportTuple P U pp i).1 hmem

/-- If each of the six subsets is nonempty, the transposed support tuple has
the corresponding `AllSixSubsetsNonempty` property. -/
lemma familySupportTuple_all_nonempty (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (hsub : ∀ i, U i ⊆ P)
    (hne : ∀ i, (U i).Nonempty) :
    AllSixSubsetsNonempty (familySupportTuple P U) := by
  intro i
  obtain ⟨p, hp⟩ := hne i
  exact ⟨⟨p, hsub i hp⟩, by simpa using hp⟩

/-- Membership in the sixfold product of nonconstant subsets provides both
ambient containment and nonemptiness. -/
lemma mem_nonconstant_pi_support (s : ℕ)
    {U : Fin 6 → Finset ℕ}
    (hU : U ∈ Fintype.piFinset (fun _ : Fin 6 ↦
      nonconstantRamanujanSubsets s)) :
    (∀ i, U i ⊆ s.primeFactors) ∧ (∀ i, (U i).Nonempty) := by
  constructor
  · intro i
    have hi := (Fintype.mem_piFinset.mp hU) i
    exact Finset.mem_powerset.mp (Finset.mem_of_mem_erase hi)
  · intro i
    have hi := (Fintype.mem_piFinset.mp hU) i
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hi)

/-- A prime occurring in exactly one of the six supports cannot satisfy the
prime-local compatibility equation, because its unique frequency is a unit
modulo that prime. -/
lemma not_sixPrimeCompatible_of_support_card_one
    {s : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors) (p : s.primeFactors)
    (hpone : (familySupportTuple s.primeFactors U p).card = 1)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ¬ sixPrimeCompatible s a := by
  classical
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  let : NeZero p.1 := ⟨hpprime.ne_zero⟩
  let : Fact (1 < p.1) := ⟨hpprime.one_lt⟩
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hpone
  have hiJ : i ∈ familySupportTuple s.primeFactors U p := by simp [hi]
  have hpi : p.1 ∈ U i := (mem_familySupportTuple _ _ _ _).mp hiJ
  have hlocal : sixLocalFrequency a p.1 =
      ((a i ⟨p.1, hpi⟩).1 : ZMod p.1) := by
    unfold sixLocalFrequency sixLocalFrequencyNat
    rw [Finset.sum_eq_single i]
    · simp [hpi]
    · intro j hj hji
      have hjJ : j ∉ familySupportTuple s.primeFactors U p := by
        rw [hi]
        simpa using hji
      have hpj : p.1 ∉ U j := by
        simpa using hjJ
      simp [hpj]
    · simp
  have hcop : (a i ⟨p.1, hpi⟩).1.Coprime p.1 :=
    (Finset.mem_filter.mp (a i ⟨p.1, hpi⟩).2).2
  have hne : ((a i ⟨p.1, hpi⟩).1 : ZMod p.1) ≠ 0 := by
    let : Fact (1 < p.1) := ⟨(Nat.prime_of_mem_primeFactors p.2).one_lt⟩
    intro hz
    have hu : ((ZMod.unitOfCoprime (a i ⟨p.1, hpi⟩).1 hcop :
        (ZMod p.1)ˣ) : ZMod p.1) ≠ 0 := Units.ne_zero _
    exact hu (by simpa using hz)
  intro hcompat
  exact hne (hlocal ▸ hcompat p.1 p.2)

/-- Exact sixth-power expansion into six labelled nonconstant divisor
supports.  No absolute values have been introduced at this stage. -/
lemma centeredRamanujanAmplitude_pow_six (s h u : ℕ) :
    centeredRamanujanAmplitude s h u ^ 6 =
      ∑ U ∈ Fintype.piFinset (fun _ : Fin 6 ↦
          nonconstantRamanujanSubsets s),
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm (U i) (u + t) := by
  simpa only [centeredRamanujanAmplitude] using
    (Finset.sum_pow' (nonconstantRamanujanSubsets s)
      (fun T ↦ ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t)) 6)

/-- Summing over the translate is performed *before* estimating any term.
This is the exact arrangement in which additive-character orthogonality
eliminates every prime support of multiplicity one. -/
theorem sum_norm_amplitude_pow_six_eq_re_support_sum
    (s h : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
      (∑ U ∈ Fintype.piFinset (fun _ : Fin 6 ↦
          nonconstantRamanujanSubsets s),
        ∑ u ∈ Finset.range s,
          ∏ i : Fin 6,
            ∑ t ∈ Finset.Icc 1 h,
              ramanujanSubsetTerm (U i) (u + t)).re := by
  calc
    ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
        ∑ u ∈ Finset.range s,
          (centeredRamanujanAmplitude s h u ^ 6).re := by
      apply Finset.sum_congr rfl
      intro u hu
      exact norm_centeredRamanujanAmplitude_pow_six_eq_re s h u hs hsquare
    _ = (∑ u ∈ Finset.range s,
          centeredRamanujanAmplitude s h u ^ 6).re := by simp
    _ = _ := by
      simp_rw [centeredRamanujanAmplitude_pow_six]
      rw [Finset.sum_comm]

/-! ## Coefficients of a fixed support family -/

/-- The scalar Ramanujan coefficient belonging to one prime subset. -/
def ramanujanSubsetCoefficient (T : Finset ℕ) : ℂ :=
  ∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))

/-- Product of the six scalar coefficients. -/
def sixRamanujanCoefficient (U : Fin 6 → Finset ℕ) : ℂ :=
  ∏ i : Fin 6, ramanujanSubsetCoefficient (U i)

lemma sum_ramanujanSubsetTerm_eq_coefficient_mul (T : Finset ℕ)
    (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) =
      ramanujanSubsetCoefficient T *
        ∑ a : PrimitiveFrequencyTuple T,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) := by
  exact sum_ramanujanSubsetTerm_eq_frequencySum T h u

/-- The prime-product frequency is an additive character. -/
lemma primitiveTupleCharacter_add {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (m n : ℕ) :
    primitiveTupleCharacter a (m + n) =
      primitiveTupleCharacter a m * primitiveTupleCharacter a n := by
  classical
  unfold primitiveTupleCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  exact Nat.mul_add _ _ _

/-- Translation of an interval factors off the value of the character at
the translating residue. -/
lemma sum_primitiveTupleCharacter_add {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) =
      primitiveTupleCharacter a u *
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t := by
  simp_rw [primitiveTupleCharacter_add]
  rw [Finset.mul_sum]

/-- The compatible interval contraction for one fixed family of six prime
supports. -/
def fixedSupportCompatibleIntervalContraction (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℂ :=
  ∑ a : (∀ i, PrimitiveFrequencyTuple (U i)),
    if sixPrimeCompatible s a then
      ∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t
    else 0

/-- If one prime occurs in exactly one support, the compatible contraction
is empty by prime-local character orthogonality. -/
lemma fixedSupportCompatibleIntervalContraction_eq_zero_of_support_card_one
    {s h : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors) (p : s.primeFactors)
    (hpone : (familySupportTuple s.primeFactors U p).card = 1) :
    fixedSupportCompatibleIntervalContraction s h U = 0 := by
  classical
  unfold fixedSupportCompatibleIntervalContraction
  apply Finset.sum_eq_zero
  intro a ha
  rw [if_neg (not_sixPrimeCompatible_of_support_card_one hsub p hpone a)]

/-- Expand the product of the six fixed-support Ramanujan summands into a
single sum over six labelled primitive-frequency tuples. -/
lemma fixedSupportRamanujanProduct_eq_frequencySum
    (U : Fin 6 → Finset ℕ) (h u : ℕ) :
    (∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm (U i) (u + t)) =
      sixRamanujanCoefficient U *
        ∑ a : (∀ i, PrimitiveFrequencyTuple (U i)),
          ∏ i : Fin 6,
            ∑ t ∈ Finset.Icc 1 h,
              primitiveTupleCharacter (a i) (u + t) := by
  simp_rw [sum_ramanujanSubsetTerm_eq_coefficient_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa using
    (Fintype.prod_sum (R := ℂ)
      (f := fun i : Fin 6 ↦ fun a : PrimitiveFrequencyTuple (U i) ↦
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)))

/-- For a fixed six-tuple of frequencies, complete-period orthogonality can
be applied after factoring all six interval translations. -/
lemma sum_six_translated_primitiveTupleCharacter
    {s : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (h : ℕ) :
    ∑ u ∈ Finset.range s,
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h,
            primitiveTupleCharacter (a i) (u + t) =
      (if sixPrimeCompatible s a then (s : ℂ) else 0) *
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t := by
  simp_rw [sum_primitiveTupleCharacter_add]
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul]
  rw [six_primitiveTupleCharacter_orthogonality hs hsquare hU a]

/-- Exact fixed-support evaluation after summing the translate over a full
period.  This is the bridge from Fourier orthogonality to the finite
compatible-frequency contraction. -/
theorem sum_fixedSupportRamanujanProduct_eq_compatibleContraction
    {s : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (h : ℕ) :
    ∑ u ∈ Finset.range s,
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h,
            ramanujanSubsetTerm (U i) (u + t) =
      (s : ℂ) * sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U := by
  simp_rw [fixedSupportRamanujanProduct_eq_frequencySum]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_six_translated_primitiveTupleCharacter hs hsquare hU]
  unfold fixedSupportCompatibleIntervalContraction
  calc
    sixRamanujanCoefficient U *
          ∑ a, (if sixPrimeCompatible s a then (s : ℂ) else 0) *
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t =
        sixRamanujanCoefficient U * ((s : ℂ) *
          ∑ a, if sixPrimeCompatible s a then
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t else 0) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcompat : sixPrimeCompatible s a <;> simp [hcompat]
    _ = (s : ℂ) * sixRamanujanCoefficient U *
          ∑ a, if sixPrimeCompatible s a then
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t else 0 := by
      ring

/-- The real contribution of one fixed six-tuple of nonconstant Ramanujan
supports to the complete-period sixth-power expansion. -/
def fixedSupportMomentContribution (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℝ :=
  (∑ u ∈ Finset.range s,
      ∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h,
          ramanujanSubsetTerm (U i) (u + t)).re

/-- The real fixed-support contribution vanishes whenever a prime occurs in
exactly one of the six supports. -/
lemma fixedSupportMomentContribution_eq_zero_of_not_admissible
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ}
    (hU : U ∈ nonemptySixSubsetFamilies s.primeFactors)
    (hbad : ¬ IsAdmissibleSixTuple
      (familySupportTuple s.primeFactors U)) :
    fixedSupportMomentContribution s h U = 0 := by
  classical
  have hsub : ∀ i, U i ⊆ s.primeFactors :=
    (mem_nonemptySixSubsetFamilies.mp hU).1
  simp only [IsAdmissibleSixTuple, sixMultiplicity] at hbad
  push_neg at hbad
  obtain ⟨p, hpone⟩ := hbad
  have hzero :=
    fixedSupportCompatibleIntervalContraction_eq_zero_of_support_card_one
      (h := h) hsub p hpone
  rw [fixedSupportMomentContribution,
    sum_fixedSupportRamanujanProduct_eq_compatibleContraction hs hsquare hsub,
    hzero]
  simp

/-- The analytic input for an admissible support family only has to bound
the norm of its coefficient-weighted compatible contraction. -/
lemma fixedSupportMomentContribution_le_of_contraction_norm
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hsub : ∀ i, U i ⊆ s.primeFactors)
    (hnorm : ‖sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U‖ ≤
      (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U)) :
    fixedSupportMomentContribution s h U ≤
      (s : ℝ) * (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U) := by
  rw [fixedSupportMomentContribution,
    sum_fixedSupportRamanujanProduct_eq_compatibleContraction hs hsquare hsub]
  calc
    ((s : ℂ) * sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U).re ≤
        ‖(s : ℂ) * (sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U)‖ := by
      rw [mul_assoc]
      exact Complex.re_le_norm _
    _ = (s : ℝ) * ‖sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U‖ := by
      rw [norm_mul, Complex.norm_natCast]
    _ ≤ (s : ℝ) * ((h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U)) :=
      mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = (s : ℝ) * (h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U) := by ring

/-- Norm of the scalar coefficient, before transposing the two products. -/
lemma norm_sixRamanujanCoefficient (U : Fin 6 → Finset ℕ)
    (hprime : ∀ i p, p ∈ U i → p.Prime) :
    ‖sixRamanujanCoefficient U‖ =
      ∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹ := by
  rw [sixRamanujanCoefficient, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ramanujanSubsetCoefficient, norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (hprime i p hp).one_le
  rw [norm_div, norm_neg, norm_one, Complex.norm_natCast,
    Nat.cast_sub hp1, one_div]

/-- Transpose a product over six subsets into a product of powers indexed by
the ambient primes. -/
lemma prod_six_subsets_eq_prod_support_card
    {M : Type*} [CommMonoid M] (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (hsub : ∀ i, U i ⊆ P) (f : ℕ → M) :
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
      ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter (fun i ↦ p ∈ U i)).card := by
  classical
  calc
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
        ∏ i : Fin 6, ∏ p ∈ P, if p ∈ U i then f p else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      have heq : P.filter (fun p ↦ p ∈ U i) = U i := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · exact fun hp ↦ hp.2
        · exact fun hp ↦ ⟨hsub i hp, hp⟩
      rw [← Finset.prod_filter]
      rw [heq]
    _ = ∏ p ∈ P, ∏ i : Fin 6, if p ∈ U i then f p else 1 := by
      rw [Finset.prod_comm]
    _ = ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter (fun i ↦ p ∈ U i)).card := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← Finset.prod_filter]
      simp

/-- Primes absent from all six supports contribute the neutral local weight,
so the ambient-prime weight may be restricted to the union of the supports. -/
lemma sixSubsetWeight_family_eq_usedPrimes_prod
    (P : Finset ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : ∀ i, U i ⊆ P) :
    sixSubsetWeight P (familySupportTuple P U) =
      ∏ p ∈ usedPrimes U,
        sixthSupportWeight (p : ℝ) (primeSupport U p) := by
  classical
  have hused : usedPrimes U ⊆ P := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
    exact hsub i hi
  unfold sixSubsetWeight
  calc
    (∏ p : P, sixthSupportWeight (p : ℝ)
        (familySupportTuple P U p)) =
        ∏ p ∈ P, sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      simpa [familySupportTuple, primeSupport] using
        (Finset.prod_attach P
          (fun p ↦ sixthSupportWeight (p : ℝ) (primeSupport U p)))
    _ = ∏ p ∈ usedPrimes U,
          sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      symm
      apply Finset.prod_subset hused
      intro p hpP hpnot
      have hnone : primeSupport U p = ∅ := by
        ext i
        simp only [mem_primeSupport]
        constructor
        · intro hpUi
          exact (hpnot (mem_usedPrimes.mpr ⟨i, hpUi⟩)).elim
        · intro hi
          simp at hi
      rw [hnone]
      simp [sixthSupportWeight]

/-- The compatible fundamental lemma, product Parseval, and the exact local
weight normalization give the coefficient-weighted estimate for one
admissible six-support family. -/
theorem norm_coefficient_mul_fixedSupportContraction_le
    {s h : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors)
    (hne : ∀ i, (U i).Nonempty)
    (hadmissible : IsAdmissibleSixTuple
      (familySupportTuple s.primeFactors U)) :
    ‖sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U‖ ≤
      (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U) := by
  classical
  have hused : usedPrimes U ⊆ s.primeFactors := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
    exact hsub i hi
  have hUused : ∀ i, U i ⊆ usedPrimes U := by
    intro i p hp
    exact mem_usedPrimes.mpr ⟨i, hp⟩
  have hPused : ∀ p ∈ usedPrimes U, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (hused hp)).two_le
  have hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1 := by
    intro p hp
    have hpP : p ∈ s.primeFactors := hused hp
    have hadm := hadmissible ⟨p, hpP⟩
    simpa [sixMultiplicity, familySupportTuple, primeSupport] using hadm
  have hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card := by
    intro p hp
    have hpos : 0 < (primeSupport U p).card := by
      obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
      exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩
    exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Nat.ne_of_gt hpos, hnoone p hp⟩)
  have hprime : ∀ i p, p ∈ U i → p.Prime := by
    intro i p hp
    exact Nat.prime_of_mem_primeFactors (hsub i hp)
  let scale : ℝ := ∏ p ∈ usedPrimes U,
    Real.sqrt p ^ ((primeSupport U p).card - 2)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    apply Finset.prod_nonneg
    intro p hp
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hfundamental :
      ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        scale * ∏ i : Fin 6,
          Real.sqrt (primitiveIntervalEnergy (U i) h) := by
    have hbound := compatibleIntervalContraction_le_of_noSingleton
      s h U hused hnoone
    simpa [scale, fixedSupportCompatibleIntervalContraction,
      compatibleIntervalContraction, compatibleFrequencyContraction,
      primitiveIntervalFourier, primitiveIntervalEnergy] using hbound
  have henergy :
      ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        scale * ∏ i : Fin 6,
          Real.sqrt ((primeProduct (U i) : ℝ) * h) :=
    six_primitiveIntervalEnergy_contraction_le U h
      (fixedSupportCompatibleIntervalContraction s h U) scale
      hprime hne hscale hfundamental
  have hcoefficient : 0 ≤
      ∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹ := by
    apply Finset.prod_nonneg
    intro i hi
    apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [norm_mul, norm_sixRamanujanCoefficient U hprime]
  calc
    (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
          ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
          (scale * ∏ i : Fin 6,
            Real.sqrt ((primeProduct (U i) : ℝ) * h)) :=
      mul_le_mul_of_nonneg_left henergy hcoefficient
    _ = (h : ℝ) ^ 3 *
          ∏ p ∈ usedPrimes U,
            sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      simpa [scale, primeSupport] using
        (six_support_energy_normalization (usedPrimes U) U h
          hUused hPused hmult)
    _ = (h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U) := by
      rw [sixSubsetWeight_family_eq_usedPrimes_prod s.primeFactors U hsub]

/-! ## Finite assembly of the fixed-support estimates -/

/-- The fixed-support contraction bound and multiplicity-one vanishing,
combined with the exact Fourier expansion and the support Euler product. -/
theorem centeredSixthMoment_le_localFactorProduct_of_fixedSupportBounds
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    (hadmissible : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        fixedSupportMomentContribution s h U ≤
          (s : ℝ) * (h : ℝ) ^ 3 *
            sixSubsetWeight s.primeFactors
              (familySupportTuple s.primeFactors U))
    (hvanish : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      ¬ IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        fixedSupportMomentContribution s h U = 0) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  have hP : ∀ p ∈ s.primeFactors, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hinj : Set.InjOn (familySupportTuple s.primeFactors)
      (nonemptySixSubsetFamilies s.primeFactors) := by
    intro U hU V hV hUV
    exact familySupportTuple_injective_on s.primeFactors
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (mem_nonemptySixSubsetFamilies.mp hV).1 hUV
  have hnonempty : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      AllSixSubsetsNonempty (familySupportTuple s.primeFactors U) := by
    intro U hU
    exact familySupportTuple_all_nonempty s.primeFactors U
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (mem_nonemptySixSubsetFamilies.mp hU).2
  have hassembly :
      ∑ U ∈ nonemptySixSubsetFamilies s.primeFactors,
          fixedSupportMomentContribution s h U ≤
        (s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p :=
    sum_six_family_contributions_le_localFactorProduct_natScale
      s.primeFactors hP (familySupportTuple s.primeFactors)
      hinj hnonempty s h (fixedSupportMomentContribution s h)
      hadmissible hvanish
  have hsum :
      ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 ≤
        (s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
    rw [sum_norm_amplitude_pow_six_eq_re_support_sum s h hs hsquare]
    simpa [fixedSupportMomentContribution, nonemptySixSubsetFamilies,
      nonconstantRamanujanSubsets] using hassembly
  have hfactor : 0 ≤ (s : ℝ) * (h : ℝ) ^ 3 *
      ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    · apply Finset.prod_nonneg
      intro p hp
      exact sixthLocalFactor_nonneg p (by exact_mod_cast hP p hp)
  have hdensityPow : density s ^ 6 ≤ density s ^ 3 :=
    pow_le_pow_of_le_one (density_nonneg s) (density_le_one s) (by norm_num)
  rw [centeredSixthMoment_eq_density_pow_six_mul s h hs hsquare]
  calc
    density s ^ 6 *
          ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 ≤
        density s ^ 6 * ((s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (density_nonneg s) _)
    _ ≤ density s ^ 3 * ((s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :=
      mul_le_mul_of_nonneg_right hdensityPow hfactor
    _ = (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p := by ring

/-- A compact interface for the sole analytic estimate: it suffices to bound
the coefficient-weighted compatible contraction for every admissible family.
All expansion, vanishing, support summation, and density bookkeeping are then
automatic. -/
theorem centeredSixthMoment_le_localFactorProduct_of_contractionBounds
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    (hcontraction : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        ‖sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U‖ ≤
            (h : ℝ) ^ 3 *
              sixSubsetWeight s.primeFactors
                (familySupportTuple s.primeFactors U)) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  apply centeredSixthMoment_le_localFactorProduct_of_fixedSupportBounds
    hs hsquare
  · intro U hU hadmissible
    exact fixedSupportMomentContribution_le_of_contraction_norm hs hsquare
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (hcontraction U hU hadmissible)
  · intro U hU hbad
    exact fixedSupportMomentContribution_eq_zero_of_not_admissible
      hs hsquare hU hbad

/-- The complete smooth-modulus sixth-moment estimate with its explicit
finite Euler product. -/
theorem centeredSixthMoment_le_localFactorProduct
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  apply centeredSixthMoment_le_localFactorProduct_of_contractionBounds
    hs hsquare
  intro U hU hadmissible
  have hsupport := mem_nonemptySixSubsetFamilies.mp hU
  exact norm_coefficient_mul_fixedSupportContraction_le
    hsupport.1 hsupport.2 hadmissible

/-! ## From the local-factor estimate to the published moment bound -/

/-- The purely algebraic final assembly: once the Fourier/fundamental-lemma
calculation has bounded the moment by the local Euler product, weak Mertens
turns that product into the fixed logarithmic power used by
`SmallPrimeSixthMomentBound`.

This lemma is deliberately kept separate from the proof of the local-factor
estimate below.  Its hypothesis is discharged in this file by
`centeredSixthMoment_le_localFactorProduct`; it is not an assumption of the
final theorem. -/
theorem exists_smallPrimeSixthMomentBound_of_localFactor
    (hlocal : ∀ {s h : ℕ}, 0 < s → Squarefree s →
      centeredSixthMoment s h ≤
        (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :
    ∃ A : ℝ, SmallPrimeSixthMomentBound A := by
  obtain ⟨C, hC, hprod⟩ := exists_sixthLocalFactor_prod_le
  let D : ℝ := max C (Real.log 2)⁻¹
  let A : ℝ := D ^ 1432
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := hC.trans_le (le_max_left _ _)
  have hA : 0 < A := pow_pos hD _
  refine ⟨A, hA, ?_⟩
  intro s h hs hsquare hh hsmooth
  let L : ℝ := Real.log (2 * (h : ℝ))
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by norm_cast; omega)
  have hlog_mono : Real.log (2 : ℝ) ≤ L := by
    dsimp [L]
    apply Real.log_le_log
    · norm_num
    · norm_cast
      omega
  have hDlog2 : 1 ≤ D * Real.log 2 := by
    have hinv : (Real.log 2)⁻¹ ≤ D := le_max_right _ _
    calc
      (1 : ℝ) = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ D * Real.log 2 := mul_le_mul_of_nonneg_right hinv hlog2.le
  have hDL : 1 ≤ D * L :=
    hDlog2.trans <| mul_le_mul_of_nonneg_left hlog_mono hD.le
  have hCD : C ≤ D := le_max_left _ _
  have hprod' :
      ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤ D ^ 1432 * L ^ 1432 := by
    calc
      ∏ p ∈ s.primeFactors, sixthLocalFactor p
          ≤ (C * L) ^ 716 := by
            dsimp [L]
            exact hprod hh hsmooth
      _ ≤ (D * L) ^ 716 := by
            exact pow_le_pow_left₀ (mul_nonneg hC.le hL)
              (mul_le_mul_of_nonneg_right hCD hL) _
      _ ≤ (D * L) ^ 1432 := by
            exact pow_le_pow_right₀ hDL (by norm_num)
      _ = D ^ 1432 * L ^ 1432 := by rw [mul_pow]
  have hscale : 0 ≤ (s : ℝ) * ((h : ℝ) * density s) ^ 3 := by
    exact mul_nonneg (Nat.cast_nonneg _) <|
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (density_nonneg s)) _
  calc
    centeredSixthMoment s h ≤
        (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p :=
      hlocal hs hsquare
    _ ≤ (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          (D ^ 1432 * L ^ 1432) :=
      mul_le_mul_of_nonneg_left hprod' hscale
    _ = A * s * ((h : ℝ) * density s) ^ 3 *
          Real.log (2 * (h : ℝ)) ^ 1432 := by
      dsimp [A, L]
      ring

/-- Unconditional existence of the absolute constant in the small-prime
sixth-moment estimate. -/
theorem exists_smallPrimeSixthMomentBound :
    ∃ A : ℝ, SmallPrimeSixthMomentBound A :=
  exists_smallPrimeSixthMomentBound_of_localFactor
    centeredSixthMoment_le_localFactorProduct

end

end Erdos220
