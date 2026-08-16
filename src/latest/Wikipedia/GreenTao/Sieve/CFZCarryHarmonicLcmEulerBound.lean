import Wikipedia.GreenTao.Sieve.CFZCarryFourierTailBound

/-!
# A finite Euler majorant for the carry harmonic LCM mass

The divisor cutoff in `smoothDivisorFamilyChoices κ R` is imposed on every
individual divisor.  It therefore couples the prime choices and does not
give an exact Euler product.  This file uses only the honest one-sided
comparison: a squarefree paired divisor family is injected into the larger
space in which, independently for every prime `p ≤ R`, an arbitrary subset
of the `2 * card κ` divisor occurrences may contain `p`.

The empty subset has weight one.  Every nonempty subset has weight `p⁻¹`,
because `p` then occurs in the global LCM.  Summing over the unrestricted
assignment space gives the finite product

`∏ p ∈ Nat.primesLE R, (1 + (2 ^ (2 * card κ) - 1) / p)`.

Only the injection into that space is used; no false equality with the
coordinatewise-truncated divisor family is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Prime-occurrence assignments -/

/-- The two divisor occurrences attached to every member of `κ`. -/
abbrev PairedDivisorOccurrence (κ : Type*) := Sum κ κ

/-- Read a paired divisor family as a function on its two copies of `κ`. -/
def pairedDivisorOccurrenceValue
    {κ : Type*} (z : κ → ℕ × ℕ) :
    PairedDivisorOccurrence κ → ℕ :=
  Sum.elim (fun q => (z q).1) (fun q => (z q).2)

/-- An unrestricted assignment gives, for every prime at most `R`, the set
of divisor occurrences in which that prime appears. -/
abbrev PairedPrimeOccurrenceAssignment
    (κ : Type*) [Fintype κ] (R : ℕ) :=
  (p : (Nat.primesLE R : Finset ℕ)) →
    Finset (PairedDivisorOccurrence κ)

/-- The prime-occurrence assignment encoded by a paired divisor family. -/
noncomputable def pairedPrimeOccurrenceAssignmentOf
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (z : κ → ℕ × ℕ) :
    PairedPrimeOccurrenceAssignment κ R :=
  fun p =>
    Finset.univ.filter fun i =>
      (p : ℕ) ∣ pairedDivisorOccurrenceValue z i

/-- Harmonic weight of an unrestricted prime-occurrence assignment. -/
noncomputable def pairedPrimeOccurrenceAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} (A : PairedPrimeOccurrenceAssignment κ R) : ℝ :=
  ∏ p,
    if (A p).Nonempty then
      (1 : ℝ) / (p : ℝ)
    else 1

theorem pairedPrimeOccurrenceAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} (A : PairedPrimeOccurrenceAssignment κ R) :
    0 ≤ pairedPrimeOccurrenceAssignmentWeight A := by
  unfold pairedPrimeOccurrenceAssignmentWeight
  exact Finset.prod_nonneg fun p _ => by
    split_ifs <;> positivity

/-! ## The unrestricted assignment sum -/

theorem sum_pairedDivisorOccurrence_localWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : ℕ) :
    (∑ S : Finset (PairedDivisorOccurrence κ),
        if S.Nonempty then (1 : ℝ) / (p : ℝ) else 1) =
      1 +
        ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
          (p : ℝ) := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hnonemptyCard :
      ((Finset.univ.filter
          (fun S : Finset (PairedDivisorOccurrence κ) =>
            S.Nonempty)).card) =
        2 ^ (2 * Fintype.card κ) - 1 := by
    have hfilter :
        Finset.univ.filter
            (fun S : Finset (PairedDivisorOccurrence κ) =>
              S.Nonempty) =
          Finset.univ.erase ∅ := by
      ext S
      simp [Finset.nonempty_iff_ne_empty]
    rw [hfilter,
      Finset.card_erase_of_mem (Finset.mem_univ (∅ :
        Finset (PairedDivisorOccurrence κ)))]
    simp [Fintype.card_finset, Fintype.card_sum, two_mul]
  have hemptyCard :
      ((Finset.univ.filter
          (fun S : Finset (PairedDivisorOccurrence κ) =>
            ¬S.Nonempty)).card) = 1 := by
    have hfilter :
        Finset.univ.filter
            (fun S : Finset (PairedDivisorOccurrence κ) =>
              ¬S.Nonempty) =
          {∅} := by
      ext S
      simp
    rw [hfilter]
    simp
  rw [hnonemptyCard, hemptyCard]
  norm_num
  ring

theorem sum_pairedPrimeOccurrenceAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    (∑ A : PairedPrimeOccurrenceAssignment κ R,
        pairedPrimeOccurrenceAssignmentWeight A) =
      ∏ p ∈ Nat.primesLE R,
        (1 +
          ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
            (p : ℝ)) := by
  classical
  calc
    (∑ A : PairedPrimeOccurrenceAssignment κ R,
        pairedPrimeOccurrenceAssignmentWeight A) =
        ∏ p : (Nat.primesLE R : Finset ℕ),
          ∑ S : Finset (PairedDivisorOccurrence κ),
            if S.Nonempty then
              (1 : ℝ) / (p : ℝ)
            else 1 := by
      simpa [pairedPrimeOccurrenceAssignmentWeight,
        Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset
          (ι := (Nat.primesLE R : Finset ℕ))
          (s := (Finset.univ :
            Finset (Finset (PairedDivisorOccurrence κ))))
          (g := fun p S =>
            if S.Nonempty then
              (1 : ℝ) / ((p : ℕ) : ℝ)
            else 1))
    _ = ∏ p : (Nat.primesLE R : Finset ℕ),
          (1 +
            ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
              ((p : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact sum_pairedDivisorOccurrence_localWeight (p : ℕ)
    _ = ∏ p ∈ Nat.primesLE R,
          (1 +
            ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
              (p : ℝ)) := by
      exact Finset.prod_coe_sort
        (Nat.primesLE R)
        (fun p : ℕ =>
          1 +
            ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
              (p : ℝ))

/-! ## Encoding supported divisor families -/

@[simp]
theorem mem_pairedPrimeOccurrenceAssignmentOf
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (z : κ → ℕ × ℕ)
    (p : (Nat.primesLE R : Finset ℕ))
    (i : PairedDivisorOccurrence κ) :
    i ∈ pairedPrimeOccurrenceAssignmentOf R z p ↔
      (p : ℕ) ∣ pairedDivisorOccurrenceValue z i := by
  simp [pairedPrimeOccurrenceAssignmentOf]

theorem nonempty_pairedPrimeOccurrenceAssignmentOf_iff_support
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (z : κ → ℕ × ℕ)
    (p : (Nat.primesLE R : Finset ℕ)) :
    (pairedPrimeOccurrenceAssignmentOf R z p).Nonempty ↔
      (pairedPrimeSupport z (p : ℕ)).Nonempty := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primesLE p.2
  constructor
  · rintro ⟨i, hi⟩
    have hpi :
        (p : ℕ) ∣ pairedDivisorOccurrenceValue z i :=
      (mem_pairedPrimeOccurrenceAssignmentOf R z p i).mp hi
    cases i with
    | inl q =>
        refine ⟨q, (mem_pairedPrimeSupport z (p : ℕ) q).2 ?_⟩
        exact Nat.dvd_lcm_of_dvd_left hpi (z q).2
    | inr q =>
        refine ⟨q, (mem_pairedPrimeSupport z (p : ℕ) q).2 ?_⟩
        exact Nat.dvd_lcm_of_dvd_right hpi (z q).1
  · rintro ⟨q, hq⟩
    have hpLocal :
        (p : ℕ) ∣ Nat.lcm (z q).1 (z q).2 := by
      simpa [pairedLocalModulus] using
        (mem_pairedPrimeSupport z (p : ℕ) q).mp hq
    rcases hp.dvd_lcm.mp hpLocal with hpLeft | hpRight
    · refine ⟨Sum.inl q, ?_⟩
      exact (mem_pairedPrimeOccurrenceAssignmentOf
        R z p (Sum.inl q)).2 hpLeft
    · refine ⟨Sum.inr q, ?_⟩
      exact (mem_pairedPrimeOccurrenceAssignmentOf
        R z p (Sum.inr q)).2 hpRight

theorem nonempty_pairedPrimeOccurrenceAssignmentOf_iff_mem_primeFactors
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (Nat.primesLE R : Finset ℕ)) :
    (pairedPrimeOccurrenceAssignmentOf R z p).Nonempty ↔
      (p : ℕ) ∈ (pairedDivisorLcm z).primeFactors := by
  rw [nonempty_pairedPrimeOccurrenceAssignmentOf_iff_support,
    mem_primeFactors_pairedDivisorLcm_iff hz]
  simp [Nat.prime_of_mem_primesLE p.2]

theorem primeFactors_pairedDivisorLcm_subset_primesLE
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z) :
    (pairedDivisorLcm z).primeFactors ⊆ Nat.primesLE R := by
  intro p hpD
  have hpPrime : p.Prime :=
    Nat.prime_of_mem_primeFactors hpD
  have hpSupport :
      (pairedPrimeSupport z p).Nonempty :=
    ((mem_primeFactors_pairedDivisorLcm_iff hz p).mp hpD).2
  obtain ⟨q, hq⟩ := hpSupport
  have hpLocal :
      p ∣ Nat.lcm (z q).1 (z q).2 := by
    simpa [pairedLocalModulus] using
      (mem_pairedPrimeSupport z p q).mp hq
  have hzq :=
    Fintype.mem_piFinset.mp hzR q
  have hleftMem :=
    (Finset.mem_product.mp hzq).1
  have hrightMem :=
    (Finset.mem_product.mp hzq).2
  have hleftPos : 0 < (z q).1 :=
    (Finset.mem_Icc.mp hleftMem).1
  have hrightPos : 0 < (z q).2 :=
    (Finset.mem_Icc.mp hrightMem).1
  have hleftLe : (z q).1 ≤ R :=
    (Finset.mem_Icc.mp hleftMem).2
  have hrightLe : (z q).2 ≤ R :=
    (Finset.mem_Icc.mp hrightMem).2
  rw [Nat.mem_primesLE]
  refine ⟨?_, hpPrime⟩
  rcases hpPrime.dvd_lcm.mp hpLocal with hpLeft | hpRight
  · exact (Nat.le_of_dvd hleftPos hpLeft).trans hleftLe
  · exact (Nat.le_of_dvd hrightPos hpRight).trans hrightLe

theorem pairedPrimeOccurrenceAssignmentWeight_of_divisor_eq_inv_lcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z) :
    pairedPrimeOccurrenceAssignmentWeight
        (pairedPrimeOccurrenceAssignmentOf R z) =
      (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  classical
  unfold pairedPrimeOccurrenceAssignmentWeight
  calc
    (∏ p : (Nat.primesLE R : Finset ℕ),
        if (pairedPrimeOccurrenceAssignmentOf R z p).Nonempty then
          (1 : ℝ) / (p : ℝ)
        else 1) =
        ∏ p : (Nat.primesLE R : Finset ℕ),
          if (p : ℕ) ∈ (pairedDivisorLcm z).primeFactors then
            (1 : ℝ) / (p : ℝ)
          else 1 := by
      apply Finset.prod_congr rfl
      intro p _hp
      simp only [
        nonempty_pairedPrimeOccurrenceAssignmentOf_iff_mem_primeFactors
          R z hz p]
    _ = ∏ p ∈ Nat.primesLE R,
          if p ∈ (pairedDivisorLcm z).primeFactors then
            (1 : ℝ) / (p : ℝ)
          else 1 := by
      exact Finset.prod_coe_sort
        (Nat.primesLE R)
        (fun p : ℕ =>
          if p ∈ (pairedDivisorLcm z).primeFactors then
            (1 : ℝ) / (p : ℝ)
          else 1)
    _ = ∏ p ∈ (pairedDivisorLcm z).primeFactors,
          (1 : ℝ) / (p : ℝ) := by
      rw [Finset.prod_ite_mem,
        Finset.inter_eq_right.mpr
          (primeFactors_pairedDivisorLcm_subset_primesLE hzR hz)]
    _ = (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
      rw [← Finset.prod_coe_sort]
      exact prod_inv_primeFactors_eq_inv_of_squarefree
        (squarefree_pairedDivisorLcm hz)

theorem pairedDivisorOccurrenceValue_mem_Icc
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (i : PairedDivisorOccurrence κ) :
    pairedDivisorOccurrenceValue z i ∈ Finset.Icc 1 R := by
  have hzq := Fintype.mem_piFinset.mp hzR
  cases i with
  | inl q =>
      exact (Finset.mem_product.mp (hzq q)).1
  | inr q =>
      exact (Finset.mem_product.mp (hzq q)).2

theorem squarefree_pairedDivisorOccurrenceValue
    {κ : Type*} {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (i : PairedDivisorOccurrence κ) :
    Squarefree (pairedDivisorOccurrenceValue z i) := by
  cases i with
  | inl q => exact (hz q).1
  | inr q => exact (hz q).2

theorem pairedDivisorOccurrenceValue_eq_of_assignment_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z z' : κ → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz'R : z' ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z)
    (hz' : SquarefreePairedDivisorChoice z')
    (hassign :
      pairedPrimeOccurrenceAssignmentOf R z =
        pairedPrimeOccurrenceAssignmentOf R z')
    (i : PairedDivisorOccurrence κ) :
    pairedDivisorOccurrenceValue z i =
      pairedDivisorOccurrenceValue z' i := by
  have hprimeFactors :
      (pairedDivisorOccurrenceValue z i).primeFactors =
        (pairedDivisorOccurrenceValue z' i).primeFactors := by
    ext p
    constructor
    · intro hpz
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors hpz
      have hpDiv :
          p ∣ pairedDivisorOccurrenceValue z i :=
        Nat.dvd_of_mem_primeFactors hpz
      have hzi :=
        Finset.mem_Icc.mp
          (pairedDivisorOccurrenceValue_mem_Icc hzR i)
      have hpLeR :
          p ≤ R :=
        (Nat.le_of_dvd hzi.1 hpDiv).trans hzi.2
      have hpR : p ∈ Nat.primesLE R :=
        Nat.mem_primesLE.mpr ⟨hpLeR, hpPrime⟩
      let pR : (Nat.primesLE R : Finset ℕ) := ⟨p, hpR⟩
      have hi :
          i ∈ pairedPrimeOccurrenceAssignmentOf R z pR :=
        (mem_pairedPrimeOccurrenceAssignmentOf R z pR i).2 hpDiv
      have hfiber :
          pairedPrimeOccurrenceAssignmentOf R z pR =
            pairedPrimeOccurrenceAssignmentOf R z' pR :=
        congrFun hassign pR
      have hi' :
          i ∈ pairedPrimeOccurrenceAssignmentOf R z' pR := by
        rw [← hfiber]
        exact hi
      have hpDiv' :
          p ∣ pairedDivisorOccurrenceValue z' i :=
        (mem_pairedPrimeOccurrenceAssignmentOf R z' pR i).1 hi'
      exact Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpDiv',
          (squarefree_pairedDivisorOccurrenceValue hz' i).ne_zero⟩
    · intro hpz'
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors hpz'
      have hpDiv :
          p ∣ pairedDivisorOccurrenceValue z' i :=
        Nat.dvd_of_mem_primeFactors hpz'
      have hz'i :=
        Finset.mem_Icc.mp
          (pairedDivisorOccurrenceValue_mem_Icc hz'R i)
      have hpLeR :
          p ≤ R :=
        (Nat.le_of_dvd hz'i.1 hpDiv).trans hz'i.2
      have hpR : p ∈ Nat.primesLE R :=
        Nat.mem_primesLE.mpr ⟨hpLeR, hpPrime⟩
      let pR : (Nat.primesLE R : Finset ℕ) := ⟨p, hpR⟩
      have hi :
          i ∈ pairedPrimeOccurrenceAssignmentOf R z' pR :=
        (mem_pairedPrimeOccurrenceAssignmentOf R z' pR i).2 hpDiv
      have hfiber :
          pairedPrimeOccurrenceAssignmentOf R z pR =
            pairedPrimeOccurrenceAssignmentOf R z' pR :=
        congrFun hassign pR
      have hi' :
          i ∈ pairedPrimeOccurrenceAssignmentOf R z pR := by
        rw [hfiber]
        exact hi
      have hpDiv' :
          p ∣ pairedDivisorOccurrenceValue z i :=
        (mem_pairedPrimeOccurrenceAssignmentOf R z pR i).1 hi'
      exact Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpDiv',
          (squarefree_pairedDivisorOccurrenceValue hz i).ne_zero⟩
  calc
    pairedDivisorOccurrenceValue z i =
        ∏ p ∈ (pairedDivisorOccurrenceValue z i).primeFactors, p := by
      symm
      exact Nat.prod_primeFactors_of_squarefree
        (squarefree_pairedDivisorOccurrenceValue hz i)
    _ = ∏ p ∈ (pairedDivisorOccurrenceValue z' i).primeFactors, p := by
      rw [hprimeFactors]
    _ = pairedDivisorOccurrenceValue z' i :=
      Nat.prod_primeFactors_of_squarefree
        (squarefree_pairedDivisorOccurrenceValue hz' i)

theorem pairedPrimeOccurrenceAssignmentOf_injective_on_smooth_squarefree
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z z' : κ → ℕ × ℕ}
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz'R : z' ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z)
    (hz' : SquarefreePairedDivisorChoice z')
    (hassign :
      pairedPrimeOccurrenceAssignmentOf R z =
        pairedPrimeOccurrenceAssignmentOf R z') :
    z = z' := by
  funext q
  apply Prod.ext
  · exact pairedDivisorOccurrenceValue_eq_of_assignment_eq
      hzR hz'R hz hz' hassign (Sum.inl q)
  · exact pairedDivisorOccurrenceValue_eq_of_assignment_eq
      hzR hz'R hz hz' hassign (Sum.inr q)

/-! ## Möbius mass as the squarefree indicator -/

theorem pairedDivisorMoebiusMass_eq_one_of_squarefree
    {κ : Type*} [Fintype κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisorMoebiusMass z = 1 := by
  unfold pairedDivisorMoebiusMass
  have hleft :
      ∀ q : κ,
        |(ArithmeticFunction.moebius (z q).1 : ℝ)| = 1 := by
    intro q
    exact_mod_cast
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (hz q).1
  have hright :
      ∀ q : κ,
        |(ArithmeticFunction.moebius (z q).2 : ℝ)| = 1 := by
    intro q
    exact_mod_cast
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (hz q).2
  simp [hleft, hright]

theorem pairedDivisorMoebiusMass_eq_zero_of_not_squarefree
    {κ : Type*} [Fintype κ]
    {z : κ → ℕ × ℕ}
    (hz : ¬SquarefreePairedDivisorChoice z) :
    pairedDivisorMoebiusMass z = 0 := by
  classical
  by_cases hleft : ∀ q : κ, Squarefree (z q).1
  · have hrightNot : ∃ q : κ, ¬Squarefree (z q).2 := by
      by_contra hright
      apply hz
      intro q
      exact ⟨hleft q,
        Classical.byContradiction fun hq => hright ⟨q, hq⟩⟩
    obtain ⟨q, hq⟩ := hrightNot
    unfold pairedDivisorMoebiusMass
    have hzero :
        (ArithmeticFunction.moebius (z q).2 : ℝ) = 0 := by
      exact_mod_cast
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    have hprodZero :
        (∏ r : κ,
          |(ArithmeticFunction.moebius (z r).2 : ℝ)|) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hzero])
    rw [hprodZero, mul_zero]
  · obtain ⟨q, hq⟩ := Classical.not_forall.mp hleft
    unfold pairedDivisorMoebiusMass
    have hzero :
        (ArithmeticFunction.moebius (z q).1 : ℝ) = 0 := by
      exact_mod_cast
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    have hprodZero :
        (∏ r : κ,
          |(ArithmeticFunction.moebius (z r).1 : ℝ)|) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hzero])
    rw [hprodZero, zero_mul]

/-- The squarefree part of the coordinatewise-truncated paired divisor
family. -/
noncomputable def squarefreeSmoothPairedDivisorChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) : Finset (κ → ℕ × ℕ) := by
  classical
  exact (smoothDivisorFamilyChoices κ R).filter
    SquarefreePairedDivisorChoice

@[simp]
theorem mem_squarefreeSmoothPairedDivisorChoices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ} :
    z ∈ squarefreeSmoothPairedDivisorChoices κ R ↔
      z ∈ smoothDivisorFamilyChoices κ R ∧
        SquarefreePairedDivisorChoice z := by
  classical
  simp [squarefreeSmoothPairedDivisorChoices]

/-- Möbius zeros reduce the harmonic mass exactly to the squarefree part of
the coordinatewise-truncated family. -/
theorem pairedDivisorHarmonicLcmMass_eq_sum_squarefree
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    pairedDivisorHarmonicLcmMass (κ := κ) R =
      ∑ z ∈ squarefreeSmoothPairedDivisorChoices κ R,
        (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  classical
  unfold pairedDivisorHarmonicLcmMass
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        ((1 : ℝ) / (pairedDivisorLcm z : ℝ)) *
          pairedDivisorMoebiusMass z) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          if SquarefreePairedDivisorChoice z then
            (1 : ℝ) / (pairedDivisorLcm z : ℝ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro z _hzR
      by_cases hz : SquarefreePairedDivisorChoice z
      · rw [pairedDivisorMoebiusMass_eq_one_of_squarefree hz]
        simp [hz]
      · rw [pairedDivisorMoebiusMass_eq_zero_of_not_squarefree hz]
        simp [hz]
    _ = ∑ z ∈ squarefreeSmoothPairedDivisorChoices κ R,
          (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
      unfold squarefreeSmoothPairedDivisorChoices
      rw [Finset.sum_filter]

/-! ## The harmonic LCM Euler majorant -/

/-- The finite Euler product obtained after independently allowing every
prime `p ≤ R` to occur in any nonempty subset of the paired divisor slots. -/
noncomputable def pairedDivisorHarmonicEulerMajorant
    (κ : Type*) [Fintype κ] (R : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE R,
    (1 +
      ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
        (p : ℝ))

theorem pairedDivisorHarmonicEulerMajorant_nonneg
    (κ : Type*) [Fintype κ] (R : ℕ) :
    0 ≤ pairedDivisorHarmonicEulerMajorant κ R := by
  unfold pairedDivisorHarmonicEulerMajorant
  exact Finset.prod_nonneg fun p _ => by positivity

/-- **Finite combinatorial Euler bound.**  The coordinatewise divisor
cutoff is used only to inject its squarefree support into the unrestricted
prime-occurrence assignment space.  Thus the comparison is deliberately an
inequality, not an equality. -/
theorem pairedDivisorHarmonicLcmMass_le_primeProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    pairedDivisorHarmonicLcmMass (κ := κ) R ≤
      ∏ p ∈ Nat.primesLE R,
        (1 +
          ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
            (p : ℝ)) := by
  classical
  let s := squarefreeSmoothPairedDivisorChoices κ R
  let encode :
      (κ → ℕ × ℕ) → PairedPrimeOccurrenceAssignment κ R :=
    pairedPrimeOccurrenceAssignmentOf R
  have hinj : Set.InjOn encode (s : Set (κ → ℕ × ℕ)) := by
    intro z hz z' hz' hEq
    have hzData :=
      mem_squarefreeSmoothPairedDivisorChoices.mp hz
    have hz'Data :=
      mem_squarefreeSmoothPairedDivisorChoices.mp hz'
    exact
      pairedPrimeOccurrenceAssignmentOf_injective_on_smooth_squarefree
        hzData.1 hz'Data.1 hzData.2 hz'Data.2 hEq
  calc
    pairedDivisorHarmonicLcmMass (κ := κ) R =
        ∑ z ∈ s, (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
      simpa [s] using
        pairedDivisorHarmonicLcmMass_eq_sum_squarefree
          (κ := κ) R
    _ = ∑ z ∈ s,
          pairedPrimeOccurrenceAssignmentWeight (encode z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzData :=
        mem_squarefreeSmoothPairedDivisorChoices.mp hz
      exact
        (pairedPrimeOccurrenceAssignmentWeight_of_divisor_eq_inv_lcm
          hzData.1 hzData.2).symm
    _ = ∑ A ∈ s.image encode,
          pairedPrimeOccurrenceAssignmentWeight A := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ A : PairedPrimeOccurrenceAssignment κ R,
          pairedPrimeOccurrenceAssignmentWeight A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (s.image encode))
      intro A _hA _hnot
      exact pairedPrimeOccurrenceAssignmentWeight_nonneg A
    _ = ∏ p ∈ Nat.primesLE R,
          (1 +
            ((2 ^ (2 * Fintype.card κ) - 1 : ℕ) : ℝ) /
              (p : ℝ)) :=
      sum_pairedPrimeOccurrenceAssignmentWeight R

theorem pairedDivisorHarmonicLcmMass_le_eulerMajorant
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    pairedDivisorHarmonicLcmMass (κ := κ) R ≤
      pairedDivisorHarmonicEulerMajorant κ R := by
  exact pairedDivisorHarmonicLcmMass_le_primeProduct R

/-! ## Selected and Selberg-scaled corollaries -/

/-- The selected Selberg prefactor times the finite harmonic Euler
majorant.  Unlike the carry coefficient mass, it is independent of `N` and
the residue `b`. -/
noncomputable def selectedCFZScaledHarmonicEulerMajorant
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R W| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    pairedDivisorHarmonicEulerMajorant
      (SelectedCFZFormIndex e) R

theorem selectedCFZScaledHarmonicEulerMajorant_nonneg
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZScaledHarmonicEulerMajorant R W e := by
  unfold selectedCFZScaledHarmonicEulerMajorant
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (pairedDivisorHarmonicEulerMajorant_nonneg
      (SelectedCFZFormIndex e) R)

/-- Explicit prime-product bound for the selected scaled harmonic mass. -/
theorem selectedCFZScaledHarmonicLcmMass_le_primeProduct
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) :
    χ.selectedCFZScaledHarmonicLcmMass R W e ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∏ p ∈ Nat.primesLE R,
          (1 +
            ((2 ^ (2 *
                Fintype.card (SelectedCFZFormIndex e)) - 1 : ℕ) : ℝ) /
              (p : ℝ)) := by
  unfold selectedCFZScaledHarmonicLcmMass
  exact mul_le_mul_of_nonneg_left
    (pairedDivisorHarmonicLcmMass_le_primeProduct R)
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))

theorem selectedCFZScaledHarmonicLcmMass_le_eulerMajorant
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) :
    χ.selectedCFZScaledHarmonicLcmMass R W e ≤
      χ.selectedCFZScaledHarmonicEulerMajorant R W e := by
  exact χ.selectedCFZScaledHarmonicLcmMass_le_primeProduct R W e

/-- Exceptional-prime coverage now bounds the actual scaled carry
coefficient mass by the explicit finite Euler majorant. -/
theorem
    selectedCFZCarryScaledFourierCoefficientMass_le_harmonicEulerMajorant
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k) (R : ℕ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    χ.selectedCFZCarryScaledFourierCoefficientMass
        (N := N) R W b e ≤
      χ.selectedCFZScaledHarmonicEulerMajorant R W e := by
  exact
    (χ.selectedCFZCarryScaledFourierCoefficientMass_le_scaledHarmonicLcmMass
      (N := N) hk hWb e R hcover).trans
      (χ.selectedCFZScaledHarmonicLcmMass_le_eulerMajorant R W e)

/-- The fully scaled complementary Fourier integral is bounded by the
finite Euler majorant times the universal Schwartz tail. -/
theorem selectedCFZCarryScaledFourierTailNorm_le_harmonicEulerMajorant
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k) (R : ℕ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (T : ℝ) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R W b e T ≤
      χ.selectedCFZScaledHarmonicEulerMajorant R W e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  calc
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R W b e T ≤
      χ.selectedCFZScaledHarmonicLcmMass R W e *
        χ.selectedCFZPairedFourierAbsoluteTail e T :=
      χ.selectedCFZCarryScaledFourierTailNorm_le_scaledHarmonicLcmMass
        (N := N) hk hWb e R hcover T
    _ ≤
      χ.selectedCFZScaledHarmonicEulerMajorant R W e *
        χ.selectedCFZPairedFourierAbsoluteTail e T :=
      mul_le_mul_of_nonneg_right
        (χ.selectedCFZScaledHarmonicLcmMass_le_eulerMajorant R W e)
        (χ.selectedCFZPairedFourierAbsoluteTail_nonneg e T)

/-- Primorial specialization of the explicit Euler-majorant tail bound. -/
theorem
    selectedCFZCarryScaledFourierTailNorm_le_harmonicEulerMajorant_primorial
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) (R : ℕ) (T : ℝ) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e T ≤
      χ.selectedCFZScaledHarmonicEulerMajorant
          R (primorial w) e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  exact
    χ.selectedCFZCarryScaledFourierTailNorm_le_harmonicEulerMajorant
      (N := N) hk hwb e R
      (fun p hp hpW =>
        selectedCFZ_exceptionalPrime_covered_by_primorial
          hbound hp hpW)
      T

/-- Growing-primorial tail vanishing now requires boundedness only of the
explicit scaled Euler majorant. -/
theorem
    tendsto_selectedCFZCarryScaledFourierTailNorm_sqrt_log_primorial_of_eulerMajorant
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ R, Nseq R ≠ 0)
    (hbound :
      ∀ R,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq R)
    (hcoprime :
      ∀ R, (primorial (wseq R)).Coprime (bseq R))
    (e : LinearFormsExponent k) (C : ℝ)
    (hMass :
      ∀ᶠ R : ℕ in Filter.atTop,
        χ.selectedCFZScaledHarmonicEulerMajorant
          R (primorial (wseq R)) e ≤ C) :
    Filter.Tendsto
      (fun R : ℕ =>
        letI : NeZero (Nseq R) := ⟨hN R⟩
        χ.selectedCFZCarryScaledFourierTailNorm
          (N := Nseq R) R (primorial (wseq R)) (bseq R) e
          (Real.sqrt (Real.log R)))
      Filter.atTop (nhds 0) := by
  apply
    χ.tendsto_selectedCFZCarryScaledFourierTailNorm_sqrt_log_primorial_of_harmonic
      hk Nseq wseq bseq hN hbound hcoprime e C
  filter_upwards [hMass] with R hR
  exact
    (χ.selectedCFZScaledHarmonicLcmMass_le_eulerMajorant
      R (primorial (wseq R)) e).trans hR

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
