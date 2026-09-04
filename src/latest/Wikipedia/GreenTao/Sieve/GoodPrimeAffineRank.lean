import Wikipedia.GreenTao.Sieve.PairedLocalFactors

/-!
# Rank-two affine densities at good primes

For a finite system of affine forms, failure of rank two modulo `p` is
detected by the vanishing of every two-by-two coefficient minor for some
distinct pair.  This file isolates a finite, explicit exceptional set using
the sum of the absolute values of all such minors.

Outside that set, pairwise independent integer coefficient vectors remain
rank two modulo `p`.  Thus every selected subfamily containing two distinct
indices has common-zero density at most `1 / p²`: its common-zero set is
contained in the common-zero set of one rank-two pair.  This is the actual
higher-order density estimate needed for the CFZ family.  Repeated indices do
not create rank, so the hypotheses use a `Finset` and explicitly require it
to be nontrivial.

The final results instantiate
`HasGoodPrimeHigherOrderDensityEstimate` for the CFZ forms and package the
estimate together with the exact local-factor inclusion--exclusion formula.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## An explicit finite exceptional set for rank two -/

/-- Sum of the absolute values of all ordered two-form coefficient minors.
Unlike `exceptionalPrimeBound`, this bound contains only the determinants
relevant to rank two. -/
def affineRankTwoMinorBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : ℕ :=
  ∑ q : κ, ∑ r : κ, ∑ i : ι, ∑ j : ι,
    Int.natAbs
      ((forms q).coefficientMinor (forms r) i j)

/-- Every coefficient minor is bounded by the explicit rank-two minor sum. -/
theorem minor_natAbs_le_affineRankTwoMinorBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ)
    (q r : κ) (i j : ι) :
    Int.natAbs
        ((forms q).coefficientMinor (forms r) i j) ≤
      affineRankTwoMinorBound forms := by
  have hj :
      Int.natAbs
          ((forms q).coefficientMinor (forms r) i j) ≤
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j') :=
    Finset.single_le_sum
      (f := fun j' : ι =>
        Int.natAbs
          ((forms q).coefficientMinor (forms r) i j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi :
      (∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j')) ≤
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j') :=
    Finset.single_le_sum
      (f := fun i' : ι =>
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hr :
      (∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j')) ≤
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun r' : κ =>
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hq :
      (∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j')) ≤
        ∑ q' : κ, ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun q' : κ =>
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact hj.trans (hi.trans (hr.trans hq))

/-- Pairwise independence supplies a nonzero minor modulo every modulus
larger than the rank-two minor bound. -/
theorem exists_minor_cast_ne_zero_of_affineRankTwoMinorBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hlarge : affineRankTwoMinorBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    exists_coefficientMinor_ne_zero (hforms hqr)
  refine ⟨i, j, intCast_zmod_ne_zero_of_natAbs_lt hij ?_⟩
  exact
    (minor_natAbs_le_affineRankTwoMinorBound
      forms q r i j).trans_lt hlarge

/-- A conservative finite set containing every prime at which a nonzero
integer minor might vanish: all primes at most the explicit minor bound. -/
def affineRankTwoExceptionalPrimes
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : Finset ℕ :=
  (Finset.range (affineRankTwoMinorBound forms + 1)).filter
    Nat.Prime

@[simp]
theorem mem_affineRankTwoExceptionalPrimes
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) (p : ℕ) :
    p ∈ affineRankTwoExceptionalPrimes forms ↔
      p.Prime ∧ p ≤ affineRankTwoMinorBound forms := by
  simp [affineRankTwoExceptionalPrimes, and_comm]

/-- Every two distinct forms have a nonzero two-by-two minor modulo a
rank-two good prime. -/
def AffineRankTwoGoodPrime
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ) : Prop :=
  p.Prime ∧
    ∀ {q r : κ}, q ≠ r →
      ∃ i j : ι,
        (((forms q).coefficientMinor (forms r) i j : ℤ) :
          ZMod p) ≠ 0

/-- Outside the explicit finite minor set, a pairwise independent integer
system is rank-two good. -/
theorem affineRankTwoGoodPrime_of_not_mem
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : p.Prime)
    (hnot : p ∉ affineRankTwoExceptionalPrimes forms) :
    AffineRankTwoGoodPrime p forms := by
  have hlarge : affineRankTwoMinorBound forms < p := by
    by_contra h
    have hle : p ≤ affineRankTwoMinorBound forms :=
      Nat.le_of_not_gt h
    exact hnot
      ((mem_affineRankTwoExceptionalPrimes forms p).mpr
        ⟨hp, hle⟩)
  refine ⟨hp, ?_⟩
  intro q r hqr
  exact exists_minor_cast_ne_zero_of_affineRankTwoMinorBound
    hforms hlarge hqr

/-- The older all-purpose exceptional bound also implies the exact
rank-two good-prime condition. -/
theorem affineRankTwoGoodPrime_of_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    AffineRankTwoGoodPrime p forms := by
  refine ⟨hp, ?_⟩
  intro q r hqr
  exact exists_minor_cast_ne_zero_of_bound
    hforms hlarge hqr

/-- At a rank-two good prime, every distinct pair of reduced linear parts
maps surjectively onto two copies of `ZMod p`.  This is the formal rank-at-
least-two statement used by the density calculation. -/
theorem pairLinearMapZMod_surjective_of_affineRankTwoGoodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} (hgood : AffineRankTwoGoodPrime p forms)
    {q r : κ} (hqr : q ≠ r) :
    Function.Surjective
      (AffineForm.pairLinearMapZMod p (forms q) (forms r)) := by
  let : Fact p.Prime := ⟨hgood.1⟩
  obtain ⟨i, j, hij⟩ := hgood.2 hqr
  exact
    AffineForm.pairLinearMapZMod_surjective_of_minor_ne_zero
      (forms q) (forms r) hij

/-! ## Selected-family rank and density -/

/-- A selected family has rank at least two modulo `p` when it contains two
distinct indices with a nonvanishing coefficient minor.  Repetition alone
cannot witness this predicate. -/
def SelectedAffineFamilyHasRankAtLeastTwo
    {κ ι : Type*} [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : Prop :=
  ∃ q ∈ s, ∃ r ∈ s, q ≠ r ∧
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0

/-- A nontrivial selected finset has rank at least two at every rank-two
good prime. -/
theorem selectedAffineFamilyHasRankAtLeastTwo_of_goodPrime
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} (hgood : AffineRankTwoGoodPrime p forms)
    {s : Finset κ} (hs : s.Nontrivial) :
    SelectedAffineFamilyHasRankAtLeastTwo p forms s := by
  have hcard : 1 < s.card :=
    Finset.one_lt_card_iff_nontrivial.mpr hs
  obtain ⟨q, hq, r, hr, hqr⟩ :=
    Finset.one_lt_card.mp hcard
  exact ⟨q, hq, r, hr, hqr, hgood.2 hqr⟩

/-- Adding zero-congruence conditions can only shrink the common-zero
support. -/
theorem affineFamilyCommonZeroFinset_subset_pair
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) {q r : κ}
    (hq : q ∈ s) (hr : r ∈ s) :
    affineFamilyCommonZeroFinset p forms s ⊆
      affineFamilyCommonZeroFinset p forms {q, r} := by
  intro x hx
  have hall :=
    (mem_affineFamilyCommonZeroFinset p forms s x).mp hx
  apply
    (mem_affineFamilyCommonZeroFinset
      p forms {q, r} x).mpr
  intro t ht
  rcases Finset.mem_insert.mp ht with hqt | htr
  · subst t
    exact hall q hq
  · have : t = r := Finset.mem_singleton.mp htr
    subst t
    exact hall r hr

/-- Common-zero density is monotone under adding selected forms. -/
theorem affineFamilyZeroDensity_le_pair
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) {q r : κ}
    (hq : q ∈ s) (hr : r ∈ s) :
    affineFamilyZeroDensity p forms s ≤
      affineFamilyZeroDensity p forms {q, r} := by
  rw [affineFamilyZeroDensity_eq_card,
    affineFamilyZeroDensity_eq_card]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast
    Finset.card_le_card
      (affineFamilyCommonZeroFinset_subset_pair
        p forms s hq hr)

/-- Every affine-family zero density is nonnegative. -/
theorem affineFamilyZeroDensity_nonneg
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    0 ≤ affineFamilyZeroDensity p forms s := by
  rw [affineFamilyZeroDensity_eq_card]
  positivity

/-- A selected rank-two witness gives the sharp upper bound `1 / p²` for
the full common-zero density.  Equality is used only for the witnessing
pair; additional forms may reduce the density. -/
theorem affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (forms : κ → AffineForm ι ℤ)
    (s : Finset κ)
    (hrank :
      SelectedAffineFamilyHasRankAtLeastTwo p forms s) :
    affineFamilyZeroDensity p forms s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  obtain ⟨q, hq, r, hr, hqr, i, j, hij⟩ := hrank
  calc
    affineFamilyZeroDensity p forms s ≤
        affineFamilyZeroDensity p forms {q, r} :=
      affineFamilyZeroDensity_le_pair
        p forms s hq hr
    _ = (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [affineFamilyZeroDensity_pair p forms hqr]
      exact AffineForm.mean_zeroFinsetZMod_mul
        hp (forms q) (forms r) hij

/-- Rank-two good primes give the same bound for every nontrivial selected
subfamily. -/
theorem affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p]
    {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (s : Finset κ) (hs : s.Nontrivial) :
    affineFamilyZeroDensity p forms s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  exact affineFamilyZeroDensity_le_inv_sq_of_rankAtLeastTwo
    hgood.1 forms s
    (selectedAffineFamilyHasRankAtLeastTwo_of_goodPrime
      hgood hs)

/-- Pairwise-independent systems satisfy the higher-order estimate required
by `PairedLocalFactors`: every selected family of cardinality at least three
has density at most `1 / p²` at good primes. -/
theorem pairwiseIndependent_hasGoodPrimeHigherOrderDensityEstimate
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms) :
    HasGoodPrimeHigherOrderDensityEstimate forms
      (fun p _s => (1 : ℝ) / (p : ℝ) ^ 2) := by
  intro p _inst hp hlarge s hs
  rw [abs_of_nonneg
    (affineFamilyZeroDensity_nonneg p forms s)]
  apply affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      hforms hp hlarge)
  exact Finset.one_lt_card_iff_nontrivial.mp (by omega)

/-! ## CFZ specialization -/

/-- Explicit determinant-only cutoff for the full CFZ affine family. -/
def cfzRankTwoMinorBound (k : ℕ) : ℕ :=
  affineRankTwoMinorBound
    (fun q : CFZFormIndex k => cfzAffineForm q)

/-- Explicit finite set of potentially rank-degenerate primes for the full
CFZ family. -/
def cfzRankTwoExceptionalPrimes (k : ℕ) : Finset ℕ :=
  affineRankTwoExceptionalPrimes
    (fun q : CFZFormIndex k => cfzAffineForm q)

@[simp]
theorem mem_cfzRankTwoExceptionalPrimes
    (k p : ℕ) :
    p ∈ cfzRankTwoExceptionalPrimes k ↔
      p.Prime ∧ p ≤ cfzRankTwoMinorBound k := by
  exact
    mem_affineRankTwoExceptionalPrimes
      (fun q : CFZFormIndex k => cfzAffineForm q) p

/-- For `k ≥ 2`, every prime outside the explicit CFZ determinant set is
rank-two good.  The lower bound on `k` excludes the genuine small-system
degeneracy in which the pairwise-independence theorem is unavailable. -/
theorem cfzAffineRankTwoGoodPrime_of_not_mem
    {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hnot : p ∉ cfzRankTwoExceptionalPrimes k) :
    AffineRankTwoGoodPrime p
      (fun q : CFZFormIndex k => cfzAffineForm q) := by
  exact affineRankTwoGoodPrime_of_not_mem
    (cfzAffineForms_pairwiseIndependent hk)
    hp hnot

/-- Actual CFZ rank-two density estimate outside the explicit finite
determinant set.  A nontrivial `Finset` is exactly the collision-free
condition that two genuinely distinct CFZ indices were selected. -/
theorem cfzAffineFamilyZeroDensity_le_inv_sq_of_not_mem
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hnot : p ∉ cfzRankTwoExceptionalPrimes k)
    (s : Finset (CFZFormIndex k)) (hs : s.Nontrivial) :
    affineFamilyZeroDensity p
        (fun q : CFZFormIndex k => cfzAffineForm q) s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  exact affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    (cfzAffineRankTwoGoodPrime_of_not_mem hk hp hnot)
    s hs

/-- The same CFZ estimate using the common all-purpose exceptional-prime
bound consumed by the rest of the sieve API. -/
theorem cfzAffineFamilyZeroDensity_le_inv_sq_of_bound
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (s : Finset (CFZFormIndex k)) (hs : s.Nontrivial) :
    affineFamilyZeroDensity p
        (fun q : CFZFormIndex k => cfzAffineForm q) s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  apply affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_pairwiseIndependent hk) hp hlarge)
  exact hs

/-- The missing higher-order interface from `PairedLocalFactors` is
unconditionally inhabited for the CFZ forms once `k ≥ 2`. -/
theorem cfz_hasGoodPrimeHigherOrderDensityEstimate
    {k : ℕ} (hk : 2 ≤ k) :
    HasGoodPrimeHigherOrderDensityEstimate
      (fun q : CFZFormIndex k => cfzAffineForm q)
      (fun p _s => (1 : ℝ) / (p : ℝ) ^ 2) := by
  exact
    pairwiseIndependent_hasGoodPrimeHigherOrderDensityEstimate
      (cfzAffineForms_pairwiseIndependent hk)

/-- The exact local-factor product expansion together with its actual CFZ
higher-order rank-two bound.  This keeps the exact finite expansion and the
arithmetic estimate visibly separate. -/
theorem mean_cfzSystemLocalCoprimeWeight_expansion_and_rankTwo_bound
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    (mean (systemLocalCoprimeWeight p
        (fun q : CFZFormIndex k => cfzAffineForm q)) =
      ((p : ℝ) / (p - 1 : ℕ)) ^
          Fintype.card (CFZFormIndex k) *
        ∑ s ∈
            (Finset.univ :
              Finset (CFZFormIndex k)).powerset,
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroDensity p
              (fun q : CFZFormIndex k => cfzAffineForm q) s) ∧
      ∀ s : Finset (CFZFormIndex k), 3 ≤ s.card →
        affineFamilyZeroDensity p
            (fun q : CFZFormIndex k => cfzAffineForm q) s ≤
          (1 : ℝ) / (p : ℝ) ^ 2 := by
  constructor
  · exact
      mean_systemLocalCoprimeWeight_eq_inclusionExclusion
        p (fun q : CFZFormIndex k => cfzAffineForm q)
  · intro s hs
    apply cfzAffineFamilyZeroDensity_le_inv_sq_of_bound
      hk hp hlarge s
    exact Finset.one_lt_card_iff_nontrivial.mp (by omega)

/-- Existing Bonferroni bounds now specialize directly to the CFZ local
factor product at every good prime. -/
theorem mean_cfzSystemLocalCoprimeWeight_bounds
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    let scale :=
      ((p : ℝ) / (p - 1 : ℕ)) ^
        Fintype.card (CFZFormIndex k)
    scale *
          (1 - (Fintype.card (CFZFormIndex k) : ℝ) / p) ≤
        mean (systemLocalCoprimeWeight p
          (fun q : CFZFormIndex k => cfzAffineForm q)) ∧
      mean (systemLocalCoprimeWeight p
          (fun q : CFZFormIndex k => cfzAffineForm q)) ≤
        scale *
          (1 - (Fintype.card (CFZFormIndex k) : ℝ) / p +
            ((Fintype.card (CFZFormIndex k) *
              (Fintype.card (CFZFormIndex k) - 1) : ℕ) : ℝ) /
                (p : ℝ) ^ 2) := by
  exact mean_systemLocalCoprimeWeight_bounds
    (cfzAffineForms_nonzero hk)
    (cfzAffineForms_pairwiseIndependent hk)
    hp hlarge

end Wikipedia.SzemeredisTheorem
