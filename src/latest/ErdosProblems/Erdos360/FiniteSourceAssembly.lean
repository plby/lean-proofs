/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerAssembly
import ErdosProblems.Erdos360.RandomDiversity

/-!
# Finite source assembly for Erdős 360

This scratch file identifies the smallest remaining source inputs between
the checked random-diversity theorem and the public lower-bound assembly.
It deliberately separates three independent obligations:

* a prime dyadic test set and its elementary large-prime factorization;
* the local modular-growth certificate for every random pool;
* Lev's high-multiplicity interval theorem.

Everything which merely packages these inputs into
`CFPTestSetSourceCompletion`, `EventuallyCFPTestSetTheorem`, and finally
`Resolution` is proved below.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## The exact Lev input -/

/-- The source form of CFP Lemma 2.2.  The diameter parameter counts
spacings, so a set contained in `Icc 0 diameter` lies in an interval of
`diameter + 1` integer points. -/
def CFPLevHighMultiplicityPrinciple : Prop :=
  ∀ (parts : List (Finset ℕ)) (ell nzero diameter : ℕ),
    IsCFPLevFamily parts ell nzero diameter →
    3 ≤ nzero →
    2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell →
    HasCFPLevInterval parts ell nzero

/-! ## Random pools before Lev -/

/-- The exact conclusion returned by the public iterated random-diversity
theorem. -/
def IsCFPRandomParts (A : Finset ℕ) (ell s diversity : ℕ)
    (parts : List (Finset ℕ)) : Prop :=
  parts.length = ell ∧
    parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
    ∀ P ∈ parts, P ⊆ A ∧ P.card = s ∧
      DiverseSampling.DiverseNat P diversity

/-- Source data after the random pools and their ordinary-growth
certificates have been constructed, but before applying Lev.  In
particular, this structure does not assume the desired quotient subset sum.
-/
structure CFPPreLevSourceData (n d y : ℕ) (Z : Finset ℕ) where
  parts : List (Finset ℕ)
  ell : ℕ
  nzero : ℕ
  diameter : ℕ
  length_eq : parts.length = ell
  pairwise : parts.Pairwise (fun P Q ↦ Disjoint P Q)
  ordinary : ∀ P ∈ parts,
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter)
  nzero_ge : 3 ≤ nzero
  lev_multiplicity :
    2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell
  parts_subset : ∀ P ∈ parts, P ⊆ Z
  dyadic_width : 2 * y ≤ ell * (nzero - 1) + 1
  sum_upper : (∑ z ∈ levFamilyUnion parts, z) < n / d
  unused_mass : n / d ≤
    (y / d + 1) * (Z.card - (levFamilyUnion parts).card)
  nonempty : Z.Nonempty

/-- The ordinary certificates in pre-Lev data produce exactly the family
hypothesis consumed by the high-multiplicity theorem. -/
theorem CFPPreLevSourceData.family
    {n d y : ℕ} {Z : Finset ℕ}
    (h : CFPPreLevSourceData n d y Z) :
    IsCFPLevFamily h.parts h.ell h.nzero h.diameter :=
  ⟨h.length_eq, h.pairwise, by
    intro P hP
    exact Classical.choice (h.ordinary P hP) |>.ordinary_properties⟩

/-- Applying only the exact Lev principle converts pre-Lev data to the
public raw source package. -/
noncomputable def CFPPreLevSourceData.toRawSourceData
    {n d y : ℕ} {Z : Finset ℕ}
    (h : CFPPreLevSourceData n d y Z)
    (hlev : CFPLevHighMultiplicityPrinciple) :
    CFPLevRawSourceData n d y Z where
  parts := h.parts
  ell := h.ell
  nzero := h.nzero
  diameter := h.diameter
  length_eq := h.length_eq
  pairwise := h.pairwise
  ordinary := h.ordinary
  lev := hlev h.parts h.ell h.nzero h.diameter h.family
    h.nzero_ge h.lev_multiplicity
  parts_subset := h.parts_subset
  dyadic_width := h.dyadic_width
  sum_upper := h.sum_upper
  unused_mass := h.unused_mass
  nonempty := h.nonempty

/-- All finite inputs for the public random-pool theorem.  The field
`ordinary` is the unique local additive-combinatorial input: in the CFP
proof it is obtained by splitting a pool into seed and pivots, applying the
modular phase machine, and using the corrected local DF theorem to exclude
small selected shifts.  The remaining fields are the exact integer
parameter ledger and R7--R9 estimates. -/
structure CFPRandomPreLevInput (n d y : ℕ) (Z : Finset ℕ) where
  A : Finset ℕ
  k : ℕ
  N : ℕ
  h : ℕ
  s : ℕ
  ell : ℕ
  diversity : ℕ
  nzero : ℕ
  diameter : ℕ
  A_subset : A ⊆ Z
  count_room : ell + 2 ≤ h
  card_A : A.card = h * s
  diverse_A : DiverseSampling.DiverseNat A k
  range_A : ∀ a ∈ A, 0 < a ∧ a ≤ N
  probability_ledger : ∀ i < ell,
    RandomDiversity.exactSplitFailureMass N s (h - i)
      (RandomDiversity.residualDiversity k h i) < 1
  diversity_ledger : ∀ i < ell,
    diversity ≤ RandomDiversity.residualDiversity k h i /
      (2 * (h - i))
  ordinary : ∀ P : Finset ℕ, P ⊆ A → P.card = s →
    DiverseSampling.DiverseNat P diversity →
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter)
  nzero_ge : 3 ≤ nzero
  lev_multiplicity :
    2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell
  dyadic_width : 2 * y ≤ ell * (nzero - 1) + 1
  post_partition : ∀ parts : List (Finset ℕ),
    IsCFPRandomParts A ell s diversity parts →
    (∑ z ∈ levFamilyUnion parts, z) < n / d ∧
      n / d ≤
        (y / d + 1) * (Z.card - (levFamilyUnion parts).card)
  Z_nonempty : Z.Nonempty

/-- The checked random-diversity theorem discharges the random partition;
only the local ordinary certificates and deterministic endpoint estimates
from `CFPRandomPreLevInput` remain. -/
noncomputable def CFPRandomPreLevInput.toPreLevSourceData
    {n d y : ℕ} {Z : Finset ℕ}
    (h : CFPRandomPreLevInput n d y Z) :
    CFPPreLevSourceData n d y Z := by
  let hex :=
    RandomDiversity.exists_disjoint_fixedCard_diverse_pieces
      h.count_room h.card_A h.diverse_A h.range_A
      h.probability_ledger h.diversity_ledger
  let parts := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hlen := hspec.1
  have hpair := hspec.2.1
  have hparts := hspec.2.2
  have hrandom : IsCFPRandomParts
      h.A h.ell h.s h.diversity parts :=
    ⟨hlen, hpair, hparts⟩
  have hpost := h.post_partition parts hrandom
  exact
    { parts := parts
      ell := h.ell
      nzero := h.nzero
      diameter := h.diameter
      length_eq := hlen
      pairwise := hpair
      ordinary := by
        intro P hP
        exact h.ordinary P (hparts P hP).1 (hparts P hP).2.1
          (hparts P hP).2.2
      nzero_ge := h.nzero_ge
      lev_multiplicity := h.lev_multiplicity
      parts_subset := by
        intro P hP
        exact (hparts P hP).1.trans h.A_subset
      dyadic_width := h.dyadic_width
      sum_upper := hpost.1
      unused_mass := hpost.2
      nonempty := h.Z_nonempty }

/-! ## From extracted color classes to the public source theorem -/

/-- Per-extraction source theorem at the last genuinely unresolved level.
Compared with `CFPTestSetSourceCompletion`, random pool selection and Lev
have not been assumed: the former is discharged by the preceding theorem,
while the latter is supplied independently as
`CFPLevHighMultiplicityPrinciple`. -/
def CFPRandomPreLevTestSetSourceCompletion
    (n colors y B L K : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (d : ℕ) (Z : Finset ℕ),
    Y.card ≤ colors * (integerColorClass Y c i).card →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
    (integerColorClass Y c i).card - Z.card ≤
      L * Nat.log 2 B + K * B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    Nonempty (CFPRandomPreLevInput n d y Z)

/-- Exact deterministic conversion to the public source theorem. -/
theorem cfpTestSetSourceCompletion_of_randomPreLev
    {n colors y B L K : ℕ} {Y : Finset (BelowTarget n)}
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : CFPRandomPreLevTestSetSourceCompletion
      n colors y B L K Y) :
    CFPTestSetSourceCompletion n colors y B L K Y := by
  intro c i d Z hlarge hd hdB hscale hloss hdiverse
  obtain ⟨hinput⟩ :=
    hsource c i d Z hlarge hd hdB hscale hloss hdiverse
  exact ⟨hinput.toPreLevSourceData.toRawSourceData hlev⟩

/-! ## Prime test sets and the eventual theorem -/

/-- One finite prime-test-set package.  This is the precise meeting point
of the prime-counting construction and the additive source theorem. -/
structure CFPPrimeRandomPreLevTestSetData
    (n colors y : ℕ) where
  Y : Finset (BelowTarget n)
  B : ℕ
  L : ℕ
  K : ℕ
  B_pos : 0 < B
  dyadic : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y
  large_prime_factor : ∀ x ∈ Y, ∃ u q : ℕ,
    u ∣ n ∧ q.Prime ∧ B < q ∧ x.1 = u * q
  source : CFPRandomPreLevTestSetSourceCompletion
    n colors y B L K Y

/-- The large-prime argument proves divisibility of the extracted common
factor; random selection, local modular growth, and Lev prove the quotient
subset sum. -/
theorem CFPPrimeRandomPreLevTestSetData.completion
    {n colors y : ℕ}
    (h : CFPPrimeRandomPreLevTestSetData n colors y)
    (hlev : CFPLevHighMultiplicityPrinciple) :
    CFPTestSetCompletion n colors y h.B h.L h.K h.Y := by
  apply cfpTestSetCompletion_of_large_prime_source h.large_prime_factor
  exact cfpTestSetSourceCompletion_of_randomPreLev hlev h.source

/-- The exact eventual residual statement.  Its fields correspond only to
the prime dyadic test set, source parameter ledger, and local modular
growth certificates; random partitioning and every later bookkeeping step
are no longer hypotheses. -/
def EventuallyCFPPrimeRandomPreLevTheorem (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    Nonempty (CFPPrimeRandomPreLevTestSetData n colors y)

/-- Complete conversion of the exact eventual residual statement to the
public test-set theorem. -/
theorem eventuallyCFPTestSetTheorem_of_primeRandomPreLev
    {c : ℝ}
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : EventuallyCFPPrimeRandomPreLevTheorem c) :
    EventuallyCFPTestSetTheorem c := by
  filter_upwards [hsource] with n hdata
  dsimp only at hdata ⊢
  obtain ⟨data⟩ := hdata
  exact ⟨data.Y, data.B, data.L, data.K, data.B_pos,
    data.dyadic, data.completion hlev⟩

/-- All public lower-bound layers are now discharged from the two exact
residual principles. -/
theorem resolution_of_primeRandomPreLev
    {c : ℝ} (hc : 0 < c)
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : EventuallyCFPPrimeRandomPreLevTheorem c) :
    Resolution := by
  apply resolution_of_exists_eventually_forces_floor
  exact ⟨c, hc, eventuallyForcesResolutionFloor_of_CFPTestSet hc
    (eventuallyCFPTestSetTheorem_of_primeRandomPreLev hlev hsource)⟩

end Erdos360

#print axioms Erdos360.resolution_of_primeRandomPreLev
