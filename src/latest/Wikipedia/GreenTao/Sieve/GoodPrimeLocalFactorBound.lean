import Wikipedia.GreenTao.Sieve.GoodPrimeAffineRank

/-!
# Quantitative good-prime local-factor remainder

This file turns the rank-two common-zero estimate into the finite
inclusion--exclusion bound used by the local Euler-factor calculation.

We allow an arbitrary real coefficient `a q` on the zero indicator of each
form.  The empty support contributes exactly `1`, the singleton supports
contribute exactly `-(∑ q, a q) / p`, and every support of cardinality at
least two has density at most `1 / p²` at a rank-two good prime.  Hence the
remaining contribution is bounded by

`(∑ S, 2 ≤ S.card, ∏ q ∈ S, |a q|) / p²`.

This finite coefficient mass is also bounded by `∏ q, (1 + |a q|)`.  Taking
all coefficients equal to one recovers the unweighted avoidance product from
`LocalEulerFactors` and gives an explicit `2 ^ card κ / p²` error.  No
infinite Euler product or convergence statement is made here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Weighted finite inclusion--exclusion -/

/-- A real-weighted version of the local avoidance product. -/
noncomputable def weightedLocalAvoidanceProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℝ) (x : ι → ZMod p) : ℝ :=
  ∏ q, (1 -
    a q * finsetIndicator ((forms q).zeroFinsetZMod p) x)

/-- Pointwise weighted inclusion--exclusion over all selected supports. -/
theorem weightedLocalAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℝ) (x : ι → ZMod p) :
    weightedLocalAvoidanceProduct p forms a x =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
          affineFamilyZeroProduct p forms s x := by
  let I : κ → ℝ :=
    fun q =>
      a q * finsetIndicator ((forms q).zeroFinsetZMod p) x
  have h :=
    Finset.prod_sub (fun _q : κ => (1 : ℝ)) I
      (Finset.univ : Finset κ)
  simpa [weightedLocalAvoidanceProduct,
    affineFamilyZeroProduct, I, Finset.prod_mul_distrib,
    mul_assoc] using h

/-- Exact mean form of weighted inclusion--exclusion. -/
theorem mean_weightedLocalAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℝ) :
    mean (weightedLocalAvoidanceProduct p forms a) =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
          affineFamilyZeroDensity p forms s := by
  rw [show weightedLocalAvoidanceProduct p forms a =
      fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroProduct p forms s x by
    funext x
    exact weightedLocalAvoidanceProduct_eq_inclusionExclusion
      p forms a x]
  calc
    mean (fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroProduct p forms s x) =
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          mean (fun x =>
            ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
              affineFamilyZeroProduct p forms s x) :=
      mean_finset_sum
        (Finset.univ : Finset κ).powerset
        (fun s x =>
          ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroProduct p forms s x)
    _ = ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroDensity p forms s := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact mean_smul _ _

/-! ## Separating empty and singleton supports -/

/-- Supports of cardinality at least two in the full finite family. -/
def higherOrderSelectedSupports
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Finset (Finset κ) :=
  (Finset.univ : Finset κ).powerset.filter
    fun s => 2 ≤ s.card

@[simp]
theorem mem_higherOrderSelectedSupports
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset κ) :
    s ∈ higherOrderSelectedSupports κ ↔ 2 ≤ s.card := by
  simp [higherOrderSelectedSupports]

/-- The complementary part of the powerset consists exactly of the empty
support and all singleton supports. -/
theorem sum_powerset_supports_of_card_lt_two
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : Finset κ → ℝ) :
    (∑ s ∈ (Finset.univ : Finset κ).powerset.filter
        (fun s => ¬ 2 ≤ s.card), F s) =
      F ∅ + ∑ q : κ, F {q} := by
  let u : Finset κ := Finset.univ
  have hlow :
      u.powerset.filter (fun s => ¬ 2 ≤ s.card) =
        u.powersetCard 0 ∪ u.powersetCard 1 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_union, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hnot⟩
      have hle : s.card ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos s.card with hzero | hpos
      · exact Or.inl ⟨hsub, hzero⟩
      · exact Or.inr
          ⟨hsub, Nat.le_antisymm hle hpos⟩
    · rintro (hzero | hone)
      · exact ⟨hzero.1, by omega⟩
      · exact ⟨hone.1, by omega⟩
  have hdisj :
      Disjoint (u.powersetCard 0) (u.powersetCard 1) := by
    rw [Finset.disjoint_left]
    intro s hs0 hs1
    have h0 := (Finset.mem_powersetCard.mp hs0).2
    have h1 := (Finset.mem_powersetCard.mp hs1).2
    omega
  change (∑ s ∈ u.powerset.filter
      (fun s => ¬ 2 ≤ s.card), F s) =
    F ∅ + ∑ q : κ, F {q}
  rw [hlow, Finset.sum_union hdisj,
    Finset.powersetCard_zero, Finset.sum_singleton,
    Finset.powersetCard_one, Finset.sum_map]
  simp [u]

/-- The signed contribution of all supports of cardinality at least two. -/
noncomputable def weightedLocalFactorRemainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℝ) : ℝ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
      affineFamilyZeroDensity p forms s

/-- Exact first-order decomposition: the empty and singleton supports are
evaluated, while every support of cardinality at least two remains in the
named remainder. -/
theorem mean_weightedLocalAvoidanceProduct_eq_firstOrder_add_remainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℝ) :
    mean (weightedLocalAvoidanceProduct p forms a) =
      1 - (∑ q, a q) / (p : ℝ) +
        weightedLocalFactorRemainder p forms a := by
  let u : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℝ :=
    fun s =>
      ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
        affineFamilyZeroDensity p forms s
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      u (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ u.filter (fun s => ¬ 2 ≤ s.card),
        term s) =
        1 - (∑ q, a q) / (p : ℝ) := by
    rw [show u.filter (fun s => ¬ 2 ≤ s.card) =
        (Finset.univ : Finset κ).powerset.filter
          (fun s => ¬ 2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two]
    simp only [term, Finset.card_empty, pow_zero,
      Finset.prod_empty, one_mul,
      affineFamilyZeroDensity_empty, Finset.card_singleton,
      pow_one, Finset.prod_singleton]
    simp_rw [affineFamilyZeroDensity_singleton_of_bound
      hnonzero hp hlarge]
    simp [div_eq_mul_inv, ← Finset.sum_mul]
    ring
  rw [mean_weightedLocalAvoidanceProduct_eq_inclusionExclusion]
  change (∑ s ∈ u, term s) =
    1 - (∑ q, a q) / (p : ℝ) +
      weightedLocalFactorRemainder p forms a
  rw [← hsplit, hlow]
  unfold weightedLocalFactorRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s) +
        (1 - (∑ q, a q) / (p : ℝ)) =
      1 - (∑ q, a q) / (p : ℝ) +
        ∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s
  ac_rfl

/-! ## Quantitative remainder bounds -/

/-- Total absolute coefficient mass carried by supports of cardinality at
least two. -/
noncomputable def weightedHigherOrderCoefficientMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℝ) : ℝ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ∏ q ∈ s, |a q|

theorem weightedHigherOrderCoefficientMass_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℝ) :
    0 ≤ weightedHigherOrderCoefficientMass a := by
  unfold weightedHigherOrderCoefficientMass
  exact Finset.sum_nonneg fun s _hs =>
    Finset.prod_nonneg fun q _hq => abs_nonneg (a q)

/-- A simpler multiplicative upper bound for the finite coefficient mass. -/
theorem weightedHigherOrderCoefficientMass_le_prod_one_add_abs
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℝ) :
    weightedHigherOrderCoefficientMass a ≤
      ∏ q, (1 + |a q|) := by
  let u : Finset κ := Finset.univ
  let massTerm : Finset κ → ℝ :=
    fun s => ∏ q ∈ s, |a q|
  have hsubset :
      higherOrderSelectedSupports κ ⊆ u.powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr
      ((Finset.mem_filter.mp hs).1 |>
        Finset.mem_powerset.mp)
  calc
    weightedHigherOrderCoefficientMass a =
        ∑ s ∈ higherOrderSelectedSupports κ,
          massTerm s := by
      rfl
    _ ≤ ∑ s ∈ u.powerset, massTerm s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro s _hs _hnot
      exact Finset.prod_nonneg fun q _hq =>
        abs_nonneg (a q)
    _ = ∏ q, (1 + |a q|) := by
      have h :=
        Finset.prod_add
          (fun q : κ => |a q|)
          (fun _q : κ => (1 : ℝ)) u
      symm
      simpa [u, massTerm, add_comm] using h

/-- Rank two controls an arbitrary real linear combination of higher-order
common-zero densities.  This is the coefficient-level interface when a local
factor has already been expanded into support coefficients which need not
factor as `∏ q ∈ s, a q`. -/
theorem abs_sum_higherOrder_mul_affineFamilyZeroDensity_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (c : Finset κ → ℝ) :
    |∑ s ∈ higherOrderSelectedSupports κ,
        c s * affineFamilyZeroDensity p forms s| ≤
      (∑ s ∈ higherOrderSelectedSupports κ, |c s|) *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  calc
    |∑ s ∈ higherOrderSelectedSupports κ,
        c s * affineFamilyZeroDensity p forms s| ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          |c s * affineFamilyZeroDensity p forms s| :=
      Finset.abs_sum_le_sum_abs
        (fun s =>
          c s * affineFamilyZeroDensity p forms s)
        (higherOrderSelectedSupports κ)
    _ ≤ ∑ s ∈ higherOrderSelectedSupports κ,
          |c s| * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs2 : 2 ≤ s.card :=
        (mem_higherOrderSelectedSupports s).mp hs
      have hsnontrivial : s.Nontrivial :=
        Finset.one_lt_card_iff_nontrivial.mp (by omega)
      have hdensity0 :
          0 ≤ affineFamilyZeroDensity p forms s :=
        affineFamilyZeroDensity_nonneg p forms s
      have hdensity :
          affineFamilyZeroDensity p forms s ≤
            (1 : ℝ) / (p : ℝ) ^ 2 :=
        affineFamilyZeroDensity_le_inv_sq_of_goodPrime
          hgood s hsnontrivial
      rw [abs_mul, abs_of_nonneg hdensity0]
      exact mul_le_mul_of_nonneg_left hdensity
        (abs_nonneg (c s))
    _ = (∑ s ∈ higherOrderSelectedSupports κ, |c s|) *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.sum_mul]

/-- Rank two bounds the full signed higher-order contribution by its
absolute coefficient mass times `1 / p²`. -/
theorem abs_weightedLocalFactorRemainder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (a : κ → ℝ) :
    |weightedLocalFactorRemainder p forms a| ≤
      weightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  unfold weightedLocalFactorRemainder
  calc
    |∑ s ∈ higherOrderSelectedSupports κ,
        ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
          affineFamilyZeroDensity p forms s| ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          |((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroDensity p forms s| :=
      Finset.abs_sum_le_sum_abs
        (fun s =>
          ((-1 : ℝ) ^ s.card * ∏ q ∈ s, a q) *
            affineFamilyZeroDensity p forms s)
        (higherOrderSelectedSupports κ)
    _ ≤ ∑ s ∈ higherOrderSelectedSupports κ,
          (∏ q ∈ s, |a q|) *
            ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs2 : 2 ≤ s.card :=
        (mem_higherOrderSelectedSupports s).mp hs
      have hsnontrivial : s.Nontrivial :=
        Finset.one_lt_card_iff_nontrivial.mp (by omega)
      have hdensity0 :
          0 ≤ affineFamilyZeroDensity p forms s :=
        affineFamilyZeroDensity_nonneg p forms s
      have hdensity :
          affineFamilyZeroDensity p forms s ≤
            (1 : ℝ) / (p : ℝ) ^ 2 :=
        affineFamilyZeroDensity_le_inv_sq_of_goodPrime
          hgood s hsnontrivial
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul, Finset.abs_prod,
        abs_of_nonneg hdensity0]
      exact mul_le_mul_of_nonneg_left hdensity
        (Finset.prod_nonneg fun q _hq => abs_nonneg (a q))
    _ = weightedHigherOrderCoefficientMass a *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
      unfold weightedHigherOrderCoefficientMass
      rw [Finset.sum_mul]

/-- The same estimate with the simpler product coefficient constant. -/
theorem abs_weightedLocalFactorRemainder_le_prod_one_add_abs
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (a : κ → ℝ) :
    |weightedLocalFactorRemainder p forms a| ≤
      (∏ q, (1 + |a q|)) *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  exact
    (abs_weightedLocalFactorRemainder_le hgood a).trans
      (mul_le_mul_of_nonneg_right
        (weightedHigherOrderCoefficientMass_le_prod_one_add_abs a)
        (by positivity))

/-- Quantitative weighted first-order expansion at a good prime. -/
theorem abs_mean_weightedLocalAvoidanceProduct_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℝ) :
    |mean (weightedLocalAvoidanceProduct p forms a) -
        (1 - (∑ q, a q) / (p : ℝ))| ≤
      weightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [mean_weightedLocalAvoidanceProduct_eq_firstOrder_add_remainder
    hnonzero hgood.1 hlarge]
  simpa using abs_weightedLocalFactorRemainder_le hgood a

/-- Product-constant form of the weighted first-order estimate. -/
theorem abs_mean_weightedLocalAvoidanceProduct_sub_firstOrder_le_prod
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℝ) :
    |mean (weightedLocalAvoidanceProduct p forms a) -
        (1 - (∑ q, a q) / (p : ℝ))| ≤
      (∏ q, (1 + |a q|)) *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [mean_weightedLocalAvoidanceProduct_eq_firstOrder_add_remainder
    hnonzero hgood.1 hlarge]
  simpa using
    abs_weightedLocalFactorRemainder_le_prod_one_add_abs
      hgood a

/-- Pairwise independence and the common exceptional-prime bound provide
all hypotheses of the weighted estimate. -/
theorem abs_mean_weightedLocalAvoidanceProduct_sub_firstOrder_le_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℝ) :
    |mean (weightedLocalAvoidanceProduct p forms a) -
        (1 - (∑ q, a q) / (p : ℝ))| ≤
      weightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  exact abs_mean_weightedLocalAvoidanceProduct_sub_firstOrder_le
    hnonzero
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      hindependent hp hlarge)
    hlarge a

/-! ## The existing unweighted local Euler factor -/

@[simp]
theorem weightedLocalAvoidanceProduct_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    weightedLocalAvoidanceProduct p forms (fun _q => 1) =
      localAvoidanceProduct p forms := by
  funext x
  simp [weightedLocalAvoidanceProduct,
    localAvoidanceProduct]

/-- Explicit `O(p⁻²)` first-order estimate for the unnormalized local
avoidance product. -/
theorem abs_mean_localAvoidanceProduct_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    |mean (localAvoidanceProduct p forms) -
        (1 - (Fintype.card κ : ℝ) / (p : ℝ))| ≤
      (2 : ℝ) ^ Fintype.card κ *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  have h :=
    abs_mean_weightedLocalAvoidanceProduct_sub_firstOrder_le_prod
      hnonzero
      (affineRankTwoGoodPrime_of_exceptionalPrimeBound
        hindependent hp hlarge)
      hlarge (fun _q : κ => (1 : ℝ))
  convert h using 1 <;> norm_num

/-- Corresponding quantitative bound for the normalized product of local
coprimality weights from `LocalEulerFactors`. -/
theorem abs_mean_systemLocalCoprimeWeight_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    let scale :=
      ((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ
    |mean (systemLocalCoprimeWeight p forms) -
        scale *
          (1 - (Fintype.card κ : ℝ) / (p : ℝ))| ≤
      scale *
        ((2 : ℝ) ^ Fintype.card κ *
          ((1 : ℝ) / (p : ℝ) ^ 2)) := by
  dsimp only
  rw [mean_systemLocalCoprimeWeight_eq, ← mul_sub,
    abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (abs_mean_localAvoidanceProduct_sub_firstOrder_le
      hnonzero hindependent hp hlarge)
    (by positivity)

/-! ## CFZ specialization -/

/-- The explicit unnormalized local-factor remainder bound for the full CFZ
family. -/
theorem abs_mean_cfzLocalAvoidanceProduct_sub_firstOrder_le
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    |mean (localAvoidanceProduct p
        (fun q : CFZFormIndex k => cfzAffineForm q)) -
      (1 -
        (Fintype.card (CFZFormIndex k) : ℝ) / (p : ℝ))| ≤
      (2 : ℝ) ^ Fintype.card (CFZFormIndex k) *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  exact abs_mean_localAvoidanceProduct_sub_firstOrder_le
    (cfzAffineForms_nonzero hk)
    (cfzAffineForms_pairwiseIndependent hk)
    hp hlarge

/-- The corresponding bound for the normalized CFZ local Euler factor. -/
theorem abs_mean_cfzSystemLocalCoprimeWeight_sub_firstOrder_le
    {k p : ℕ} (hk : 2 ≤ k) [NeZero p] (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    let scale :=
      ((p : ℝ) / (p - 1 : ℕ)) ^
        Fintype.card (CFZFormIndex k)
    |mean (systemLocalCoprimeWeight p
        (fun q : CFZFormIndex k => cfzAffineForm q)) -
      scale *
        (1 -
          (Fintype.card (CFZFormIndex k) : ℝ) / (p : ℝ))| ≤
      scale *
        ((2 : ℝ) ^ Fintype.card (CFZFormIndex k) *
          ((1 : ℝ) / (p : ℝ) ^ 2)) := by
  exact abs_mean_systemLocalCoprimeWeight_sub_firstOrder_le
    (cfzAffineForms_nonzero hk)
    (cfzAffineForms_pairwiseIndependent hk)
    hp hlarge

end Wikipedia.SzemeredisTheorem
