import Wikipedia.GreenTao.Sieve.CFZEulerProductControl
import Wikipedia.GreenTao.Sieve.SmoothCutoffFourier

/-!
# Complex good-prime local factors after Fourier inversion

Fourier inversion turns each of the two smooth divisor sums attached to a
form into a complex multiplicative phase.  At a prime `p`, if the two phases
are `z` and `w`, the four squarefree divisor choices contribute

`1 - (z + w - z * w) 1_{p ∣ ψ(x)}`.

Thus the arithmetic local factor is a complex-weighted avoidance average.
This file develops that average directly over `ℂ`, proves its exact finite
inclusion--exclusion expansion, and isolates the singleton contribution.
At a rank-two good prime the remaining supports have density at most
`p⁻²`, so the complex remainder is bounded by the product of
`1 + ‖a q‖`.

For the Fourier coefficients, every divisor phase has norm at most one when
`R ≥ 2`, hence `‖z + w - z * w‖ ≤ 3`.  Consequently the higher-order
coefficient mass is at most `4 ^ m` for a system of `m` forms.  Above
`p ≥ 6m`, the complex first-order model has norm at least `1/2`; division by
that model therefore gives the explicit ratio estimate

`‖localRatio p - 1‖ ≤ 2 * 4 ^ m / p²`.

The final CFZ theorem masks the finite exceptional range and packages these
ratios in a complex analogue of `HasPrimeSquareError`, including
multipliability of the resulting remainder Euler product.

This does not yet compare the first-order model with the local factors of
the appropriate multivariate zeta quotient.  That analytic comparison, and
the subsequent parameter-uniform integration, are separate steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Complex finite averages -/

/-- The normalized average of a complex-valued function on a finite type. -/
noncomputable def complexMean
    {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  𝔼 x, f x

theorem complexMean_finset_sum
    {α κ : Type*} [Fintype α]
    (s : Finset κ) (F : κ → α → ℂ) :
    complexMean (fun x => ∑ i ∈ s, F i x) =
      ∑ i ∈ s, complexMean (F i) := by
  exact Finset.expect_sum_comm Finset.univ s
    (fun x i => F i x)

theorem complexMean_mul
    {α : Type*} [Fintype α]
    (c : ℂ) (f : α → ℂ) :
    complexMean (fun x => c * f x) =
      c * complexMean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

/-- Complex averaging commutes with the canonical embedding of real-valued
functions. -/
theorem complexMean_ofReal
    {α : Type*} [Fintype α] (f : α → ℝ) :
    complexMean (fun x => (f x : ℂ)) =
      (mean f : ℂ) := by
  unfold complexMean mean
  exact (algebraMap.coe_expect
    (N := ℂ) Finset.univ f).symm

/-! ## Exact complex inclusion--exclusion -/

/-- The pointwise local avoidance product with arbitrary complex
coefficients. -/
noncomputable def complexWeightedLocalAvoidanceProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) (x : ι → ZMod p) : ℂ :=
  ∏ q, (1 -
    a q *
      (finsetIndicator ((forms q).zeroFinsetZMod p) x : ℂ))

/-- Pointwise complex-weighted inclusion--exclusion over selected
supports. -/
theorem complexWeightedLocalAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) (x : ι → ZMod p) :
    complexWeightedLocalAvoidanceProduct p forms a x =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroProduct p forms s x : ℂ) := by
  let I : κ → ℂ :=
    fun q =>
      a q *
        (finsetIndicator ((forms q).zeroFinsetZMod p) x : ℂ)
  have h :=
    Finset.prod_sub (fun _q : κ => (1 : ℂ)) I
      (Finset.univ : Finset κ)
  simpa [complexWeightedLocalAvoidanceProduct,
    affineFamilyZeroProduct, I, Finset.prod_mul_distrib,
    mul_assoc] using h

/-- The complex arithmetic local factor, defined as the normalized
finite-field average of the pointwise avoidance product. -/
noncomputable def complexWeightedLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) : ℂ :=
  complexMean (complexWeightedLocalAvoidanceProduct p forms a)

/-- Exact complex inclusion--exclusion formula for the averaged local
factor. -/
theorem complexWeightedLocalFactor_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroDensity p forms s : ℂ) := by
  rw [complexWeightedLocalFactor,
    show complexWeightedLocalAvoidanceProduct p forms a =
        fun x =>
          ∑ s ∈ (Finset.univ : Finset κ).powerset,
            ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
              (affineFamilyZeroProduct p forms s x : ℂ) by
      funext x
      exact
        complexWeightedLocalAvoidanceProduct_eq_inclusionExclusion
          p forms a x]
  calc
    complexMean (fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroProduct p forms s x : ℂ)) =
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          complexMean (fun x =>
            ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
              (affineFamilyZeroProduct p forms s x : ℂ)) :=
      complexMean_finset_sum
        (Finset.univ : Finset κ).powerset
        (fun s x =>
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroProduct p forms s x : ℂ))
    _ = ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [complexMean_mul, complexMean_ofReal]
      rfl

/-- Complex specialization of the elementary decomposition of supports of
cardinality less than two. -/
theorem sum_powerset_supports_of_card_lt_two_complex
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : Finset κ → ℂ) :
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

/-- The signed complex contribution of supports of cardinality at least
two. -/
noncomputable def complexWeightedLocalFactorRemainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) : ℂ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
      (affineFamilyZeroDensity p forms s : ℂ)

/-- Exact first-order decomposition of the complex local factor. -/
theorem complexWeightedLocalFactor_eq_firstOrder_add_remainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      1 - (∑ q, a q) / (p : ℂ) +
        complexWeightedLocalFactorRemainder p forms a := by
  let u : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℂ :=
    fun s =>
      ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
        (affineFamilyZeroDensity p forms s : ℂ)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      u (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ u.filter (fun s => ¬ 2 ≤ s.card),
        term s) =
        1 - (∑ q, a q) / (p : ℂ) := by
    rw [show u.filter (fun s => ¬ 2 ≤ s.card) =
        (Finset.univ : Finset κ).powerset.filter
          (fun s => ¬ 2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two_complex]
    simp only [term, Finset.card_empty, pow_zero,
      Finset.prod_empty, one_mul,
      affineFamilyZeroDensity_empty, Complex.ofReal_one,
      Finset.card_singleton, pow_one, Finset.prod_singleton]
    simp_rw [affineFamilyZeroDensity_singleton_of_bound
      hnonzero hp hlarge]
    push_cast
    simp_rw [neg_one_mul, neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  rw [complexWeightedLocalFactor_eq_inclusionExclusion]
  change (∑ s ∈ u, term s) =
    1 - (∑ q, a q) / (p : ℂ) +
      complexWeightedLocalFactorRemainder p forms a
  rw [← hsplit, hlow]
  unfold complexWeightedLocalFactorRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s) +
        (1 - (∑ q, a q) / (p : ℂ)) =
      1 - (∑ q, a q) / (p : ℂ) +
        ∑ s ∈ u.filter (fun s => 2 ≤ s.card), term s
  ac_rfl

/-! ## Norm bounds for the complex remainder -/

/-- Total norm mass carried by supports of cardinality at least two. -/
noncomputable def complexWeightedHigherOrderCoefficientMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℂ) : ℝ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ∏ q ∈ s, ‖a q‖

theorem complexWeightedHigherOrderCoefficientMass_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℂ) :
    0 ≤ complexWeightedHigherOrderCoefficientMass a := by
  unfold complexWeightedHigherOrderCoefficientMass
  exact Finset.sum_nonneg fun s _hs =>
    Finset.prod_nonneg fun q _hq => norm_nonneg (a q)

/-- The complex coefficient mass is bounded by the full subset-product
mass. -/
theorem complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℂ) :
    complexWeightedHigherOrderCoefficientMass a ≤
      ∏ q, (1 + ‖a q‖) := by
  let u : Finset κ := Finset.univ
  let massTerm : Finset κ → ℝ :=
    fun s => ∏ q ∈ s, ‖a q‖
  have hsubset :
      higherOrderSelectedSupports κ ⊆ u.powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr
      ((Finset.mem_filter.mp hs).1 |>
        Finset.mem_powerset.mp)
  calc
    complexWeightedHigherOrderCoefficientMass a =
        ∑ s ∈ higherOrderSelectedSupports κ,
          massTerm s := by
      rfl
    _ ≤ ∑ s ∈ u.powerset, massTerm s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro s _hs _hnot
      exact Finset.prod_nonneg fun q _hq =>
        norm_nonneg (a q)
    _ = ∏ q, (1 + ‖a q‖) := by
      have h :=
        Finset.prod_add
          (fun q : κ => ‖a q‖)
          (fun _q : κ => (1 : ℝ)) u
      symm
      simpa [u, massTerm, add_comm] using h

/-- Rank two bounds the complex higher-order contribution by its total
coefficient norm mass times `p⁻²`. -/
theorem norm_complexWeightedLocalFactorRemainder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactorRemainder p forms a‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  unfold complexWeightedLocalFactorRemainder
  calc
    ‖∑ s ∈ higherOrderSelectedSupports κ,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroDensity p forms s : ℂ)‖ ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          ‖((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ)‖ :=
      norm_sum_le
        (higherOrderSelectedSupports κ)
        (fun s =>
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ))
    _ ≤ ∑ s ∈ higherOrderSelectedSupports κ,
          (∏ q ∈ s, ‖a q‖) *
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
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
        one_pow, one_mul, norm_prod, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hdensity0]
      exact mul_le_mul_of_nonneg_left hdensity
        (Finset.prod_nonneg fun q _hq => norm_nonneg (a q))
    _ = complexWeightedHigherOrderCoefficientMass a *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
      unfold complexWeightedHigherOrderCoefficientMass
      rw [Finset.sum_mul]

/-- Product-constant form of the complex remainder estimate. -/
theorem norm_complexWeightedLocalFactorRemainder_le_prod
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactorRemainder p forms a‖ ≤
      (∏ q, (1 + ‖a q‖)) *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  exact
    (norm_complexWeightedLocalFactorRemainder_le hgood a).trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm a)
        (by positivity))

/-- Quantitative complex first-order expansion at a good prime. -/
theorem norm_complexWeightedLocalFactor_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactor p forms a -
        (1 - (∑ q, a q) / (p : ℂ))‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [complexWeightedLocalFactor_eq_firstOrder_add_remainder
    hnonzero hgood.1 hlarge]
  simpa using norm_complexWeightedLocalFactorRemainder_le hgood a

/-! ## A stable complex first-order ratio -/

/-- The first-order local model belonging to a complex coefficient
family. -/
noncomputable def complexFirstOrderLocalModel
    {κ : Type*} [Fintype κ] (p : ℕ) (a : κ → ℂ) : ℂ :=
  1 - (∑ q, a q) / (p : ℂ)

/-- If every coefficient has norm at most three, then the first-order
model stays at least one half away from zero above `6m`. -/
theorem one_half_le_norm_complexFirstOrderLocalModel
    {κ : Type*} [Fintype κ]
    {p : ℕ} (hp : p.Prime)
    (hcard : 6 * Fintype.card κ ≤ p)
    {a : κ → ℂ} (ha : ∀ q, ‖a q‖ ≤ 3) :
    (1 : ℝ) / 2 ≤ ‖complexFirstOrderLocalModel p a‖ := by
  have hsum :
      ‖∑ q, a q‖ ≤ 3 * Fintype.card κ := by
    calc
      ‖∑ q, a q‖ ≤ ∑ q, ‖a q‖ :=
        norm_sum_le Finset.univ a
      _ ≤ ∑ _q : κ, (3 : ℝ) :=
        Finset.sum_le_sum fun q _hq => ha q
      _ = 3 * Fintype.card κ := by
        simp [mul_comm]
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hcardR :
      6 * (Fintype.card κ : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hcard
  have hquot :
      ‖(∑ q, a q) / (p : ℂ)‖ ≤ (1 : ℝ) / 2 := by
    rw [Complex.norm_div, Complex.norm_natCast,
      div_le_iff₀ hpR]
    nlinarith
  change
    (1 : ℝ) / 2 ≤
      ‖(1 : ℂ) - (∑ q, a q) / (p : ℂ)‖
  calc
    (1 : ℝ) / 2 ≤
        1 - ‖(∑ q, a q) / (p : ℂ)‖ := by
      linarith
    _ =
        ‖(1 : ℂ)‖ -
          ‖(∑ q, a q) / (p : ℂ)‖ := by
      rw [norm_one]
    _ ≤
        ‖(1 : ℂ) -
          (∑ q, a q) / (p : ℂ)‖ :=
      norm_sub_norm_le _ _

/-- The actual complex local factor divided by its first-order model. -/
noncomputable def complexWeightedLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) : ℂ :=
  complexWeightedLocalFactor p forms a /
    complexFirstOrderLocalModel p a

/-- The actual/model ratio has an explicit square-decaying complex error
whenever all coefficients have norm at most three. -/
theorem norm_complexWeightedLocalRatio_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcard : 6 * Fintype.card κ ≤ p)
    (a : κ → ℂ) (ha : ∀ q, ‖a q‖ ≤ 3) :
    ‖complexWeightedLocalRatio p forms a - 1‖ ≤
      (2 * ∏ q, (1 + ‖a q‖)) /
        (p : ℝ) ^ 2 := by
  let model := complexFirstOrderLocalModel p a
  have hmodelHalf : (1 : ℝ) / 2 ≤ ‖model‖ := by
    exact one_half_le_norm_complexFirstOrderLocalModel
      hp hcard ha
  have hmodelPos : 0 < ‖model‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hmodelHalf
  have hlocal :
      ‖complexWeightedLocalFactor p forms a - model‖ ≤
        (∏ q, (1 + ‖a q‖)) *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
    simpa [model, complexFirstOrderLocalModel] using
      (norm_complexWeightedLocalFactor_sub_firstOrder_le
        hnonzero
        (affineRankTwoGoodPrime_of_exceptionalPrimeBound
          hindependent hp hlarge)
        hlarge a |>.trans
          (mul_le_mul_of_nonneg_right
            (complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm a)
            (by positivity)))
  have hmodelNe : model ≠ 0 :=
    norm_pos_iff.mp hmodelPos
  rw [complexWeightedLocalRatio,
    div_sub_one hmodelNe, Complex.norm_div]
  calc
    ‖complexWeightedLocalFactor p forms a - model‖ /
          ‖model‖ ≤
        2 *
          ‖complexWeightedLocalFactor p forms a - model‖ := by
      rw [div_le_iff₀ hmodelPos]
      have hnonneg :
          0 ≤
            ‖complexWeightedLocalFactor p forms a - model‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        2 *
          ((∏ q, (1 + ‖a q‖)) *
            ((1 : ℝ) / (p : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hlocal (by norm_num)
    _ =
        (2 * ∏ q, (1 + ‖a q‖)) /
          (p : ℝ) ^ 2 := by
      ring

/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff

/-- The exact norm of the multiplicative cutoff phase. -/
theorem norm_cutoffMultiplicativePhase
    (x t : ℝ) :
    ‖cutoffMultiplicativePhase x t‖ =
      Real.exp (-x) := by
  rw [cutoffMultiplicativePhase_eq, norm_mul,
    norm_inverseFourierCharacter, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]

/-- At a prime, every Fourier divisor phase has norm at most one once the
sieve scale is at least two. -/
theorem norm_divisorMultiplicativePhase_le_one
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (t : ℝ) :
    ‖divisorMultiplicativePhase R p t‖ ≤ 1 := by
  rw [divisorMultiplicativePhase,
    norm_cutoffMultiplicativePhase]
  have hlogp :
      0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlogR :
      0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ R by omega))
  have hdiv :
      0 ≤ Real.log (p : ℝ) / Real.log (R : ℝ) :=
    div_nonneg hlogp hlogR
  calc
    Real.exp (-(Real.log (p : ℝ) / Real.log (R : ℝ))) ≤
        Real.exp 0 :=
      Real.exp_le_exp.mpr (neg_nonpos.mpr hdiv)
    _ = 1 := Real.exp_zero

end SmoothSieveCutoff

/-- The coefficient of the prime-zero indicator obtained from the two
squarefree divisor choices attached to one form. -/
noncomputable def pairedFourierPrimeCoefficient
    (R p : ℕ) (t u : ℝ) : ℂ :=
  SmoothSieveCutoff.divisorMultiplicativePhase R p t +
    SmoothSieveCutoff.divisorMultiplicativePhase R p u -
      SmoothSieveCutoff.divisorMultiplicativePhase R p t *
        SmoothSieveCutoff.divisorMultiplicativePhase R p u

/-- If both divisor phases lie in the closed unit ball, their paired
coefficient has norm at most three. -/
theorem norm_add_sub_mul_le_three
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖z + w - z * w‖ ≤ 3 := by
  calc
    ‖z + w - z * w‖ ≤
        ‖z + w‖ + ‖z * w‖ :=
      norm_sub_le _ _
    _ ≤ (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖ := by
      rw [norm_mul]
      exact add_le_add (norm_add_le z w) le_rfl
    _ ≤ 3 := by
      nlinarith [norm_nonneg z, norm_nonneg w]

/-- Uniform norm bound for the Fourier-paired coefficient at a prime. -/
theorem norm_pairedFourierPrimeCoefficient_le_three
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (t u : ℝ) :
    ‖pairedFourierPrimeCoefficient R p t u‖ ≤ 3 := by
  exact norm_add_sub_mul_le_three
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR hp t)
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR hp u)

/-- The arithmetic local factor after assigning two Fourier parameters to
each affine form. -/
noncomputable def pairedFourierLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) : ℂ :=
  complexWeightedLocalFactor p forms
    (fun q => pairedFourierPrimeCoefficient R p (t q) (u q))

/-- Its matching first-order complex model. -/
noncomputable def pairedFourierFirstOrderLocalModel
    {κ : Type*} [Fintype κ]
    (R p : ℕ) (t u : κ → ℝ) : ℂ :=
  complexFirstOrderLocalModel p
    (fun q => pairedFourierPrimeCoefficient R p (t q) (u q))

/-- The Fourier-parameter-dependent actual/model ratio. -/
noncomputable def pairedFourierLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) : ℂ :=
  pairedFourierLocalFactor R p forms t u /
    pairedFourierFirstOrderLocalModel R p t u

/-- The Fourier coefficient mass is uniformly at most `4^m`. -/
theorem complexWeightedHigherOrderCoefficientMass_pairedFourier_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (t u : κ → ℝ) :
    complexWeightedHigherOrderCoefficientMass
        (fun q =>
          pairedFourierPrimeCoefficient R p (t q) (u q)) ≤
      (4 : ℝ) ^ Fintype.card κ := by
  calc
    complexWeightedHigherOrderCoefficientMass
        (fun q =>
          pairedFourierPrimeCoefficient R p (t q) (u q)) ≤
        ∏ q,
          (1 +
            ‖pairedFourierPrimeCoefficient
              R p (t q) (u q)‖) :=
      complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm _
    _ ≤ ∏ _q : κ, (4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro q _hq
        positivity
      · intro q _hq
        linarith [
          norm_pairedFourierPrimeCoefficient_le_three
            hR hp (t q) (u q)]
    _ = (4 : ℝ) ^ Fintype.card κ := by
      simp

/-- Exact first-order decomposition of the
Fourier-parameter-dependent local factor. -/
theorem pairedFourierLocalFactor_eq_firstOrder_add_remainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {R p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (t u : κ → ℝ) :
    pairedFourierLocalFactor R p forms t u =
      pairedFourierFirstOrderLocalModel R p t u +
        complexWeightedLocalFactorRemainder p forms
          (fun q =>
            pairedFourierPrimeCoefficient
              R p (t q) (u q)) := by
  exact complexWeightedLocalFactor_eq_firstOrder_add_remainder
    hnonzero hp hlarge _

/-- Explicit good-prime `O_m(p⁻²)` remainder before division by the
first-order model. -/
theorem norm_pairedFourierLocalFactor_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p forms t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card κ /
        (p : ℝ) ^ 2 := by
  have hgood :=
    affineRankTwoGoodPrime_of_exceptionalPrimeBound
      hindependent hp hlarge
  have hbase :=
    norm_complexWeightedLocalFactor_sub_firstOrder_le
      hnonzero hgood hlarge
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
  simpa [pairedFourierLocalFactor,
    pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel, div_eq_mul_inv] using
    hbase.trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_pairedFourier_le
          hR hp t u)
        (by positivity))

/-- Uniform square-error constant for complex Fourier local ratios. -/
noncomputable def pairedFourierLocalRatioErrorConstant
    (m : ℕ) : ℝ :=
  2 * (4 : ℝ) ^ m

theorem pairedFourierLocalRatioErrorConstant_nonneg
    (m : ℕ) :
    0 ≤ pairedFourierLocalRatioErrorConstant m := by
  rw [pairedFourierLocalRatioErrorConstant]
  positivity

/-- Explicit good-prime ratio estimate, uniform in all Fourier
parameters. -/
theorem norm_pairedFourierLocalRatio_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcard : 6 * Fintype.card κ ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalRatio R p forms t u - 1‖ ≤
      pairedFourierLocalRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  have h :=
    norm_complexWeightedLocalRatio_sub_one_le
      hnonzero hindependent hp hlarge hcard
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
      (fun q =>
        norm_pairedFourierPrimeCoefficient_le_three
          hR hp (t q) (u q))
  have hprod :
      (∏ q : κ,
          (1 +
            ‖pairedFourierPrimeCoefficient
              R p (t q) (u q)‖)) ≤
        (4 : ℝ) ^ Fintype.card κ := by
    calc
      (∏ q : κ,
          (1 +
            ‖pairedFourierPrimeCoefficient
              R p (t q) (u q)‖)) ≤
          ∏ _q : κ, (4 : ℝ) := by
        apply Finset.prod_le_prod
        · intro q _hq
          positivity
        · intro q _hq
          linarith [
            norm_pairedFourierPrimeCoefficient_le_three
              hR hp (t q) (u q)]
      _ = (4 : ℝ) ^ Fintype.card κ := by
        simp
  change
    ‖complexWeightedLocalRatio p forms
        (fun q =>
          pairedFourierPrimeCoefficient R p (t q) (u q)) - 1‖ ≤
      pairedFourierLocalRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2
  rw [pairedFourierLocalRatioErrorConstant]
  exact
    h.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by norm_num))
        (sq_nonneg (p : ℝ)))

/-! ## Complex square-error Euler-product interface -/

/-- Uniform square-decay control for complex local factors. -/
def HasComplexPrimeSquareError
    (C : ℝ) (localFactor : Nat.Primes → ℂ) : Prop :=
  0 ≤ C ∧
    ∀ p, ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2

namespace HasComplexPrimeSquareError

theorem constant_nonneg
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (h : HasComplexPrimeSquareError C localFactor) :
    0 ≤ C :=
  h.1

theorem error_le
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (h : HasComplexPrimeSquareError C localFactor)
    (p : Nat.Primes) :
    ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2 :=
  h.2 p

theorem summable_majorant
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (_h : HasComplexPrimeSquareError C localFactor) :
    Summable
      (fun p : Nat.Primes =>
        C / (p : ℝ) ^ 2) := by
  simpa [div_eq_mul_inv] using
    summable_prime_inv_sq.mul_left C

/-- The norms of all complex local errors are summable. -/
theorem summable_norm_error
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (h : HasComplexPrimeSquareError C localFactor) :
    Summable
      (fun p : Nat.Primes =>
        ‖localFactor p - 1‖) := by
  exact Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    h.error_le
    h.summable_majorant

/-- A complex square-decaying local-factor family has a convergent
unordered Euler product. -/
theorem multipliable
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (h : HasComplexPrimeSquareError C localFactor) :
    Multipliable localFactor := by
  have hm :=
    multipliable_one_add_of_summable
      (f := fun p : Nat.Primes => localFactor p - 1)
      h.summable_norm_error
  have heq :
      (fun p : Nat.Primes =>
        1 + (localFactor p - 1)) =
        localFactor := by
    funext p
    ring
  rw [heq] at hm
  exact hm

end HasComplexPrimeSquareError

/-- Replace every complex local factor below a numerical cutoff by one. -/
def boundedMaskedComplexPrimeLocalFactor
    (B : ℕ) (localFactor : Nat.Primes → ℂ) :
    Nat.Primes → ℂ :=
  fun p => if (p : ℕ) ≤ B then 1 else localFactor p

@[simp]
theorem boundedMaskedComplexPrimeLocalFactor_of_le
    {B : ℕ} {localFactor : Nat.Primes → ℂ}
    {p : Nat.Primes} (hp : (p : ℕ) ≤ B) :
    boundedMaskedComplexPrimeLocalFactor B localFactor p = 1 := by
  simp [boundedMaskedComplexPrimeLocalFactor, hp]

@[simp]
theorem boundedMaskedComplexPrimeLocalFactor_of_lt
    {B : ℕ} {localFactor : Nat.Primes → ℂ}
    {p : Nat.Primes} (hp : B < (p : ℕ)) :
    boundedMaskedComplexPrimeLocalFactor B localFactor p =
      localFactor p := by
  have hnot : ¬(p : ℕ) ≤ B :=
    Nat.not_le.mpr hp
  simp [boundedMaskedComplexPrimeLocalFactor, hnot]

/-- A complex square-error estimate above a cutoff becomes global after
masking. -/
theorem hasComplexPrimeSquareError_boundedMasked
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (B : ℕ) (hC : 0 ≤ C)
    (herror :
      ∀ p : Nat.Primes, B < (p : ℕ) →
        ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2) :
    HasComplexPrimeSquareError C
      (boundedMaskedComplexPrimeLocalFactor B localFactor) := by
  refine ⟨hC, fun p => ?_⟩
  by_cases hp : (p : ℕ) ≤ B
  · rw [boundedMaskedComplexPrimeLocalFactor_of_le hp]
    simp only [sub_self, norm_zero]
    exact div_nonneg hC (sq_nonneg (p : ℝ))
  · have hlt : B < (p : ℕ) :=
      Nat.lt_of_not_ge hp
    rw [boundedMaskedComplexPrimeLocalFactor_of_lt hlt]
    exact herror p hlt

/-! ## CFZ specialization -/

/-- Cutoff containing the CFZ rank exceptions and the stability range
`p ≥ 6m` for the complex first-order model. -/
def cfzComplexEulerExceptionalBound (k : ℕ) : ℕ :=
  max
    (exceptionalPrimeBound
      (fun q : CFZFormIndex k => cfzAffineForm q))
    (6 * Fintype.card (CFZFormIndex k))

/-- The Fourier-dependent CFZ actual/model local ratio. -/
noncomputable def cfzPairedFourierLocalRatio
    (R k : ℕ)
    (t u : CFZFormIndex k → ℝ)
    (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierLocalRatio R (p : ℕ)
    (fun q : CFZFormIndex k => cfzAffineForm q) t u

/-- The square-error constant for the complex CFZ ratio. -/
noncomputable def cfzComplexEulerErrorConstant
    (k : ℕ) : ℝ :=
  pairedFourierLocalRatioErrorConstant
    (Fintype.card (CFZFormIndex k))

theorem cfzComplexEulerErrorConstant_nonneg
    (k : ℕ) :
    0 ≤ cfzComplexEulerErrorConstant k :=
  pairedFourierLocalRatioErrorConstant_nonneg _

/-- Explicit good-prime complex square-error estimate for the CFZ
Fourier local ratio, uniform in every Fourier parameter. -/
theorem norm_cfzPairedFourierLocalRatio_sub_one_le
    {k R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (t u : CFZFormIndex k → ℝ)
    (p : Nat.Primes)
    (hlarge : cfzComplexEulerExceptionalBound k < (p : ℕ)) :
    ‖cfzPairedFourierLocalRatio R k t u p - 1‖ ≤
      cfzComplexEulerErrorConstant k /
        (p : ℝ) ^ 2 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hexceptional :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hcard :
      6 * Fintype.card (CFZFormIndex k) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  simpa [cfzPairedFourierLocalRatio,
    cfzComplexEulerErrorConstant] using
    (norm_pairedFourierLocalRatio_sub_one_le
      (cfzAffineForms_nonzero hk)
      (cfzAffineForms_pairwiseIndependent hk)
      hR p.prop hexceptional hcard t u)

/-- After masking the explicit finite range, the CFZ complex ratio has a
global square-decaying error, uniformly in the Fourier parameters. -/
theorem hasComplexPrimeSquareError_cfzPairedFourierLocalRatio
    {k R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (t u : CFZFormIndex k → ℝ) :
    HasComplexPrimeSquareError
      (cfzComplexEulerErrorConstant k)
      (boundedMaskedComplexPrimeLocalFactor
        (cfzComplexEulerExceptionalBound k)
        (cfzPairedFourierLocalRatio R k t u)) := by
  exact hasComplexPrimeSquareError_boundedMasked
    (cfzComplexEulerExceptionalBound k)
    (cfzComplexEulerErrorConstant_nonneg k)
    (fun p hp =>
      norm_cfzPairedFourierLocalRatio_sub_one_le
        hk hR t u p hp)

/-- The masked Fourier-dependent CFZ remainder Euler product is
multipliable. -/
theorem multipliable_cfzPairedFourierLocalRatio
    {k R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (t u : CFZFormIndex k → ℝ) :
    Multipliable
      (boundedMaskedComplexPrimeLocalFactor
        (cfzComplexEulerExceptionalBound k)
        (cfzPairedFourierLocalRatio R k t u)) :=
  (hasComplexPrimeSquareError_cfzPairedFourierLocalRatio
    hk hR t u).multipliable

end Wikipedia.SzemeredisTheorem
