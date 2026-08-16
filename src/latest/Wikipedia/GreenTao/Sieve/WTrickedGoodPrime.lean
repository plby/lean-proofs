import Wikipedia.GreenTao.Sieve.ComplexZetaModelComparison
import Wikipedia.GreenTao.Sieve.CyclicMajorant
import Wikipedia.GreenTao.Sieve.WTrickedLocalFactors

/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/

/-- Every form has a nonzero linear coefficient modulo the prime `p`.
Unlike `NonzeroCoefficientVectors`, this is a direct modular assertion. -/
def AffineNonzeroGoodPrime
    {κ ι : Type*} [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ) : Prop :=
  p.Prime ∧
    ∀ q : κ, ∃ i : ι,
      ((forms q).coefficient i : ZMod p) ≠ 0

/-- The usual integer exceptional bound supplies the direct modular
one-form predicate for the original, unscaled system. -/
theorem affineNonzeroGoodPrime_of_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    AffineNonzeroGoodPrime p forms := by
  refine ⟨hp, fun q => ?_⟩
  exact exists_coefficient_cast_ne_zero_of_bound
    hnonzero hlarge q

/-- Direct modular nondegeneracy is inherited by an arbitrary reindexed
subfamily. -/
theorem AffineNonzeroGoodPrime.comp
    {κ κ' ι : Type*} [Fintype ι]
    {p : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms)
    (f : κ' → κ) :
    AffineNonzeroGoodPrime p (fun q => forms (f q)) := by
  exact ⟨hgood.1, fun q => hgood.2 (f q)⟩

/-- Rank-two good-prime geometry is inherited by an injectively reindexed
subfamily. -/
theorem AffineRankTwoGoodPrime.comp
    {κ κ' ι : Type*} [Fintype κ] [Fintype κ'] [Fintype ι]
    {p : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (f : κ' → κ) (hf : Function.Injective f) :
    AffineRankTwoGoodPrime p (fun q => forms (f q)) := by
  refine ⟨hgood.1, ?_⟩
  intro q r hqr
  exact hgood.2 (hf.ne hqr)

/-! ## Scaling identities and W-trick preservation -/

/-- A W-trick multiplies every coefficient minor by `W²`.  The two affine
constants do not occur in this identity. -/
@[simp]
theorem wTrickedAffineForm_coefficientMinor
    {ι : Type*} (W b c : ℕ)
    (ψ φ : AffineForm ι ℤ) (i j : ι) :
    (wTrickedAffineForm W b ψ).coefficientMinor
        (wTrickedAffineForm W c φ) i j =
      (W : ℤ) ^ 2 * ψ.coefficientMinor φ i j := by
  simp only [AffineForm.coefficientMinor,
    wTrickedAffineForm_coefficient]
  ring

/-- At a modulus not dividing `W`, its residue class is nonzero. -/
theorem natCast_zmod_ne_zero_of_not_dvd
    {W p : ℕ} (hpW : ¬p ∣ W) :
    (W : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hpW

/-- A nonzero modular coefficient survives W-scaling. -/
theorem wTrickedAffineForm_coefficient_cast_ne_zero
    {ι : Type*} {W b p : ℕ} (hp : p.Prime)
    (hpW : ¬p ∣ W) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    ((wTrickedAffineForm W b ψ).coefficient i : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [wTrickedAffineForm_coefficient, Int.cast_mul,
    Int.cast_natCast]
  exact mul_ne_zero
    (natCast_zmod_ne_zero_of_not_dvd hpW) hi

/-- A nonzero modular minor survives W-scaling, uniformly in the two affine
constants. -/
theorem wTrickedAffineForm_coefficientMinor_cast_ne_zero
    {ι : Type*} {W b c p : ℕ} (hp : p.Prime)
    (hpW : ¬p ∣ W) (ψ φ : AffineForm ι ℤ)
    {i j : ι}
    (hij : (ψ.coefficientMinor φ i j : ZMod p) ≠ 0) :
    ((wTrickedAffineForm W b ψ).coefficientMinor
        (wTrickedAffineForm W c φ) i j : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [wTrickedAffineForm_coefficientMinor]
  push_cast
  exact mul_ne_zero
    (pow_ne_zero 2 (natCast_zmod_ne_zero_of_not_dvd hpW))
    hij

/-- Formwise-varying affine constants preserve one-form good-prime
geometry.  This includes carry-dependent constants. -/
theorem AffineNonzeroGoodPrime.wTricked
    {κ ι : Type*} [Fintype ι]
    {p W : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ) :
    AffineNonzeroGoodPrime p
      (fun q => wTrickedAffineForm W (b q) (forms q)) := by
  refine ⟨hgood.1, fun q => ?_⟩
  obtain ⟨i, hi⟩ := hgood.2 q
  exact ⟨i,
    wTrickedAffineForm_coefficient_cast_ne_zero
      hgood.1 hpW (forms q) hi⟩

/-- A common affine constant is the usual W-trick specialization of
`AffineNonzeroGoodPrime.wTricked`. -/
theorem AffineNonzeroGoodPrime.wTricked_const
    {κ ι : Type*} [Fintype ι]
    {p W : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : ℕ) :
    AffineNonzeroGoodPrime p
      (fun q => wTrickedAffineForm W b (forms q)) := by
  simpa using hgood.wTricked hpW (fun _q : κ => b)

/-- Formwise-varying affine constants preserve rank-two good-prime
geometry. -/
theorem AffineRankTwoGoodPrime.wTricked
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {p W : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ) :
    AffineRankTwoGoodPrime p
      (fun q => wTrickedAffineForm W (b q) (forms q)) := by
  refine ⟨hgood.1, ?_⟩
  intro q r hqr
  obtain ⟨i, j, hij⟩ := hgood.2 hqr
  exact ⟨i, j,
    wTrickedAffineForm_coefficientMinor_cast_ne_zero
      hgood.1 hpW (forms q) (forms r) hij⟩

/-- Common-constant form of rank-two preservation. -/
theorem AffineRankTwoGoodPrime.wTricked_const
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {p W : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : ℕ) :
    AffineRankTwoGoodPrime p
      (fun q => wTrickedAffineForm W b (forms q)) := by
  simpa using hgood.wTricked hpW (fun _q : κ => b)

/-! ## Exact one- and two-form densities -/

/-- Direct modular one-form geometry gives exact singleton density without
an integer exceptional-bound hypothesis. -/
theorem affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms) (q : κ) :
    affineFamilyZeroDensity p forms {q} = (1 : ℝ) / p := by
  rw [affineFamilyZeroDensity_singleton]
  obtain ⟨i, hi⟩ := hgood.2 q
  exact AffineForm.mean_zeroFinsetZMod
    hgood.1 (forms q) hi

/-- Exact singleton density for a W-tricked system at `p ∤ W`, uniform in
all affine constants. -/
theorem affineFamilyZeroDensity_singleton_wTricked
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {p W : ℕ} [NeZero p] {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ) (q : κ) :
    affineFamilyZeroDensity p
        (fun r => wTrickedAffineForm W (b r) (forms r)) {q} =
      (1 : ℝ) / p := by
  exact affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
    (hgood.wTricked hpW b) q

/-- Exact distinct-pair density for a W-tricked system at `p ∤ W`. -/
theorem affineFamilyZeroDensity_pair_wTricked
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p W : ℕ} [NeZero p] {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    {q r : κ} (hqr : q ≠ r) :
    affineFamilyZeroDensity p
        (fun s => wTrickedAffineForm W (b s) (forms s)) {q, r} =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [affineFamilyZeroDensity_pair _ _ hqr]
  obtain ⟨i, j, hij⟩ := hgood.2 hqr
  exact AffineForm.mean_zeroFinsetZMod_mul hgood.1 _ _
    (wTrickedAffineForm_coefficientMinor_cast_ne_zero
      hgood.1 hpW (forms q) (forms r) hij)

/-- Every nontrivial selected subfamily of a W-tricked rank-two system has
common-zero density at most `p⁻²`. -/
theorem affineFamilyZeroDensity_le_inv_sq_wTricked
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p W : ℕ} [NeZero p] {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    (s : Finset κ) (hs : s.Nontrivial) :
    affineFamilyZeroDensity p
        (fun q => wTrickedAffineForm W (b q) (forms q)) s ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  exact affineFamilyZeroDensity_le_inv_sq_of_goodPrime
    (hgood.wTricked hpW b) s hs

/-! ## Complex first-order expansion from modular geometry -/

/-- Exact first-order expansion under the direct modular one-form
predicate.  This is the replacement for the integer-size-dependent
`complexWeightedLocalFactor_eq_firstOrder_add_remainder` at W-tricked
primes. -/
theorem complexWeightedLocalFactor_eq_firstOrder_add_remainder_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      1 - (∑ q, a q) / (p : ℂ) +
        complexWeightedLocalFactorRemainder p forms a := by
  let univSupports : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset
  let term : Finset κ → ℂ :=
    fun s =>
      ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
        (affineFamilyZeroDensity p forms s : ℂ)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      univSupports (fun s => 2 ≤ s.card) term
  have hlow :
      (∑ s ∈ univSupports.filter (fun s => ¬2 ≤ s.card),
        term s) =
        1 - (∑ q, a q) / (p : ℂ) := by
    rw [show
        univSupports.filter (fun s => ¬2 ≤ s.card) =
          (Finset.univ : Finset κ).powerset.filter
            (fun s => ¬2 ≤ s.card) by rfl,
      sum_powerset_supports_of_card_lt_two_complex]
    simp only [term, Finset.card_empty, pow_zero,
      Finset.prod_empty, one_mul,
      affineFamilyZeroDensity_empty, Complex.ofReal_one,
      Finset.card_singleton, pow_one, Finset.prod_singleton]
    simp_rw [
      affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
        hnonzero]
    push_cast
    simp_rw [neg_one_mul, neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  rw [complexWeightedLocalFactor_eq_inclusionExclusion]
  change (∑ s ∈ univSupports, term s) =
    1 - (∑ q, a q) / (p : ℂ) +
      complexWeightedLocalFactorRemainder p forms a
  rw [← hsplit, hlow]
  unfold complexWeightedLocalFactorRemainder
    higherOrderSelectedSupports
  change
    (∑ s ∈ univSupports.filter (fun s => 2 ≤ s.card), term s) +
        (1 - (∑ q, a q) / (p : ℂ)) =
      1 - (∑ q, a q) / (p : ℂ) +
        ∑ s ∈ univSupports.filter (fun s => 2 ≤ s.card), term s
  ac_rfl

/-- Complex local-factor remainder bound using only direct modular
one- and two-form geometry. -/
theorem norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactor p forms a -
        (1 - (∑ q, a q) / (p : ℂ))‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [
    complexWeightedLocalFactor_eq_firstOrder_add_remainder_of_goodPrime
      hnonzero]
  simpa using
    norm_complexWeightedLocalFactorRemainder_le hrankTwo a

/-! ## Stable complex and paired-Fourier ratios -/

/-- Direct-good-prime version of the stable complex local ratio estimate.
No integer exceptional bound for `forms` appears. -/
theorem norm_complexWeightedLocalRatio_sub_one_le_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hcard : 6 * Fintype.card κ ≤ p)
    (a : κ → ℂ) (ha : ∀ q, ‖a q‖ ≤ 3) :
    ‖complexWeightedLocalRatio p forms a - 1‖ ≤
      (2 * ∏ q, (1 + ‖a q‖)) /
        (p : ℝ) ^ 2 := by
  let model := complexFirstOrderLocalModel p a
  have hmodelHalf : (1 : ℝ) / 2 ≤ ‖model‖ := by
    exact one_half_le_norm_complexFirstOrderLocalModel
      hnonzero.1 hcard ha
  have hmodelPos : 0 < ‖model‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hmodelHalf
  have hlocal :
      ‖complexWeightedLocalFactor p forms a - model‖ ≤
        (∏ q, (1 + ‖a q‖)) *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
    simpa [model, complexFirstOrderLocalModel] using
      (norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
        hnonzero hrankTwo a |>.trans
          (mul_le_mul_of_nonneg_right
            (complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm
              a)
            (by positivity)))
  have hmodelNe : model ≠ 0 :=
    norm_pos_iff.mp hmodelPos
  rw [complexWeightedLocalRatio,
    div_sub_one hmodelNe, Complex.norm_div]
  calc
    ‖complexWeightedLocalFactor p forms a - model‖ /
          ‖model‖ ≤
        2 * ‖complexWeightedLocalFactor p forms a - model‖ := by
      rw [div_le_iff₀ hmodelPos]
      have hnonneg :
          0 ≤ ‖complexWeightedLocalFactor p forms a - model‖ :=
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

/-- The W-tricked paired-Fourier arithmetic factor differs from its
first-order model by `O(4^m p⁻²)` at every direct good prime `p ∤ W`.
Affine constants may vary by form. -/
theorem norm_pairedFourierLocalFactor_wTricked_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {W R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    (hR : 2 ≤ R) (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card κ /
        (p : ℝ) ^ 2 := by
  have hbase :=
    norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
      (hnonzero.wTricked hpW b)
      (hrankTwo.wTricked hpW b)
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
  simpa [pairedFourierLocalFactor,
    pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel, div_eq_mul_inv] using
    hbase.trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_pairedFourier_le
          hR hnonzero.1 t u)
        (by positivity))

/-- Direct first-order ratio estimate for a W-tricked paired-Fourier
factor. -/
theorem norm_pairedFourierLocalRatio_wTricked_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {W R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    (hR : 2 ≤ R) (hcard : 6 * Fintype.card κ ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalRatio R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u - 1‖ ≤
      pairedFourierLocalRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  have h :=
    norm_complexWeightedLocalRatio_sub_one_le_of_goodPrime
      (hnonzero.wTricked hpW b)
      (hrankTwo.wTricked hpW b)
      hcard
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
      (fun q =>
        norm_pairedFourierPrimeCoefficient_le_three
          hR hnonzero.1 (t q) (u q))
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
              hR hnonzero.1 (t q) (u q)]
      _ = (4 : ℝ) ^ Fintype.card κ := by
        simp
  change
    ‖complexWeightedLocalRatio p
        (fun q => wTrickedAffineForm W (b q) (forms q))
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

/-! ## Direct comparison with the zeta Euler model -/

/-- The W-tricked arithmetic factor and the exact zeta Euler model differ
by `O_m(p⁻²)` under direct modular good-prime hypotheses. -/
theorem norm_pairedFourierLocalFactor_wTricked_sub_zetaModel_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {W R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    (hR : 2 ≤ R) (hseven : 7 ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
        fourierZetaSystemEulerLocalFactor R p t u‖ ≤
      complexArithmeticZetaDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  have harithmetic :=
    norm_pairedFourierLocalFactor_wTricked_sub_firstOrder_le
      hnonzero hrankTwo hpW b hR t u
  have hzeta :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hnonzero.1 hseven t u
  have htriangle :
      ‖pairedFourierLocalFactor R p
            (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
          fourierZetaSystemEulerLocalFactor R p t u‖ ≤
        ‖pairedFourierLocalFactor R p
              (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
            pairedFourierFirstOrderLocalModel R p t u‖ +
          ‖fourierZetaSystemEulerLocalFactor R p t u -
            pairedFourierFirstOrderLocalModel R p t u‖ := by
    have hrearrange :
        pairedFourierLocalFactor R p
              (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
            fourierZetaSystemEulerLocalFactor R p t u =
          (pairedFourierLocalFactor R p
                (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
              pairedFourierFirstOrderLocalModel R p t u) -
            (fourierZetaSystemEulerLocalFactor R p t u -
              pairedFourierFirstOrderLocalModel R p t u) := by
      ring
    rw [hrearrange]
    exact norm_sub_le _ _
  calc
    ‖pairedFourierLocalFactor R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
        fourierZetaSystemEulerLocalFactor R p t u‖ ≤
        ‖pairedFourierLocalFactor R p
              (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
            pairedFourierFirstOrderLocalModel R p t u‖ +
          ‖fourierZetaSystemEulerLocalFactor R p t u -
            pairedFourierFirstOrderLocalModel R p t u‖ :=
      htriangle
    _ ≤
        (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2 +
          complexZetaModelDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2 :=
      add_le_add harithmetic hzeta
    _ =
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaDifferenceConstant]
      ring

/-- Strongest local statement: the direct ratio between the W-tricked
arithmetic factor and the exact zeta Euler model is `1 + O_m(p⁻²)`. -/
theorem norm_pairedFourierArithmeticToZetaLocalRatio_wTricked_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {W R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : κ → ℕ)
    (hR : 2 ≤ R)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let zeta :=
    fourierZetaSystemEulerLocalFactor R p t u
  have hzetaQuarter :
      (1 : ℝ) / 4 ≤ ‖zeta‖ := by
    exact one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
      hR hnonzero.1 hcut t u
  have hzetaPos : 0 < ‖zeta‖ :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      hzetaQuarter
  have hcomparison :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hdiff :
      ‖pairedFourierLocalFactor R p
            (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
          zeta‖ ≤
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    simpa [zeta] using
      norm_pairedFourierLocalFactor_wTricked_sub_zetaModel_le
        hnonzero hrankTwo hpW b hR
        ((Nat.le_max_left 7
          (6 * Fintype.card κ)).trans hcomparison)
        t u
  have hzetaNe : zeta ≠ 0 :=
    norm_pos_iff.mp hzetaPos
  rw [pairedFourierArithmeticToZetaLocalRatio,
    div_sub_one hzetaNe, Complex.norm_div]
  calc
    ‖pairedFourierLocalFactor R p
          (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
        zeta‖ / ‖zeta‖ ≤
        4 *
          ‖pairedFourierLocalFactor R p
              (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
            zeta‖ := by
      rw [div_le_iff₀ hzetaPos]
      have hnonneg :
          0 ≤
            ‖pairedFourierLocalFactor R p
                (fun q => wTrickedAffineForm W (b q) (forms q)) t u -
              zeta‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        4 *
          (complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaRatioErrorConstant]
      ring

/-! ## Uniform selected-CFZ specialization -/

/-- The number of forms selected by a Boolean exponent is at most the
number of forms in the ambient CFZ system. -/
theorem card_selectedCFZFormIndex_le
    {k : ℕ} (e : LinearFormsExponent k) :
    Fintype.card (SelectedCFZFormIndex e) ≤
      Fintype.card (CFZFormIndex k) := by
  exact Fintype.card_subtype_le _

/-- The elementary zeta-model comparison cutoff is monotone in the number
of forms. -/
theorem complexZetaModelComparisonCutoff_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelComparisonCutoff m ≤
      complexZetaModelComparisonCutoff n := by
  unfold complexZetaModelComparisonCutoff
  exact max_le_max le_rfl (Nat.mul_le_mul_left 6 hmn)

/-- The natural-valued zeta-model error constant is monotone in the number
of forms. -/
theorem complexZetaModelDifferenceNat_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelDifferenceNat m ≤
      complexZetaModelDifferenceNat n := by
  unfold complexZetaModelDifferenceNat
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 8 hmn)
    (Nat.mul_le_mul_left 49
      (Nat.pow_le_pow_right (by omega) hmn))

/-- The nonvanishing cutoff for the exact zeta Euler model is monotone in
the number of forms. -/
theorem complexZetaModelNonzeroCutoff_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelNonzeroCutoff m ≤
      complexZetaModelNonzeroCutoff n := by
  unfold complexZetaModelNonzeroCutoff
  exact max_le_max
    (complexZetaModelComparisonCutoff_mono hmn)
    (Nat.mul_le_mul_left 4
      (complexZetaModelDifferenceNat_mono hmn))

/-- A single exceptional cutoff for every selected CFZ subfamily.  It is
computed from the original full CFZ family, before W-scaling, and hence
depends only on `k`. -/
def wTrickedCFZComplexExceptionalBound (k : ℕ) : ℕ :=
  max
    (exceptionalPrimeBound
      (fun q : CFZFormIndex k => cfzAffineForm q))
    (complexZetaModelNonzeroCutoff
      (Fintype.card (CFZFormIndex k)))

/-- Every selected original CFZ family has direct modular one-form geometry
above the full-family k-only exceptional bound. -/
theorem selectedCFZAffineNonzeroGoodPrime
    {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k) :
    AffineNonzeroGoodPrime p
      (fun q : SelectedCFZFormIndex e =>
        cfzAffineForm q.1) := by
  exact
    (affineNonzeroGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_nonzero hk) hp hlarge).comp
        (fun q : SelectedCFZFormIndex e => q.1)

/-- Every selected original CFZ family has direct modular rank-two geometry
above the same full-family k-only exceptional bound. -/
theorem selectedCFZAffineRankTwoGoodPrime
    {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k) :
    AffineRankTwoGoodPrime p
      (fun q : SelectedCFZFormIndex e =>
        cfzAffineForm q.1) := by
  exact
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_pairwiseIndependent hk) hp hlarge).comp
        (fun q : SelectedCFZFormIndex e => q.1)
        Subtype.coe_injective

/-- Selected CFZ one- and two-form modular geometry survives W-scaling with
arbitrary formwise constants.  The constants can in particular encode
carry choices. -/
theorem selectedCFZWTrickedGoodPrime
    {k W p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime) (hpW : ¬p ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k)
    (b : SelectedCFZFormIndex e → ℕ) :
    AffineNonzeroGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W (b q) (cfzAffineForm q.1)) ∧
      AffineRankTwoGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W (b q) (cfzAffineForm q.1)) := by
  exact
    ⟨(selectedCFZAffineNonzeroGoodPrime hk hp hlarge e).wTricked
        hpW b,
      (selectedCFZAffineRankTwoGoodPrime hk hp hlarge e).wTricked
        hpW b⟩

/-- Uniform selected-CFZ arithmetic local-factor estimate against the
first-order model.  The only exceptional cutoff is the k-only cutoff of the
original family. -/
theorem norm_selectedCFZPairedFourierLocalFactor_wTricked_sub_firstOrder_le
    {k W R p : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hR : 2 ≤ R)
    (hlarge : wTrickedCFZComplexExceptionalBound k < p)
    (e : LinearFormsExponent k)
    (b : SelectedCFZFormIndex e → ℕ)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ‖pairedFourierLocalFactor R p
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W (b q) (cfzAffineForm q.1)) t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
        (p : ℝ) ^ 2 := by
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p :=
    (Nat.le_max_left _ _).trans_lt hlarge
  exact
    norm_pairedFourierLocalFactor_wTricked_sub_firstOrder_le
      (selectedCFZAffineNonzeroGoodPrime
        hk hp horiginal e)
      (selectedCFZAffineRankTwoGoodPrime
        hk hp horiginal e)
      hpW b hR t u

/-- Uniform selected-CFZ arithmetic local-factor estimate against the exact
zeta Euler model. -/
theorem norm_selectedCFZPairedFourierLocalFactor_wTricked_sub_zetaModel_le
    {k W R p : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hR : 2 ≤ R)
    (hlarge : wTrickedCFZComplexExceptionalBound k < p)
    (e : LinearFormsExponent k)
    (b : SelectedCFZFormIndex e → ℕ)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ‖pairedFourierLocalFactor R p
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W (b q) (cfzAffineForm q.1)) t u -
        fourierZetaSystemEulerLocalFactor R p t u‖ ≤
      complexArithmeticZetaDifferenceConstant
          (Fintype.card (SelectedCFZFormIndex e)) /
        (p : ℝ) ^ 2 := by
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hfullZeta :
      complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)) ≤ p :=
    (Nat.le_max_right _ _).trans hlarge.le
  have hseven : 7 ≤ p := by
    exact
      (Nat.le_max_left 7
        (6 * Fintype.card (CFZFormIndex k))).trans
        ((Nat.le_max_left _ _).trans hfullZeta)
  exact
    norm_pairedFourierLocalFactor_wTricked_sub_zetaModel_le
      (selectedCFZAffineNonzeroGoodPrime
        hk hp horiginal e)
      (selectedCFZAffineRankTwoGoodPrime
        hk hp horiginal e)
      hpW b hR hseven t u

/-- Strongest uniform selected-CFZ endpoint: the W-tricked arithmetic/zeta
local ratio is `1 + O_k(p⁻²)` for every selected subfamily, with arbitrary
formwise constants, whenever `p ∤ W` and `p` exceeds a cutoff depending only
on `k`. -/
theorem
    norm_selectedCFZPairedFourierArithmeticToZetaLocalRatio_wTricked_sub_one_le
    {k W R p : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hR : 2 ≤ R)
    (hlarge : wTrickedCFZComplexExceptionalBound k < p)
    (e : LinearFormsExponent k)
    (b : SelectedCFZFormIndex e → ℕ)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio R p
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W (b q) (cfzAffineForm q.1)) t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card (SelectedCFZFormIndex e)) /
        (p : ℝ) ^ 2 := by
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hfullZeta :
      complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)) ≤ p :=
    (Nat.le_max_right _ _).trans hlarge.le
  have hselectedZeta :
      complexZetaModelNonzeroCutoff
          (Fintype.card (SelectedCFZFormIndex e)) ≤ p :=
    (complexZetaModelNonzeroCutoff_mono
      (card_selectedCFZFormIndex_le e)).trans hfullZeta
  exact
    norm_pairedFourierArithmeticToZetaLocalRatio_wTricked_sub_one_le
      (selectedCFZAffineNonzeroGoodPrime
        hk hp horiginal e)
      (selectedCFZAffineRankTwoGoodPrime
        hk hp horiginal e)
      hpW b hR hselectedZeta t u

/-- Common-constant specialization matching the usual expression
`q ↦ wTrickedAffineForm W b (forms q)`. -/
theorem
    norm_selectedCFZPairedFourierArithmeticToZetaLocalRatio_wTricked_const_sub_one_le
    {k W b R p : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hR : 2 ≤ R)
    (hlarge : wTrickedCFZComplexExceptionalBound k < p)
    (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio R p
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W b (cfzAffineForm q.1)) t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card (SelectedCFZFormIndex e)) /
        (p : ℝ) ^ 2 := by
  simpa using
    norm_selectedCFZPairedFourierArithmeticToZetaLocalRatio_wTricked_sub_one_le
      hk hp hpW hR hlarge e
      (fun _q : SelectedCFZFormIndex e => b) t u

end Wikipedia.SzemeredisTheorem
