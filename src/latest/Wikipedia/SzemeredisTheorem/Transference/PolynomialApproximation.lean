import Mathlib.Topology.ContinuousMap.Weierstrass
import Wikipedia.SzemeredisTheorem.Transference.DenseModel

/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/

/-- Product of a finite sequence of tests.  The degree-zero monomial is the
constant-one function. -/
def testMonomial
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) : Ω → ℝ :=
  fun x => ∏ i, q (s i) x

@[simp]
theorem testMonomial_apply
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) (x : Ω) :
    testMonomial q s x = ∏ i, q (s i) x :=
  rfl

/-- Sum of the absolute values of the coefficients of a polynomial. -/
noncomputable def polynomialCoefficientL1 (p : ℝ[X]) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

theorem polynomialCoefficientL1_nonneg (p : ℝ[X]) :
    0 ≤ polynomialCoefficientL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

/-- Pairing commutes with a finite sum in its right input. -/
theorem finitePairing_finset_sum_right
    {Ω κ : Type*} [Fintype Ω]
    (f : Ω → ℝ) (s : Finset κ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i ∈ s, q i x) =
      ∑ i ∈ s, finitePairing f (q i) := by
  classical
  unfold finitePairing mean
  calc
    (𝔼 x, f x * ∑ i ∈ s, q i x) =
        𝔼 x, ∑ i ∈ s, f x * q i x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, 𝔼 x, f x * q i x := by
      exact Finset.expect_sum_comm Finset.univ s _

/-- Pairing commutes with a sum over a finite type in its right input. -/
theorem finitePairing_fintype_sum_right
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (f : Ω → ℝ) (q : κ → Ω → ℝ) :
    finitePairing f (fun x => ∑ i, q i x) =
      ∑ i, finitePairing f (q i) := by
  simpa using finitePairing_finset_sum_right f Finset.univ q

/-- Exact ordered expansion of a power of a finite test combination. -/
theorem finiteTestCombination_pow_eq_sum_monomials
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ)
    (n : ℕ) (x : Ω) :
    (finiteTestCombination q c x) ^ n =
      ∑ s : Fin n → τ,
        (∏ i, c (s i)) * testMonomial q s x := by
  classical
  rw [finiteTestCombination_apply, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.prod_mul_distrib]
  rfl

/-- Exact pointwise expansion of a polynomial evaluated on a finite test
combination. -/
theorem polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (p : ℝ[X]) (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    p.eval (finiteTestCombination q c x) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            testMonomial q s x := by
  classical
  rw [Polynomial.eval_eq_sum]
  change
    (∑ n ∈ p.support,
      p.coeff n * (finiteTestCombination q c x) ^ n) = _
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteTestCombination_pow_eq_sum_monomials,
    Finset.mul_sum]
  apply Fintype.sum_congr
  intro s
  ring

/-- Exact expansion after pairing a polynomial in a test combination with
an arbitrary function. -/
theorem finitePairing_polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (p : ℝ[X])
    (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f
        (fun x => p.eval (finiteTestCombination q c x)) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing f (testMonomial q s) := by
  classical
  have heval :
      (fun x => p.eval (finiteTestCombination q c x)) =
        fun x => ∑ n ∈ p.support,
          ∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              testMonomial q s x := by
    funext x
    exact polynomial_eval_finiteTestCombination p q c x
  rw [heval, finitePairing_finset_sum_right]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finitePairing_fintype_sum_right]
  apply Fintype.sum_congr
  intro s
  change
    finitePairing f
        ((p.coeff n * ∏ i, c (s i)) • testMonomial q s) =
      _
  exact
    finitePairing_smul_right
      (p.coeff n * ∏ i, c (s i)) f (testMonomial q s)

/-- The sum of absolute ordered monomial coefficients is the corresponding
power of the coefficient `ℓ¹`-norm. -/
theorem sum_abs_coefficientMonomial
    {τ : Type*} [Fintype τ]
    (c : τ → ℝ) (n : ℕ) :
    ∑ s : Fin n → τ, |∏ i, c (s i)| =
      coefficientL1 c ^ n := by
  classical
  unfold coefficientL1
  rw [Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.abs_prod]

/-- Uniform correlation estimate for all products of at most `d` tests. -/
def HasMonomialCorrelationBound
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ)
    (d : ℕ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d → ∀ s : Fin n → τ,
    |finitePairing (ν - fun _ => 1) (testMonomial q s)| ≤ η

/-- Expanding a polynomial loses at most the coefficient `ℓ¹`-norm when the
coefficient vector of the test combination is normalized. -/
theorem abs_finitePairing_polynomial_eval_le
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    {η : ℝ} (p : ℝ[X]) (c : τ → ℝ)
    (hc : coefficientL1 c = 1)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    |finitePairing (ν - fun _ => 1)
        (fun x => p.eval (finiteTestCombination q c x))| ≤
      polynomialCoefficientL1 p * η := by
  classical
  rw [finitePairing_polynomial_eval_finiteTestCombination]
  calc
    |∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing (ν - fun _ => 1)
              (testMonomial q s)| ≤
        ∑ n ∈ p.support,
          |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * η := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| ≤
            ∑ s : Fin n → τ,
              |(p.coeff n * ∏ i, c (s i)) *
                finitePairing (ν - fun _ => 1)
                  (testMonomial q s)| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s : Fin n → τ,
              |p.coeff n| * |∏ i, c (s i)| * η := by
          apply Finset.sum_le_sum
          intro s hs
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hmono n
              (Polynomial.le_natDegree_of_mem_supp n hn) s)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |p.coeff n| *
              (∑ s : Fin n → τ, |∏ i, c (s i)|) * η := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = |p.coeff n| * η := by
          rw [sum_abs_coefficientMonomial, hc, one_pow, mul_one]
    _ = polynomialCoefficientL1 p * η := by
      rw [polynomialCoefficientL1, Finset.sum_mul]

/-! ## Bounded combinations and approximation of positive part -/

/-- Every member of a finite test family is pointwise in `[0,1]`. -/
def IsUnitBoundedTestFamily
    {Ω τ : Type*} (q : τ → Ω → ℝ) : Prop :=
  ∀ t, IsUnitBounded (q t)

/-- A test combination is pointwise bounded by the coefficient `ℓ¹`-norm
when every test is `[0,1]`-valued. -/
theorem abs_finiteTestCombination_le_coefficientL1
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    (c : τ → ℝ) (x : Ω) :
    |finiteTestCombination q c x| ≤ coefficientL1 c := by
  classical
  rw [finiteTestCombination_apply]
  calc
    |∑ t, c t * q t x| ≤ ∑ t, |c t * q t x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, |c t| := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have habs : |q t x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [(hq t).nonneg x]
        · exact (hq t).le_one x
      exact mul_le_of_le_one_right (abs_nonneg (c t)) habs
    _ = coefficientL1 c := by
      rfl

/-- A normalized test combination takes values in `[-1,1]`. -/
theorem finiteTestCombination_mem_unitInterval
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    finiteTestCombination q c x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, ← abs_le]
  simpa [hc] using
    abs_finiteTestCombination_le_coefficientL1 hq c x

/-- A polynomial uniformly approximates positive part on the unit interval
to the displayed error. -/
def ApproximatesPositivePartOnUnitInterval
    (p : ℝ[X]) (δ : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |p.eval x - max x 0| ≤ δ

/-- Weierstrass approximation for positive part on `[-1,1]`. -/
theorem exists_polynomial_approximating_positivePart
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℝ[X], ApproximatesPositivePartOnUnitInterval p δ := by
  have hcontinuous :
      ContinuousOn (fun x : ℝ => max x 0)
        (Set.Icc (-1 : ℝ) 1) :=
    (continuous_id.max continuous_const).continuousOn
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      (-1 : ℝ) 1 (fun x : ℝ => max x 0)
      hcontinuous δ hδ
  exact ⟨p, fun x hx => (hp x hx).le⟩

/-- Pointwise polynomial approximation after substituting a normalized test
combination. -/
theorem polynomial_eval_approximates_positivePart_combination
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ : ℝ}
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    {c : τ → ℝ} (hc : coefficientL1 c = 1)
    (x : Ω) :
    |p.eval (finiteTestCombination q c x) -
        positivePart (finiteTestCombination q c) x| ≤ δ := by
  exact hp _ (finiteTestCombination_mem_unitInterval hq hc x)

/-! ## Quantitative positive-part correlation -/

/-- An error bounded pointwise by `δ` contributes at most `δ` times the
mean absolute size of the left factor to a normalized pairing. -/
theorem abs_finitePairing_le_mul_mean_abs
    {Ω : Type*} [Fintype Ω]
    (f e : Ω → ℝ) {δ : ℝ}
    (he : ∀ x, |e x| ≤ δ) :
    |finitePairing f e| ≤ δ * mean (fun x => |f x|) := by
  calc
    |finitePairing f e| ≤ mean (fun x => |f x * e x|) := by
      unfold finitePairing mean
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x => δ * |f x|) := by
      apply mean_mono
      intro x
      rw [abs_mul]
      have hmul :=
        mul_le_mul_of_nonneg_left (he x) (abs_nonneg (f x))
      simpa [mul_comm] using hmul
    _ = δ * mean (fun x => |f x|) :=
      mean_smul δ _

/-- The absolute mean of the centered majorant. -/
noncomputable def centeredAbsoluteMean
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) : ℝ :=
  mean fun x => |ν x - 1|

theorem centeredAbsoluteMean_nonneg
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) :
    0 ≤ centeredAbsoluteMean ν :=
  mean_nonneg fun _ => abs_nonneg _

/-- For a nonnegative majorant, its centered absolute mean is bounded by
its mean plus one. -/
theorem centeredAbsoluteMean_le_mean_add_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    centeredAbsoluteMean ν ≤ mean ν + 1 := by
  unfold centeredAbsoluteMean
  calc
    mean (fun x => |ν x - 1|) ≤
        mean (fun x => ν x + 1) := by
      apply mean_mono
      intro x
      rw [abs_le]
      constructor <;> linarith [hν x]
    _ = mean ν + mean (fun _ : Ω => (1 : ℝ)) :=
      mean_add _ _
    _ = mean ν + 1 := by
      rw [mean_const]

/-- Polynomial approximation plus monomial correlation estimates imply the
normalized positive-part correlation bound used by dense-model duality. -/
theorem hasNormalizedPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasNormalizedPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) := by
  intro c hc
  let Q := finiteTestCombination q c
  let P : Ω → ℝ := fun x => p.eval (Q x)
  have hpoly :
      finitePairing (ν - fun _ => 1) P ≤
        polynomialCoefficientL1 p * η := by
    exact le_trans (le_abs_self _) <|
      abs_finitePairing_polynomial_eval_le p c hc hmono
  have hpoint :
      ∀ x, |positivePart Q x - P x| ≤ δ := by
    intro x
    have hx :=
      polynomial_eval_approximates_positivePart_combination
        hq hp hc x
    simpa [Q, P, abs_sub_comm] using hx
  have herr0 :
      |finitePairing (ν - fun _ => 1)
        (positivePart Q - P)| ≤
          δ * centeredAbsoluteMean ν := by
    have hbase :=
      abs_finitePairing_le_mul_mean_abs
        (ν - fun _ => 1) (positivePart Q - P)
        (by
          intro x
          simpa using hpoint x)
    have hcentered :
        (fun x =>
          |(ν - (fun _ : Ω => (1 : ℝ))) x|) =
          (fun x => |ν x - 1|) := by
      funext x
      rfl
    rw [hcentered] at hbase
    exact hbase
  have herr :
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤ δ * M := by
    calc
      finitePairing (ν - fun _ => 1)
          (positivePart Q - P) ≤
          |finitePairing (ν - fun _ => 1)
            (positivePart Q - P)| :=
        le_abs_self _
      _ ≤ δ * centeredAbsoluteMean ν := herr0
      _ ≤ δ * M :=
        mul_le_mul_of_nonneg_left hM hδ
  have hsplit :
      finitePairing (ν - fun _ => 1) (positivePart Q) =
        finitePairing (ν - fun _ => 1) P +
          finitePairing (ν - fun _ => 1)
            (positivePart Q - P) := by
    rw [← finitePairing_add_right]
    congr 1
    funext x
    simp
  rw [hsplit]
  exact add_le_add hpoly herr

/-- Homogeneous form of the polynomial dense-model estimate. -/
theorem hasPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) :=
  hasPositivePartCorrelationBound_of_normalized q ν _
    (hasNormalizedPositivePartCorrelationBound_of_polynomial
      hq hδ hp hM hmono)

end Wikipedia.SzemeredisTheorem
