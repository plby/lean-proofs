/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1028
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.UniformOn

/-!
# The quadratic Lindeberg replacement estimate

This file formalizes the degree-two instance of the
Mossel--O'Donnell--Oleszkiewicz invariance estimate used in Section 11 of
Kwan--Sah--Sauermann--Sawhney.  Pair coefficients are stored only once: the
entry `pair i j` is used when `i < j`.  Thus `influence q i` is exactly the
sum of the squares of the coefficients of the multilinear monomials which
contain `i`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace Erdos88
namespace Invariance

/-- The two Rademacher signs. -/
def rademacherSign : Bool → ℝ
  | false => -1
  | true => 1

/-- Normalized counting expectation on a nonempty finite type. -/
noncomputable def finiteExpectation (A : Type*) [Fintype A] [Nonempty A]
    (f : A → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card A : ℝ)

/-- Coefficients of a multilinear polynomial of degree at most two.  Only
`pair i j` with `i < j` is used. -/
structure QuadraticCoeffs (n : ℕ) where
  constant : ℝ
  linear : Fin n → ℝ
  pair : Fin n → Fin n → ℝ

namespace QuadraticCoeffs

variable {n : ℕ}

/-- The symmetric, zero-diagonal kernel represented by the upper-triangular
array `pair`. -/
def symPair (q : QuadraticCoeffs n) (i j : Fin n) : ℝ :=
  if i < j then q.pair i j else if j < i then q.pair j i else 0

@[simp] lemma symPair_self (q : QuadraticCoeffs n) (i : Fin n) :
    q.symPair i i = 0 := by simp [symPair]

lemma symPair_comm (q : QuadraticCoeffs n) (i j : Fin n) :
    q.symPair i j = q.symPair j i := by
  by_cases hij : i < j
  · have hji : ¬j < i := not_lt_of_ge (Fin.le_of_lt hij)
    simp [symPair, hij, hji]
  · by_cases hji : j < i
    · simp [symPair, hij, hji]
    · have heq : i = j := Fin.le_antisymm (Fin.not_lt.mp hji) (Fin.not_lt.mp hij)
      subst j
      simp

/-- Evaluation of the coefficient array.  The factor `1/2` compensates for
the two appearances of every off-diagonal coefficient in the symmetric
double sum. -/
noncomputable def eval (q : QuadraticCoeffs n) (x : Fin n → ℝ) : ℝ :=
  q.constant + ∑ i, q.linear i * x i +
    (1 / 2 : ℝ) * ∑ i, ∑ j, q.symPair i j * x i * x j

lemma measurable_eval (q : QuadraticCoeffs n) : Measurable q.eval := by
  exact (measurable_const.add (Finset.measurable_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i))).add
    (measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ ↦
      Finset.measurable_sum Finset.univ fun j _ ↦
        (measurable_const.mul (measurable_pi_apply i)).mul (measurable_pi_apply j)))

/-- The MOO influence: the squared coefficient norm of the monomials which
contain the indicated coordinate. -/
def influence (q : QuadraticCoeffs n) (t : Fin n) : ℝ :=
  q.linear t ^ 2 + ∑ j, q.symPair t j ^ 2

lemma influence_nonneg (q : QuadraticCoeffs n) (t : Fin n) :
    0 ≤ q.influence t := by
  simp only [influence]
  positivity

/-- Restriction to all coordinates except the first one. -/
def tail (q : QuadraticCoeffs (n + 1)) : QuadraticCoeffs n where
  constant := q.constant
  linear i := q.linear i.succ
  pair i j := q.pair i.succ j.succ

/-- After fixing the first coordinate to `a`, this is the resulting
quadratic polynomial in the remaining coordinates. -/
def fixHead (q : QuadraticCoeffs (n + 1)) (a : ℝ) : QuadraticCoeffs n where
  constant := q.constant + a * q.linear 0
  linear i := q.linear i.succ + a * q.pair 0 i.succ
  pair i j := q.pair i.succ j.succ

/-- Coefficient of the first coordinate, with the tail held fixed. -/
def headDerivative (q : QuadraticCoeffs (n + 1)) (x : Fin n → ℝ) : ℝ :=
  q.linear 0 + ∑ j, q.pair 0 j.succ * x j

@[simp] lemma eval_zero (q : QuadraticCoeffs 0) (x : Fin 0 → ℝ) :
    q.eval x = q.constant := by
  simp [eval]

/-! ## Coordinate decomposition -/
/-- The part of a quadratic polynomial which does not use coordinate `t`,
written in the coordinates supplied by `Fin.succAbove t`. -/
noncomputable def coordinateBase (q : QuadraticCoeffs (n + 1)) (t : Fin (n + 1))
    (y : Fin n → ℝ) : ℝ :=
  q.constant + ∑ j, q.linear (t.succAbove j) * y j +
    (1 / 2 : ℝ) * ∑ j, ∑ k,
      q.symPair (t.succAbove j) (t.succAbove k) * y j * y k

/-- The coefficient of coordinate `t`, after the remaining coordinates have
been collected using `Fin.succAbove t`. -/
def coordinateSlope (q : QuadraticCoeffs (n + 1)) (t : Fin (n + 1))
    (y : Fin n → ℝ) : ℝ :=
  q.linear t + ∑ j, q.symPair t (t.succAbove j) * y j

lemma measurable_coordinateBase (q : QuadraticCoeffs (n + 1)) (t : Fin (n + 1)) :
    Measurable (q.coordinateBase t) := by
  exact (measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦
      measurable_const.mul (measurable_pi_apply j))).add
    (measurable_const.mul (Finset.measurable_sum Finset.univ fun j _ ↦
      Finset.measurable_sum Finset.univ fun k _ ↦
        (measurable_const.mul (measurable_pi_apply j)).mul (measurable_pi_apply k)))

lemma measurable_coordinateSlope (q : QuadraticCoeffs (n + 1)) (t : Fin (n + 1)) :
    Measurable (q.coordinateSlope t) := by
  exact measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦
    measurable_const.mul (measurable_pi_apply j))

/-- A multilinear quadratic polynomial is affine in any one coordinate. -/
lemma eval_piFinSuccAbove (q : QuadraticCoeffs (n + 1)) (t : Fin (n + 1))
    (z : ℝ) (y : Fin n → ℝ) :
    q.eval ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) =
      q.coordinateBase t y + q.coordinateSlope t y * z := by
  let x : Fin (n + 1) → ℝ := Fin.insertNth t z y
  have hx :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) = x := by
    rfl
  rw [hx]
  have hlin := Fin.sum_univ_succAbove (fun i ↦ q.linear i * x i) t
  have houter := Fin.sum_univ_succAbove
    (fun i ↦ ∑ j, q.symPair i j * x i * x j) t
  have hrow (i : Fin (n + 1)) := Fin.sum_univ_succAbove
    (fun j ↦ q.symPair i j * x i * x j) t
  simp only [eval, coordinateBase, coordinateSlope]
  rw [hlin, houter, hrow t]
  simp_rw [hrow (t.succAbove _)]
  simp only [x, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    symPair_self, zero_mul]
  simp_rw [q.symPair_comm (t.succAbove _) t]
  rw [Finset.sum_add_distrib]
  have hleft :
      (∑ j, q.symPair t (t.succAbove j) * z * y j) =
        z * ∑ j, q.symPair t (t.succAbove j) * y j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright :
      (∑ j, q.symPair t (t.succAbove j) * y j * z) =
        (∑ j, q.symPair t (t.succAbove j) * y j) * z := by
    rw [Finset.sum_mul]
  rw [hleft, hright]
  ring

/-- In successor dimension the influence is visibly the squared coefficient
norm of the affine coordinate slope. -/
lemma influence_eq_coordinateSlopeNorm (q : QuadraticCoeffs (n + 1))
    (t : Fin (n + 1)) :
    q.influence t = q.linear t ^ 2 +
      ∑ j : Fin n, q.symPair t (t.succAbove j) ^ 2 := by
  rw [influence, Fin.sum_univ_succAbove (fun j ↦ q.symPair t j ^ 2) t]
  simp

end QuadraticCoeffs

/-- The standard real Gaussian law. -/
noncomputable abbrev standardGaussian : Measure ℝ := gaussianReal 0 1

/-- The uniform law on the two Rademacher signs, realized as the pushforward
of the uniform law on `Bool`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  (PMF.uniformOfFintype Bool).toMeasure.map rademacherSign

noncomputable instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Product measure of `n` independent standard Gaussians. -/
noncomputable def gaussianProductMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ standardGaussian

noncomputable instance (n : ℕ) : IsProbabilityMeasure (gaussianProductMeasure n) := by
  dsimp [gaussianProductMeasure]
  infer_instance

/-- Expectation under independent standard Gaussians. -/
noncomputable def gaussianExpectation {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, f x ∂gaussianProductMeasure n

/-- Product measure of independent Rademacher signs. -/
noncomputable def rademacherProductMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ rademacherMeasure

noncomputable instance (n : ℕ) : IsProbabilityMeasure (rademacherProductMeasure n) := by
  dsimp [rademacherProductMeasure]
  infer_instance

/-- Integral presentation of Rademacher expectation. -/
noncomputable def rademacherIntegralExpectation {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, f x ∂rademacherProductMeasure n

/-- Expectation under independent uniform Rademacher signs. -/
noncomputable def rademacherExpectation {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  finiteExpectation (Fin n → Bool)
    (fun ξ ↦ f fun i ↦ rademacherSign (ξ i))

/-! ## Finite and product Rademacher expectations -/
lemma uniformOfFintype_toMeasure_eq_uniformOn_univ
    (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] :
    (PMF.uniformOfFintype A).toMeasure =
      ProbabilityTheory.uniformOn (Set.univ : Set A) := by
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_uniformOfFintype_apply {a} (measurableSet_singleton a)]
  simp [ProbabilityTheory.uniformOn_univ]

lemma pi_uniformBool_eq_uniformFunction (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype Bool).toMeasure) =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  calc
    (Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype Bool).toMeasure) =
        Measure.pi (fun _ : Fin n ↦
          ProbabilityTheory.uniformOn (Set.univ : Set Bool)) := by
            simp_rw [uniformOfFintype_toMeasure_eq_uniformOn_univ Bool]
    _ = ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool)) := by
      rw [← ProbabilityTheory.uniformOn_pi
        (f := fun _ : Fin n ↦ (Set.univ : Set Bool))]
      congr 1
      ext x
      simp
    _ = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure :=
      (uniformOfFintype_toMeasure_eq_uniformOn_univ (Fin n → Bool)).symm

lemma rademacherProductMeasure_eq_map (n : ℕ) :
    rademacherProductMeasure n =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure.map
        (fun ξ i ↦ rademacherSign (ξ i)) := by
  calc
    rademacherProductMeasure n =
        Measure.pi (fun _ : Fin n ↦
          (PMF.uniformOfFintype Bool).toMeasure.map rademacherSign) := by
            rfl
    _ = (Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype Bool).toMeasure).map
          (fun ξ i ↦ rademacherSign (ξ i)) := by
            symm
            exact Measure.pi_map_pi fun _ ↦ (measurable_of_finite _).aemeasurable
    _ = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure.map
          (fun ξ i ↦ rademacherSign (ξ i)) := by
            rw [pi_uniformBool_eq_uniformFunction]

/-- The normalized finite sum and the product-measure presentations of
Rademacher expectation agree for measurable functions. -/
lemma rademacherIntegralExpectation_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    rademacherIntegralExpectation f = rademacherExpectation f := by
  rw [rademacherIntegralExpectation, rademacherProductMeasure_eq_map,
    MeasureTheory.integral_map]
  · rw [PMF.integral_eq_sum]
    unfold rademacherExpectation finiteExpectation
    simp only [PMF.uniformOfFintype_apply, Fintype.card_pi,
      Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      smul_eq_mul]
    rw [← Finset.mul_sum]
    exact mul_comm _ _
  · exact (measurable_of_finite
      (fun ξ : Fin n → Bool ↦ fun i ↦ rademacherSign (ξ i))).aemeasurable
  · exact hf.aestronglyMeasurable

@[simp] lemma rademacherExpectation_const {n : ℕ} (c : ℝ) :
    rademacherExpectation (n := n) (fun _ ↦ c) = c := by
  simp [rademacherExpectation, finiteExpectation]

@[simp] lemma gaussianExpectation_const {n : ℕ} (c : ℝ) :
    gaussianExpectation (n := n) (fun _ ↦ c) = c := by
  simp [gaussianExpectation]

/-- Coordinate law in the Lindeberg chain: the first `t` coordinates are
Gaussian and the rest are Rademacher. -/
noncomputable def hybridCoordinateMeasure {n : ℕ} (t : ℕ) (i : Fin n) : Measure ℝ :=
  if (i : ℕ) < t then standardGaussian else rademacherMeasure

noncomputable instance {n : ℕ} (t : ℕ) (i : Fin n) :
    IsProbabilityMeasure (hybridCoordinateMeasure t i) := by
  rw [hybridCoordinateMeasure]
  split <;> infer_instance

/-- Product law at one point of the Lindeberg replacement chain. -/
noncomputable def hybridMeasure (n t : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (hybridCoordinateMeasure t)

noncomputable instance (n t : ℕ) : IsProbabilityMeasure (hybridMeasure n t) := by
  dsimp [hybridMeasure]
  infer_instance

/-! ## The hybrid replacement chain -/
@[simp] lemma hybridMeasure_zero (n : ℕ) :
    hybridMeasure n 0 = rademacherProductMeasure n := by
  unfold hybridMeasure rademacherProductMeasure
  congr with i

lemma hybridMeasure_eq_gaussian (n t : ℕ) (hnt : n ≤ t) :
    hybridMeasure n t = gaussianProductMeasure n := by
  simp only [hybridMeasure, gaussianProductMeasure]
  congr with i
  simp [hybridCoordinateMeasure, Nat.lt_of_lt_of_le i.isLt hnt]

/-- Removing the coordinate whose index is the current replacement time
leaves the same hybrid chain in one lower dimension. -/
lemma hybridMeasure_succAbove {n : ℕ} (t : Fin (n + 1)) :
    (Measure.pi fun j : Fin n ↦ hybridCoordinateMeasure t.val (t.succAbove j)) =
      hybridMeasure n t.val := by
  simp only [hybridMeasure]
  congr 1
  funext j
  simp only [hybridCoordinateMeasure]
  congr 1
  apply propext
  exact Fin.succAbove_lt_iff_castSucc_lt t j

/-- A bounded `C⁴` test.  Boundedness is used only to discharge the Fubini
integrability conditions.  The numerical replacement error depends solely on
the fourth-derivative bound. -/
structure IsBoundedC4Test (psi : ℝ → ℝ) (M : ℝ) : Prop where
  contDiff : ContDiff ℝ 4 psi
  bounded : ∃ B : ℝ, ∀ x, |psi x| ≤ B
  fourth_nonneg : 0 ≤ M
  fourth_bound : ∀ x, |iteratedDeriv 4 psi x| ≤ M

/-- Global fourth-order Taylor remainder with the normalization used in the
Lindeberg argument. -/
lemma taylor_remainder_four (psi : ℝ → ℝ) (M a h : ℝ)
    (hpsi : ContDiff ℝ 4 psi) (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |iteratedDeriv 4 psi x| ≤ M) :
    |psi (a + h) -
        (psi a + deriv psi a * h + iteratedDeriv 2 psi a * h ^ 2 / 2 +
          iteratedDeriv 3 psi a * h ^ 3 / 6)| ≤
      M * |h| ^ 4 / 24 := by
  by_cases hh : h = 0
  · subst h
    simp
  have hax : a ≠ a + h := by
    intro ha
    apply hh
    linarith
  have hu : UniqueDiffOn ℝ (Set.uIcc a (a + h)) := uniqueDiffOn_uIcc hax
  have hpsi' : ContDiffOn ℝ (3 + 1) psi (Set.uIcc a (a + h)) := by
    convert hpsi.contDiffOn using 1 <;> norm_num
  obtain ⟨c, _hc, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := psi) (x := a + h) (x₀ := a)
      (n := 3) hax hpsi'
  have hder0 : iteratedDerivWithin 0 psi (Set.uIcc a (a + h)) a = iteratedDeriv 0 psi a :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hpsi.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc
  have hder1 : iteratedDerivWithin 1 psi (Set.uIcc a (a + h)) a = iteratedDeriv 1 psi a :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hpsi.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc
  have hder2 : iteratedDerivWithin 2 psi (Set.uIcc a (a + h)) a = iteratedDeriv 2 psi a :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hpsi.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc
  have hder3 : iteratedDerivWithin 3 psi (Set.uIcc a (a + h)) a = iteratedDeriv 3 psi a :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hpsi.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc
  have hta :
      taylorWithinEval psi 3 (Set.uIcc a (a + h)) a (a + h) =
        psi a + deriv psi a * h + iteratedDeriv 2 psi a * h ^ 2 / 2 +
          iteratedDeriv 3 psi a * h ^ 3 / 6 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hder0, hder1, hder2, hder3,
      iteratedDeriv_zero, iteratedDeriv_one] <;> ring
  rw [hta] at hrem
  rw [hrem]
  calc
    |iteratedDeriv 4 psi c * ((a + h) - a) ^ 4 / (Nat.factorial 4 : ℝ)| =
        |iteratedDeriv 4 psi c| * |h| ^ 4 / 24 := by
      rw [abs_div, abs_mul, abs_pow]
      norm_num <;> ring
    _ ≤ M * |h| ^ 4 / 24 := by
      gcongr
      exact hbound c

lemma integral_rademacher (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂rademacherMeasure = (f (-1) + f 1) / 2 := by
  rw [rademacherMeasure, MeasureTheory.integral_map]
  · rw [PMF.integral_eq_sum]
    simp [PMF.uniformOfFintype_apply, rademacherSign]
    ring
  · exact (measurable_of_finite rademacherSign).aemeasurable
  · exact hf.aestronglyMeasurable

@[simp] lemma integral_id_rademacher : ∫ x, x ∂rademacherMeasure = 0 := by
  simpa using integral_rademacher id continuous_id

@[simp] lemma integral_sq_rademacher : ∫ x, x ^ 2 ∂rademacherMeasure = 1 := by
  rw [integral_rademacher (fun x : ℝ ↦ x ^ 2) (by fun_prop)]
  norm_num

@[simp] lemma integral_cube_rademacher : ∫ x, x ^ 3 ∂rademacherMeasure = 0 := by
  rw [integral_rademacher (fun x : ℝ ↦ x ^ 3) (by fun_prop)]
  norm_num

@[simp] lemma integral_fourth_rademacher : ∫ x, x ^ 4 ∂rademacherMeasure = 1 := by
  rw [integral_rademacher (fun x : ℝ ↦ x ^ 4) (by fun_prop)]
  norm_num

lemma integrable_pow_rademacher (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) rademacherMeasure := by
  rw [rademacherMeasure]
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_of_finite _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun b ↦ by
    cases b <;> simp [rademacherSign]

lemma integrable_pow_standardGaussian (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) standardGaussian := by
  apply (integrable_norm_iff (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ ↦ x ^ k) standardGaussian)).mp
  simpa [Real.norm_eq_abs, abs_pow] using
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
      (p := (k : NNReal))).integrable_norm_pow'

lemma standardGaussian_moment_eq_iteratedDeriv (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂standardGaussian) =
      iteratedDeriv k (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) 0 := by
  change (∫ x : ℝ, ((fun x : ℝ ↦ x) ^ k) x ∂gaussianReal 0 1) = _
  rw [← iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x)
    (by simp : 0 ∈ interior (integrableExpSet
      (fun x : ℝ ↦ x) (gaussianReal 0 1))) k]
  rw [mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]

lemma deriv_standardGaussian_mgf :
    deriv (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t ↦ t * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [_root_.deriv_exp (by fun_prop)]
  rw [deriv_div_const, deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_one :
    deriv (fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_id'', deriv_div_const, deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_two :
    deriv (fun t : ℝ ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_three :
    deriv (fun t : ℝ ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const, deriv_id'',
    deriv_fun_pow (by fun_prop) 3, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

@[simp] lemma standardGaussian_moment_one :
    ∫ x : ℝ, x ^ 1 ∂standardGaussian = 0 := by
  simpa using (integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))

@[simp] lemma standardGaussian_moment_two :
    ∫ x : ℝ, x ^ 2 ∂standardGaussian = 1 := by
  rw [standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_standardGaussian_mgf,
    deriv_standardGaussian_mgf_one]
  norm_num

@[simp] lemma standardGaussian_moment_three :
    ∫ x : ℝ, x ^ 3 ∂standardGaussian = 0 := by
  rw [standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_standardGaussian_mgf, deriv_standardGaussian_mgf_one,
    deriv_standardGaussian_mgf_two]
  norm_num

@[simp] lemma standardGaussian_moment_four :
    ∫ x : ℝ, x ^ 4 ∂standardGaussian = 3 := by
  rw [standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_standardGaussian_mgf, deriv_standardGaussian_mgf_one,
    deriv_standardGaussian_mgf_two, deriv_standardGaussian_mgf_three]
  norm_num

/-- The cubic Taylor polynomial at `a`, evaluated at increment `h`. -/
noncomputable def cubicTaylor (psi : ℝ → ℝ) (a h : ℝ) : ℝ :=
  psi a + deriv psi a * h + iteratedDeriv 2 psi a * h ^ 2 / 2 +
    iteratedDeriv 3 psi a * h ^ 3 / 6

lemma taylor_remainder_four' {psi : ℝ → ℝ} {M : ℝ}
    (hpsi : IsBoundedC4Test psi M) (a h : ℝ) :
    |psi (a + h) - cubicTaylor psi a h| ≤ M * |h| ^ 4 / 24 := by
  simpa only [cubicTaylor] using
    taylor_remainder_four psi M a h hpsi.contDiff hpsi.fourth_nonneg hpsi.fourth_bound

lemma integrable_cubicTaylor_standardGaussian (psi : ℝ → ℝ) (a s : ℝ) :
    Integrable (fun x ↦ cubicTaylor psi a (s * x)) standardGaussian := by
  have h0 : Integrable (fun _ : ℝ ↦ psi a) standardGaussian := integrable_const _
  have h1 : Integrable (fun x : ℝ ↦ deriv psi a * (s * x)) standardGaussian := by
    exact (integrable_pow_standardGaussian 1).const_mul (deriv psi a * s) |>.congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h2 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 2 psi a * (s * x) ^ 2 / 2) standardGaussian := by
    exact ((integrable_pow_standardGaussian 2).const_mul
      (iteratedDeriv 2 psi a * s ^ 2 / 2)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h3 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 3 psi a * (s * x) ^ 3 / 6) standardGaussian := by
    exact ((integrable_pow_standardGaussian 3).const_mul
      (iteratedDeriv 3 psi a * s ^ 3 / 6)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  exact ((h0.add h1).add h2).add h3

lemma integrable_cubicTaylor_rademacher (psi : ℝ → ℝ) (a s : ℝ) :
    Integrable (fun x ↦ cubicTaylor psi a (s * x)) rademacherMeasure := by
  have h0 : Integrable (fun _ : ℝ ↦ psi a) rademacherMeasure := integrable_const _
  have h1 : Integrable (fun x : ℝ ↦ deriv psi a * (s * x)) rademacherMeasure := by
    exact (integrable_pow_rademacher 1).const_mul (deriv psi a * s) |>.congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h2 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 2 psi a * (s * x) ^ 2 / 2) rademacherMeasure := by
    exact ((integrable_pow_rademacher 2).const_mul
      (iteratedDeriv 2 psi a * s ^ 2 / 2)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h3 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 3 psi a * (s * x) ^ 3 / 6) rademacherMeasure := by
    exact ((integrable_pow_rademacher 3).const_mul
      (iteratedDeriv 3 psi a * s ^ 3 / 6)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  exact ((h0.add h1).add h2).add h3

lemma integral_cubicTaylor_standardGaussian (psi : ℝ → ℝ) (a s : ℝ) :
    ∫ x, cubicTaylor psi a (s * x) ∂standardGaussian =
      psi a + iteratedDeriv 2 psi a * s ^ 2 / 2 := by
  have h0 : Integrable (fun _ : ℝ ↦ psi a) standardGaussian := integrable_const _
  have h1 : Integrable (fun x : ℝ ↦ deriv psi a * (s * x)) standardGaussian := by
    exact (integrable_pow_standardGaussian 1).const_mul (deriv psi a * s) |>.congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h2 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 2 psi a * (s * x) ^ 2 / 2) standardGaussian := by
    exact ((integrable_pow_standardGaussian 2).const_mul
      (iteratedDeriv 2 psi a * s ^ 2 / 2)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have h3 : Integrable
      (fun x : ℝ ↦ iteratedDeriv 3 psi a * (s * x) ^ 3 / 6) standardGaussian := by
    exact ((integrable_pow_standardGaussian 3).const_mul
      (iteratedDeriv 3 psi a * s ^ 3 / 6)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  have hcubic : (fun x : ℝ ↦ cubicTaylor psi a (s * x)) =
      (((fun _ : ℝ ↦ psi a) +
        (fun x : ℝ ↦ deriv psi a * (s * x))) +
        (fun x : ℝ ↦ iteratedDeriv 2 psi a * (s * x) ^ 2 / 2)) +
        (fun x : ℝ ↦ iteratedDeriv 3 psi a * (s * x) ^ 3 / 6) := by
    funext x
    simp [cubicTaylor]
  rw [hcubic]
  change (∫ x, ((psi a + deriv psi a * (s * x)) +
      iteratedDeriv 2 psi a * (s * x) ^ 2 / 2) +
      iteratedDeriv 3 psi a * (s * x) ^ 3 / 6 ∂standardGaussian) = _
  have hi3 :
      (∫ x, ((psi a + deriv psi a * (s * x)) +
          iteratedDeriv 2 psi a * (s * x) ^ 2 / 2) +
          iteratedDeriv 3 psi a * (s * x) ^ 3 / 6 ∂standardGaussian) =
        (∫ x, (psi a + deriv psi a * (s * x)) +
          iteratedDeriv 2 psi a * (s * x) ^ 2 / 2 ∂standardGaussian) +
        ∫ x, iteratedDeriv 3 psi a * (s * x) ^ 3 / 6 ∂standardGaussian := by
    simpa only [Pi.add_apply] using (integral_add ((h0.add h1).add h2) h3)
  have hi2 :
      (∫ x, (psi a + deriv psi a * (s * x)) +
          iteratedDeriv 2 psi a * (s * x) ^ 2 / 2 ∂standardGaussian) =
        (∫ x, psi a + deriv psi a * (s * x) ∂standardGaussian) +
        ∫ x, iteratedDeriv 2 psi a * (s * x) ^ 2 / 2 ∂standardGaussian := by
    simpa only [Pi.add_apply] using (integral_add (h0.add h1) h2)
  have hi1 :
      (∫ x, psi a + deriv psi a * (s * x) ∂standardGaussian) =
        (∫ _x, psi a ∂standardGaussian) +
        ∫ x, deriv psi a * (s * x) ∂standardGaussian := by
    simpa only [Pi.add_apply] using (integral_add h0 h1)
  rw [hi3, hi2, hi1]
  simp_rw [show ∀ x : ℝ, deriv psi a * (s * x) =
      (deriv psi a * s) * x ^ 1 by intro; ring]
  simp_rw [show ∀ x : ℝ, iteratedDeriv 2 psi a * (s * x) ^ 2 / 2 =
      (iteratedDeriv 2 psi a * s ^ 2 / 2) * x ^ 2 by intro; ring]
  simp_rw [show ∀ x : ℝ, iteratedDeriv 3 psi a * (s * x) ^ 3 / 6 =
      (iteratedDeriv 3 psi a * s ^ 3 / 6) * x ^ 3 by intro; ring]
  rw [integral_const, integral_const_mul, integral_const_mul, integral_const_mul]
  simp

lemma integral_cubicTaylor_rademacher (psi : ℝ → ℝ) (a s : ℝ) :
    ∫ x, cubicTaylor psi a (s * x) ∂rademacherMeasure =
      psi a + iteratedDeriv 2 psi a * s ^ 2 / 2 := by
  rw [integral_rademacher _ (by unfold cubicTaylor; fun_prop)]
  simp [cubicTaylor]
  ring

lemma IsBoundedC4Test.integrable_affine {psi : ℝ → ℝ} {M : ℝ}
    (hpsi : IsBoundedC4Test psi M) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (a s : ℝ) : Integrable (fun x ↦ psi (a + s * x)) mu := by
  obtain ⟨B, hB⟩ := hpsi.bounded
  refine Integrable.mono' (integrable_const B) ?_ ?_
  · exact hpsi.contDiff.continuous.aestronglyMeasurable.comp_measurable (by fun_prop)
  · exact Filter.Eventually.of_forall fun x ↦ hB _

lemma remainder_integral_rademacher_bound {psi : ℝ → ℝ} {M : ℝ}
    (hpsi : IsBoundedC4Test psi M) (a s : ℝ) :
    |∫ x, psi (a + s * x) - cubicTaylor psi a (s * x) ∂rademacherMeasure| ≤
      M * |s| ^ 4 / 24 := by
  let R : ℝ → ℝ := fun x ↦ psi (a + s * x) - cubicTaylor psi a (s * x)
  have hR : Integrable R rademacherMeasure :=
    (hpsi.integrable_affine rademacherMeasure a s).sub
      (integrable_cubicTaylor_rademacher psi a s)
  have hdom : Integrable (fun x : ℝ ↦ (M * |s| ^ 4 / 24) * x ^ 4)
      rademacherMeasure := (integrable_pow_rademacher 4).const_mul _
  calc
    |∫ x, R x ∂rademacherMeasure| ≤ ∫ x, |R x| ∂rademacherMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (M * |s| ^ 4 / 24) * x ^ 4 ∂rademacherMeasure := by
      apply integral_mono hR.abs hdom
      intro x
      calc
        |R x| ≤ M * |s * x| ^ 4 / 24 := taylor_remainder_four' hpsi a (s * x)
        _ = (M * |s| ^ 4 / 24) * x ^ 4 := by
          rw [abs_mul, mul_pow]
          have hx : |x| ^ 4 = x ^ 4 := by
            rw [← abs_pow, abs_of_nonneg] <;> positivity
          rw [hx]
          ring
    _ = M * |s| ^ 4 / 24 := by
      rw [integral_const_mul, integral_fourth_rademacher]
      ring

lemma remainder_integral_standardGaussian_bound {psi : ℝ → ℝ} {M : ℝ}
    (hpsi : IsBoundedC4Test psi M) (a s : ℝ) :
    |∫ x, psi (a + s * x) - cubicTaylor psi a (s * x) ∂standardGaussian| ≤
      M * |s| ^ 4 / 8 := by
  let R : ℝ → ℝ := fun x ↦ psi (a + s * x) - cubicTaylor psi a (s * x)
  have hR : Integrable R standardGaussian :=
    (hpsi.integrable_affine standardGaussian a s).sub
      (integrable_cubicTaylor_standardGaussian psi a s)
  have hdom : Integrable (fun x : ℝ ↦ (M * |s| ^ 4 / 24) * x ^ 4)
      standardGaussian := (integrable_pow_standardGaussian 4).const_mul _
  calc
    |∫ x, R x ∂standardGaussian| ≤ ∫ x, |R x| ∂standardGaussian :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (M * |s| ^ 4 / 24) * x ^ 4 ∂standardGaussian := by
      apply integral_mono hR.abs hdom
      intro x
      calc
        |R x| ≤ M * |s * x| ^ 4 / 24 := taylor_remainder_four' hpsi a (s * x)
        _ = (M * |s| ^ 4 / 24) * x ^ 4 := by
          rw [abs_mul, mul_pow]
          have hx : |x| ^ 4 = x ^ 4 := by
            rw [← abs_pow, abs_of_nonneg] <;> positivity
          rw [hx]
          ring
    _ = M * |s| ^ 4 / 8 := by
      rw [integral_const_mul, standardGaussian_moment_four]
      ring

/-- One-coordinate Lindeberg replacement.  The two laws agree through degree
three; their fourth moments are one and three. -/
theorem affine_rademacher_gaussian_replacement {psi : ℝ → ℝ} {M : ℝ}
    (hpsi : IsBoundedC4Test psi M) (a s : ℝ) :
    |(∫ x, psi (a + s * x) ∂rademacherMeasure) -
        ∫ x, psi (a + s * x) ∂standardGaussian| ≤ M * |s| ^ 4 / 6 := by
  let R : ℝ → ℝ := fun x ↦ psi (a + s * x) - cubicTaylor psi a (s * x)
  have hrad :
      (∫ x, psi (a + s * x) ∂rademacherMeasure) =
        (∫ x, R x ∂rademacherMeasure) +
          ∫ x, cubicTaylor psi a (s * x) ∂rademacherMeasure := by
    calc
      (∫ x, psi (a + s * x) ∂rademacherMeasure) =
          ∫ x, R x + cubicTaylor psi a (s * x) ∂rademacherMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by simp [R]
      _ = _ := integral_add
        ((hpsi.integrable_affine rademacherMeasure a s).sub
          (integrable_cubicTaylor_rademacher psi a s))
        (integrable_cubicTaylor_rademacher psi a s)
  have hgauss :
      (∫ x, psi (a + s * x) ∂standardGaussian) =
        (∫ x, R x ∂standardGaussian) +
          ∫ x, cubicTaylor psi a (s * x) ∂standardGaussian := by
    calc
      (∫ x, psi (a + s * x) ∂standardGaussian) =
          ∫ x, R x + cubicTaylor psi a (s * x) ∂standardGaussian := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by simp [R]
      _ = _ := integral_add
        ((hpsi.integrable_affine standardGaussian a s).sub
          (integrable_cubicTaylor_standardGaussian psi a s))
        (integrable_cubicTaylor_standardGaussian psi a s)
  rw [hrad, hgauss, integral_cubicTaylor_rademacher,
    integral_cubicTaylor_standardGaussian]
  rw [add_sub_add_right_eq_sub]
  calc
    |(∫ x, R x ∂rademacherMeasure) - ∫ x, R x ∂standardGaussian| ≤
        |∫ x, R x ∂rademacherMeasure| +
          |∫ x, R x ∂standardGaussian| := abs_sub _ _
    _ ≤ M * |s| ^ 4 / 24 + M * |s| ^ 4 / 8 :=
      add_le_add (remainder_integral_rademacher_bound hpsi a s)
        (remainder_integral_standardGaussian_bound hpsi a s)
    _ = M * |s| ^ 4 / 6 := by ring

/-- Fourth moment of an independent centered increment.  This is the
algebraic induction step behind the degree-one `2→4` estimate. -/
lemma integral_add_pow_four_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX4 : Integrable (fun ω ↦ X ω ^ 4) P)
    (hY4 : Integrable (fun ω ↦ Y ω ^ 4) P) {v w : ℝ}
    (hY1 : ∫ ω, Y ω ∂P = 0) (hY2 : ∫ ω, Y ω ^ 2 ∂P = v)
    (hY3 : ∫ ω, Y ω ^ 3 ∂P = 0) (hY4m : ∫ ω, Y ω ^ 4 ∂P = w) :
    ∫ ω, (X ω + Y ω) ^ 4 ∂P =
      (∫ ω, X ω ^ 4 ∂P) + 6 * v * (∫ ω, X ω ^ 2 ∂P) + w := by
  have h31 : Integrable (fun ω ↦ X ω ^ 3 * Y ω) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.pow 3 |>.mul hY) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      have hp : 0 ≤ (X ω - Y ω) ^ 2 *
          (2 * X ω ^ 2 + (X ω + Y ω) ^ 2) := by positivity
      have hm : 0 ≤ (X ω + Y ω) ^ 2 *
          (2 * X ω ^ 2 + (X ω - Y ω) ^ 2) := by positivity
      exact abs_le.mpr ⟨by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)], by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)]⟩
  have h22 : Integrable (fun ω ↦ X ω ^ 2 * Y ω ^ 2) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.pow 2 |>.mul (hY.pow 2)) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      exact abs_le.mpr ⟨by
        nlinarith [sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2),
          sq_nonneg (X ω * Y ω)], by
        nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2)]⟩
  have h13 : Integrable (fun ω ↦ X ω * Y ω ^ 3) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.mul (hY.pow 3)) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      have hp : 0 ≤ (Y ω - X ω) ^ 2 *
          (2 * Y ω ^ 2 + (Y ω + X ω) ^ 2) := by positivity
      have hm : 0 ≤ (Y ω + X ω) ^ 2 *
          (2 * Y ω ^ 2 + (Y ω - X ω) ^ 2) := by positivity
      exact abs_le.mpr ⟨by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)], by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)]⟩
  have hexpand :
      ∫ ω, (X ω + Y ω) ^ 4 ∂P =
        (∫ ω, X ω ^ 4 ∂P) + 4 * (∫ ω, X ω ^ 3 * Y ω ∂P) +
          6 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) +
          4 * (∫ ω, X ω * Y ω ^ 3 ∂P) + ∫ ω, Y ω ^ 4 ∂P := by
    have hi1 : (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂P) =
        (∫ ω, X ω ^ 4 ∂P) + ∫ ω, 4 * (X ω ^ 3 * Y ω) ∂P := by
      simpa only [Pi.add_apply] using integral_add hX4 (h31.const_mul 4)
    have hi2 :
        (∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2) ∂P) =
        (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂P) +
          ∫ ω, 6 * (X ω ^ 2 * Y ω ^ 2) ∂P := by
      simpa only [Pi.add_apply] using
        integral_add (hX4.add (h31.const_mul 4)) (h22.const_mul 6)
    have hi3 :
        (∫ ω, ((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3) ∂P) =
        (∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2) ∂P) +
          ∫ ω, 4 * (X ω * Y ω ^ 3) ∂P := by
      simpa only [Pi.add_apply] using
        integral_add ((hX4.add (h31.const_mul 4)).add (h22.const_mul 6))
          (h13.const_mul 4)
    have hi4 :
        (∫ ω, (((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3)) + Y ω ^ 4 ∂P) =
        (∫ ω, ((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3) ∂P) +
          ∫ ω, Y ω ^ 4 ∂P := by
      simpa only [Pi.add_apply] using
        integral_add (((hX4.add (h31.const_mul 4)).add (h22.const_mul 6)).add
          (h13.const_mul 4)) hY4
    calc
      (∫ ω, (X ω + Y ω) ^ 4 ∂P) =
          ∫ ω, (((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
            6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3)) +
            Y ω ^ 4 ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦ by ring
      _ = _ := by
        rw [hi4, hi3, hi2, hi1, integral_const_mul, integral_const_mul,
          integral_const_mul]
  rw [hexpand]
  have h31z := Erdos1028.expectation_pow_three_mul_eq_zero hXY hX hY hY1
  have h13z : ∫ ω, X ω * Y ω ^ 3 ∂P = 0 := by
    have hind : IndepFun X (fun ω ↦ Y ω ^ 3) P :=
      hXY.comp measurable_id (measurable_id.pow_const 3)
    have hfac := hind.integral_mul_eq_mul_integral hX (hY.pow 3)
    have hfac' : (∫ ω, X ω * Y ω ^ 3 ∂P) =
        (∫ ω, X ω ∂P) * ∫ ω, Y ω ^ 3 ∂P := by
      simpa only [Pi.mul_apply] using hfac
    rw [hfac', hY3, mul_zero]
  have h22f := Erdos1028.expectation_sq_mul_sq_eq_mul_expectation_sq hXY hX hY
  rw [h31z, h13z, h22f, hY2, hY4m]
  ring

/-- Exact second moment after adjoining an independent centered increment. -/
lemma integral_add_sq_centered
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X Y : Omega → ℝ} (hXY : IndepFun X Y P)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX4 : Integrable (fun w ↦ X w ^ 4) P)
    (hY4 : Integrable (fun w ↦ Y w ^ 4) P) {v : ℝ}
    (hY1 : ∫ w, Y w ∂P = 0) (hY2 : ∫ w, Y w ^ 2 ∂P = v) :
    ∫ w, (X w + Y w) ^ 2 ∂P = (∫ w, X w ^ 2 ∂P) + v := by
  have hX2 := Erdos1028.integrable_pow_of_integrable_pow_four hX hX4 2 (by norm_num)
  have hY2i := Erdos1028.integrable_pow_of_integrable_pow_four hY hY4 2 (by norm_num)
  have hXYi : Integrable (fun w ↦ X w * Y w) P := by
    refine Integrable.mono' (hX2.add hY2i) (hX.mul hY) ?_
    exact Filter.Eventually.of_forall fun w ↦ by
      simp only [Pi.add_apply]
      have h := two_mul_le_add_sq |X w| |Y w|
      have hx : |X w| ^ 2 = X w ^ 2 := sq_abs _
      have hy : |Y w| ^ 2 = Y w ^ 2 := sq_abs _
      rw [hx, hy] at h
      calc
        ‖X w * Y w‖ = |X w| * |Y w| := by
          rw [Real.norm_eq_abs, abs_mul]
        _ ≤ X w ^ 2 + Y w ^ 2 := by
          nlinarith [h, abs_nonneg (X w), abs_nonneg (Y w)]
  have hfac0 := hXY.integral_mul_eq_mul_integral hX hY
  have hfac : (∫ w, X w * Y w ∂P) = (∫ w, X w ∂P) * ∫ w, Y w ∂P := by
    simpa only [Pi.mul_apply] using hfac0
  have hi1 : (∫ w, X w ^ 2 + 2 * (X w * Y w) ∂P) =
      (∫ w, X w ^ 2 ∂P) + ∫ w, 2 * (X w * Y w) ∂P := by
    simpa only [Pi.add_apply] using integral_add hX2 (hXYi.const_mul 2)
  have hi2 : (∫ w, (X w ^ 2 + 2 * (X w * Y w)) + Y w ^ 2 ∂P) =
      (∫ w, X w ^ 2 + 2 * (X w * Y w) ∂P) + ∫ w, Y w ^ 2 ∂P := by
    simpa only [Pi.add_apply] using integral_add (hX2.add (hXYi.const_mul 2)) hY2i
  calc
    (∫ w, (X w + Y w) ^ 2 ∂P) =
        ∫ w, (X w ^ 2 + 2 * (X w * Y w)) + Y w ^ 2 ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by ring
    _ = _ := by
      rw [hi2, hi1, integral_const_mul, hfac, hY1, mul_zero, mul_zero, hY2]
      ring

/-- First four moment assumptions used for one coordinate in a mixed
Rademacher/Gaussian linear form. -/
structure HasReplacementMoments
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega → ℝ) (variance : ℝ) : Prop where
  measurable : Measurable X
  integrable_fourth : Integrable (fun w ↦ X w ^ 4) P
  first : ∫ w, X w ∂P = 0
  second : ∫ w, X w ^ 2 ∂P = variance
  third : ∫ w, X w ^ 3 ∂P = 0
  fourth_le : ∫ w, X w ^ 4 ∂P ≤ 3 * variance ^ 2

lemma integrable_add_pow_four
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {X Y : Omega → ℝ}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX4 : Integrable (fun w ↦ X w ^ 4) P)
    (hY4 : Integrable (fun w ↦ Y w ^ 4) P) :
    Integrable (fun w ↦ (X w + Y w) ^ 4) P := by
  refine Integrable.mono' ((hX4.add hY4).const_mul 8) ((hX.add hY).pow 4) ?_
  exact Filter.Eventually.of_forall fun w ↦ by
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have hab : |X w + Y w| ≤ |X w| + |Y w| := abs_add_le _ _
    have hpow : |X w + Y w| ^ 4 ≤ (|X w| + |Y w|) ^ 4 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hab 4
    have hpoly : (|X w| + |Y w|) ^ 4 ≤
        8 * (|X w| ^ 4 + |Y w| ^ 4) := by
      have hp : 0 ≤ (|X w| - |Y w|) ^ 2 *
          ((|X w| - |Y w|) ^ 2 + 6 * (|X w| + |Y w|) ^ 2) := by positivity
      nlinarith
    have hXabs : |X w| ^ 4 = X w ^ 4 := by
      rw [← abs_pow, abs_of_nonneg] <;> positivity
    have hYabs : |Y w| ^ 4 = Y w ^ 4 := by
      rw [← abs_pow, abs_of_nonneg] <;> positivity
    rw [abs_pow]
    calc
      |X w + Y w| ^ 4 ≤ 8 * (|X w| ^ 4 + |Y w| ^ 4) := hpow.trans hpoly
      _ = 8 * (X w ^ 4 + Y w ^ 4) := by rw [hXabs, hYabs]

lemma HasReplacementMoments.const_mul
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {X : Omega → ℝ}
    {v : ℝ} (hX : HasReplacementMoments P X v) (a : ℝ) :
    HasReplacementMoments P (fun w ↦ a * X w) (a ^ 2 * v) where
  measurable := hX.measurable.const_mul _
  integrable_fourth := by
    convert hX.integrable_fourth.const_mul (a ^ 4) using 1 <;> funext w <;> ring
  first := by rw [integral_const_mul, hX.first, mul_zero]
  second := by
    simp_rw [show ∀ w, (a * X w) ^ 2 = a ^ 2 * X w ^ 2 by intro; ring]
    rw [integral_const_mul, hX.second]
  third := by
    simp_rw [show ∀ w, (a * X w) ^ 3 = a ^ 3 * X w ^ 3 by intro; ring]
    rw [integral_const_mul, hX.third, mul_zero]
  fourth_le := by
    simp_rw [show ∀ w, (a * X w) ^ 4 = a ^ 4 * X w ^ 4 by intro; ring]
    rw [integral_const_mul]
    calc
      a ^ 4 * (∫ w, X w ^ 4 ∂P) ≤ a ^ 4 * (3 * v ^ 2) :=
        mul_le_mul_of_nonneg_left hX.fourth_le (by positivity)
      _ = 3 * (a ^ 2 * v) ^ 2 := by ring

lemma rademacher_hasReplacementMoments :
    HasReplacementMoments rademacherMeasure id 1 where
  measurable := measurable_id
  integrable_fourth := integrable_pow_rademacher 4
  first := integral_id_rademacher
  second := integral_sq_rademacher
  third := integral_cube_rademacher
  fourth_le := by
    have h : ∫ x : ℝ, id x ^ 4 ∂rademacherMeasure = 1 := by
      simpa only [id_eq] using integral_fourth_rademacher
    rw [h]
    norm_num

lemma standardGaussian_hasReplacementMoments :
    HasReplacementMoments standardGaussian id 1 where
  measurable := measurable_id
  integrable_fourth := integrable_pow_standardGaussian 4
  first := by simpa using standardGaussian_moment_one
  second := by simpa only [id_eq] using standardGaussian_moment_two
  third := by simpa only [id_eq] using standardGaussian_moment_three
  fourth_le := by
    have h : ∫ x : ℝ, id x ^ 4 ∂standardGaussian = 3 := by
      simpa only [id_eq] using standardGaussian_moment_four
    rw [h]
    norm_num

/-- Sharp `2 -> 4` estimate for an affine linear form in independent
coordinates whose first four moments are Gaussian-dominated. -/
theorem affineLinear_fourthMoment_le
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I] [DecidableEq I]
    {P : Measure Omega} [IsProbabilityMeasure P] (xi : I → Omega → ℝ)
    (hindep : iIndepFun xi P) (hmom : ∀ i, HasReplacementMoments P (xi i) 1)
    (b : ℝ) (a : I → ℝ) (s : Finset I) :
    ∫ w, (b + ∑ i ∈ s, a i * xi i w) ^ 4 ∂P ≤
      3 * (b ^ 2 + ∑ i ∈ s, a i ^ 2) ^ 2 := by
  have hall : ∀ u : Finset I,
      Integrable (fun w ↦ (b + ∑ i ∈ u, a i * xi i w) ^ 4) P ∧
      (∫ w, (b + ∑ i ∈ u, a i * xi i w) ^ 2 ∂P) =
        b ^ 2 + ∑ i ∈ u, a i ^ 2 ∧
      (∫ w, (b + ∑ i ∈ u, a i * xi i w) ^ 4 ∂P) ≤
        3 * (b ^ 2 + ∑ i ∈ u, a i ^ 2) ^ 2 := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        constructor
        · simpa using (integrable_const (b ^ 4) : Integrable (fun _ : Omega ↦ b ^ 4) P)
        constructor <;> simp
        nlinarith [sq_nonneg (b ^ 2)]
    | @insert i u hi ihu =>
        let X : Omega → ℝ := fun w ↦ b + ∑ j ∈ u, a j * xi j w
        let Y : Omega → ℝ := fun w ↦ a i * xi i w
        have hscaled : iIndepFun (fun j w ↦ a j * xi j w) P := by
          simpa [Function.comp_def] using
            hindep.comp (fun j x ↦ a j * x) (fun _ ↦ by fun_prop)
        have hscaled_meas : ∀ j, Measurable (fun w ↦ a j * xi j w) :=
          fun j ↦ (hmom j).measurable.const_mul _
        have hbase := hscaled.indepFun_finsetSum_of_notMem hscaled_meas hi
        have hXY : IndepFun X Y P := by
          have hc := hbase.comp
            (show Measurable (fun x : ℝ ↦ b + x) by fun_prop)
            (show Measurable (fun x : ℝ ↦ x) by fun_prop)
          simpa only [X, Y, Function.comp_def, Pi.add_apply, Finset.sum_apply] using hc
        have hXm : AEStronglyMeasurable X P := by
          exact (measurable_const.add
            (Finset.measurable_sum u fun j _ ↦ hscaled_meas j)).aestronglyMeasurable
        have hYm : AEStronglyMeasurable Y P :=
          ((hmom i).measurable.const_mul _).aestronglyMeasurable
        have hYi : HasReplacementMoments P Y (a i ^ 2) := by
          simpa [Y] using (hmom i).const_mul (a i)
        rcases ihu with ⟨hX4, hX2, hX4le⟩
        have hXY4 : Integrable (fun w ↦ (X w + Y w) ^ 4) P :=
          integrable_add_pow_four hXm hYm hX4 hYi.integrable_fourth
        have hsecond : ∫ w, (X w + Y w) ^ 2 ∂P =
            (b ^ 2 + ∑ j ∈ u, a j ^ 2) + a i ^ 2 := by
          rw [integral_add_sq_centered hXY hXm hYm hX4 hYi.integrable_fourth
            hYi.first hYi.second, hX2]
        have hfourth_eq : ∫ w, (X w + Y w) ^ 4 ∂P =
            (∫ w, X w ^ 4 ∂P) +
              6 * a i ^ 2 * (∫ w, X w ^ 2 ∂P) + ∫ w, Y w ^ 4 ∂P := by
          exact integral_add_pow_four_centered hXY hXm hYm hX4 hYi.integrable_fourth
            hYi.first hYi.second hYi.third rfl
        have hfourth : ∫ w, (X w + Y w) ^ 4 ∂P ≤
            3 * ((b ^ 2 + ∑ j ∈ u, a j ^ 2) + a i ^ 2) ^ 2 := by
          rw [hfourth_eq, hX2]
          calc
            (∫ w, X w ^ 4 ∂P) + 6 * a i ^ 2 *
                (b ^ 2 + ∑ j ∈ u, a j ^ 2) + ∫ w, Y w ^ 4 ∂P ≤
              3 * (b ^ 2 + ∑ j ∈ u, a j ^ 2) ^ 2 +
                6 * a i ^ 2 * (b ^ 2 + ∑ j ∈ u, a j ^ 2) +
                3 * (a i ^ 2) ^ 2 := by
              gcongr
              · exact hYi.fourth_le
            _ = 3 * ((b ^ 2 + ∑ j ∈ u, a j ^ 2) + a i ^ 2) ^ 2 := by ring
        constructor
        · simpa [X, Y, Finset.sum_insert hi, add_assoc, add_left_comm, add_comm] using hXY4
        constructor
        · simpa [X, Y, Finset.sum_insert hi, add_assoc, add_left_comm, add_comm] using hsecond
        · simpa [X, Y, Finset.sum_insert hi, add_assoc, add_left_comm, add_comm] using hfourth
  exact (hall s).2.2

/-- Every coordinate law in the hybrid chain has centered variance one and
fourth moment at most the Gaussian fourth moment. -/
lemma hybridCoordinate_hasReplacementMoments {n t : ℕ} (i : Fin n) :
    HasReplacementMoments (hybridCoordinateMeasure t i) id 1 := by
  by_cases hit : (i : ℕ) < t
  · simpa [hybridCoordinateMeasure, hit] using standardGaussian_hasReplacementMoments
  · simpa [hybridCoordinateMeasure, hit] using rademacher_hasReplacementMoments

/-- Coordinate projections under a hybrid product law satisfy the common
replacement moment assumptions. -/
lemma hybridEval_hasReplacementMoments {n t : ℕ} (i : Fin n) :
    HasReplacementMoments (hybridMeasure n t) (fun x : Fin n → ℝ ↦ x i) 1 := by
  let hi := hybridCoordinate_hasReplacementMoments (t := t) i
  refine ⟨measurable_pi_apply i, ?_, ?_, ?_, ?_, ?_⟩
  · have h := integrable_comp_eval (μ := hybridCoordinateMeasure t) (i := i)
      hi.integrable_fourth
    simpa only [hybridMeasure, id_eq] using h
  · have h := integral_comp_eval (μ := hybridCoordinateMeasure t) (i := i)
      (show AEStronglyMeasurable (fun y : ℝ ↦ y) (hybridCoordinateMeasure t i) by
        fun_prop)
    simpa only [hybridMeasure] using h.trans hi.first
  · have h := integral_comp_eval (μ := hybridCoordinateMeasure t) (i := i)
      (show AEStronglyMeasurable (fun y : ℝ ↦ y ^ 2) (hybridCoordinateMeasure t i) by
        fun_prop)
    simpa only [hybridMeasure] using h.trans hi.second
  · have h := integral_comp_eval (μ := hybridCoordinateMeasure t) (i := i)
      (show AEStronglyMeasurable (fun y : ℝ ↦ y ^ 3) (hybridCoordinateMeasure t i) by
        fun_prop)
    simpa only [hybridMeasure] using h.trans hi.third
  · have h := integral_comp_eval (μ := hybridCoordinateMeasure t) (i := i)
      (show AEStronglyMeasurable (fun y : ℝ ↦ y ^ 4) (hybridCoordinateMeasure t i) by
        fun_prop)
    calc
      (∫ x, x i ^ 4 ∂hybridMeasure n t) =
          ∫ y, y ^ 4 ∂hybridCoordinateMeasure t i := by
            simpa only [hybridMeasure] using h
      _ ≤ 3 * (1 : ℝ) ^ 2 := hi.fourth_le

/-- The coordinate projections of a hybrid product law are independent. -/
lemma hybridEval_iIndepFun (n t : ℕ) :
    iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) (hybridMeasure n t) := by
  change iIndepFun (fun i (x : Fin n → ℝ) ↦ x i)
    (Measure.pi (hybridCoordinateMeasure t))
  simpa only [id_eq] using
    (iIndepFun_pi (μ := hybridCoordinateMeasure t)
      (X := fun _ : Fin n ↦ id) (fun _ ↦ aemeasurable_id))

/-- Fourth powers of affine linear forms are integrable under the same
coordinate hypotheses used by `affineLinear_fourthMoment_le`. -/
theorem affineLinear_fourthMoment_integrable
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I] [DecidableEq I]
    {P : Measure Omega} [IsFiniteMeasure P] (xi : I → Omega → ℝ)
    (hmom : ∀ i, HasReplacementMoments P (xi i) 1)
    (b : ℝ) (a : I → ℝ) (s : Finset I) :
    Integrable (fun w ↦ (b + ∑ i ∈ s, a i * xi i w) ^ 4) P := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (integrable_const (b ^ 4) : Integrable (fun _ : Omega ↦ b ^ 4) P)
  | @insert i s his ih =>
      let X : Omega → ℝ := fun w ↦ b + ∑ j ∈ s, a j * xi j w
      let Y : Omega → ℝ := fun w ↦ a i * xi i w
      have hXm : AEStronglyMeasurable X P := by
        exact (measurable_const.add (Finset.measurable_sum s fun j _ ↦
          measurable_const.mul (hmom j).measurable)).aestronglyMeasurable
      have hYm : AEStronglyMeasurable Y P :=
        (measurable_const.mul (hmom i).measurable).aestronglyMeasurable
      have hY4 : Integrable (fun w ↦ Y w ^ 4) P := by
        simpa [Y] using ((hmom i).const_mul (a i)).integrable_fourth
      have hXY4 := integrable_add_pow_four hXm hYm ih hY4
      simpa [X, Y, Finset.sum_insert his, add_assoc, add_left_comm, add_comm] using hXY4

/-- Hybrid-product affine linear forms satisfy the sharp Gaussian-dominated
fourth-moment estimate. -/
lemma hybrid_affineLinear_fourthMoment_le {n t : ℕ} (b : ℝ) (a : Fin n → ℝ) :
    ∫ x, (b + ∑ i, a i * x i) ^ 4 ∂hybridMeasure n t ≤
      3 * (b ^ 2 + ∑ i, a i ^ 2) ^ 2 := by
  simpa using affineLinear_fourthMoment_le
    (xi := fun i (x : Fin n → ℝ) ↦ x i) (hybridEval_iIndepFun n t)
    (fun i ↦ hybridEval_hasReplacementMoments i) b a Finset.univ

lemma hybrid_affineLinear_fourthMoment_integrable {n t : ℕ}
    (b : ℝ) (a : Fin n → ℝ) :
    Integrable (fun x ↦ (b + ∑ i, a i * x i) ^ 4) (hybridMeasure n t) := by
  simpa using affineLinear_fourthMoment_integrable
    (xi := fun i (x : Fin n → ℝ) ↦ x i)
    (fun i ↦ hybridEval_hasReplacementMoments i) b a Finset.univ

/-- After deleting the coordinate replaced at time `t`, advancing the hybrid
chain by one leaves the law of all remaining coordinates unchanged. -/
lemma hybridMeasure_succAbove_succ {n : ℕ} (t : Fin (n + 1)) :
    (Measure.pi fun j : Fin n ↦ hybridCoordinateMeasure (t.val + 1) (t.succAbove j)) =
      hybridMeasure n t.val := by
  simp only [hybridMeasure]
  congr 1
  funext j
  by_cases hj : j.castSucc < t
  · have hjval : j.val < t.val := hj
    have hnot : ¬t.val < j.val := fun h ↦ (Nat.lt_asymm hjval h)
    simp [hybridCoordinateMeasure, Fin.succAbove_of_castSucc_lt t j hj, hjval, hnot]
  · have htj : t ≤ j.castSucc := le_of_not_gt hj
    simp [hybridCoordinateMeasure, Fin.succAbove_of_le_castSucc t j htj,
      Nat.succ_lt_succ_iff]

/-- Splitting the coordinate at the current replacement time exhibits a
Rademacher factor and the common law of the remaining coordinates. -/
lemma hybridMeasure_split_rademacher {n : ℕ} (t : Fin (n + 1)) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t)
      (hybridMeasure (n + 1) t.val)
      (rademacherMeasure.prod (hybridMeasure n t.val)) := by
  have h := measurePreserving_piFinSuccAbove (hybridCoordinateMeasure t.val) t
  have ht : hybridCoordinateMeasure t.val t = rademacherMeasure := by
    simp [hybridCoordinateMeasure]
  rw [ht, hybridMeasure_succAbove t] at h
  exact h

/-- One step later, the split coordinate is Gaussian while the law of all
remaining coordinates is unchanged. -/
lemma hybridMeasure_split_gaussian {n : ℕ} (t : Fin (n + 1)) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t)
      (hybridMeasure (n + 1) (t.val + 1))
      (standardGaussian.prod (hybridMeasure n t.val)) := by
  have h := measurePreserving_piFinSuccAbove (hybridCoordinateMeasure (t.val + 1)) t
  have ht : hybridCoordinateMeasure (t.val + 1) t = standardGaussian := by
    simp [hybridCoordinateMeasure]
  rw [ht, hybridMeasure_succAbove_succ t] at h
  exact h

lemma IsBoundedC4Test.integrable_measurable_comp
    {psi : ℝ → ℝ} {M : ℝ} (hpsi : IsBoundedC4Test psi M)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (f : Omega → ℝ) (hf : Measurable f) : Integrable (fun w ↦ psi (f w)) P := by
  obtain ⟨B, hB⟩ := hpsi.bounded
  refine Integrable.mono' (integrable_const B) ?_ ?_
  · exact hpsi.contDiff.continuous.measurable.comp hf |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w ↦ hB _

/-- A single Lindeberg step for a multilinear quadratic polynomial.  The
coordinate at time `t` is changed from Rademacher to Gaussian, while all
other hybrid coordinates retain the same law. -/
theorem hybrid_step_quadratic {n : ℕ} (q : QuadraticCoeffs (n + 1))
    (t : Fin (n + 1)) {psi : ℝ → ℝ} {M : ℝ} (hpsi : IsBoundedC4Test psi M) :
    |(∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) t.val) -
        ∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) (t.val + 1)| ≤
      (M / 2) * q.influence t ^ 2 := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t
  let g : ℝ × (Fin n → ℝ) → ℝ := fun p ↦
    psi (q.coordinateBase t p.2 + q.coordinateSlope t p.2 * p.1)
  let Fr : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, psi (q.coordinateBase t y + q.coordinateSlope t y * z) ∂rademacherMeasure
  let Fg : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, psi (q.coordinateBase t y + q.coordinateSlope t y * z) ∂standardGaussian
  have hcomp : (fun x ↦ psi (q.eval x)) = g ∘ split := by
    funext x
    apply congrArg psi
    calc
      q.eval x = q.eval (split.symm (split x)) := by rw [split.symm_apply_apply]
      _ = q.coordinateBase t (split x).2 +
          q.coordinateSlope t (split x).2 * (split x).1 := by
        exact q.eval_piFinSuccAbove t (split x).1 (split x).2
  have hfullRad : Integrable (fun x ↦ psi (q.eval x))
      (hybridMeasure (n + 1) t.val) :=
    hpsi.integrable_measurable_comp _ q.eval q.measurable_eval
  have hfullGauss : Integrable (fun x ↦ psi (q.eval x))
      (hybridMeasure (n + 1) (t.val + 1)) :=
    hpsi.integrable_measurable_comp _ q.eval q.measurable_eval
  have hpairRad : Integrable g
      (rademacherMeasure.prod (hybridMeasure n t.val)) := by
    apply ((hybridMeasure_split_rademacher t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullRad
  have hpairGauss : Integrable g
      (standardGaussian.prod (hybridMeasure n t.val)) := by
    apply ((hybridMeasure_split_gaussian t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullGauss
  have hrad : (∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) t.val) =
      ∫ y, Fr y ∂hybridMeasure n t.val := by
    calc
      (∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) t.val) =
          ∫ x, g (split x) ∂hybridMeasure (n + 1) t.val := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂rademacherMeasure.prod (hybridMeasure n t.val) :=
        (hybridMeasure_split_rademacher t).integral_comp' g
      _ = ∫ y, Fr y ∂hybridMeasure n t.val := by
        simpa [g, Fr] using integral_prod_symm g hpairRad
  have hgauss : (∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) (t.val + 1)) =
      ∫ y, Fg y ∂hybridMeasure n t.val := by
    calc
      (∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) (t.val + 1)) =
          ∫ x, g (split x) ∂hybridMeasure (n + 1) (t.val + 1) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂standardGaussian.prod (hybridMeasure n t.val) :=
        (hybridMeasure_split_gaussian t).integral_comp' g
      _ = ∫ y, Fg y ∂hybridMeasure n t.val := by
        simpa [g, Fg] using integral_prod_symm g hpairGauss
  have hFr : Integrable Fr (hybridMeasure n t.val) := by
    simpa [g, Fr] using hpairRad.integral_prod_right
  have hFg : Integrable Fg (hybridMeasure n t.val) := by
    simpa [g, Fg] using hpairGauss.integral_prod_right
  have hslope4 : Integrable (fun y ↦ q.coordinateSlope t y ^ 4)
      (hybridMeasure n t.val) := by
    simpa [QuadraticCoeffs.coordinateSlope] using
      hybrid_affineLinear_fourthMoment_integrable (t := t.val) (q.linear t)
        (fun j ↦ q.symPair t (t.succAbove j))
  have hdom : Integrable (fun y ↦ M * |q.coordinateSlope t y| ^ 4 / 6)
      (hybridMeasure n t.val) := by
    have habs : Integrable (fun y ↦ |q.coordinateSlope t y| ^ 4)
        (hybridMeasure n t.val) := by
      convert hslope4 using 1
      funext y
      rw [← abs_pow, abs_of_nonneg] <;> positivity
    convert habs.const_mul (M / 6) using 1
    funext y
    ring
  have hslope_le : (∫ y, q.coordinateSlope t y ^ 4 ∂hybridMeasure n t.val) ≤
      3 * q.influence t ^ 2 := by
    rw [q.influence_eq_coordinateSlopeNorm t]
    simpa [QuadraticCoeffs.coordinateSlope] using
      hybrid_affineLinear_fourthMoment_le (t := t.val) (q.linear t)
        (fun j ↦ q.symPair t (t.succAbove j))
  rw [hrad, hgauss, ← integral_sub hFr hFg]
  calc
    |∫ y, Fr y - Fg y ∂hybridMeasure n t.val| ≤
        ∫ y, |Fr y - Fg y| ∂hybridMeasure n t.val :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, M * |q.coordinateSlope t y| ^ 4 / 6 ∂hybridMeasure n t.val := by
      apply integral_mono (hFr.sub hFg).abs hdom
      intro y
      exact affine_rademacher_gaussian_replacement hpsi
        (q.coordinateBase t y) (q.coordinateSlope t y)
    _ = (M / 6) * ∫ y, q.coordinateSlope t y ^ 4 ∂hybridMeasure n t.val := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        have habs : |q.coordinateSlope t y| ^ 4 = q.coordinateSlope t y ^ 4 := by
          rw [← abs_pow, abs_of_nonneg] <;> positivity
        change M * |q.coordinateSlope t y| ^ 4 / 6 =
          (M / 6) * q.coordinateSlope t y ^ 4
        rw [habs]
        ring
    _ ≤ (M / 6) * (3 * q.influence t ^ 2) :=
      mul_le_mul_of_nonneg_left hslope_le
        (div_nonneg hpsi.fourth_nonneg (by norm_num))
    _ = (M / 2) * q.influence t ^ 2 := by ring

/-- The triangle inequality along a finite sequence, in the form needed for
the Lindeberg replacement chain. -/
lemma telescoping_abs (F : ℕ → ℝ) (n : ℕ) :
    |F 0 - F n| ≤ ∑ i : Fin n, |F i.val - F (i.val + 1)| := by
  calc
    |F 0 - F n| = |∑ k ∈ Finset.range n, (F k - F (k + 1))| := by
      rw [Finset.sum_range_sub']
    _ ≤ ∑ k ∈ Finset.range n, |F k - F (k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |F i.val - F (i.val + 1)| := by
      simpa using (Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ ↦ |F k - F (k + 1)|) (n := n)).symm

/-- Degree-two MOO invariance under the product-measure presentations, with
the stronger constant furnished by the direct fourth-order Taylor argument. -/
theorem quadratic_invariance_integral_sharp {n : ℕ} (q : QuadraticCoeffs n)
    {psi : ℝ → ℝ} {M : ℝ} (hpsi : IsBoundedC4Test psi M) :
    |(∫ x, psi (q.eval x) ∂rademacherProductMeasure n) -
        ∫ x, psi (q.eval x) ∂gaussianProductMeasure n| ≤
      (M / 2) * ∑ i, q.influence i ^ 2 := by
  cases n with
  | zero =>
      rw [← hybridMeasure_zero 0,
        ← hybridMeasure_eq_gaussian 0 0 (by norm_num)]
      simp
  | succ n =>
      rw [← hybridMeasure_zero (n + 1),
        ← hybridMeasure_eq_gaussian (n + 1) (n + 1) le_rfl]
      let F : ℕ → ℝ := fun t ↦
        ∫ x, psi (q.eval x) ∂hybridMeasure (n + 1) t
      calc
        |F 0 - F (n + 1)| ≤
            ∑ i : Fin (n + 1), |F i.val - F (i.val + 1)| :=
          telescoping_abs F (n + 1)
        _ ≤ ∑ i : Fin (n + 1), (M / 2) * q.influence i ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          simpa [F] using hybrid_step_quadratic q i hpsi
        _ = (M / 2) * ∑ i : Fin (n + 1), q.influence i ^ 2 := by
          rw [Finset.mul_sum]

/-- The degree-two Mossel--O'Donnell--Oleszkiewicz replacement estimate in
the `27/4` normalization used by Kwan--Sah--Sauermann--Sawhney. -/
theorem quadratic_invariance_integral {n : ℕ} (q : QuadraticCoeffs n)
    {psi : ℝ → ℝ} {M : ℝ} (hpsi : IsBoundedC4Test psi M) :
    |(∫ x, psi (q.eval x) ∂rademacherProductMeasure n) -
        ∫ x, psi (q.eval x) ∂gaussianProductMeasure n| ≤
      (27 / 4 : ℝ) * M * ∑ i, q.influence i ^ 2 := by
  have hsum : 0 ≤ ∑ i, q.influence i ^ 2 := by positivity
  calc
    |(∫ x, psi (q.eval x) ∂rademacherProductMeasure n) -
        ∫ x, psi (q.eval x) ∂gaussianProductMeasure n| ≤
        (M / 2) * ∑ i, q.influence i ^ 2 :=
      quadratic_invariance_integral_sharp q hpsi
    _ ≤ (27 / 4 : ℝ) * M * ∑ i, q.influence i ^ 2 := by
      nlinarith [hpsi.fourth_nonneg]

/-- Finite-uniform Rademacher formulation of the degree-two MOO estimate. -/
theorem quadratic_invariance {n : ℕ} (q : QuadraticCoeffs n)
    {psi : ℝ → ℝ} {M : ℝ} (hpsi : IsBoundedC4Test psi M) :
    |rademacherExpectation (fun x ↦ psi (q.eval x)) -
        gaussianExpectation (fun x ↦ psi (q.eval x))| ≤
      (27 / 4 : ℝ) * M * ∑ i, q.influence i ^ 2 := by
  have hmeas : Measurable (fun x ↦ psi (q.eval x)) :=
    hpsi.contDiff.continuous.measurable.comp q.measurable_eval
  rw [← rademacherIntegralExpectation_eq _ hmeas]
  simpa only [rademacherIntegralExpectation, gaussianExpectation] using
    quadratic_invariance_integral q hpsi

end Invariance
end Erdos88
