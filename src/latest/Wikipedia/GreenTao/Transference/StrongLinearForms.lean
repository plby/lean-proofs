import Wikipedia.GreenTao.LinearForms.Condition
import Wikipedia.GreenTao.LinearForms.Independence
import Wikipedia.SzemeredisTheorem.Transference.GeneralizedConvolution
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev

/-!
# Algebraic strong-linear-forms primitives

This file contains the finite algebra behind the strong linear-forms and
densification arguments:

* centered factors `ν - 1`;
* products over Boolean cubes and corner systems;
* exact Boolean inclusion--exclusion expansions;
* cancellation of the constant terms;
* the resulting centered CFZ-moment estimate from the ordinary
  linear-forms condition;
* an `L²` contraction for coordinate-sum fiber convolutions, and a
  hypothesis-driven centered-moment consequence.

No analytic estimate for a sieve majorant is asserted here. Those estimates
must supply the explicit subproduct or moment hypotheses used below.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The Boolean cube with coordinate set `ι`. -/
abbrev BooleanCube (ι : Type*) :=
  ι → Bool

/-- The centered version of a real-valued function. -/
def centeredFactor {Ω : Type*} (ν : Ω → ℝ) (x : Ω) : ℝ :=
  ν x - 1

@[simp]
theorem centeredFactor_one {Ω : Type*} (x : Ω) :
    centeredFactor (fun _ : Ω => (1 : ℝ)) x = 0 := by
  simp [centeredFactor]

/-- Product of the centered entries of a finite vector. -/
def centeredProduct {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  ∏ i, (a i - 1)

/-- The subproduct selected by a Boolean exponent vector. -/
def cubeSelectedProduct {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then a i else 1

/-- The sign contributed by the unselected entries in a Boolean
inclusion--exclusion expansion. -/
def cubeSign {ι : Type*} [Fintype ι] (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then 1 else -1

/-- A raw term in the expansion of `∏ i, (a i - 1)`. -/
def cubeExpansionTerm {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then a i else -1

@[simp]
theorem cubeSelectedProduct_false {ι : Type*} [Fintype ι]
    (a : ι → ℝ) :
    cubeSelectedProduct a (fun _ => false) = 1 := by
  simp [cubeSelectedProduct]

@[simp]
theorem cubeSelectedProduct_true {ι : Type*} [Fintype ι]
    (a : ι → ℝ) :
    cubeSelectedProduct a (fun _ => true) = ∏ i, a i := by
  simp [cubeSelectedProduct]

@[simp]
theorem abs_cubeSign {ι : Type*} [Fintype ι]
    (e : BooleanCube ι) :
    |cubeSign e| = 1 := by
  rw [cubeSign, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases e i <;> simp

/-- The signs in a nonempty Boolean cube cancel. -/
theorem sum_cubeSign_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∑ e : BooleanCube ι, cubeSign e = 0 := by
  have h := (Fintype.prod_sum
    (fun _ : ι => fun b : Bool => if b then (1 : ℝ) else -1)).symm
  simpa [cubeSign] using h

/-- Split a raw expansion term into its sign and selected subproduct. -/
theorem cubeExpansionTerm_eq_sign_mul_selected
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) :
    cubeExpansionTerm a e =
      cubeSign e * cubeSelectedProduct a e := by
  rw [cubeExpansionTerm, cubeSign, cubeSelectedProduct,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases e i <;> simp

/-- Exact Boolean expansion of a product of centered factors. -/
theorem centeredProduct_eq_sum_cube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    centeredProduct a =
      ∑ e : BooleanCube ι, cubeExpansionTerm a e := by
  rw [centeredProduct]
  calc
    (∏ i, (a i - 1)) =
        ∏ i, ∑ b : Bool, if b then a i else -1 := by
      apply Fintype.prod_congr
      intro i
      simp
      ring
    _ = _ := Fintype.prod_sum _

/-- Inclusion--exclusion form of the centered-product expansion. -/
theorem centeredProduct_eq_sum_sign_mul_selected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    centeredProduct a =
      ∑ e : BooleanCube ι,
        cubeSign e * cubeSelectedProduct a e := by
  rw [centeredProduct_eq_sum_cube]
  apply Fintype.sum_congr
  intro e
  exact cubeExpansionTerm_eq_sign_mul_selected a e

/-- Product over all corners of a Boolean cube. -/
def cornerProduct
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Ω → ℝ) (ψ : BooleanCube ι → Ω) : ℝ :=
  ∏ ω : BooleanCube ι, ν (ψ ω)

/-- Product of centered factors over all corners of a Boolean cube. -/
def centeredCornerProduct
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Ω → ℝ) (ψ : BooleanCube ι → Ω) : ℝ :=
  centeredProduct (fun ω => ν (ψ ω))

/-- A Boolean-selected subproduct of the corners of a cube. -/
def selectedCornerProduct
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Ω → ℝ) (ψ : BooleanCube ι → Ω)
    (e : BooleanCube (BooleanCube ι)) : ℝ :=
  cubeSelectedProduct (fun ω => ν (ψ ω)) e

/-- Exact expansion for a centered product indexed by Boolean corners. -/
theorem centeredCornerProduct_eq_sum
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Ω → ℝ) (ψ : BooleanCube ι → Ω) :
    centeredCornerProduct ν ψ =
      ∑ e : BooleanCube (BooleanCube ι),
        cubeSign e * selectedCornerProduct ν ψ e := by
  exact centeredProduct_eq_sum_sign_mul_selected
    (fun ω => ν (ψ ω))

/-- Normalized averaging commutes with a finite sum. -/
theorem mean_fintype_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (F : ι → Ω → ℝ) :
    mean (fun x => ∑ i, F i x) = ∑ i, mean (F i) := by
  unfold mean
  exact Finset.expect_sum_comm Finset.univ Finset.univ
    (fun x i => F i x)

/-- Average the exact centered-product expansion term by term. -/
theorem mean_centeredProduct_eq_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (a : ι → Ω → ℝ) :
    mean (fun x => centeredProduct (fun i => a i x)) =
      ∑ e : BooleanCube ι,
        cubeSign e *
          mean (fun x =>
            cubeSelectedProduct (fun i => a i x) e) := by
  calc
    mean (fun x => centeredProduct (fun i => a i x)) =
        mean (fun x => ∑ e : BooleanCube ι,
          cubeSign e *
            cubeSelectedProduct (fun i => a i x) e) := by
      apply congrArg mean
      funext x
      exact centeredProduct_eq_sum_sign_mul_selected
        (fun i => a i x)
    _ = ∑ e : BooleanCube ι,
        mean (fun x => cubeSign e *
          cubeSelectedProduct (fun i => a i x) e) :=
      mean_fintype_sum _
    _ = _ := by
      apply Fintype.sum_congr
      intro e
      exact mean_smul (cubeSign e) _

/-- If the coefficients sum to zero, one may center every summand without
changing the weighted sum. -/
theorem sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero
    {κ : Type*} [Fintype κ] (s m : κ → ℝ)
    (hs : ∑ e, s e = 0) :
    (∑ e, s e * m e) =
      ∑ e, s e * (m e - 1) := by
  calc
    (∑ e, s e * m e) =
        ∑ e, (s e * (m e - 1) + s e) := by
      apply Fintype.sum_congr
      intro e
      ring
    _ = (∑ e, s e * (m e - 1)) + ∑ e, s e :=
      Finset.sum_add_distrib
    _ = _ := by rw [hs, add_zero]

/-- Cancellation of all constant terms in the average of a nonempty
centered product. -/
theorem mean_centeredProduct_eq_sum_deviations
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (a : ι → Ω → ℝ) :
    mean (fun x => centeredProduct (fun i => a i x)) =
      ∑ e : BooleanCube ι, cubeSign e *
        (mean (fun x =>
          cubeSelectedProduct (fun i => a i x) e) - 1) := by
  rw [mean_centeredProduct_eq_sum]
  exact sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero _ _
    sum_cubeSign_eq_zero

/-- Every Boolean-selected subproduct has mean within `η` of one. -/
def HasBooleanSubproductCondition
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (a : ι → Ω → ℝ) (η : ℝ) : Prop :=
  ∀ e : BooleanCube ι,
    |mean (fun x =>
      cubeSelectedProduct (fun i => a i x) e) - 1| ≤ η

/-- Inclusion--exclusion bounds a centered product by the number of Boolean
subproducts times the common error. -/
theorem abs_mean_centeredProduct_le_card_mul
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    {a : ι → Ω → ℝ} {η : ℝ}
    (h : HasBooleanSubproductCondition a η) :
    |mean (fun x => centeredProduct (fun i => a i x))| ≤
      (Fintype.card (BooleanCube ι) : ℝ) * η := by
  rw [mean_centeredProduct_eq_sum_deviations]
  calc
    |∑ e : BooleanCube ι, cubeSign e *
        (mean (fun x =>
          cubeSelectedProduct (fun i => a i x) e) - 1)| ≤
        ∑ e : BooleanCube ι, |cubeSign e *
          (mean (fun x =>
            cubeSelectedProduct (fun i => a i x) e) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e : BooleanCube ι, η := by
      apply Finset.sum_le_sum
      intro e _
      simpa [abs_mul] using h e
    _ = (Fintype.card (BooleanCube ι) : ℝ) * η := by
      simp

/-- Cardinality-explicit version of the centered-product bound. -/
theorem abs_mean_centeredProduct_le_two_pow
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    {a : ι → Ω → ℝ} {η : ℝ}
    (h : HasBooleanSubproductCondition a η) :
    |mean (fun x => centeredProduct (fun i => a i x))| ≤
      (2 : ℝ) ^ Fintype.card ι * η := by
  simpa [BooleanCube, Fintype.card_fun, Fintype.card_bool] using
    abs_mean_centeredProduct_le_card_mul h

/-! ## Specialization to the CFZ linear-forms system -/

/-- The CFZ family as a finite family of real-valued functions on doubled
variable vectors. -/
def cfzFactorFamily (k N : ℕ) (ν : ZMod N → ℝ) :
    CFZFormIndex k → CubePoint k N → ℝ :=
  fun q x => ν (apLinearForm k N q.1 q.2 x)

/-- Convert a Boolean selector on the sigma-type of CFZ forms to the
dependent exponent format used by `HasLinearFormsCondition`. -/
def cfzExponentOfCube {k : ℕ}
    (e : BooleanCube (CFZFormIndex k)) : LinearFormsExponent k :=
  fun j ω => e ⟨j, ω⟩

/-- Boolean-selected product of CFZ forms. -/
def cfzSelectedProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (e : BooleanCube (CFZFormIndex k))
    (x : CubePoint k N) : ℝ :=
  cubeSelectedProduct (fun q => cfzFactorFamily k N ν q x) e

/-- Product of all centered CFZ factors. -/
def cfzCenteredProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (x : CubePoint k N) : ℝ :=
  centeredProduct (fun q => cfzFactorFamily k N ν q x)

theorem cfzSelectedProduct_eq_linearFormsProduct
    (k N : ℕ) (ν : ZMod N → ℝ)
    (e : BooleanCube (CFZFormIndex k))
    (x : CubePoint k N) :
    cfzSelectedProduct k N ν e x =
      linearFormsProduct k N ν (cfzExponentOfCube e) x := by
  rw [cfzSelectedProduct, cubeSelectedProduct, linearFormsProduct,
    Fintype.prod_sigma]
  rfl

/-- The existing linear-forms condition is precisely the Boolean
subproduct condition for the nondependent CFZ family. -/
theorem HasLinearFormsCondition.hasBooleanSubproductCondition
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η) :
    HasBooleanSubproductCondition (cfzFactorFamily k N ν) η := by
  intro e
  have he := h (cfzExponentOfCube e)
  have hfun :
      (fun x => cubeSelectedProduct
        (fun q => cfzFactorFamily k N ν q x) e) =
      linearFormsProduct k N ν (cfzExponentOfCube e) := by
    funext x
    exact cfzSelectedProduct_eq_linearFormsProduct k N ν e x
  rw [hfun]
  exact he

/-- Exact inclusion--exclusion expansion of the centered CFZ product. -/
theorem cfzCenteredProduct_eq_sum
    (k N : ℕ) (ν : ZMod N → ℝ) (x : CubePoint k N) :
    cfzCenteredProduct k N ν x =
      ∑ e : BooleanCube (CFZFormIndex k),
        cubeSign e *
          linearFormsProduct k N ν (cfzExponentOfCube e) x := by
  rw [cfzCenteredProduct,
    centeredProduct_eq_sum_sign_mul_selected]
  apply Fintype.sum_congr
  intro e
  have he :
      cubeSelectedProduct
          (fun q => cfzFactorFamily k N ν q x) e =
        linearFormsProduct k N ν (cfzExponentOfCube e) x := by
    change cfzSelectedProduct k N ν e x = _
    exact cfzSelectedProduct_eq_linearFormsProduct k N ν e x
  rw [he]

/-- The centered CFZ moment is a signed sum of deviations of the ordinary
linear-forms moments. -/
theorem mean_cfzCenteredProduct_eq_sum_deviations
    {k N : ℕ} [NeZero N] (hk : 0 < k)
    (ν : ZMod N → ℝ) :
    mean (cfzCenteredProduct k N ν) =
      ∑ e : BooleanCube (CFZFormIndex k), cubeSign e *
        (mean (linearFormsProduct k N ν (cfzExponentOfCube e)) - 1) := by
  let j : Fin k := ⟨0, hk⟩
  let ω : DeletedCube k j := fun _ => false
  let : Nonempty (CFZFormIndex k) := ⟨⟨j, ω⟩⟩
  change mean (fun x =>
    centeredProduct (fun q => cfzFactorFamily k N ν q x)) = _
  rw [mean_centeredProduct_eq_sum_deviations]
  apply Fintype.sum_congr
  intro e
  have he :
      (fun x => cubeSelectedProduct
        (fun q => cfzFactorFamily k N ν q x) e) =
      linearFormsProduct k N ν (cfzExponentOfCube e) := by
    funext x
    change cfzSelectedProduct k N ν e x = _
    exact cfzSelectedProduct_eq_linearFormsProduct k N ν e x
  rw [he]

/-- Honest centered-moment consequence of the quantitative linear-forms
condition. This is algebraic inclusion--exclusion, not the deeper
iterated-Cauchy--Schwarz estimate. -/
theorem HasLinearFormsCondition.abs_mean_cfzCenteredProduct_le
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η) (hk : 0 < k) :
    |mean (cfzCenteredProduct k N ν)| ≤
      (2 : ℝ) ^ Fintype.card (CFZFormIndex k) * η := by
  let j : Fin k := ⟨0, hk⟩
  let ω : DeletedCube k j := fun _ => false
  let : Nonempty (CFZFormIndex k) := ⟨⟨j, ω⟩⟩
  change |mean (fun x =>
    centeredProduct (fun q => cfzFactorFamily k N ν q x))| ≤ _
  exact abs_mean_centeredProduct_le_two_pow
    h.hasBooleanSubproductCondition

/-! ## Fiber convolution and second moments -/

/-- Jensen/Cauchy--Schwarz for a normalized average on a finite nonempty
type. -/
theorem sq_mean_le_mean_sq
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (mean f) ^ 2 ≤ mean (fun x => f x ^ 2) := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq
    Finset.univ f (fun _ : α => (1 : ℝ))
  simpa [mean] using h

/-- A coordinate-sum fiber average contracts the pointwise square. -/
theorem fiberConvolution_sq_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    (fiberConvolution (n + 1) w z) ^ 2 ≤
      fiberConvolution (n + 1) (fun x => w x ^ 2) z := by
  rw [fiberConvolution_succ, fiberConvolution_succ]
  exact sq_mean_le_mean_sq (fun y : Fin n → G =>
    w (sumFiberTuple n z y))

/-- `L²` contraction for coordinate-sum fiber convolution. -/
theorem fiberConvolution_secondMoment_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) :
    mean (fun z =>
      (fiberConvolution (n + 1) w z) ^ 2) ≤
        mean (fun x => w x ^ 2) := by
  calc
    mean (fun z =>
        (fiberConvolution (n + 1) w z) ^ 2) ≤
        mean (fiberConvolution (n + 1)
          (fun x => w x ^ 2)) :=
      mean_mono fun z => fiberConvolution_sq_le n w z
    _ = mean (fun x => w x ^ 2) :=
      mean_fiberConvolution (n + 1) (fun x => w x ^ 2)

/-- `L²` contraction specialized to generalized convolutions. -/
theorem generalizedConvolution_secondMoment_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) :
    mean (fun z =>
      (generalizedConvolution (n + 1) u z) ^ 2) ≤
        mean (fun x => cutTestProduct u x ^ 2) :=
  fiberConvolution_secondMoment_le n (cutTestProduct u)

/-- Exact expansion of the centered second moment. -/
theorem mean_centered_sq
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    mean (fun x => (f x - 1) ^ 2) =
      mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
  calc
    mean (fun x => (f x - 1) ^ 2) =
        mean (fun x =>
          f x ^ 2 + ((-2 : ℝ) * f x + 1)) := by
      apply congrArg mean
      funext x
      ring
    _ = mean (fun x => f x ^ 2) +
        mean (fun x => (-2 : ℝ) * f x + 1) :=
      mean_add _ _
    _ = mean (fun x => f x ^ 2) +
        (mean (fun x => (-2 : ℝ) * f x) +
          mean (fun _ : α => (1 : ℝ))) := by
      rw [mean_add]
    _ = mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
      rw [mean_smul, mean_const]
      ring

/-- The two moment estimates needed in densification imply a centered `L²`
bound for the generalized convolution. Both estimates are explicit
hypotheses; no strong linear-forms estimate is smuggled into this lemma. -/
theorem generalizedConvolution_centered_secondMoment_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1))
    {η₁ η₂ : ℝ}
    (hmean : |mean (cutTestProduct u) - 1| ≤ η₁)
    (hsecond :
      mean (fun x => cutTestProduct u x ^ 2) ≤ 1 + η₂) :
    mean (fun z =>
      (generalizedConvolution (n + 1) u z - 1) ^ 2) ≤
        η₂ + 2 * η₁ := by
  have hmean_lower :
      1 - η₁ ≤ mean (cutTestProduct u) := by
    have hneg := (abs_le.mp hmean).1
    linarith
  have hl2 := generalizedConvolution_secondMoment_le n u
  rw [mean_centered_sq, mean_generalizedConvolution]
  linarith

/-- Squared `L¹` consequence of the preceding centered `L²` bound. -/
theorem generalizedConvolution_centered_absMean_sq_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1))
    {η₁ η₂ : ℝ}
    (hmean : |mean (cutTestProduct u) - 1| ≤ η₁)
    (hsecond :
      mean (fun x => cutTestProduct u x ^ 2) ≤ 1 + η₂) :
    (mean (fun z =>
      |generalizedConvolution (n + 1) u z - 1|)) ^ 2 ≤
        η₂ + 2 * η₁ := by
  calc
    (mean (fun z =>
        |generalizedConvolution (n + 1) u z - 1|)) ^ 2 ≤
        mean (fun z =>
          |generalizedConvolution (n + 1) u z - 1| ^ 2) :=
      sq_mean_le_mean_sq _
    _ = mean (fun z =>
        (generalizedConvolution (n + 1) u z - 1) ^ 2) := by
      apply congrArg mean
      funext z
      exact sq_abs _
    _ ≤ η₂ + 2 * η₁ :=
      generalizedConvolution_centered_secondMoment_le
        n u hmean hsecond

end Wikipedia.SzemeredisTheorem
