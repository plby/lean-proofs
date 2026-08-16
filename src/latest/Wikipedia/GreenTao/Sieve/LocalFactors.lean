import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Wikipedia.GreenTao.Sieve.ExceptionalPrimes

/-!
# Elementary local densities of affine forms

This starts the local-factor calculation with the exact one-form density.
An integer affine form is reduced modulo `p`; if one coefficient remains
nonzero and `p` is prime, its linear part is surjective.  All fibers then
have the same cardinality, so the zero congruence occupies exactly a
`1 / p` fraction of the finite vector space (recorded first as an exact
natural-number identity).
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm

/-- The linear part of an integer affine form after reduction modulo `p`. -/
def linearMapZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ) :
    (ι → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun x := ∑ i, (ψ.coefficient i : ZMod p) * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Evaluate an integer affine form after reducing all coefficients modulo
`p`. -/
def evalZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) : ZMod p :=
  (ψ.constant : ZMod p) + ψ.linearMapZMod p x

@[simp]
theorem linearMapZMod_single {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (i : ι) (a : ZMod p) :
    ψ.linearMapZMod p (Pi.single i a) =
      (ψ.coefficient i : ZMod p) * a := by
  simp [linearMapZMod, Pi.single_apply, eq_comm]

@[simp]
theorem evalZMod_eq_zero_iff {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    ψ.evalZMod p x = 0 ↔
      ψ.linearMapZMod p x = -(ψ.constant : ZMod p) := by
  simp [evalZMod, eq_neg_iff_add_eq_zero, add_comm]

/-- The finite solution set of the affine congruence `ψ(x)=0 mod p`. -/
def zeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ) :
    Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ψ.linearMapZMod p x = -(ψ.constant : ZMod p)

@[simp]
theorem mem_zeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ ψ.zeroFinsetZMod p ↔ ψ.evalZMod p x = 0 := by
  simp [zeroFinsetZMod, evalZMod_eq_zero_iff]

/-- A nonzero coefficient makes the reduced linear form surjective over the
prime field. -/
theorem linearMapZMod_surjective_of_coefficient_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    Function.Surjective (ψ.linearMapZMod p) := by
  classical
  intro y
  let x : ι → ZMod p :=
    fun j =>
      if j = i then (ψ.coefficient i : ZMod p)⁻¹ * y else 0
  refine ⟨x, ?_⟩
  simp [linearMapZMod, x, hi]

/-- The two-output linear map defined by a pair of affine forms after
reduction modulo `p`. -/
def pairLinearMapZMod {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ φ : AffineForm ι ℤ) :
    (ι → ZMod p) →ₗ[ZMod p] ZMod p × ZMod p :=
  (ψ.linearMapZMod p).prod (φ.linearMapZMod p)

@[simp]
theorem pairLinearMapZMod_apply {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    pairLinearMapZMod p ψ φ x =
      (ψ.linearMapZMod p x, φ.linearMapZMod p x) :=
  rfl

/-- A nonzero two-by-two coefficient minor makes the pair of reduced linear
forms jointly surjective. -/
theorem pairLinearMapZMod_surjective_of_minor_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (ψ φ : AffineForm ι ℤ)
    {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    Function.Surjective (pairLinearMapZMod p ψ φ) := by
  intro y
  have hij : i ≠ j := by
    intro hij
    subst j
    simp [coefficientMinor] at hdet
  let det : ZMod p :=
    (ψ.coefficient i : ZMod p) *
        (φ.coefficient j : ZMod p) -
      (ψ.coefficient j : ZMod p) *
        (φ.coefficient i : ZMod p)
  have hdet' : det ≠ 0 := by
    simpa [det, coefficientMinor] using hdet
  let u : ZMod p :=
    det⁻¹ *
      ((φ.coefficient j : ZMod p) * y.1 -
        (ψ.coefficient j : ZMod p) * y.2)
  let v : ZMod p :=
    det⁻¹ *
      (-(φ.coefficient i : ZMod p) * y.1 +
        (ψ.coefficient i : ZMod p) * y.2)
  let x : ι → ZMod p :=
    Pi.single i u + Pi.single j v
  refine ⟨x, ?_⟩
  apply Prod.ext
  · change ψ.linearMapZMod p x = y.1
    rw [show x = Pi.single i u + Pi.single j v by rfl,
      map_add, linearMapZMod_single, linearMapZMod_single]
    simp only [u, v]
    field_simp [hdet']
    simp only [det]
    ring
  · change φ.linearMapZMod p x = y.2
    rw [show x = Pi.single i u + Pi.single j v by rfl,
      map_add, linearMapZMod_single, linearMapZMod_single]
    simp only [u, v]
    field_simp [hdet']
    simp only [det]
    ring

/-- The simultaneous zero set of two affine congruences modulo `p`. -/
def commonZeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ) :
    Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ψ.evalZMod p x = 0 ∧ φ.evalZMod p x = 0

@[simp]
theorem mem_commonZeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ commonZeroFinsetZMod p ψ φ ↔
      ψ.evalZMod p x = 0 ∧ φ.evalZMod p x = 0 := by
  simp [commonZeroFinsetZMod]

/-- Exact cardinal form of the codimension-two density of two independent
affine congruences. -/
theorem card_commonZeroFinsetZMod_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    p ^ 2 * (commonZeroFinsetZMod p ψ φ).card =
      p ^ Fintype.card ι := by
  letI : Fact p.Prime := ⟨hp⟩
  let L := pairLinearMapZMod p ψ φ
  have hsurj : Function.Surjective L :=
    pairLinearMapZMod_surjective_of_minor_ne_zero ψ φ hdet
  let target : ZMod p × ZMod p :=
    (-(ψ.constant : ZMod p), -(φ.constant : ZMod p))
  have hcommon :
      commonZeroFinsetZMod p ψ φ =
        Finset.univ.filter fun x : ι → ZMod p => L x = target := by
    ext x
    simp [L, target, evalZMod_eq_zero_iff]
  have hfiber (y : ZMod p × ZMod p) :
      ((Finset.univ.filter fun x : ι → ZMod p => L x = y).card) =
        (commonZeroFinsetZMod p ψ φ).card := by
    have h :=
      AddMonoidHom.card_fiber_eq_of_mem_range L.toAddMonoidHom
        (hsurj y) (hsurj target)
    rw [hcommon]
    change
      (Finset.univ.filter fun g : ι → ZMod p => L g = y).card =
        (Finset.univ.filter fun g : ι → ZMod p => L g = target).card
    exact h
  have hsplit :
      Fintype.card (ι → ZMod p) =
        ∑ y : ZMod p × ZMod p,
          (Finset.univ.filter fun x : ι → ZMod p =>
            L x = y).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (ι → ZMod p)))
        (t := (Finset.univ : Finset (ZMod p × ZMod p)))
        (f := fun x => L x)
        (fun _ _ => Finset.mem_univ _))
  rw [Fintype.card_fun, ZMod.card] at hsplit
  have hsplit' :
      p ^ Fintype.card ι =
        p ^ 2 * (commonZeroFinsetZMod p ψ φ).card := by
    calc
      p ^ Fintype.card ι =
          ∑ y : ZMod p × ZMod p,
            (Finset.univ.filter fun x : ι → ZMod p =>
              L x = y).card := hsplit
      _ = ∑ _y : ZMod p × ZMod p,
          (commonZeroFinsetZMod p ψ φ).card := by
        apply Finset.sum_congr rfl
        intro y _
        exact hfiber y
      _ = p ^ 2 * (commonZeroFinsetZMod p ψ φ).card := by
        simp [ZMod.card, pow_two]
  exact hsplit'.symm

/-- Exact cardinal form of the one-congruence local density. -/
theorem card_zeroFinsetZMod_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    p * (ψ.zeroFinsetZMod p).card =
      p ^ Fintype.card ι := by
  letI : Fact p.Prime := ⟨hp⟩
  let L := ψ.linearMapZMod p
  have hsurj : Function.Surjective L :=
    ψ.linearMapZMod_surjective_of_coefficient_ne_zero hi
  let target : ZMod p := -(ψ.constant : ZMod p)
  have hfiber (y : ZMod p) :
      ((Finset.univ.filter fun x : ι → ZMod p => L x = y).card) =
        (ψ.zeroFinsetZMod p).card := by
    have h :=
      AddMonoidHom.card_fiber_eq_of_mem_range L.toAddMonoidHom
        (hsurj y) (hsurj target)
    change
      (Finset.univ.filter fun g : ι → ZMod p => L g = y).card =
        (Finset.univ.filter fun g : ι → ZMod p => L g = target).card
    exact h
  have hsplit :
      Fintype.card (ι → ZMod p) =
        ∑ y : ZMod p,
          (Finset.univ.filter fun x : ι → ZMod p =>
            L x = y).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (ι → ZMod p)))
        (t := (Finset.univ : Finset (ZMod p)))
        (f := fun x => L x)
        (fun _ _ => Finset.mem_univ _))
  rw [Fintype.card_fun, ZMod.card] at hsplit
  have hsplit' :
      p ^ Fintype.card ι =
        p * (ψ.zeroFinsetZMod p).card := by
    calc
      p ^ Fintype.card ι =
          ∑ y : ZMod p,
            (Finset.univ.filter fun x : ι → ZMod p =>
              L x = y).card := hsplit
      _ = ∑ _y : ZMod p, (ψ.zeroFinsetZMod p).card := by
        apply Finset.sum_congr rfl
        intro y _
        exact hfiber y
      _ = p * (ψ.zeroFinsetZMod p).card := by
        simp [ZMod.card]
  exact hsplit'.symm

/-- The exact normalized density of one nondegenerate affine congruence. -/
theorem mean_zeroFinsetZMod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    mean (finsetIndicator (ψ.zeroFinsetZMod p)) = (1 : ℝ) / p := by
  rw [mean_finsetIndicator, Fintype.card_fun, ZMod.card]
  have hcard := card_zeroFinsetZMod_mul hp ψ hi
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpow0 : ((p : ℝ) ^ Fintype.card ι) ≠ 0 :=
    pow_ne_zero _ hp0
  have hcardR :
      (p : ℝ) * ((ψ.zeroFinsetZMod p).card : ℝ) =
        (p : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hcard
  field_simp
  simpa [mul_comm] using hcardR

/-- The exact normalized density of two independent affine congruences. -/
theorem mean_commonZeroFinsetZMod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    mean (finsetIndicator (commonZeroFinsetZMod p ψ φ)) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [mean_finsetIndicator, Fintype.card_fun, ZMod.card]
  have hcard :=
    card_commonZeroFinsetZMod_mul hp ψ φ hdet
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hcardR :
      (p : ℝ) ^ 2 *
          ((commonZeroFinsetZMod p ψ φ).card : ℝ) =
        (p : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hcard
  field_simp
  simpa [mul_comm] using hcardR

/-- Multiplying the two zero-congruence indicators is exactly the indicator
of their simultaneous zero set. -/
theorem finsetIndicator_zero_mul_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ φ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x =
      finsetIndicator (commonZeroFinsetZMod p ψ φ) x := by
  simp only [finsetIndicator]
  by_cases hψ : ψ.evalZMod p x = 0 <;>
    by_cases hφ : φ.evalZMod p x = 0 <;>
    simp [hψ, hφ]

/-- Pairwise modular independence gives the exact second mixed moment of
the two congruence indicators. -/
theorem mean_zeroFinsetZMod_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    mean (fun x =>
      finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [show
    (fun x =>
      finsetIndicator (ψ.zeroFinsetZMod p) x *
        finsetIndicator (φ.zeroFinsetZMod p) x) =
      finsetIndicator (commonZeroFinsetZMod p ψ φ) by
        funext x
        exact finsetIndicator_zero_mul_zero p ψ φ x]
  exact mean_commonZeroFinsetZMod hp ψ φ hdet

end AffineForm

/-- Beyond the explicit exceptional-prime bound, every form in a nonzero
system has exact zero-congruence density `1 / p`. -/
theorem mean_zeroFinsetZMod_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (q : κ) :
    mean (finsetIndicator ((forms q).zeroFinsetZMod p)) =
      (1 : ℝ) / p := by
  obtain ⟨i, hi⟩ :=
    exists_coefficient_cast_ne_zero_of_bound hforms hlarge q
  exact AffineForm.mean_zeroFinsetZMod hp (forms q) hi

/-- Beyond the explicit exceptional-prime bound, distinct forms in a
pairwise-independent system have exact simultaneous zero density `1 / p²`. -/
theorem mean_zeroFinsetZMod_mul_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    mean (fun x =>
      finsetIndicator ((forms q).zeroFinsetZMod p) x *
        finsetIndicator ((forms r).zeroFinsetZMod p) x) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  obtain ⟨i, j, hij⟩ :=
    exists_minor_cast_ne_zero_of_bound hforms hlarge hqr
  exact AffineForm.mean_zeroFinsetZMod_mul
    hp (forms q) (forms r) hij

end Wikipedia.SzemeredisTheorem
