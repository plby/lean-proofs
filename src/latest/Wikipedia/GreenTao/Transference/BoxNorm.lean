import Wikipedia.SzemeredisTheorem.Finite.CauchySchwarz
import Wikipedia.SzemeredisTheorem.Transference.CutDiscrepancy

/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Pair a function on `(n + 1)` coordinates at two values of its first
coordinate. -/
def pairedTupleFunction {G : Type*} {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) (p : G × G) :
    (Fin n → G) → ℝ :=
  fun y => F (Fin.cons p.1 y) * F (Fin.cons p.2 y)

/-- Select the first component at `false` and the second at `true`. -/
def selectPair {G : Type*} (p : G × G) : Bool → G
  | false => p.1
  | true => p.2

@[simp]
theorem selectPair_false {G : Type*} (p : G × G) :
    selectPair p false = p.1 :=
  rfl

@[simp]
theorem selectPair_true {G : Type*} (p : G × G) :
    selectPair p true = p.2 :=
  rfl

/-- Vertex of a cube whose `i`-th pair of endpoints is `x i`. -/
def cubeVertex {G : Type*} {n : ℕ}
    (x : Fin n → G × G) (ω : Fin n → Bool) : Fin n → G :=
  fun i => selectPair (x i) (ω i)

@[simp]
theorem cubeVertex_cons
    {G : Type*} {n : ℕ}
    (p : G × G) (x : Fin n → G × G)
    (b : Bool) (ω : Fin n → Bool) :
    cubeVertex (Fin.cons p x) (Fin.cons b ω) =
      Fin.cons (selectPair p b) (cubeVertex x ω) := by
  funext i
  cases i using Fin.cases <;> simp [cubeVertex]

/-- The recursive box moment.  At each successor step the first coordinate
is duplicated and the two resulting copies of the function are multiplied.
-/
noncomputable def boxMoment {G : Type*} [Fintype G] :
    (n : ℕ) → ((Fin n → G) → ℝ) → ℝ
  | 0, F => mean F
  | n + 1, F =>
      mean fun p : G × G =>
        boxMoment n (pairedTupleFunction F p)

@[simp]
theorem boxMoment_zero {G : Type*} [Fintype G]
    (F : (Fin 0 → G) → ℝ) :
    boxMoment 0 F = mean F :=
  rfl

@[simp]
theorem boxMoment_succ {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    boxMoment (n + 1) F =
      mean fun p : G × G =>
        boxMoment n (pairedTupleFunction F p) :=
  rfl

/-- Explicit cube-vertex form of the box moment. -/
noncomputable def cubeMean {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) : ℝ :=
  mean fun x : Fin n → G × G =>
    ∏ ω : Fin n → Bool, F (cubeVertex x ω)

/-- Package two Boolean-indexed endpoints as a pair, independently in every
coordinate. -/
def endpointTupleEquiv {G : Type*} {n : ℕ} :
    (Fin n → Bool → G) ≃ (Fin n → G × G) where
  toFun x i := (x i false, x i true)
  invFun x i := selectPair (x i)
  left_inv x := by
    funext i b
    cases b <;> rfl
  right_inv x := by
    funext i
    exact Prod.ext rfl rfl

@[simp]
theorem endpointTupleEquiv_apply_fst
    {G : Type*} {n : ℕ}
    (x : Fin n → Bool → G) (i : Fin n) :
    (endpointTupleEquiv x i).1 = x i false :=
  rfl

@[simp]
theorem endpointTupleEquiv_apply_snd
    {G : Type*} {n : ℕ}
    (x : Fin n → Bool → G) (i : Fin n) :
    (endpointTupleEquiv x i).2 = x i true :=
  rfl

/-- Cube moment with the two endpoints represented as a Boolean-indexed
function rather than a pair. -/
noncomputable def cubeFunctionMean
    {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) : ℝ :=
  mean fun x : Fin n → Bool → G =>
    ∏ ω : Fin n → Bool, F (fun i => x i (ω i))

/-- The endpoint-function and endpoint-pair presentations give the same
cube average. -/
theorem cubeFunctionMean_eq_cubeMean
    {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) :
    cubeFunctionMean n F = cubeMean n F := by
  unfold cubeFunctionMean cubeMean mean
  apply Fintype.expect_equiv (endpointTupleEquiv (G := G) (n := n))
  intro x
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg F
  funext i
  cases h : ω i <;> simp [cubeVertex, h]

/-- Splitting the head cube coordinate pairs the two head-coordinate copies
of `F` at every remaining cube vertex. -/
theorem cubeProduct_cons
    {G : Type*} {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (p : G × G) (x : Fin n → G × G) :
    (∏ ω : Fin (n + 1) → Bool,
        F (cubeVertex (Fin.cons p x) ω)) =
      ∏ ω : Fin n → Bool,
        pairedTupleFunction F p (cubeVertex x ω) := by
  calc
    (∏ ω : Fin (n + 1) → Bool,
        F (cubeVertex (Fin.cons p x) ω)) =
        ∏ q : Bool × (Fin n → Bool),
          F (cubeVertex (Fin.cons p x)
            (Fin.cons q.1 q.2)) := by
      apply Fintype.prod_equiv
        (Fin.consEquiv
          (fun _ : Fin (n + 1) => Bool)).symm
      intro ω
      simp
    _ = ∏ ω : Fin n → Bool, ∏ b : Bool,
          F (cubeVertex (Fin.cons p x)
            (Fin.cons b ω)) :=
      Fintype.prod_prod_type_right _
    _ = ∏ ω : Fin n → Bool,
          pairedTupleFunction F p (cubeVertex x ω) := by
      apply Finset.prod_congr rfl
      intro ω _
      simp [pairedTupleFunction, mul_comm]

/-- The explicit cube mean obeys the same successor recursion as
`boxMoment`. -/
theorem cubeMean_succ
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    cubeMean (n + 1) F =
      mean fun p : G × G =>
        cubeMean n (pairedTupleFunction F p) := by
  unfold cubeMean
  rw [mean_fin_cons]
  unfold mean₂
  apply congrArg mean
  funext p
  apply congrArg mean
  funext x
  exact cubeProduct_cons F p x

/-- Recursive and explicit cube-vertex descriptions of the box moment
coincide. -/
theorem boxMoment_eq_cubeMean
    {G : Type*} [Fintype G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ),
      boxMoment n F = cubeMean n F := by
  intro n
  induction n with
  | zero =>
      intro F
      simp [boxMoment, cubeMean, mean]
      exact congrArg F (Subsingleton.elim _ _)
  | succ n ih =>
      intro F
      rw [boxMoment_succ, cubeMean_succ]
      apply congrArg mean
      funext p
      exact ih (pairedTupleFunction F p)

/-- A coordinate cut form for an arbitrary function on a finite product. -/
noncomputable def coordinateCutForm
    {G : Type*} [Fintype G] (n : ℕ)
    (F : (Fin n → G) → ℝ) (u : CutTestFamily G n) : ℝ :=
  mean fun x => F x * ∏ i, u i (eraseCoordinate i x)

/-- Absolute boundedness is the natural hypothesis for the Cauchy--Schwarz
argument; unlike cut discrepancy, signs of the coordinate factors do not
matter. -/
def IsAbsBoundedCutTest {G : Type*} {n : ℕ}
    (u : CutTestFamily G n) : Prop :=
  ∀ i x, |u i x| ≤ 1

theorem IsBoundedCutTest.isAbsBounded
    {G : Type*} {n : ℕ} {u : CutTestFamily G n}
    (hu : IsBoundedCutTest u) :
    IsAbsBoundedCutTest u := by
  intro i x
  rw [abs_of_nonneg (hu.nonneg i x)]
  exact hu.le_one i x

@[simp]
theorem eraseCoordinate_zero_cons
    {G : Type*} {n : ℕ} (a : G) (y : Fin n → G) :
    eraseCoordinate (0 : Fin (n + 1)) (Fin.cons a y) = y := by
  funext j
  simp [eraseCoordinate_apply]

@[simp]
theorem eraseCoordinate_succ_cons
    {G : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : G) (y : Fin (n + 1) → G) :
    eraseCoordinate i.succ (Fin.cons a y) =
      Fin.cons a (eraseCoordinate i y) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp [eraseCoordinate_apply]
  | succ j =>
      simp [eraseCoordinate_apply]

/-- After duplicating the head coordinate, pair every remaining deleted
coordinate factor.  The `n = 0` branch is vacuous. -/
def pairedTailCut
    {G : Type*} :
    {n : ℕ} →
      CutTestFamily G (n + 1) → G × G → CutTestFamily G n
  | 0, _, _ => fun i _ => Fin.elim0 i
  | _ + 1, u, p => fun i z =>
      u i.succ (Fin.cons p.1 z) *
        u i.succ (Fin.cons p.2 z)

theorem pairedTailCut_abs_le_one
    {G : Type*} {n : ℕ}
    {u : CutTestFamily G (n + 1)}
    (hu : IsAbsBoundedCutTest u) (p : G × G) :
    IsAbsBoundedCutTest (pairedTailCut u p) := by
  intro i z
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [pairedTailCut, abs_mul]
      exact mul_le_one₀ (hu i.succ _) (abs_nonneg _) (hu i.succ _)

/-- The part of a successor-dimensional cut form left after its head
coordinate factor has been pulled outside the head-coordinate mean. -/
noncomputable def tailCutIntegrand
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (y : Fin n → G) (a : G) : ℝ :=
  F (Fin.cons a y) *
    ∏ i : Fin n,
      u i.succ
        (eraseCoordinate i.succ (Fin.cons a y))

/-- Split a successor-dimensional cut form into the deleted-head factor and
the remaining inner integrand. -/
theorem coordinateCutForm_succ
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1)) :
    coordinateCutForm (n + 1) F u =
      mean₂ fun y : Fin n → G => fun a : G =>
        u 0 y * tailCutIntegrand F u y a := by
  calc
    coordinateCutForm (n + 1) F u =
        mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.cons a y) *
            ∏ i, u i
              (eraseCoordinate i (Fin.cons a y))) := by
      exact mean_fin_cons _
    _ = mean₂ (fun y : Fin n → G => fun a : G =>
          F (Fin.cons a y) *
            ∏ i, u i
              (eraseCoordinate i (Fin.cons a y))) :=
      mean₂_comm _
    _ = mean₂ fun y : Fin n → G => fun a : G =>
          u 0 y * tailCutIntegrand F u y a := by
      apply congrArg mean
      funext y
      apply congrArg mean
      funext a
      simp only
      rw [Fin.prod_univ_succ]
      simp only [eraseCoordinate_zero_cons]
      simp [tailCutIntegrand]
      ring

/-- Multiplying the two inner integrands produced by Cauchy--Schwarz is
exactly the lower-dimensional cut integrand with paired function and paired
cut factors. -/
theorem tailCutIntegrand_mul
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (y : Fin n → G) (p : G × G) :
    tailCutIntegrand F u y p.1 *
        tailCutIntegrand F u y p.2 =
      pairedTupleFunction F p y *
        ∏ i, pairedTailCut u p i (eraseCoordinate i y) := by
  cases n with
  | zero =>
      simp [tailCutIntegrand, pairedTupleFunction]
  | succ n =>
      simp only [tailCutIntegrand, pairedTupleFunction]
      rw [mul_mul_mul_comm]
      rw [← Finset.prod_mul_distrib]
      simp only [eraseCoordinate_succ_cons, pairedTailCut]

/-- One Cauchy--Schwarz step: delete the head cut factor, duplicate the head
coordinate, and pair all remaining factors. -/
theorem coordinateCutForm_sq_le_paired_mean
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    coordinateCutForm (n + 1) F u ^ 2 ≤
      mean fun p : G × G =>
        coordinateCutForm n
          (pairedTupleFunction F p) (pairedTailCut u p) := by
  rw [coordinateCutForm_succ]
  calc
    mean₂ (fun y : Fin n → G => fun a : G =>
        u 0 y * tailCutIntegrand F u y a) ^ 2 ≤
        mean₂ (fun y : Fin n → G => fun p : G × G =>
          tailCutIntegrand F u y p.1 *
            tailCutIntegrand F u y p.2) :=
      cauchySchwarz_eliminate_outer_factor
        (fun y : Fin n → G => u 0 y)
        (fun y : Fin n → G => fun a : G =>
          tailCutIntegrand F u y a)
        (fun y => hu 0 y)
    _ = mean₂ (fun p : G × G => fun y : Fin n → G =>
          tailCutIntegrand F u y p.1 *
            tailCutIntegrand F u y p.2) :=
      mean₂_comm _
    _ = mean (fun p : G × G =>
          coordinateCutForm n
            (pairedTupleFunction F p) (pairedTailCut u p)) := by
      unfold mean₂
      apply congrArg mean
      funext p
      unfold coordinateCutForm
      apply congrArg mean
      funext y
      exact tailCutIntegrand_mul F u y p

/-- Generalized von Neumann inequality for finite coordinate cut forms.
After one Cauchy--Schwarz step per coordinate, every cut factor has
disappeared and the resulting expression is the full recursive box moment.
-/
theorem coordinateCutForm_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ)
      (u : CutTestFamily G n),
      IsAbsBoundedCutTest u →
        coordinateCutForm n F u ^ (2 ^ n) ≤
          boxMoment n F := by
  intro n
  induction n with
  | zero =>
      intro F u _
      simp [coordinateCutForm]
  | succ n ih =>
      intro F u hu
      let C : G × G → ℝ := fun p =>
        coordinateCutForm n
          (pairedTupleFunction F p) (pairedTailCut u p)
      have hcs :
          coordinateCutForm (n + 1) F u ^ 2 ≤ mean C := by
        simpa [C] using
          coordinateCutForm_sq_le_paired_mean F u hu
      calc
        coordinateCutForm (n + 1) F u ^ (2 ^ (n + 1)) =
            (coordinateCutForm (n + 1) F u ^ 2) ^ (2 ^ n) := by
          rw [pow_succ, mul_comm, pow_mul]
        _ ≤ mean C ^ (2 ^ n) :=
          pow_le_pow_left₀ (sq_nonneg _) hcs _
        _ ≤ mean (fun p => C p ^ (2 ^ n)) :=
          mean_pow_two_le_mean_pow_two' C n
        _ ≤ mean (fun p : G × G =>
            boxMoment n (pairedTupleFunction F p)) := by
          apply mean_mono
          intro p
          exact ih
            (pairedTupleFunction F p)
            (pairedTailCut u p)
            (pairedTailCut_abs_le_one hu p)
        _ = boxMoment (n + 1) F :=
          rfl

/-- Explicit cube-vertex version of the generalized von Neumann
inequality. -/
theorem coordinateCutForm_pow_le_cubeMean
    {G : Type*} [Fintype G] [Nonempty G]
    (n : ℕ) (F : (Fin n → G) → ℝ)
    (u : CutTestFamily G n)
    (hu : IsAbsBoundedCutTest u) :
    coordinateCutForm n F u ^ (2 ^ n) ≤
      mean (fun x : Fin n → G × G =>
        ∏ ω : Fin n → Bool, F (cubeVertex x ω)) := by
  change coordinateCutForm n F u ^ (2 ^ n) ≤ cubeMean n F
  rw [← boxMoment_eq_cubeMean]
  exact coordinateCutForm_pow_le_boxMoment n F u hu

/-- The coordinate theorem specialized to the cut correlation used by the
transference layer. -/
theorem cutCorrelation_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r)
    (hu : IsAbsBoundedCutTest u) :
    cutCorrelation r f g u ^ (2 ^ r) ≤
      boxMoment r (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) := by
  simpa [cutCorrelation, coordinateCutForm] using
    coordinateCutForm_pow_le_boxMoment r
      (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i))
      u hu

/-- Absolute-value form in every positive dimension. -/
theorem abs_cutCorrelation_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] [AddCommGroup G]
    (n : ℕ) (f g : G → ℝ)
    (u : CutTestFamily G (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    |cutCorrelation (n + 1) f g u| ^ (2 ^ (n + 1)) ≤
      boxMoment (n + 1)
        (fun x : Fin (n + 1) → G =>
          f (∑ i, x i) - g (∑ i, x i)) := by
  have heven : Even (2 ^ (n + 1)) :=
    even_two.pow_of_ne_zero (Nat.succ_ne_zero n)
  rw [heven.pow_abs]
  exact cutCorrelation_pow_le_boxMoment (n + 1) f g u hu

/-- `[0,1]`-valued cut tests satisfy the hypotheses of the generalized von
Neumann bound. -/
theorem bounded_cutCorrelation_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r)
    (hu : IsBoundedCutTest u) :
    cutCorrelation r f g u ^ (2 ^ r) ≤
      boxMoment r (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) :=
  cutCorrelation_pow_le_boxMoment r f g u hu.isAbsBounded

end Wikipedia.SzemeredisTheorem
