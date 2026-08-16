import Wikipedia.GreenTao.Transference.WeightedStrongLinearForms

/-!
# Repeated weighted Cauchy--Schwarz for strong linear forms

This file supplies the recursive analytic bridge which precedes the
algebraic endpoint in `WeightedStrongLinearForms`.

The recursion is the quantitative finite version of Conlon--Fox--Zhao,
Lemma 6.3.  A parameterized cut system consists of a possibly signed core
and one nonnegative factor for every deleted coordinate.  Each factor is
dominated by a designated majorant.  One Cauchy--Schwarz step

* removes the head factor;
* pays the normalized mean of its majorant;
* duplicates the head coordinate;
* pairs every remaining factor; and
* inserts the removed majorant into the new core.

After all coordinates have been processed, the core is the product of all
copies of the original centered factor together with exactly one copy of
each selected face majorant.  No pointwise bound on the majorants is used.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Weighted finite Cauchy--Schwarz -/

/-- Cauchy--Schwarz with a nonnegative weight:

`(𝔼 u w)² ≤ (𝔼 u) (𝔼 u w²)`.
-/
theorem mean_mul_sq_le_weighted
    {Ω : Type*} [Fintype Ω]
    (u w : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) :
    mean (fun x => u x * w x) ^ 2 ≤
      mean u * mean (fun x => u x * w x ^ 2) := by
  have hcs :=
    mean_mul_sq_le_product
      (fun x => Real.sqrt (u x))
      (fun x => Real.sqrt (u x) * w x)
  have hlinear :
      mean (fun x => Real.sqrt (u x) *
        (Real.sqrt (u x) * w x)) =
        mean (fun x => u x * w x) := by
    apply congrArg mean
    funext x
    rw [← mul_assoc, Real.mul_self_sqrt (hu x)]
  have hweight :
      mean (fun x => Real.sqrt (u x) ^ 2) = mean u := by
    apply congrArg mean
    funext x
    exact Real.sq_sqrt (hu x)
  have hsquare :
      mean (fun x => (Real.sqrt (u x) * w x) ^ 2) =
        mean (fun x => u x * w x ^ 2) := by
    apply congrArg mean
    funext x
    rw [mul_pow, Real.sq_sqrt (hu x)]
  rw [hlinear, hweight, hsquare] at hcs
  exact hcs

/-- A nonnegative weight may be enlarged on both factors in the weighted
Cauchy--Schwarz bound. -/
theorem mean_mul_sq_le_majorized
    {Ω : Type*} [Fintype Ω]
    (u v w : Ω → ℝ)
    (hu : ∀ x, 0 ≤ u x)
    (huv : ∀ x, u x ≤ v x) :
    mean (fun x => u x * w x) ^ 2 ≤
      mean v * mean (fun x => v x * w x ^ 2) := by
  have hv : ∀ x, 0 ≤ v x :=
    fun x => (hu x).trans (huv x)
  calc
    mean (fun x => u x * w x) ^ 2 ≤
        mean u * mean (fun x => u x * w x ^ 2) :=
      mean_mul_sq_le_weighted u w hu
    _ ≤ mean v * mean (fun x => v x * w x ^ 2) := by
      exact mul_le_mul
        (mean_mono huv)
        (mean_mono fun x =>
          mul_le_mul_of_nonneg_right (huv x) (sq_nonneg (w x)))
        (mean_nonneg fun x => mul_nonneg (hu x) (sq_nonneg (w x)))
        (mean_nonneg hv)

/-- Weighted Cauchy--Schwarz in the form used by one recursive
coordinate-elimination step.  Squaring the inner mean replaces the inner
variable by two independent copies. -/
theorem cauchySchwarz_eliminate_outer_majorized
    {X Y : Type*} [Fintype X] [Fintype Y]
    (u v : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, 0 ≤ u x)
    (huv : ∀ x, u x ≤ v x) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean v *
        mean₂ (fun x => fun p : Y × Y =>
          v x * F x p.1 * F x p.2) := by
  have hrewrite :
      mean₂ (fun x y => u x * F x y) =
        mean (fun x => u x * mean (F x)) := by
    unfold mean₂
    apply congrArg mean
    funext x
    exact mean_smul (u x) (F x)
  rw [hrewrite]
  calc
    mean (fun x => u x * mean (F x)) ^ 2 ≤
        mean v *
          mean (fun x => v x * mean (F x) ^ 2) :=
      mean_mul_sq_le_majorized u v (fun x => mean (F x)) hu huv
    _ =
        mean v *
          mean₂ (fun x => fun p : Y × Y =>
            v x * F x p.1 * F x p.2) := by
      apply congrArg (fun z : ℝ => mean v * z)
      unfold mean₂
      apply congrArg mean
      funext x
      calc
        v x * mean (F x) ^ 2 =
            v x *
              mean (fun p : Y × Y =>
                F x p.1 * F x p.2) := by
          rw [mean_sq_eq_mean_pair_mul]
        _ =
            mean (fun p : Y × Y =>
              v x * F x p.1 * F x p.2) := by
          simpa only [smul_eq_mul, mul_assoc] using
            (mean_smul (v x)
              (fun p : Y × Y => F x p.1 * F x p.2)).symm

/-- Fubini in the form which moves the middle variable across a product
parameter.  This is the bookkeeping identity needed after a coordinate has
been duplicated. -/
theorem mean_prod_swap_middle
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℝ) :
    mean₂ (fun q : A × B => fun c => F q.1 q.2 c) =
      mean₂ (fun q : A × C => fun b => F q.1 b q.2) := by
  change
    mean (fun q : A × B => mean (fun c => F q.1 q.2 c)) =
      mean (fun q : A × C => mean (fun b => F q.1 b q.2))
  rw [mean_prod_type
        (fun a : A => fun b : B => mean (fun c : C => F a b c)),
      mean_prod_type
        (fun a : A => fun c : C => mean (fun b : B => F a b c))]
  apply congrArg mean
  funext a
  exact mean₂_comm (F a)

/-! ## Parameterized majorized cut systems -/

/-- A cut system with an external finite parameter space.  The external
parameter records the pairs created by coordinates already processed by
Cauchy--Schwarz. -/
structure MajorizedCutSystem
    (P G : Type*) (n : ℕ) where
  core : P → (Fin n → G) → ℝ
  factor : P → CutTestFamily G n
  majorant : P → CutTestFamily G n
  factor_nonneg :
    ∀ p i x, 0 ≤ factor p i x
  factor_le_majorant :
    ∀ p i x, factor p i x ≤ majorant p i x

namespace MajorizedCutSystem

variable {P G : Type*} {n : ℕ}

/-- Every designated majorant is nonnegative. -/
theorem majorant_nonneg
    (S : MajorizedCutSystem P G n)
    (p : P) (i : Fin n) (x : Fin (n - 1) → G) :
    0 ≤ S.majorant p i x :=
  (S.factor_nonneg p i x).trans
    (S.factor_le_majorant p i x)

/-- The normalized cut expression represented by a system. -/
noncomputable def form
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G n) : ℝ :=
  mean₂ fun p x =>
    S.core p x *
      ∏ i, S.factor p i (eraseCoordinate i x)

/-- The factor left after the head deleted-coordinate factor has been
pulled outside the head-coordinate mean. -/
noncomputable def tailIntegrand
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G) : ℝ :=
  S.core p (Fin.cons a y) *
    ∏ i : Fin n,
      S.factor p i.succ
        (eraseCoordinate i.succ (Fin.cons a y))

/-- The majorant-only moment paid when the head coordinate is removed. -/
noncomputable def headMajorantMean
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) : ℝ :=
  mean₂ fun p y => S.majorant p 0 y

/-- One recursive weighted Cauchy--Schwarz transform.  The new parameter
contains the two copies of the removed head coordinate. -/
def next
    {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1)) :
    MajorizedCutSystem (P × (G × G)) G n := by
  cases n with
  | zero =>
      exact
        { core := fun q y =>
            S.majorant q.1 0 y *
              S.core q.1 (Fin.cons q.2.1 y) *
              S.core q.1 (Fin.cons q.2.2 y)
          factor := fun _ i => Fin.elim0 i
          majorant := fun _ i => Fin.elim0 i
          factor_nonneg := fun _ i => Fin.elim0 i
          factor_le_majorant := fun _ i => Fin.elim0 i }
  | succ m =>
      exact
        { core := fun q y =>
            S.majorant q.1 0 y *
              S.core q.1 (Fin.cons q.2.1 y) *
              S.core q.1 (Fin.cons q.2.2 y)
          factor := fun q i z =>
            S.factor q.1 i.succ (Fin.cons q.2.1 z) *
              S.factor q.1 i.succ (Fin.cons q.2.2 z)
          majorant := fun q i z =>
            S.majorant q.1 i.succ (Fin.cons q.2.1 z) *
              S.majorant q.1 i.succ (Fin.cons q.2.2 z)
          factor_nonneg := fun q i z =>
            mul_nonneg
              (S.factor_nonneg q.1 i.succ _)
              (S.factor_nonneg q.1 i.succ _)
          factor_le_majorant := fun q i z => by
            exact mul_le_mul
              (S.factor_le_majorant q.1 i.succ _)
              (S.factor_le_majorant q.1 i.succ _)
              (S.factor_nonneg q.1 i.succ _)
              (S.majorant_nonneg q.1 i.succ _) }

/-- Pointwise form of splitting off the head deleted-coordinate factor. -/
theorem integrand_cons
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G) :
    S.core p (Fin.cons a y) *
          ∏ i, S.factor p i
            (eraseCoordinate i (Fin.cons a y)) =
      S.factor p 0 y * S.tailIntegrand p y a := by
  cases n with
  | zero =>
      simp [tailIntegrand]
      ring_nf
  | succ n =>
      rw [Fin.prod_univ_succ]
      simp only [eraseCoordinate_zero_cons]
      simp [tailIntegrand]
      ring

/-- Split a parameterized successor-dimensional form into its head factor
and the remaining inner integrand. -/
theorem form_succ
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    S.form =
      mean₂ (fun q : P × (Fin n → G) => fun a : G =>
        S.factor q.1 0 q.2 *
          S.tailIntegrand q.1 q.2 a) := by
  unfold form
  calc
    mean₂ (fun p x =>
        S.core p x *
          ∏ i, S.factor p i (eraseCoordinate i x)) =
        mean (fun p =>
          mean₂ (fun a : G => fun y : Fin n → G =>
            S.core p (Fin.cons a y) *
              ∏ i, S.factor p i
                (eraseCoordinate i (Fin.cons a y)))) := by
      unfold mean₂
      apply congrArg mean
      funext p
      exact mean_fin_cons _
    _ = mean (fun p =>
          mean₂ (fun y : Fin n → G => fun a : G =>
            S.core p (Fin.cons a y) *
              ∏ i, S.factor p i
                (eraseCoordinate i (Fin.cons a y)))) := by
      apply congrArg mean
      funext p
      exact mean₂_comm _
    _ = mean₂ (fun q : P × (Fin n → G) => fun a : G =>
          S.core q.1 (Fin.cons a q.2) *
            ∏ i, S.factor q.1 i
              (eraseCoordinate i (Fin.cons a q.2))) := by
      simpa only [mean₂] using
        (mean_prod_type
          (fun p : P => fun y : Fin n → G =>
            mean (fun a : G =>
              S.core p (Fin.cons a y) *
                ∏ i, S.factor p i
                  (eraseCoordinate i (Fin.cons a y))))).symm
    _ = mean₂ (fun q : P × (Fin n → G) => fun a : G =>
          S.factor q.1 0 q.2 *
            S.tailIntegrand q.1 q.2 a) := by
      unfold mean₂
      apply congrArg mean
      funext q
      apply congrArg mean
      funext a
      exact S.integrand_cons q.1 q.2 a

/-- The two copies of the tail integrand, together with the paid head
majorant, are exactly the integrand of the transformed cut system. -/
theorem tailIntegrand_pair
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G × G) :
    S.majorant p 0 y *
          S.tailIntegrand p y a.1 *
          S.tailIntegrand p y a.2 =
      S.next.core (p, a) y *
        ∏ i, S.next.factor (p, a) i
          (eraseCoordinate i y) := by
  cases n with
  | zero =>
      simp [tailIntegrand, next]
  | succ n =>
      simp only [tailIntegrand, next]
      simp only [eraseCoordinate_succ_cons]
      rw [Finset.prod_mul_distrib]
      ac_rfl

/-- One CFZ weighted Cauchy--Schwarz step.  The head factor is enlarged to
its designated majorant, the head coordinate is duplicated, and all
remaining factors are paired. -/
theorem form_sq_le_headMajorantMean_mul_next_form
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    S.form ^ 2 ≤ S.headMajorantMean * S.next.form := by
  rw [S.form_succ]
  calc
    mean₂ (fun q : P × (Fin n → G) => fun a : G =>
        S.factor q.1 0 q.2 *
          S.tailIntegrand q.1 q.2 a) ^ 2 ≤
        mean (fun q : P × (Fin n → G) =>
          S.majorant q.1 0 q.2) *
          mean₂ (fun q : P × (Fin n → G) => fun a : G × G =>
            S.majorant q.1 0 q.2 *
              S.tailIntegrand q.1 q.2 a.1 *
              S.tailIntegrand q.1 q.2 a.2) := by
      exact cauchySchwarz_eliminate_outer_majorized
        (fun q : P × (Fin n → G) => S.factor q.1 0 q.2)
        (fun q : P × (Fin n → G) => S.majorant q.1 0 q.2)
        (fun q : P × (Fin n → G) => fun a : G =>
          S.tailIntegrand q.1 q.2 a)
        (fun q => S.factor_nonneg q.1 0 q.2)
        (fun q => S.factor_le_majorant q.1 0 q.2)
    _ = S.headMajorantMean *
        mean₂ (fun q : P × (G × G) => fun y : Fin n → G =>
          S.majorant q.1 0 y *
            S.tailIntegrand q.1 y q.2.1 *
            S.tailIntegrand q.1 y q.2.2) := by
      apply congrArg₂ (· * ·)
      · change
          mean (fun q : P × (Fin n → G) =>
            S.majorant q.1 0 q.2) =
            mean₂ (fun p : P => fun y : Fin n → G =>
              S.majorant p 0 y)
        exact mean_prod_type
          (fun p : P => fun y : Fin n → G =>
            S.majorant p 0 y)
      · exact mean_prod_swap_middle
          (A := P) (B := Fin n → G) (C := G × G)
          (fun p y a =>
            S.majorant p 0 y *
              S.tailIntegrand p y a.1 *
              S.tailIntegrand p y a.2)
    _ = S.headMajorantMean * S.next.form := by
      apply congrArg (fun z : ℝ => S.headMajorantMean * z)
      unfold form mean₂
      apply congrArg mean
      funext q
      apply congrArg mean
      funext y
      exact S.tailIntegrand_pair q.1 y q.2

/-! ## Quantitative iteration -/

/-- The majorant moment paid in one step is nonnegative. -/
theorem headMajorantMean_nonneg
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    0 ≤ S.headMajorantMean := by
  unfold headMajorantMean mean₂
  exact mean_nonneg fun p =>
    mean_nonneg fun y => S.majorant_nonneg p 0 y

/-- A uniform upper bound for the current majorant moment gives the
absolute-value form of one recursive weighted Cauchy--Schwarz step. -/
theorem abs_form_sq_le_bound_mul_abs_next_form
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    {B : ℝ} (hB : S.headMajorantMean ≤ B) :
    |S.form| ^ 2 ≤ B * |S.next.form| := by
  calc
    |S.form| ^ 2 = S.form ^ 2 := sq_abs S.form
    _ ≤ S.headMajorantMean * S.next.form :=
      S.form_sq_le_headMajorantMean_mul_next_form
    _ ≤ S.headMajorantMean * |S.next.form| :=
      mul_le_mul_of_nonneg_left
        (le_abs_self S.next.form) S.headMajorantMean_nonneg
    _ ≤ B * |S.next.form| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg S.next.form)

/-- Recursive input for the quantitative CFZ iteration.  At every
successor stage the paid majorant moment is at most `B`; at the
zero-dimensional endpoint the remaining form has absolute value at most
`E`. -/
def HasRecursiveBounds
    {G : Type u} [Fintype G] (B E : ℝ) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S => |S.form| ≤ E
  | _, _, _n + 1, S =>
      S.headMajorantMean ≤ B ∧
        HasRecursiveBounds B E S.next

/-- Closed quantitative form of the repeated weighted Cauchy--Schwarz
recursion:

`|Q₀|^(2^n) ≤ B^(2^n - 1) E`.

Thus the `n` paid majorant moments occur with total multiplicity
`1 + 2 + ⋯ + 2^(n-1) = 2^n - 1`. -/
theorem abs_form_pow_two_le
    {G : Type u} [Fintype G] {B E : ℝ} (hB0 : 0 ≤ B) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasRecursiveBounds B E S →
        |S.form| ^ (2 ^ n) ≤ B ^ (2 ^ n - 1) * E := by
  intro P instP n S hS
  induction n generalizing P with
  | zero =>
      simpa [HasRecursiveBounds] using hS
  | succ n ih =>
      change
        S.headMajorantMean ≤ B ∧
          HasRecursiveBounds B E S.next at hS
      have hstep :
          |S.form| ^ 2 ≤ B * |S.next.form| :=
        S.abs_form_sq_le_bound_mul_abs_next_form hS.1
      have hnext :
          |S.next.form| ^ (2 ^ n) ≤
            B ^ (2 ^ n - 1) * E :=
        ih S.next hS.2
      have hexponent :
          2 ^ n + (2 ^ n - 1) = 2 ^ (n + 1) - 1 := by
        have hpow : 0 < 2 ^ n := by positivity
        rw [pow_succ]
        omega
      calc
        |S.form| ^ (2 ^ (n + 1)) =
            (|S.form| ^ 2) ^ (2 ^ n) := by
          rw [pow_succ, mul_comm, pow_mul]
        _ ≤ (B * |S.next.form|) ^ (2 ^ n) :=
          pow_le_pow_left₀ (sq_nonneg _) hstep _
        _ = B ^ (2 ^ n) * |S.next.form| ^ (2 ^ n) := by
          rw [mul_pow]
        _ ≤ B ^ (2 ^ n) *
            (B ^ (2 ^ n - 1) * E) :=
          mul_le_mul_of_nonneg_left hnext (pow_nonneg hB0 _)
        _ = B ^ (2 ^ (n + 1) - 1) * E := by
          rw [← mul_assoc, ← pow_add, hexponent]

end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/

/-- Every CFZ subproduct has mean at most `1 + η`.  This is the
one-sided consequence of the linear-forms condition used to pay the
majorant moments in the repeated Cauchy--Schwarz argument. -/
theorem HasLinearFormsCondition.mean_linearFormsProduct_le_one_add
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    (e : LinearFormsExponent k) :
    mean (linearFormsProduct k N ν e) ≤ 1 + η := by
  have hupper :
      mean (linearFormsProduct k N ν e) - 1 ≤ η :=
    (le_abs_self
      (mean (linearFormsProduct k N ν e) - 1)).trans (hLF e)
  linarith

namespace MajorizedCutSystem

/-- Build a majorized cut system from arbitrary nonnegative factors bounded
by `1`.  The designated majorants are all the constant function `1`. -/
def ofBoundedFactors
    {P G : Type*} {n : ℕ}
    (core : P → (Fin n → G) → ℝ)
    (factor : P → CutTestFamily G n)
    (hfactor_nonneg : ∀ p i x, 0 ≤ factor p i x)
    (hfactor_le_one : ∀ p i x, factor p i x ≤ 1) :
    MajorizedCutSystem P G n where
  core := core
  factor := factor
  majorant := fun _ _ _ => 1
  factor_nonneg := hfactor_nonneg
  factor_le_majorant := hfactor_le_one

/-- Every designated majorant in a system is identically one. -/
def HasUnitMajorants
    {P G : Type*} {n : ℕ}
    (S : MajorizedCutSystem P G n) : Prop :=
  ∀ p i x, S.majorant p i x = 1

@[simp]
theorem ofBoundedFactors_hasUnitMajorants
    {P G : Type*} {n : ℕ}
    (core : P → (Fin n → G) → ℝ)
    (factor : P → CutTestFamily G n)
    (hfactor_nonneg : ∀ p i x, 0 ≤ factor p i x)
    (hfactor_le_one : ∀ p i x, factor p i x ≤ 1) :
    HasUnitMajorants
      (ofBoundedFactors core factor
        hfactor_nonneg hfactor_le_one) :=
  fun _ _ _ => rfl

/-- Pairing preserves the fact that all designated majorants are one. -/
theorem HasUnitMajorants.next
    {P G : Type*} {n : ℕ}
    {S : MajorizedCutSystem P G (n + 1)}
    (hS : HasUnitMajorants S) :
    HasUnitMajorants S.next := by
  cases n with
  | zero =>
      intro _ i
      exact Fin.elim0 i
  | succ n =>
      intro q i z
      change
        S.majorant q.1 i.succ (Fin.cons q.2.1 z) *
            S.majorant q.1 i.succ (Fin.cons q.2.2 z) =
          1
      rw [hS, hS, one_mul]

/-- With nonempty averaging spaces, a unit majorant costs exactly one in
one Cauchy--Schwarz step. -/
theorem HasUnitMajorants.headMajorantMean_eq_one
    {P G : Type*} [Fintype P] [Nonempty P]
    [Fintype G] [Nonempty G] {n : ℕ}
    {S : MajorizedCutSystem P G (n + 1)}
    (hS : HasUnitMajorants S) :
    S.headMajorantMean = 1 := by
  unfold headMajorantMean
  calc
    mean₂ (fun p y => S.majorant p 0 y) =
        mean₂ (fun _ : P => fun _ : Fin n → G => (1 : ℝ)) := by
      unfold mean₂
      apply congrArg mean
      funext p
      apply congrArg mean
      funext y
      exact hS p 0 y
    _ = 1 := by
      simp [mean₂, mean]

/-- A structural certificate that identifies every majorant moment created
by the recursion with an ordinary CFZ linear-forms subproduct and
identifies the final zero-dimensional form with the weighted centered-face
endpoint.

The selector at an intermediate stage is completely arbitrary.  Hence the
certificate supports any mixture of factors bounded by `1` (use the empty
selector) and factors enlarged to their corresponding CFZ majorants. -/
def HasCFZCertificate
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N] (ν : ZMod N → ℝ) (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S =>
      ∃ other : LinearFormsExponent k,
        (∀ ω, other j ω = false) ∧
          S.form =
            mean (fun x =>
              faceCenteredProduct k N ν j x *
                linearFormsProduct k N ν other x)
  | _, _, _n + 1, S =>
      ∃ e : LinearFormsExponent k,
        S.headMajorantMean =
            mean (linearFormsProduct k N ν e) ∧
          HasCFZCertificate ν j S.next

/-- The terminal-only part of a CFZ certificate.  This is useful for
systems whose majorants are all one, since then every intermediate moment
is discharged automatically by the empty linear-forms selector. -/
def HasCFZTerminal
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N] (ν : ZMod N → ℝ) (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S =>
      ∃ other : LinearFormsExponent k,
        (∀ ω, other j ω = false) ∧
          S.form =
            mean (fun x =>
              faceCenteredProduct k N ν j x *
                linearFormsProduct k N ν other x)
  | _, _, _n + 1, S =>
      HasCFZTerminal ν j S.next

/-- Unit majorants turn a terminal certificate into a full CFZ recursive
certificate.  In particular this handles all arbitrary nonnegative
two-copy factors bounded by `1`. -/
theorem HasUnitMajorants.hasCFZCertificate
    {k N : ℕ} [NeZero N] {ν : ZMod N → ℝ}
    {G : Type u} [Fintype G] [Nonempty G] (j : Fin k) :
    ∀ {P : Type u} [Fintype P] [Nonempty P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasUnitMajorants S →
      HasCFZTerminal ν j S →
        HasCFZCertificate ν j S := by
  intro P instP instPNonempty n S hunit hterminal
  induction n generalizing P with
  | zero =>
      exact hterminal
  | succ n ih =>
      change HasCFZTerminal ν j S.next at hterminal
      refine ⟨emptyLinearFormsExponent k, ?_, ?_⟩
      · calc
          S.headMajorantMean = 1 :=
            hunit.headMajorantMean_eq_one
          _ = mean (linearFormsProduct k N ν
              (emptyLinearFormsExponent k)) := by
            have hproduct :
                linearFormsProduct k N ν
                    (emptyLinearFormsExponent k) =
                  fun _ => 1 := by
              funext x
              exact linearFormsProduct_empty k N ν x
            rw [hproduct]
            simp [mean]
      · exact ih S.next hunit.next hterminal

/-- A CFZ certificate discharges all recursive analytic bounds: every
intermediate majorant moment costs at most `1 + η`, and the terminal form
is controlled by the weighted strong-linear-forms endpoint. -/
theorem hasRecursiveBounds_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasCFZCertificate ν j S →
        HasRecursiveBounds
          (1 + η)
          ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
          S := by
  intro P instP n S hS
  induction n generalizing P with
  | zero =>
      rcases hS with ⟨other, hother, hterminal⟩
      change
        |S.form| ≤
          (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η
      rw [hterminal]
      exact hLF.abs_mean_faceCenteredProduct_mul_le
        j other hother
  | succ n ih =>
      rcases hS with ⟨e, hmoment, hnext⟩
      change
        S.headMajorantMean ≤ 1 + η ∧
          HasRecursiveBounds
            (1 + η)
            ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
            S.next
      constructor
      · rw [hmoment]
        exact hLF.mean_linearFormsProduct_le_one_add e
      · exact ih S.next hnext

/-- Quantitative weighted strong-linear-forms Cauchy--Schwarz bridge.

For a system with `n` remaining coordinates, arbitrary nonnegative cut
factors may be used as long as they are dominated by the certified
majorants.  Repeated Cauchy--Schwarz then costs
`(1 + η)^(2^n - 1)` and terminates at the exact weighted endpoint already
proved in `WeightedStrongLinearForms`. -/
theorem abs_form_pow_two_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S) :
    |S.form| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) := by
  exact abs_form_pow_two_le
    (B := 1 + η)
    (E := (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
    (by linarith [hLF.error_nonneg])
    S
    (hasRecursiveBounds_of_hasCFZCertificate hLF j S hS)

/-- Root-extracted form of the weighted strong-linear-forms estimate.

This is the interface used by relative counting: it keeps the analytic
parameter conversion separate from the Cauchy--Schwarz recursion. -/
theorem abs_form_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ n - 1) *
          ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) ≤
        ε ^ (2 ^ n)) :
    |S.form| ≤ ε := by
  exact le_of_pow_le_pow_left₀
    (pow_ne_zero _ two_ne_zero) hε
    ((abs_form_pow_two_le_of_hasCFZCertificate hLF j S hS).trans hconvert)

/-- Bounded-factor specialization of the weighted bridge.  If every
majorant is identically one, only the transformed terminal identity needs
to be supplied. -/
theorem abs_form_pow_two_le_of_unitMajorants
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] [Nonempty G] (j : Fin k)
    {P : Type u} [Fintype P] [Nonempty P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hunit : HasUnitMajorants S)
    (hterminal : HasCFZTerminal ν j S) :
    |S.form| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) := by
  exact
    abs_form_pow_two_le_of_hasCFZCertificate hLF j S
      (hunit.hasCFZCertificate j S hterminal)

/-- Fully explicit constructor-level version for arbitrary nonnegative
cut factors bounded by one. -/
theorem abs_ofBoundedFactors_form_pow_two_le
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] [Nonempty G] (j : Fin k)
    {P : Type u} [Fintype P] [Nonempty P] {n : ℕ}
    (core : P → (Fin n → G) → ℝ)
    (factor : P → CutTestFamily G n)
    (hfactor_nonneg : ∀ p i x, 0 ≤ factor p i x)
    (hfactor_le_one : ∀ p i x, factor p i x ≤ 1)
    (hterminal :
      HasCFZTerminal ν j
        (ofBoundedFactors core factor
          hfactor_nonneg hfactor_le_one)) :
    |(ofBoundedFactors core factor
        hfactor_nonneg hfactor_le_one).form| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) := by
  exact
    abs_form_pow_two_le_of_unitMajorants hLF j
      (ofBoundedFactors core factor
        hfactor_nonneg hfactor_le_one)
      (ofBoundedFactors_hasUnitMajorants
        core factor hfactor_nonneg hfactor_le_one)
      hterminal

end MajorizedCutSystem

end Wikipedia.SzemeredisTheorem
