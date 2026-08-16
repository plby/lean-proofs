import Wikipedia.SzemeredisTheorem.Transference.CutDiscrepancy

/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Multiplication by a unit, regarded only as an additive automorphism. -/
noncomputable def mulAddEquivOfIsUnit
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a) :
    R ≃+ R :=
  DistribMulAction.toAddEquiv R ha.unit

@[simp]
theorem mulAddEquivOfIsUnit_apply
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a)
    (x : R) :
    mulAddEquivOfIsUnit a ha x = a * x := by
  change (ha.unit : R) * x = a * x
  rw [IsUnit.unit_spec]

/-- Apply an additive automorphism independently in every coordinate. -/
def coordinatewiseAddEquiv
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G) :
    (ι → G) ≃ (ι → G) where
  toFun x i := e i (x i)
  invFun x i := (e i).symm (x i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (e i).apply_symm_apply (x i)

@[simp]
theorem coordinatewiseAddEquiv_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    coordinatewiseAddEquiv e x i = e i (x i) :=
  rfl

@[simp]
theorem coordinatewiseAddEquiv_symm_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    (coordinatewiseAddEquiv e).symm x i =
      (e i).symm (x i) :=
  rfl

/-- Pull a deleted-coordinate test through independent coordinate
automorphisms. -/
def pullCutTest
    {G : Type*} [AddCommGroup G] {r : ℕ}
    (e : Fin r → G ≃+ G) (u : CutTestFamily G r) :
    CutTestFamily G r := by
  cases r with
  | zero =>
      exact fun i => Fin.elim0 i
  | succ n =>
      exact fun i y =>
        u i (fun t => (e (i.succAbove t)).symm (y t))

theorem IsBoundedCutTest.pull
    {G : Type*} [AddCommGroup G] {r : ℕ}
    {e : Fin r → G ≃+ G} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    IsBoundedCutTest (pullCutTest e u) := by
  constructor
  · intro i x
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
        exact hu.nonneg i
          (fun t => (e (i.succAbove t)).symm (x t))
  · intro i x
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
        exact hu.le_one i
          (fun t => (e (i.succAbove t)).symm (x t))

/-- Cut correlation with an automorphic linear form in place of the literal
coordinate sum. -/
noncomputable def linearCutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, e i (x i)) -
        g (∑ i, e i (x i))) *
      ∏ i, u i (eraseCoordinate i x)

/-- Coordinatewise automorphisms turn a weighted-sum correlation into an
ordinary sum correlation with pulled-back tests. -/
theorem linearCutCorrelation_eq_cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) :
    linearCutCorrelation r e f g u =
      cutCorrelation r f g (pullCutTest e u) := by
  cases r with
  | zero =>
      simp [linearCutCorrelation, cutCorrelation, pullCutTest]
  | succ n =>
      unfold linearCutCorrelation cutCorrelation mean
      apply Fintype.expect_equiv (coordinatewiseAddEquiv e)
      intro x
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      change
        u i (eraseCoordinate i x) =
          u i (fun t =>
            (e (i.succAbove t)).symm
              (eraseCoordinate i
                (coordinatewiseAddEquiv e x) t))
      congr 1
      funext t
      simp

/-- Ordinary cut discrepancy controls every correlation obtained by
automorphic coordinate scalings. -/
theorem CutDiscrepancyLe.abs_linearCutCorrelation_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε)
    (e : Fin r → G ≃+ G)
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    |linearCutCorrelation r e f g u| ≤ ε := by
  rw [linearCutCorrelation_eq_cutCorrelation]
  exact h.apply_bounded (pullCutTest e u) hu.pull

end Wikipedia.SzemeredisTheorem
