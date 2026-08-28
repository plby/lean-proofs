import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingAffine
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingMatrix
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEta

/-!
# The distinguished form as an actual integral second cohomology class

The class below is defined in the genuine singular cochain complex.  Its
normalization is fixed by evaluation on the ordered products of positive
period loops: `u,w` has value one and `γ,δ` has value six.  These exact
integral periods also identify its associated real tangent form and the
imaginary part of the already constructed first-linear Hermitian form.

No Chern-class, singular cup-product, or complex-orientation comparison
is asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusTypeOneOne SpecialPeriods
open Elliptic Elliptic.HigherHomology

/-- The source's distinguished form gives a genuine integral singular cohomology class. -/
def etaClass (p : PeriodDomain) : SingularCohomology p.Torus 2 :=
  coefficientClass p periodRelationEta

/-- Its normalization is an equality of evaluations on actual positive period-loop products. -/
theorem etaClass_evaluate_periodLoops (p : PeriodDomain) (x y : Lattice) :
    singularEvaluation p.Torus 2 (etaClass p)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      x 1 * y 2 - x 2 * y 1 + 6 * (x 0 * y 3 - x 3 * y 0) := by
  rw [etaClass, coefficientClass_evaluate_periodLoops]
  simp only [coordinateForm_apply, coordinateValue, periodRelationEta,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    zero_mul, one_mul, add_zero, zero_add]
  ring

/-- The literal integral values on all six ordered coordinate two-cycles. -/
theorem etaClass_evaluate_basis_pair (p : PeriodDomain) (k : Fin 6) :
    singularEvaluation p.Torus 2 (etaClass p)
      (product11 p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) =
      periodRelationEta k :=
  coefficientClass_evaluate_basis_pair p periodRelationEta k

/-- The actual positive `u,w` two-cycle, not an abstract basis coordinate. -/
def etaPairCycle (p : PeriodDomain) : SingularHomology p.Torus 2 :=
  product11 p.Torus (loopHomologyClass (p.periodLoop (Pi.single 1 1)))
    (loopHomologyClass (p.periodLoop (Pi.single 2 1)))

/-- Evaluation on that genuine cycle is an integral linear functional. -/
def etaEvaluation (p : PeriodDomain) : SingularCohomology p.Torus 2 →ₗ[ℤ] ℤ :=
  (singularEvaluation p.Torus 2).flip (etaPairCycle p)

theorem etaEvaluation_apply (p : PeriodDomain) (a : SingularCohomology p.Torus 2) :
    etaEvaluation p a = singularEvaluation p.Torus 2 a (etaPairCycle p) := rfl

@[simp] theorem etaEvaluation_etaClass (p : PeriodDomain) :
    etaEvaluation p (etaClass p) = 1 := by
  have h := etaClass_evaluate_basis_pair p (3 : Fin 6)
  simpa only [etaEvaluation_apply, etaPairCycle, coefficientPair, periodRelationEta,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

/-- The distinguished native class is nonzero, as witnessed by an actual two-cycle. -/
theorem etaClass_ne_zero (p : PeriodDomain) : etaClass p ≠ 0 := by
  intro h
  have he := etaEvaluation_etaClass p
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- The class is primitive: no nonunit integer divides it in actual singular cohomology. -/
theorem etaClass_primitive (p : PeriodDomain) (r : ℤ)
    (a : SingularCohomology p.Torus 2) (ha : r • a = etaClass p) : IsUnit r := by
  have he := congrArg (etaEvaluation p) ha
  rw [map_zsmul, etaEvaluation_etaClass, zsmul_eq_mul] at he
  exact isUnit_iff_dvd_one.mpr ⟨etaEvaluation p a, he.symm⟩

/-- Integer multiples remain distinct in the genuine native cohomology group. -/
theorem etaClass_zsmul_injective (p : PeriodDomain) :
    Function.Injective (fun r : ℤ => r • etaClass p) := by
  intro r s h
  have he := congrArg (etaEvaluation p) h
  simpa using he

/-- Its exact integral periods are those of the actual distinguished tangent form. -/
theorem etaClass_real_periods (p : PeriodDomain) (x y : Lattice) :
    (singularEvaluation p.Torus 2 (etaClass p)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) : ℝ) =
      etaTangent p (PeriodTorusTypeOneOne.periodEquiv p (fun i => (x i : ℝ)))
        (PeriodTorusTypeOneOne.periodEquiv p (fun i => (y i : ℝ))) :=
  coefficientClass_real_periods p periodRelationEta x y

/-- The genuine integral periods equal the imaginary part of the actual associated form. -/
theorem etaClass_hermitian_periods (p : PeriodDomain) (x y : Lattice) :
    (singularEvaluation p.Torus 2 (etaClass p)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) : ℝ) =
      (etaHermitian p (PeriodTorusTypeOneOne.periodEquiv p (fun i => (x i : ℝ)))
        (PeriodTorusTypeOneOne.periodEquiv p (fun i => (y i : ℝ)))).im := by
  rw [etaHermitian_im]
  exact etaClass_real_periods p x y

/-- The first actual period-change map preserves the distinguished native class. -/
theorem etaClass_pullback_step₁ (p : PeriodDomain) :
    singularCohomologyPullback p.step₁ContinuousMap 2 (etaClass p.step₁) = etaClass p := by
  unfold etaClass
  rw [coefficientClass_pullback_step₁]
  exact congrArg (coefficientClass p) coefficientPullback_A₁_eta

/-- The second actual period-change map preserves the same positively normalized class. -/
theorem etaClass_pullback_step₂ (p : PeriodDomain) :
    singularCohomologyPullback p.step₂ContinuousMap 2 (etaClass p.step₂) = etaClass p := by
  unfold etaClass
  rw [coefficientClass_pullback_step₂]
  exact congrArg (coefficientClass p) coefficientPullback_A₂_eta

/-- The actual cusp period change also preserves the genuine integral class. -/
theorem etaClass_pullback_step₀ (p : PeriodDomain) :
    singularCohomologyPullback p.step₀ContinuousMap 2 (etaClass p.step₀) = etaClass p := by
  unfold etaClass
  rw [coefficientClass_pullback_step₀]
  exact congrArg (coefficientClass p) coefficientPullback_M₀_eta

theorem coefficientPullback_kind_eta (j : Kind) :
    coefficientPullback j.matrix.mulVecLin periodRelationEta = periodRelationEta := by
  cases j with
  | three => exact coefficientPullback_A₁_eta
  | four => exact coefficientPullback_A₂_eta

/-- Every actual affine elliptic map preserves the native class, for every integer twist. -/
theorem etaClass_pullback_affineBiholomorph (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    singularCohomologyPullback
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) 2
        (etaClass p.val) = etaClass p.val := by
  unfold etaClass
  rw [coefficientClass_pullback_affineBiholomorph, coefficientPullback_kind_eta]

/-- In admissible elliptic quotients the native class belongs to the actual all-deck invariants. -/
theorem etaClass_mem_deckInvariants (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    etaClass p.val ∈ periodCohomologyInvariants j p v hv 2 :=
  (coefficientClass_mem_deckInvariants_iff j p v hv periodRelationEta).mpr
    (coefficientPullback_kind_eta j)

/-- The equality is an actual cochain-induced pullback for every finite deck element. -/
theorem etaClass_pullback_deck (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (g : CyclicGroup j) :
    singularCohomologyPullback (surfaceDeckMap j p v hv g) 2 (etaClass p.val) =
      etaClass p.val :=
  coefficientClass_deck_invariant_of_preserved j p v hv periodRelationEta
    (coefficientPullback_kind_eta j) g

/-- The distinguished class as an element of the genuine invariant cohomology submodule. -/
def etaInvariantClass (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) : periodCohomologyInvariants j p v hv 2 :=
  ⟨etaClass p.val, etaClass_mem_deckInvariants j p v hv⟩

@[simp] theorem etaInvariantClass_coe (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    (etaInvariantClass j p v hv : SingularCohomology p.val.Torus 2) = etaClass p.val := rfl

/-- Compatibility with all three actual period-change pullbacks characterizes the native η line. -/
theorem coefficientClass_common_pullbacks_iff_unique_eta (p : PeriodDomain) (E : Fin 6 → ℤ) :
    (singularCohomologyPullback p.step₁ContinuousMap 2 (coefficientClass p.step₁ E) =
        coefficientClass p E ∧
      singularCohomologyPullback p.step₂ContinuousMap 2 (coefficientClass p.step₂ E) =
        coefficientClass p E ∧
      singularCohomologyPullback p.step₀ContinuousMap 2 (coefficientClass p.step₀ E) =
        coefficientClass p E) ↔
      ∃! n : ℤ, coefficientClass p E = n • etaClass p := by
  rw [coefficientClass_pullback_step₁, coefficientClass_pullback_step₂,
    coefficientClass_pullback_step₀]
  simp only [(coefficientClass_injective p).eq_iff]
  have h (n : ℤ) : coefficientClass p E = n • etaClass p ↔
      E = n • periodRelationEta := by
    rw [etaClass, ← coefficientClass_smul]
    exact (coefficientClass_injective p).eq_iff
  simp_rw [h]
  exact coefficientPullback_common_fixed_iff_unique_multiple E

end Wikipedia.HopfProblem.PeriodTorusCohomology
