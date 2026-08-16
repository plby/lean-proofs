import Wikipedia.SzemeredisTheorem.Finite.ProductMean
import Wikipedia.SzemeredisTheorem.Transference.BooleanCutReduction

/-!
# Moments of generalized convolutions

Products of generalized convolutions are averages over independent copies of
the corresponding sum fibers.  This file records that disintegration
exactly and packages the remaining analytic estimate as a concrete moment
condition.  It is the interface at which iterated Cauchy--Schwarz and the
linear-forms estimate enter the dense-model proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-- The expanded fiber moment corresponding to a product of generalized
convolutions. -/
noncomputable def convolutionMonomialMoment
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (ν : G → ℝ) {n : ℕ}
    (u : Fin n → CutTestFamily G (r + 1)) : ℝ :=
  mean₂ fun z : G => fun y : Fin n → (Fin r → G) =>
    (ν z - 1) *
      ∏ a, cutTestProduct (u a)
        (sumFiberTuple r z (y a))

/-- Product of generalized convolutions as a single average over independent
fiber variables. -/
theorem prod_generalizedConvolution_succ_eq_mean
    {G ι : Type*} [Fintype G] [AddCommGroup G]
    [Fintype ι] [DecidableEq ι]
    (r : ℕ) (u : ι → CutTestFamily G (r + 1))
    (z : G) :
    (∏ a, generalizedConvolution (r + 1) (u a) z) =
      mean (fun y : ι → (Fin r → G) =>
        ∏ a, cutTestProduct (u a)
          (sumFiberTuple r z (y a))) := by
  simp_rw [generalizedConvolution_succ]
  exact prod_mean fun a y =>
    cutTestProduct (u a) (sumFiberTuple r z y)

/-- Pairing the centered majorant with a monomial of generalized
convolutions is exactly the expanded fiber moment. -/
theorem finitePairing_testMonomial_generalizedConvolution
    {G τ : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (ν : G → ℝ)
    (u : τ → CutTestFamily G (r + 1))
    {n : ℕ} (s : Fin n → τ) :
    finitePairing (ν - fun _ => 1)
        (testMonomial
          (fun t => generalizedConvolution (r + 1) (u t)) s) =
      convolutionMonomialMoment r ν (fun a => u (s a)) := by
  unfold finitePairing convolutionMonomialMoment mean₂
  apply congrArg mean
  funext z
  change
    (ν z - 1) *
        (∏ a, generalizedConvolution (r + 1) (u (s a)) z) =
      mean (fun y : Fin n → (Fin r → G) =>
        (ν z - 1) *
          ∏ a, cutTestProduct (u (s a))
            (sumFiberTuple r z (y a)))
  rw [prod_generalizedConvolution_succ_eq_mean]
  exact (mean_smul (ν z - 1) _).symm

/-- Uniform expanded moment estimate for arbitrary bounded cut-test
families. -/
def HasConvolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r d : ℕ) (ν : G → ℝ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d →
    ∀ u : Fin n → CutTestFamily G (r + 1),
      (∀ a, IsBoundedCutTest (u a)) →
        |convolutionMonomialMoment r ν u| ≤ η

/-- The expanded moment estimate for the Boolean vertices needed by the
finite dense-model theorem. -/
def HasBooleanConvolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r d : ℕ) (ν : G → ℝ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d →
    ∀ b : Fin n → BooleanCutAssignment G (r + 1),
      |convolutionMonomialMoment r ν
        (fun a => cutTestFamilyOfBooleanAssignment (b a))| ≤ η

/-- A moment estimate for arbitrary bounded cut tests specializes to the
Boolean moment estimate. -/
theorem HasConvolutionMomentBound.toBoolean
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasConvolutionMomentBound r d ν η) :
    HasBooleanConvolutionMomentBound r d ν η := by
  intro n hn b
  exact h n hn
    (fun a => cutTestFamilyOfBooleanAssignment (b a))
    (fun a => cutTestFamilyOfBooleanAssignment_bounded (b a))

/-- Boolean expanded moments are precisely the monomial correlations of the
Boolean generalized-convolution family. -/
theorem hasMonomialCorrelationBound_booleanCutConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasBooleanConvolutionMomentBound r d ν η) :
    HasMonomialCorrelationBound
      (booleanCutConvolution (G := G) (r + 1))
      ν d η := by
  intro n hn b
  change
    |finitePairing (ν - fun _ => 1)
      (testMonomial
        (fun t =>
          generalizedConvolution (r + 1)
            (cutTestFamilyOfBooleanAssignment t)) b)| ≤ η
  rw [finitePairing_testMonomial_generalizedConvolution
    r ν (fun t => cutTestFamilyOfBooleanAssignment t) b]
  exact h n hn b

/-- The arbitrary bounded moment condition supplies the monomial
correlation input of polynomial dense-model duality. -/
theorem HasConvolutionMomentBound.hasMonomialCorrelationBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r d : ℕ} {ν : G → ℝ} {η : ℝ}
    (h : HasConvolutionMomentBound r d ν η) :
    HasMonomialCorrelationBound
      (booleanCutConvolution (G := G) (r + 1))
      ν d η :=
  hasMonomialCorrelationBound_booleanCutConvolution h.toBoolean

/-- Direct polynomial cut-dense-model consequence of the expanded
convolution moment condition. -/
theorem exists_cutDiscrepancy_model_of_convolutionMomentBound
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmoment :
      HasConvolutionMomentBound r p.natDegree ν η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe (r + 1) f g
        (polynomialCoefficientL1 p * η + δ * M) := by
  exact exists_cutDiscrepancy_model_of_monomialCorrelationBound
    (r + 1) (Nat.succ_pos r)
    hδ hη hM0 hf0 hfν hp hM
    hmoment.hasMonomialCorrelationBound

end Wikipedia.SzemeredisTheorem
