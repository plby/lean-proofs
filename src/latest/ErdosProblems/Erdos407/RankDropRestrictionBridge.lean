/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RestrictionIndex
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Restricting a Roth derivative to box bases

The normal derivative supplied by `RestrictionIndex` is written in canonical
form-adapted coordinates.  The rank-drop estimates, however, are available
on an `S`-integral basis of each approximation hyperplane.  This file proves
that substituting such bases into the restricted derivative preserves
nonvanishing.
-/

namespace Erdos407.RankDropRestrictionBridge

open scoped BigOperators

noncomputable section

open Erdos407.GeneralizedRoth

/-- Parameters for one `n`-element basis in each of `blocks` hyperplanes of
an ambient `(n+1)`-dimensional vector space. -/
abbrev ParameterVar (blocks n : ℕ) := Fin blocks × Fin n

/-- Substitute, block by block, linear combinations of the supplied basis
vectors into an ambient block polynomial. -/
def substituteBoxBases {blocks n : ℕ}
    (x : Fin blocks → Fin n → Fin (n + 1) → ℚ)
    (P : MvPolynomial (RothIndex.BlockVar blocks n) ℚ) :
    MvPolynomial (ParameterVar blocks n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun hj => ∑ l : Fin n,
      MvPolynomial.C (x hj.1 l hj.2) * MvPolynomial.X (hj.1, l)) P

/-- Evaluation after the block-basis substitution is evaluation at the
corresponding linear combinations of basis vectors. -/
theorem eval_substituteBoxBases {blocks n : ℕ}
    (x : Fin blocks → Fin n → Fin (n + 1) → ℚ)
    (P : MvPolynomial (RothIndex.BlockVar blocks n) ℚ)
    (t : ParameterVar blocks n → ℚ) :
    MvPolynomial.eval t (substituteBoxBases x P) =
      MvPolynomial.eval
        (fun hj => ∑ l : Fin n, t (hj.1, l) * x hj.1 l hj.2) P := by
  unfold substituteBoxBases
  change MvPolynomial.eval t
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun hj => ∑ l : Fin n,
          MvPolynomial.C (x hj.1 l hj.2) * MvPolynomial.X (hj.1, l)) P) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun u : RothIndex.BlockVar blocks n → ℚ =>
    MvPolynomial.eval u P)
  funext hj
  simp [Function.comp_apply, mul_comm]

/-- Set every adapted normal coordinate to zero. -/
def zeroNormalCoordinates {blocks n : ℕ}
    (M : FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (a : RothIndex.BlockVar blocks n → ℚ) :
    RothIndex.BlockVar blocks n → ℚ :=
  fun hj => if hj.2 = pivotIndex (M hj.1) (hM hj.1) then 0 else a hj

/-- A restricted normal derivative has no normal-coordinate variables, so
its value is unchanged when all those coordinates are set to zero. -/
theorem eval_restrictedDividedDerivative_zeroNormal {blocks n : ℕ}
    (M : FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar blocks n) ℚ)
    (I : RestrictionIndex.NormalOrder blocks)
    (a : RothIndex.BlockVar blocks n → ℚ) :
    MvPolynomial.eval a
        (RestrictionIndex.restrictedDividedDerivative M hM P I) =
      MvPolynomial.eval (zeroNormalCoordinates M hM a)
        (RestrictionIndex.restrictedDividedDerivative M hM P I) := by
  classical
  unfold RestrictionIndex.restrictedDividedDerivative
  unfold RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply Finsupp.prod_congr
  intro hj hhj
  by_cases hp : hj.2 = pivotIndex (M hj.1) (hM hj.1)
  · have hz : RestrictionIndex.tangentialExponent M hM e hj = 0 := by
      simp [RestrictionIndex.tangentialExponent, hp]
    simp [hz]
  · simp [zeroNormalCoordinates, hp]

/-- The canonical kernel point represented by adapted coordinates whose
normal coordinate has been set to zero. -/
def kernelPoint {blocks n : ℕ}
    (M : FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (a : RothIndex.BlockVar blocks n → ℚ)
    (h : Fin blocks) : Fin (n + 1) → ℚ :=
  fun j =>
    if hj : j = pivotIndex (M h) (hM h) then
      -(∑ k ∈ Finset.univ.erase (pivotIndex (M h) (hM h)),
          M h k * a (h, k)) / M h (pivotIndex (M h) (hM h))
    else a (h, j)

/-- The canonical point really lies in the kernel of the corresponding
normal form. -/
theorem form_eval_kernelPoint_eq_zero {blocks n : ℕ}
    (M : FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (a : RothIndex.BlockVar blocks n → ℚ) (h : Fin blocks) :
    (∑ j, M h j * kernelPoint M hM a h j) = 0 := by
  classical
  let p := pivotIndex (M h) (hM h)
  have hp : M h p ≠ 0 := pivotIndex_coeff_ne_zero (M h) (hM h)
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin (n + 1) => M h j * kernelPoint M hM a h j)
    (Finset.mem_univ p)]
  have hoff :
      (∑ x ∈ Finset.univ.erase p, M h x * kernelPoint M hM a h x) =
        ∑ x ∈ Finset.univ.erase p, M h x * a (h, x) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j ≠ p := (Finset.mem_erase.mp hj).1
    simp [kernelPoint, p, hjp]
  rw [show kernelPoint M hM a h p =
      -(∑ k ∈ Finset.univ.erase p, M h k * a (h, k)) / M h p by
        simp [kernelPoint, p]]
  rw [hoff]
  field_simp
  ring

/-- The zero-normal adapted coordinates of `a` are exactly the standard
coordinates of its canonical kernel point. -/
theorem kernelPoint_eq_zeroNormalCoordinates {blocks n : ℕ}
    (M : FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (a : RothIndex.BlockVar blocks n → ℚ)
    (h : Fin blocks) (j : Fin (n + 1))
    (hj : j ≠ pivotIndex (M h) (hM h)) :
    kernelPoint M hM a h j = zeroNormalCoordinates M hM a (h, j) := by
  simp [kernelPoint, zeroNormalCoordinates, hj]

end

end Erdos407.RankDropRestrictionBridge
