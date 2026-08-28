import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyMixed
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Literal complex coordinates for local antiholomorphic calculus

The three coordinates and their constant basis vectors are ordinary complex
coordinates.  Splitting off one coordinate is a complex continuous linear
equivalence, and all derivative identities use the actual real derivative.
-/

noncomputable section

open Complex Filter Set
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

abbrev Coordinates := Fin 3 → ℂ

/-- The constant vector in one of the original complex coordinate directions. -/
def basisVector (i : Fin 3) : Coordinates := Pi.single i 1

/-- The actual antiholomorphic derivative in a complex coordinate direction. -/
def coordinateDbar (i : Fin 3) (f : Coordinates → ℂ) (q : Coordinates) : ℂ :=
  HolomorphicDolbeaultThree.dbar f q (basisVector i)

@[simp] theorem basisVector_self (i : Fin 3) : basisVector i i = 1 := by
  simp [basisVector]

@[simp] theorem basisVector_of_ne {i j : Fin 3} (h : j ≠ i) :
    basisVector i j = 0 := by
  simp [basisVector, h]

theorem contDiff_coordinateDbar (i : Fin 3) {f : Coordinates → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateDbar i f) :=
  contDiff_dbar_apply hf (basisVector i)

theorem coordinateDbar_congr (i : Fin 3) {f g : Coordinates → ℂ}
    {q : Coordinates} (h : f =ᶠ[𝓝 q] g) :
    coordinateDbar i f q = coordinateDbar i g q :=
  congrArg (fun L => L (basisVector i)) (dbar_congr h)

theorem coordinateDbar_coordinateDbar {f : Coordinates → ℂ}
    (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (q : Coordinates) :
    coordinateDbar i (coordinateDbar j f) q =
      coordinateDbar j (coordinateDbar i f) q :=
  dbar_dbar hf q (basisVector i) (basisVector j)

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The genuine antiholomorphic differential obeys the chain rule for complex
linear coordinate maps. -/
theorem dbar_complex_linear_comp (L : E →L[ℂ] F) {f : F → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f (L q)) (v : E) :
    HolomorphicDolbeaultThree.dbar (f ∘ L) q v =
      HolomorphicDolbeaultThree.dbar f (L q) (L v) := by
  have he := (hf.hasFDerivAt.comp q (L.restrictScalars ℝ).hasFDerivAt).fderiv
  simp only [HolomorphicDolbeaultThree.dbar_apply, he,
    ContinuousLinearMap.comp_apply]
  change (fderiv ℝ f (L q) (L v) + I * fderiv ℝ f (L q) (L (I • v))) / 2 = _
  rw [map_smul]

end Composition

/-- The other coordinates are honest complex parameters. -/
abbrev CoordinateParameter (i : Fin 3) := {j : Fin 3 // j ≠ i} → ℂ

/-- Split a coordinate from the remaining complex coordinates. -/
def coordinateSplitLinear (i : Fin 3) :
    Coordinates ≃ₗ[ℂ] CoordinateParameter i × ℂ where
  toFun q := (fun j => q j, q i)
  invFun p j := if h : j = i then p.2 else p.1 ⟨j, h⟩
  left_inv q := by
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv p := by
    apply Prod.ext
    · funext j
      simp [j.property]
    · simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The split is complex continuous linear, not a replacement of the atlas. -/
def coordinateSplit (i : Fin 3) :
    Coordinates ≃L[ℂ] CoordinateParameter i × ℂ :=
  (coordinateSplitLinear i).toContinuousLinearEquiv

@[simp] theorem coordinateSplit_apply (i : Fin 3) (q : Coordinates) :
    coordinateSplit i q = (fun j : {j : Fin 3 // j ≠ i} => q j, q i) := rfl

theorem coordinateSplit_symm_apply (i : Fin 3)
    (p : CoordinateParameter i × ℂ) (j : Fin 3) :
    (coordinateSplit i).symm p j =
      if h : j = i then p.2 else p.1 ⟨j, h⟩ := rfl

@[simp] theorem coordinateSplit_symm_self (i : Fin 3)
    (p : CoordinateParameter i × ℂ) : (coordinateSplit i).symm p i = p.2 := by
  simp [coordinateSplit_symm_apply]

/-- Holding the parameter coordinates fixed is literally a coordinate update. -/
theorem coordinateSplit_symm_update (i : Fin 3) (q : Coordinates) (z : ℂ) :
    (coordinateSplit i).symm ((coordinateSplit i q).1, z) =
      Function.update q i z := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [coordinateSplit_symm_apply, coordinateSplit_apply, h]

@[simp] theorem coordinateSplit_basis_self (i : Fin 3) :
    coordinateSplit i (basisVector i) = (0, 1) := by
  apply Prod.ext
  · funext j
    exact basisVector_of_ne j.property
  · exact basisVector_self i

/-- A direction other than the integrated one is a pure parameter direction. -/
theorem coordinateSplit_basis_of_ne (i j : Fin 3) (h : j ≠ i) :
    coordinateSplit i (basisVector j) =
      ((coordinateSplit i (basisVector j)).1, 0) := by
  apply Prod.ext
  · rfl
  · exact basisVector_of_ne h.symm

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
