import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalCoordinates

/-!
# Cauchy–Green in a literal coordinate

Each operator integrates the original function along one complex coordinate,
with the other two coordinates fixed.  The auxiliary split only identifies
this exact integral with the previously verified parameterized integral.
-/

noncomputable section

open Complex Filter Set
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

open PeriodTorusLineBundleClassification

/-- The actual Cauchy–Green integral in coordinate `i`. -/
def coordinateCauchy (i : Fin 3) (f : Coordinates → ℂ) (q : Coordinates) : ℂ :=
  HolomorphicCousin.cauchyGreen (fun z => f (Function.update q i z)) (q i)

/-- The same function, expressed with coordinate `i` separated from its
remaining complex parameters. -/
def splitFunction (i : Fin 3) (f : Coordinates → ℂ) :
    CoordinateParameter i × ℂ → ℂ := f ∘ (coordinateSplit i).symm

@[simp] theorem splitFunction_apply (i : Fin 3) (f : Coordinates → ℂ)
    (p : CoordinateParameter i × ℂ) :
    splitFunction i f p = f ((coordinateSplit i).symm p) := rfl

@[simp] theorem splitFunction_split (i : Fin 3) (f : Coordinates → ℂ)
    (q : Coordinates) : splitFunction i f (coordinateSplit i q) = f q := by
  simp only [splitFunction_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem contDiff_splitFunction (i : Fin 3) {n : ℕ∞}
    {f : Coordinates → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (splitFunction i f) :=
  hf.comp ((coordinateSplit i).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff

theorem splitFunction_support (i : Fin 3) {f : Coordinates → ℂ} {k : Set ℂ}
    (hfk : ∀ q, q i ∉ k → f q = 0) :
    ∀ p z, z ∉ k → splitFunction i f (p, z) = 0 := by
  intro p z hz
  apply hfk
  simpa only [coordinateSplit_symm_self] using hz

/-- Identification with the genuine parameter-dependent integral. -/
theorem coordinateCauchy_eq (i : Fin 3) (f : Coordinates → ℂ) :
    coordinateCauchy i f = cauchySecond (splitFunction i f) ∘ coordinateSplit i := by
  funext q
  dsimp only [coordinateCauchy, Function.comp_apply, cauchySecond]
  rw [show (coordinateSplit i q).2 = q i from rfl]
  congr 1
  funext z
  exact (congrArg f (coordinateSplit_symm_update i q z)).symm

/-- Directional derivatives transform by the actual complex linear split. -/
theorem coordinateDbar_comp_split (i j : Fin 3)
    {g : CoordinateParameter i × ℂ → ℂ} {q : Coordinates}
    (hg : DifferentiableAt ℝ g (coordinateSplit i q)) :
    coordinateDbar j (g ∘ coordinateSplit i) q =
      HolomorphicDolbeaultThree.dbar g (coordinateSplit i q)
        (coordinateSplit i (basisVector j)) :=
  dbar_complex_linear_comp (coordinateSplit i).toContinuousLinearMap hg (basisVector j)

/-- The parameter derivative of the split function is the original derivative
in a different coordinate. -/
theorem parameterDbar_splitFunction (i j : Fin 3) (h : j ≠ i)
    {f : Coordinates → ℂ} {p : CoordinateParameter i × ℂ}
    (hf : DifferentiableAt ℝ f ((coordinateSplit i).symm p)) :
    Cauchy.parameterDbar (coordinateSplit i (basisVector j)).1 (splitFunction i f) p =
      coordinateDbar j f ((coordinateSplit i).symm p) := by
  rw [Cauchy.parameterDbar_eq_dbar]
  change HolomorphicDolbeaultThree.dbar (f ∘ (coordinateSplit i).symm) p _ = _
  have he : HolomorphicDolbeaultThree.dbar (f ∘ (coordinateSplit i).symm) p
      ((coordinateSplit i (basisVector j)).1, 0) =
      HolomorphicDolbeaultThree.dbar f ((coordinateSplit i).symm p)
        ((coordinateSplit i).symm ((coordinateSplit i (basisVector j)).1, 0)) :=
    dbar_complex_linear_comp (coordinateSplit i).symm.toContinuousLinearMap hf _
  rw [he]
  rw [← coordinateSplit_basis_of_ne i j h]
  simp only [ContinuousLinearEquiv.symm_apply_apply, coordinateDbar]

/-- The integrated-coordinate derivative of a split function is the original
coordinate derivative. -/
theorem lastDbar_splitFunction (i : Fin 3) {f : Coordinates → ℂ}
    {p : CoordinateParameter i × ℂ}
    (hf : DifferentiableAt ℝ f ((coordinateSplit i).symm p)) :
    Cauchy.lastDbar (splitFunction i f) p =
      coordinateDbar i f ((coordinateSplit i).symm p) := by
  have hs : DifferentiableAt ℝ (splitFunction i f) p :=
    hf.comp p
      (((coordinateSplit i).symm.toContinuousLinearMap.restrictScalars ℝ).differentiableAt)
  rw [Cauchy.lastDbar_eq_dbar hs]
  change HolomorphicDolbeaultThree.dbar (f ∘ (coordinateSplit i).symm) p _ = _
  have he : HolomorphicDolbeaultThree.dbar (f ∘ (coordinateSplit i).symm) p (0, 1) =
      HolomorphicDolbeaultThree.dbar f ((coordinateSplit i).symm p)
        ((coordinateSplit i).symm (0, 1)) :=
    dbar_complex_linear_comp (coordinateSplit i).symm.toContinuousLinearMap hf _
  rw [he]
  rw [← coordinateSplit_basis_self i]
  simp only [ContinuousLinearEquiv.symm_apply_apply, coordinateDbar]

/-- This coordinate derivative is also the literal one-variable slice
derivative; the equality follows from the chain rule, not a new definition. -/
theorem coordinateDbar_slice (i : Fin 3) {f : Coordinates → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f q) :
    coordinateDbar i f q =
      HolomorphicCousin.dbar (fun z => f (Function.update q i z)) (q i) := by
  have hs : DifferentiableAt ℝ f ((coordinateSplit i).symm (coordinateSplit i q)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  have he := lastDbar_splitFunction i hs
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  rw [← he]
  dsimp only [Cauchy.lastDbar]
  rw [show (coordinateSplit i q).2 = q i from rfl]
  congr 1
  funext z
  exact congrArg f (coordinateSplit_symm_update i q z)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
