import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterBasic

/-!
# Genuine joint and base differentials of a smooth torus family

The full derivative of the actual joint lift is invariant under changes
of the real torus representative. It therefore descends to the original
base times the torus. Joint continuity follows from smoothness of the
lifted derivative and the original product quotient map.
-/

noncomputable section

open Function TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*}

/-- Extend the original family by zero only outside its open base. -/
def ambientValue (g : U × UnitAddTorus d → ℂ) (x : ℂ × UnitAddTorus d) : ℂ := by
  classical
  exact if hx : x.1 ∈ U then g (⟨x.1, hx⟩, x.2) else 0

@[simp] theorem ambientValue_apply (g : U × UnitAddTorus d → ℂ)
    (b : U) (t : UnitAddTorus d) :
    ambientValue g ((b : ℂ), t) = g (b, t) := by
  simp only [ambientValue, dif_pos b.property]

/-- The lifted and quotient-valued ambient representatives are the same actual function. -/
theorem ambientLift_eq_ambientValue (g : U × UnitAddTorus d → ℂ)
    (z : ℂ) (x : d → ℝ) :
    ambientLift g (z, x) = ambientValue g (z, torusQuotient x) := rfl

/-- Vertical lattice shifts leave the entire ambient lift unchanged, including off the base. -/
theorem ambientLift_add_vertical (g : U × UnitAddTorus d → ℂ)
    (z : ℂ) (x v : d → ℝ) (hv : torusQuotient v = 0) :
    ambientLift g (z, x + v) = ambientLift g (z, x) := by
  simp only [ambientLift, torusQuotient_add, hv, add_zero]

variable [Fintype d]

namespace SmoothFamily

variable (f : SmoothFamily U d)

/-- The full real derivative, not merely its vertical restriction, is independent of the lift. -/
theorem ambientLift_fderiv_eq (z : ℂ) (x y : d → ℝ)
    (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (ambientLift f) (z, x) = fderiv ℝ (ambientLift f) (z, y) := by
  have hshift : (fun p : ℂ × (d → ℝ) => ambientLift f (p + (0, y - x))) =
      ambientLift f := by
    funext p
    change ambientLift f (p.1 + 0, p.2 + (y - x)) = ambientLift f p
    rw [add_zero]
    exact ambientLift_add_vertical f p.1 p.2 (y - x)
      (by rw [torusQuotient_sub, hxy, sub_self])
  calc
    fderiv ℝ (ambientLift f) (z, x) =
        fderiv ℝ (fun p : ℂ × (d → ℝ) => ambientLift f (p + (0, y - x))) (z, x) := by
      rw [hshift]
    _ = fderiv ℝ (ambientLift f) ((z, x) + (0, y - x)) :=
      fderiv_comp_add_right (0, y - x)
    _ = fderiv ℝ (ambientLift f) (z, y) := by
      congr 1
      apply Prod.ext
      · simp
      · change x + (y - x) = y
        abel

/-- The actual descended full derivative in joint real base and torus coordinates. -/
def jointDifferential (p : U × UnitAddTorus d) : (ℂ × (d → ℝ)) →L[ℝ] ℂ :=
  fderiv ℝ (ambientLift f) ((p.1 : ℂ), surjInv torusQuotient_surjective p.2)

/-- Evaluating at any real lift gives exactly the original joint derivative. -/
@[simp] theorem jointDifferential_lift (b : U) (x : d → ℝ) :
    f.jointDifferential (b, torusQuotient x) = fderiv ℝ (ambientLift f) ((b : ℂ), x) := by
  unfold jointDifferential
  rw [f.ambientLift_fderiv_eq (b : ℂ) _ x
    (surjInv_eq torusQuotient_surjective (torusQuotient x))]

/-- The original smooth-lift hypothesis supplies smoothness of its full derivative. -/
theorem jointLift_fderiv_contDiffOn :
    ContDiffOn ℝ ∞ (fderiv ℝ (ambientLift f)) (Smooth.baseProductDomain U (d → ℝ)) :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen
    (Smooth.baseProductDomain_isOpen U (d → ℝ))).mp f.smooth_lift).2

/-- Joint continuity of the descended derivative is a consequence, not part of the family data. -/
theorem jointDifferential_continuous : Continuous f.jointDifferential := by
  apply familyQuotient_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun x : U × (d → ℝ) =>
      fderiv ℝ (ambientLift f) ((x.1 : ℂ), x.2)) :=
    f.jointLift_fderiv_contDiffOn.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun x => x.1.property)
  simpa only [Function.comp_def, familyQuotient, jointDifferential_lift] using h

/-- Restrict the actual joint differential to the real base directions. -/
def baseDifferential (p : U × UnitAddTorus d) : ℂ →L[ℝ] ℂ :=
  (f.jointDifferential p).comp (ContinuousLinearMap.inl ℝ ℂ (d → ℝ))

@[simp] theorem baseDifferential_apply (p : U × UnitAddTorus d) (v : ℂ) :
    f.baseDifferential p v = f.jointDifferential p (v, 0) := rfl

@[simp] theorem baseDifferential_lift (b : U) (x : d → ℝ) :
    f.baseDifferential (b, torusQuotient x) =
      (fderiv ℝ (ambientLift f) ((b : ℂ), x)).comp
        (ContinuousLinearMap.inl ℝ ℂ (d → ℝ)) := by
  rw [baseDifferential, jointDifferential_lift]

/-- The genuine base differential varies jointly continuously over the base and torus. -/
theorem baseDifferential_continuous : Continuous f.baseDifferential :=
  f.jointDifferential_continuous.clm_comp continuous_const

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
