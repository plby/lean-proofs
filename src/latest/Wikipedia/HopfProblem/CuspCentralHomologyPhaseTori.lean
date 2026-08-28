import Wikipedia.HopfProblem.CuspCollapseFibreTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The actual compact phases in ordered product-torus coordinates

Each complex unit phase is converted to its unit-period additive circle.
The first two coordinates always come from the compact fibre torus; the
last coordinate is the radial frontier circle. The displayed projection
and section make this ordering explicit for homology naturality.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace PeriodTorusHigherHomology

/-- A complex unit phase, measured in positive unit-period coordinates. -/
def circleCoordinateHomeomorph : Circle ≃ₜ AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

@[simp] theorem circleCoordinateHomeomorph_symm_apply (x : AddCircle (1 : ℝ)) :
    circleCoordinateHomeomorph.symm x = AddCircle.toCircle x :=
  AddCircle.homeomorphCircle_apply one_ne_zero x

@[simp] theorem circleCoordinateHomeomorph_one : circleCoordinateHomeomorph 1 = 0 := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]

theorem circleCoordinateHomeomorph_mul (u v : Circle) :
    circleCoordinateHomeomorph (u * v) =
      circleCoordinateHomeomorph u + circleCoordinateHomeomorph v := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_add,
    ← circleCoordinateHomeomorph_symm_apply, ← circleCoordinateHomeomorph_symm_apply,
    Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

theorem circleCoordinateHomeomorph_zpow (u : Circle) (n : ℤ) :
    circleCoordinateHomeomorph (u ^ n) = n • circleCoordinateHomeomorph u := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zsmul,
    ← circleCoordinateHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

/-- The positive exponential circle parameter has the positive additive coordinate. -/
theorem circleCoordinateHomeomorph_exp (x : ℝ) :
    circleCoordinateHomeomorph (Circle.exp (2 * Real.pi * x)) =
      (x : AddCircle (1 : ℝ)) := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply,
    AddCircle.toCircle_apply_mk, div_one]

/-- The compact fibre torus has its literal two ordered circle coordinates. -/
def compactFibreTorusHomeomorph : CompactFibreTorus ≃ₜ ProductTorus 2 :=
  Homeomorph.piCongrRight (fun _ : Fin 2 => circleCoordinateHomeomorph)

@[simp] theorem compactFibreTorusHomeomorph_apply (u : CompactFibreTorus) (i : Fin 2) :
    compactFibreTorusHomeomorph u i = circleCoordinateHomeomorph (u i) := rfl

@[simp] theorem compactFibreTorusHomeomorph_symm_apply (x : ProductTorus 2) (i : Fin 2) :
    compactFibreTorusHomeomorph.symm x i = AddCircle.toCircle (x i) :=
  circleCoordinateHomeomorph_symm_apply (x i)

@[simp] theorem compactFibreTorusHomeomorph_one : compactFibreTorusHomeomorph 1 = 0 := by
  funext i
  exact circleCoordinateHomeomorph_one

theorem compactFibreTorusHomeomorph_mul (u v : CompactFibreTorus) :
    compactFibreTorusHomeomorph (u * v) =
      compactFibreTorusHomeomorph u + compactFibreTorusHomeomorph v := by
  funext i
  exact circleCoordinateHomeomorph_mul (u i) (v i)

theorem compactFibreTorusHomeomorph_zpow (u : CompactFibreTorus) (n : ℤ) :
    compactFibreTorusHomeomorph (u ^ n) = n • compactFibreTorusHomeomorph u := by
  funext i
  exact circleCoordinateHomeomorph_zpow (u i) n

theorem compactFibreTorusHomeomorph_exp (x : Fin 2 → ℝ) :
    compactFibreTorusHomeomorph (fun i => Circle.exp (2 * Real.pi * x i)) =
      coordinateProjection 2 x := by
  funext i
  exact circleCoordinateHomeomorph_exp (x i)

/-- Split the final coordinate, preserving the order of all earlier coordinates. -/
def productTorusLastHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ ProductTorus n × AddCircle (1 : ℝ) where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  continuous_toFun := (continuous_pi (fun i => continuous_apply i.castSucc)).prodMk
    (continuous_apply (Fin.last n))
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (continuous_snd : Continuous (fun p : ProductTorus n × AddCircle (1 : ℝ) => p.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        ((continuous_apply j).comp continuous_fst :
          Continuous (fun p : ProductTorus n × AddCircle (1 : ℝ) => p.1 j))

@[simp] theorem productTorusLastHomeomorph_apply (n : ℕ) (x : ProductTorus (n + 1)) :
    productTorusLastHomeomorph n x = (fun i => x i.castSucc, x (Fin.last n)) := rfl

@[simp] theorem productTorusLastHomeomorph_symm_apply (n : ℕ)
    (p : ProductTorus n × AddCircle (1 : ℝ)) :
    (productTorusLastHomeomorph n).symm p = Fin.snoc p.1 p.2 := rfl

/-- The compact fibre phases followed by the actual frontier circle form the ordered three-torus. -/
def fibreTorusCircleHomeomorph : (CompactFibreTorus × Circle) ≃ₜ ProductTorus 3 :=
  (compactFibreTorusHomeomorph.prodCongr circleCoordinateHomeomorph).trans
    (productTorusLastHomeomorph 2).symm

@[simp] theorem fibreTorusCircleHomeomorph_apply (p : CompactFibreTorus × Circle) :
    fibreTorusCircleHomeomorph p =
      Fin.snoc (compactFibreTorusHomeomorph p.1) (circleCoordinateHomeomorph p.2) := rfl

@[simp] theorem fibreTorusCircleHomeomorph_castSucc (p : CompactFibreTorus × Circle)
    (i : Fin 2) :
    fibreTorusCircleHomeomorph p i.castSucc = circleCoordinateHomeomorph (p.1 i) := by
  rw [fibreTorusCircleHomeomorph_apply, Fin.snoc_castSucc]
  rfl

@[simp] theorem fibreTorusCircleHomeomorph_last (p : CompactFibreTorus × Circle) :
    fibreTorusCircleHomeomorph p (Fin.last 2) = circleCoordinateHomeomorph p.2 := by
  rw [fibreTorusCircleHomeomorph_apply, Fin.snoc_last]

@[simp] theorem fibreTorusCircleHomeomorph_symm_fst (x : ProductTorus 3) (i : Fin 2) :
    (fibreTorusCircleHomeomorph.symm x).1 i = AddCircle.toCircle (x i.castSucc) :=
  circleCoordinateHomeomorph_symm_apply _

@[simp] theorem fibreTorusCircleHomeomorph_symm_snd (x : ProductTorus 3) :
    (fibreTorusCircleHomeomorph.symm x).2 = AddCircle.toCircle (x (Fin.last 2)) :=
  circleCoordinateHomeomorph_symm_apply _

/-- Forget precisely the last, radial-circle coordinate. -/
def productTorusFibreProjection : C(ProductTorus 3, ProductTorus 2) :=
  ⟨fun x i => x i.castSucc, continuous_pi (fun i => continuous_apply i.castSucc)⟩

/-- Add the identity in the last circle coordinate. -/
def productTorusFibreSection : C(ProductTorus 2, ProductTorus 3) :=
  ⟨fun x => (productTorusLastHomeomorph 2).symm (x, 0),
    (productTorusLastHomeomorph 2).symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩

@[simp] theorem productTorusFibreProjection_section (x : ProductTorus 2) :
    productTorusFibreProjection (productTorusFibreSection x) = x := by
  funext i
  change Fin.snoc (α := fun _ : Fin 3 => AddCircle (1 : ℝ)) x 0 i.castSucc = x i
  rw [Fin.snoc_castSucc]

/-- The actual compact-phase projection commutes with the ordered torus identification. -/
@[simp] theorem productTorusFibreProjection_homeomorph (p : CompactFibreTorus × Circle) :
    productTorusFibreProjection (fibreTorusCircleHomeomorph p) =
      compactFibreTorusHomeomorph p.1 := by
  funext i
  exact fibreTorusCircleHomeomorph_castSucc p i

theorem productTorusFibreProjection_natural :
    productTorusFibreProjection.comp
        (fibreTorusCircleHomeomorph : C(CompactFibreTorus × Circle, ProductTorus 3)) =
      (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)).comp
        ContinuousMap.fst := by
  apply ContinuousMap.ext
  exact productTorusFibreProjection_homeomorph

@[simp] theorem fibreTorusCircleHomeomorph_section (u : CompactFibreTorus) :
    fibreTorusCircleHomeomorph (u, 1) =
      productTorusFibreSection (compactFibreTorusHomeomorph u) := by
  change Fin.snoc (α := fun _ : Fin 3 => AddCircle (1 : ℝ))
      (compactFibreTorusHomeomorph u) (circleCoordinateHomeomorph 1) =
    Fin.snoc (α := fun _ : Fin 3 => AddCircle (1 : ℝ)) (compactFibreTorusHomeomorph u) 0
  rw [circleCoordinateHomeomorph_one]

end Wikipedia.HopfProblem.CuspCentralHomology
