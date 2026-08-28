import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology

/-!
# The literal zero-γ fibre in the real period torus

The first additive-circle coordinate is taken through the actual standard
lattice quotient.  Its zero fibre is homeomorphic to the product of the
remaining three circles.  Inserting zero in the first circle coordinate
gives a genuine continuous retraction, with exact formulas on the original
standard-lattice representatives.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open PeriodTorusHigherHomology

/-- The actual first circle coordinate of the real standard-lattice quotient. -/
def fibreGamma : C(RealTorus₄, AddCircle (1 : ℝ)) :=
  ⟨fun x => flatTorusCircleHomeomorph x 0,
    (continuous_apply 0).comp flatTorusCircleHomeomorph.continuous⟩

@[simp] theorem fibreGamma_mkQ (x : RealPlane₄) :
    fibreGamma (standardLattice.mkQ x) = (x 0 : AddCircle (1 : ℝ)) := by
  change flatTorusCircleHomeomorph (standardLattice.mkQ x) 0 = _
  rw [flatTorusCircleHomeomorph_mkQ]
  rfl

@[simp] theorem fibreGamma_zero : fibreGamma 0 = 0 := by
  simpa only [map_zero, Pi.zero_apply, AddCircle.coe_zero] using
    fibreGamma_mkQ (0 : RealPlane₄)

/-- The actual zero fibre, with the subtype topology of the original real torus. -/
abbrev Fibre := {x : RealTorus₄ // fibreGamma x = 0}

/-- The literal inclusion, not a map transported from a substitute fibre. -/
def fibreInclusion : C(Fibre, RealTorus₄) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem fibreInclusion_apply (x : Fibre) : fibreInclusion x = x.val := rfl

theorem fibreInclusion_injective : Function.Injective fibreInclusion :=
  Subtype.val_injective

/-- Deleting the first coordinate identifies this literal fibre with an actual three-torus. -/
def fibreHomeomorph : Fibre ≃ₜ ProductTorus 3 where
  toFun x i := flatTorusCircleHomeomorph x.val i.succ
  invFun y := ⟨flatTorusCircleHomeomorph.symm (Fin.cons 0 y), by
    change flatTorusCircleHomeomorph
      (flatTorusCircleHomeomorph.symm (Fin.cons 0 y)) 0 = 0
    rw [Homeomorph.apply_symm_apply]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply flatTorusCircleHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact x.property.symm
    · rfl
  right_inv y := by
    funext i
    exact congrFun (flatTorusCircleHomeomorph.apply_symm_apply (Fin.cons 0 y)) i.succ
  continuous_toFun := continuous_pi fun i =>
    (continuous_apply i.succ).comp
      (flatTorusCircleHomeomorph.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact flatTorusCircleHomeomorph.symm.continuous.comp
      ((productTorusSuccHomeomorph 3).symm.continuous.comp
        (continuous_const.prodMk continuous_id))

@[simp] theorem fibreHomeomorph_apply (x : Fibre) (i : Fin 3) :
    fibreHomeomorph x i = flatTorusCircleHomeomorph x.val i.succ := rfl

/-- The inverse inserts a genuine zero circle coordinate before taking
the original quotient inverse. -/
@[simp] theorem fibreHomeomorph_symm_apply (y : ProductTorus 3) :
    (fibreHomeomorph.symm y).val = flatTorusCircleHomeomorph.symm (Fin.cons 0 y) := rfl

/-- A point of the literal fibre specified by a real representative
in the last three coordinates. -/
def fibreMkQ (x : Fin 3 → ℝ) : Fibre :=
  ⟨standardLattice.mkQ (Fin.cons 0 x), by rw [fibreGamma_mkQ]; rfl⟩

@[simp] theorem fibreMkQ_val (x : Fin 3 → ℝ) :
    (fibreMkQ x).val = standardLattice.mkQ (Fin.cons 0 x) := rfl

/-- Native representatives reduce coordinate by coordinate on the actual three-torus. -/
@[simp] theorem fibreHomeomorph_mkQ (x : Fin 3 → ℝ) :
    fibreHomeomorph (fibreMkQ x) = coordinateProjection 3 x := by
  funext i
  change flatTorusCircleHomeomorph (standardLattice.mkQ (Fin.cons 0 x)) i.succ = _
  rw [flatTorusCircleHomeomorph_mkQ]
  rfl

/-- The inverse formula is equality in the original standard-lattice quotient. -/
theorem fibreHomeomorph_symm_coordinateProjection (x : Fin 3 → ℝ) :
    (fibreHomeomorph.symm (coordinateProjection 3 x)).val =
      standardLattice.mkQ (Fin.cons 0 x) := by
  have h : fibreHomeomorph.symm (coordinateProjection 3 x) = fibreMkQ x := by
    apply fibreHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, fibreHomeomorph_mkQ]
  exact congrArg Subtype.val h

/-- Setting the first circle coordinate to zero gives a genuine retraction to the literal fibre. -/
def fibreRetraction : C(RealTorus₄, Fibre) :=
  ⟨fun x => fibreHomeomorph.symm (fun i => flatTorusCircleHomeomorph x i.succ),
    fibreHomeomorph.symm.continuous.comp
      (continuous_pi fun i => (continuous_apply i.succ).comp
        flatTorusCircleHomeomorph.continuous)⟩

@[simp] theorem fibreRetraction_val (x : RealTorus₄) :
    (fibreRetraction x).val =
      flatTorusCircleHomeomorph.symm
        (Fin.cons 0 (fun i => flatTorusCircleHomeomorph x i.succ)) := rfl

/-- The retraction fixes every point of the actual zero fibre. -/
@[simp] theorem fibreRetraction_inclusion (x : Fibre) :
    fibreRetraction (fibreInclusion x) = x :=
  fibreHomeomorph.symm_apply_apply x

theorem fibreRetraction_comp_inclusion :
    fibreRetraction.comp fibreInclusion = ContinuousMap.id Fibre :=
  ContinuousMap.ext fibreRetraction_inclusion

/-- On original real representatives, the retraction literally replaces
the first coordinate by zero. -/
theorem fibreRetraction_mkQ (x : RealPlane₄) :
    (fibreRetraction (standardLattice.mkQ x)).val =
      standardLattice.mkQ (Fin.cons 0 (fun i => x i.succ)) := by
  change (fibreHomeomorph.symm
    (fun i => flatTorusCircleHomeomorph (standardLattice.mkQ x) i.succ)).val = _
  rw [flatTorusCircleHomeomorph_mkQ]
  exact fibreHomeomorph_symm_coordinateProjection (fun i => x i.succ)

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
