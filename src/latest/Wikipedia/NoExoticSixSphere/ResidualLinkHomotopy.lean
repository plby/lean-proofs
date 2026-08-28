import Wikipedia.NoExoticSixSphere.ResidualLinkOperators

/-!
# Deforming the genuine local operator link to a constant-leading-block model

First remove the actual source and target shears. Then contract only the
argument of the leading block inside the residual-coordinate ball, retaining
the original nonzero residual column on the link. Both homotopies stay in
the actual injective-operator space.
-/

noncomputable section

open Set Function Metric unitInterval

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne CorankOneEuclidean Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D : X → BlockMap (Vector 2) (Vector 4)}

theorem Data.continuous_shearFamily (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Continuous (fun p : I × Sphere 3 ↦ deformation (p.1 : ℝ) (D (d.link ε p.2))) := by
  have hparam : Continuous (fun p : I × Sphere 3 ↦ ((p.1 : ℝ), D (d.link ε p.2))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((hD.comp (d.continuous_link hε hball)).comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hd : ContinuousAt
      (fun z : ℝ × BlockMap (Vector 2) (Vector 4) ↦ CorankOne.deformation z.1 z.2)
      ((p.1 : ℝ), D (d.link ε p.2)) :=
    (CorankOne.contDiffAt_deformation (p.1 : ℝ) (D (d.link ε p.2))
      (d.leading_link hε hball p.2)).continuousAt
  exact hd.comp (f := fun z : I × Sphere 3 ↦ ((z.1 : ℝ), D (d.link ε z.2)))
    (x := p) hparam.continuousAt

def Data.shearSphere (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(I × Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun p ↦ deformation (p.1 : ℝ) (D (d.link ε p.2))) (by
    intro p
    apply injective_deformation _ _ (d.leading_link hε hball p.2)
    rw [d.residual_link hε hball p.2]
    exact scaledParameter_ne_zero hε p.2) (d.continuous_shearFamily hD hε hball)

def Data.shearHomotopy (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (d.linkOperators hD hε hball).Homotopy (d.residualOperators hD hε hball) where
  toFun := d.shearSphere hD hε hball
  continuous_toFun := (d.shearSphere hD hε hball).continuous
  map_zero_left q := by
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean (deformation 0 (D (d.link ε q))) =
      CorankOneEuclidean.toEuclidean (D (d.link ε q))
    rw [deformation_zero _ (d.leading_link hε hball q)]
  map_one_left q := by
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean (deformation 1 (D (d.link ε q))) =
      CorankOneEuclidean.toEuclidean (diagonal (leading (D (d.link ε q))) (scaledParameter ε q))
    rw [deformation_one, d.residual_link hε hball q]

def Data.leadingSphere (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(I × Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun p ↦ diagonal (leading (D (d.radial ε p))) (scaledParameter ε p.2))
    (fun p ↦ injective_diagonal _ (d.leading_radial hε hball p).injective _
      (scaledParameter_ne_zero hε p.2))
    ((contDiff_diagonal (E := Vector 2) (F := Vector 4)).continuous.comp
      (((contDiff_leading (E := Vector 2) (F := Vector 4)).continuous.comp
        (hD.comp (d.continuous_radial hε hball))).prodMk
          ((continuous_scaledParameter ε).comp continuous_snd)))

def Data.leadingHomotopy (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (d.residualOperators hD hε hball).Homotopy (d.centerOperators hε hball) where
  toFun := d.leadingSphere hD hε hball
  continuous_toFun := (d.leadingSphere hD hε hball).continuous
  map_zero_left q := by
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean
      (diagonal (leading (D (d.radial ε (0, q)))) (scaledParameter ε q)) = _
    rw [d.radial_zero]
    rfl
  map_one_left q := by
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean
      (diagonal (leading (D (d.radial ε (1, q)))) (scaledParameter ε q)) = _
    rw [d.radial_one]
    rfl

theorem Data.link_homotopic_center (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (d.linkOperators hD hε hball).Homotopic (d.centerOperators hε hball) :=
  ⟨(d.shearHomotopy hD hε hball).trans (d.leadingHomotopy hD hε hball)⟩

theorem Data.link_parity_eq_center (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (d.linkOperators hD hε hball) =
      Monomorphism.sphereParity 1 (d.centerOperators hε hball) :=
  Monomorphism.sphereParity_homotopic 1 (d.link_homotopic_center hD hε hball)

end NoExoticSixSphere.ResidualCoordinates
