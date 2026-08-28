import Wikipedia.NoExoticSixSphere.StabilizedResidualModel
import Wikipedia.NoExoticSixSphere.ResidualBallChart

/-!
# The actual stabilized residual link does not extend

The first homotopy removes the original Schur shears. The second contracts
the leading block through the actual residual-coordinate ball, retaining
the nonzero residual column on the link. The resulting constant model has
the proved nonzero obstruction. All maps remain actual injective operators.
-/

noncomputable section

open Set Function Metric unitInterval

namespace NoExoticSixSphere.StabilizedResidual

open GLOrthonormalization CorankOne Stiefel ResidualCoordinates DiskBoundary

variable {k : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D : X → BlockMap (Vector (k + 2)) (Vector 4)}

theorem leading_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    (leading (D (d.link ε q))).IsInvertible :=
  d.leading_inverse (hball (scaledParameter_mem_closedBall hε q))

theorem leading_center (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (leading (D (d.coord.symm 0))).IsInvertible :=
  d.leading_inverse (hball (Metric.mem_closedBall_self hε.le))

theorem injective_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    Injective (D (d.link ε q)) := by
  apply (injective_iff_residual_ne_zero _ (leading_link d hε hball q)).mpr
  rw [d.residual_link hε hball q]
  exact scaledParameter_ne_zero hε q

def linkOperators (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun q ↦ D (d.link ε q)) (injective_link d hε hball)
    (hD.comp (d.continuous_link hε hball))

def residualOperators (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun q ↦ diagonal (leading (D (d.link ε q))) (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ (leading_link d hε hball q).injective _
      (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
      (((contDiff_leading (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
        (hD.comp (d.continuous_link hε hball))).prodMk (continuous_scaledParameter ε)))

def centerOperators (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun q ↦ diagonal (leading (D (d.coord.symm 0))) (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ (leading_center d hε hball).injective _
      (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
      (continuous_const.prodMk (continuous_scaledParameter ε)))

theorem continuous_shearFamily (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Continuous (fun p : I × Sphere 3 ↦ deformation (p.1 : ℝ) (D (d.link ε p.2))) := by
  have hparam : Continuous (fun p : I × Sphere 3 ↦ ((p.1 : ℝ), D (d.link ε p.2))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((hD.comp (d.continuous_link hε hball)).comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hd := (CorankOne.contDiffAt_deformation (p.1 : ℝ) (D (d.link ε p.2))
    (leading_link d hε hball p.2)).continuousAt
  exact hd.comp (f := fun z : I × Sphere 3 ↦ ((z.1 : ℝ), D (d.link ε z.2)))
    (x := p) hparam.continuousAt

def shearSphere (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(I × Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun p ↦ deformation (p.1 : ℝ) (D (d.link ε p.2))) (by
    intro p
    apply injective_deformation _ _ (leading_link d hε hball p.2)
    rw [d.residual_link hε hball p.2]
    exact scaledParameter_ne_zero hε p.2) (continuous_shearFamily d hD hε hball)

def shearHomotopy (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (linkOperators d hD hε hball).Homotopy (residualOperators d hD hε hball) where
  toFun := shearSphere d hD hε hball
  continuous_toFun := (shearSphere d hD hε hball).continuous
  map_zero_left q := by
    apply Subtype.ext
    change toEuclidean k (deformation 0 (D (d.link ε q))) = toEuclidean k (D (d.link ε q))
    rw [deformation_zero _ (leading_link d hε hball q)]
  map_one_left q := by
    apply Subtype.ext
    change toEuclidean k (deformation 1 (D (d.link ε q))) =
      toEuclidean k (diagonal (leading (D (d.link ε q))) (scaledParameter ε q))
    rw [deformation_one, d.residual_link hε hball q]

def leadingSphere (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(I × Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun p ↦ diagonal (leading (D (d.radial ε p))) (scaledParameter ε p.2))
    (fun p ↦ injective_diagonal _ (d.leading_radial hε hball p).injective _
      (scaledParameter_ne_zero hε p.2))
    ((contDiff_diagonal (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
      (((contDiff_leading (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
        (hD.comp (d.continuous_radial hε hball))).prodMk
          ((continuous_scaledParameter ε).comp continuous_snd)))

def leadingHomotopy (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (residualOperators d hD hε hball).Homotopy (centerOperators d hε hball) where
  toFun := leadingSphere d hD hε hball
  continuous_toFun := (leadingSphere d hD hε hball).continuous
  map_zero_left q := by
    apply Subtype.ext
    change toEuclidean k
      (diagonal (leading (D (d.radial ε (0, q)))) (scaledParameter ε q)) = _
    rw [d.radial_zero]
    rfl
  map_one_left q := by
    apply Subtype.ext
    change toEuclidean k
      (diagonal (leading (D (d.radial ε (1, q)))) (scaledParameter ε q)) = _
    rw [d.radial_one]
    rfl

theorem link_homotopic_center (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (linkOperators d hD hε hball).Homotopic (centerOperators d hε hball) :=
  ⟨(shearHomotopy d hD hε hball).trans (leadingHomotopy d hD hε hball)⟩

theorem centerOperators_not_extends (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ¬ Extends (centerOperators d hε hball) := by
  obtain ⟨a, ha⟩ := leading_center d hε hball
  have he : centerOperators d hε hball = constantModel k a hε := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change toEuclidean k (diagonal (leading (D (d.coord.symm 0))) (scaledParameter ε q)) =
      toEuclidean k (diagonal a.toContinuousLinearMap (scaledParameter ε q))
    rw [← ha]
  rw [he]
  exact constantModel_not_extends k a hε

theorem linkOperators_not_extends (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ¬ Extends (linkOperators d hD hε hball) := by
  intro he
  exact centerOperators_not_extends d hε hball
    ((extends_homotopic_iff (link_homotopic_center d hD hε hball)).mp he)

end NoExoticSixSphere.StabilizedResidual
