import Wikipedia.NoExoticSixSphere.ResidualLink
import Wikipedia.NoExoticSixSphere.CorankOneDeformation
import Wikipedia.NoExoticSixSphere.InjectiveOperatorLinearCoordinates

/-!
# The original operator sphere and its residual models

These are continuous maps into the actual injective-operator space. The
original map evaluates the given operator family on the genuine inverse-
function link; the model retains its residual column and leading block.
-/

noncomputable section

open Set Function Metric

namespace NoExoticSixSphere.CorankOneEuclidean

open GLOrthonormalization CorankOne Stiefel

def monoMap {Y : Type*} [TopologicalSpace Y]
    (L : Y → BlockMap (Vector 2) (Vector 4)) (hi : ∀ y, Injective (L y))
    (hL : Continuous L) : C(Y, Monomorphism.Space 6 3) where
  toFun y := ⟨toEuclidean (L y), injective_toEuclidean (L y) (hi y)⟩
  continuous_toFun := (toEuclidean.continuous.comp hL).subtype_mk _

end NoExoticSixSphere.CorankOneEuclidean

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne CorankOneEuclidean Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D : X → BlockMap (Vector 2) (Vector 4)}

theorem Data.leading_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    (leading (D (d.link ε q))).IsInvertible :=
  d.leading_inverse (hball (scaledParameter_mem_closedBall hε q))

theorem Data.leading_center (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    (leading (D (d.coord.symm 0))).IsInvertible := by
  apply d.leading_inverse
  apply hball
  apply Metric.mem_closedBall.mpr
  simpa only [dist_self] using hε.le

theorem Data.injective_link (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) (q : Sphere 3) :
    Injective (D (d.link ε q)) := by
  apply (injective_iff_residual_ne_zero _ (d.leading_link hε hball q)).mpr
  rw [d.residual_link hε hball q]
  exact scaledParameter_ne_zero hε q

def Data.linkOperators (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun q ↦ D (d.link ε q)) (d.injective_link hε hball)
    (hD.comp (d.continuous_link hε hball))

def Data.residualOperators (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun q ↦ diagonal (leading (D (d.link ε q))) (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ (d.leading_link hε hball q).injective _
      (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector 2) (F := Vector 4)).continuous.comp
      (((contDiff_leading (E := Vector 2) (F := Vector 4)).continuous.comp
        (hD.comp (d.continuous_link hε hball))).prodMk (continuous_scaledParameter ε)))

def Data.centerOperators (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    C(Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun q ↦ diagonal (leading (D (d.coord.symm 0))) (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ (d.leading_center hε hball).injective _
      (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector 2) (F := Vector 4)).continuous.comp
      (continuous_const.prodMk (continuous_scaledParameter ε)))

end NoExoticSixSphere.ResidualCoordinates
