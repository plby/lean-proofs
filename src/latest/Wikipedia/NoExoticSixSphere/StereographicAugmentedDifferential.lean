import Wikipedia.NoExoticSixSphere.StereographicConformalDifferential
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# The global augmented differential of the actual compactification

Adjoin the actual radial sphere vector to the actual inverse-chart
derivative. This gives a continuous family of linear equivalences,
with continuous inverses, over the entire original Euclidean space.
The final coordinates use the ordinary last-axis stabilization order.
-/

noncomputable section

namespace NoExoticSixSphere.StereographicEquator

def augmentedEquiv (n : ℕ) (x : V n) : (V n × ℝ) ≃L[ℝ] V (n + 1) :=
  (((LinearEquiv.smulOfNeZero ℝ (V n) (finiteScale n x)
    (finiteScale_pos n x).ne').toContinuousLinearEquiv).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
        ((stabilizedEquiv n).trans (finiteReflection n x).toContinuousLinearEquiv)

theorem augmentedEquiv_apply (n : ℕ) (x : V n) (p : V n × ℝ) :
    augmentedEquiv n x p = fderiv ℝ (finiteAmbient n) x p.1 + p.2 • finiteAmbient n x := by
  change finiteReflection n x (lift n (finiteScale n x • p.1) +
    p.2 • (spherePole n).val) = _
  rw [lift_smul, map_add, map_smul, map_smul, finiteReflection_pole,
    fderiv_finiteAmbient_apply]

theorem augmentedEquiv_symm_apply (n : ℕ) (x : V n) (w : V (n + 1)) :
    (augmentedEquiv n x).symm w =
      ((finiteScale n x)⁻¹ • project n (finiteReflection n x w),
        inner ℝ (spherePole n).val (finiteReflection n x w)) := by
  change ((finiteScale n x)⁻¹ • ((stabilizedEquiv n).symm
      ((finiteReflection n x).symm w)).1,
    ((stabilizedEquiv n).symm ((finiteReflection n x).symm w)).2) = _
  rw [finiteReflection_symm, stabilizedEquiv_symm_apply]

theorem continuous_augmentedEquiv (n : ℕ) :
    Continuous (fun x ↦ (augmentedEquiv n x).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro p
  change Continuous (fun x : V n ↦ augmentedEquiv n x p)
  simp_rw [augmentedEquiv_apply, fderiv_finiteAmbient_apply]
  exact ((continuous_finiteScale n).smul
    ((continuous_finiteReflection n).clm_apply continuous_const)).add
      ((contDiff_finiteAmbient n).continuous.const_smul p.2)

theorem continuous_augmentedEquiv_symm (n : ℕ) :
    Continuous (fun x ↦ (augmentedEquiv n x).symm.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro w
  change Continuous (fun x : V n ↦ (augmentedEquiv n x).symm w)
  simp_rw [augmentedEquiv_symm_apply]
  have hR := (continuous_finiteReflection n).clm_apply (continuous_const (y := w))
  exact (((continuous_finiteScale n).inv₀ (fun x ↦ (finiteScale_pos n x).ne')).smul
    ((project n).continuous.comp hR)).prodMk
      ((innerSL ℝ (spherePole n).val).continuous.comp hR)

def augmentedSourceCoordinates (n : ℕ) : V (n + 1) ≃L[ℝ] (V n × ℝ) :=
  (EuclideanTailCoordinates.split n).toContinuousLinearEquiv.trans
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V n)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ (V n)))

def augmentedCoordinates (n : ℕ) (x : V n) : V (n + 1) ≃L[ℝ] V (n + 1) :=
  (augmentedSourceCoordinates n).trans (augmentedEquiv n x)

theorem augmentedCoordinates_apply (n : ℕ) (x : V n) (v : V (n + 1)) :
    augmentedCoordinates n x v =
      fderiv ℝ (finiteAmbient n) x (EuclideanTailCoordinates.split n v).snd +
        (EuclideanTailCoordinates.split n v).fst • finiteAmbient n x :=
  augmentedEquiv_apply n x (augmentedSourceCoordinates n v)

theorem continuous_augmentedCoordinates (n : ℕ) :
    Continuous (fun x ↦ (augmentedCoordinates n x).toContinuousLinearMap) := by
  change Continuous (fun x ↦ (augmentedEquiv n x).toContinuousLinearMap.comp
    (augmentedSourceCoordinates n).toContinuousLinearMap)
  exact (continuous_augmentedEquiv n).clm_comp continuous_const

theorem continuous_augmentedCoordinates_symm (n : ℕ) :
    Continuous (fun x ↦ (augmentedCoordinates n x).symm.toContinuousLinearMap) := by
  change Continuous (fun x ↦ (augmentedSourceCoordinates n).symm.toContinuousLinearMap.comp
    (augmentedEquiv n x).symm.toContinuousLinearMap)
  exact continuous_const.clm_comp (continuous_augmentedEquiv_symm n)

end NoExoticSixSphere.StereographicEquator
