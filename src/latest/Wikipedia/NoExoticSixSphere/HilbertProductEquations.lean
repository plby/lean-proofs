import Wikipedia.NoExoticSixSphere.OrthogonalRightInverseProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentials of actual paired ambient equations

The defining functions themselves are paired, and the resulting derivative
and canonical orthogonal right inverse retain their ordered block formulas.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.HilbertProduct

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def equations (f : E → F) (g : G → H) (x : WithLp 2 (E × G)) : WithLp 2 (F × H) :=
  WithLp.toLp 2 (f x.fst, g x.snd)

theorem hasFDerivAt_equations {f : E → F} {g : G → H}
    {D : E →L[ℝ] F} {A : G →L[ℝ] H} {x : WithLp 2 (E × G)}
    (hf : HasFDerivAt f D x.fst) (hg : HasFDerivAt g A x.snd) :
    HasFDerivAt (equations f g) (map D A) x :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F H).symm.hasFDerivAt.comp x
    ((HasFDerivAt.prodMap (x.fst, x.snd) hf hg).comp x
      (WithLp.prodContinuousLinearEquiv 2 ℝ E G).hasFDerivAt)

theorem fderiv_equations {f : E → F} {g : G → H} {x : WithLp 2 (E × G)}
    (hf : DifferentiableAt ℝ f x.fst) (hg : DifferentiableAt ℝ g x.snd) :
    fderiv ℝ (equations f g) x = map (fderiv ℝ f x.fst) (fderiv ℝ g x.snd) :=
  (hasFDerivAt_equations hf.hasFDerivAt hg.hasFDerivAt).fderiv

theorem contDiff_equations {f : E → F} {g : G → H}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (equations f g) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F H).symm.contDiff.comp
    ((hf.prodMap hg).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E G).contDiff)

end NoExoticSixSphere.HilbertProduct
