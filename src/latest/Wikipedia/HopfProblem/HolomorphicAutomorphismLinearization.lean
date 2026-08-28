import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Coordinate changes of normalized displacements

The limit of small coordinate displacements transforms by the genuine
coordinate derivative. Both endpoints may move. This is the analytic
step needed to glue limits of automorphisms near the identity into an
actual tangent vector field.
-/

noncomputable section

open Asymptotics Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismLinearization

/-- Strict differentiability transports limits of rescaled differences,
even when both base points move. The rescaling may be arbitrary; only
the displayed convergence of the rescaled source difference is used. -/
theorem tendsto_scaled_difference
    {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {l : Filter α} {f : E → F} {L : E →L[ℂ] F} {x : E}
    (hf : HasStrictFDerivAt f L x)
    {a b : α → E} {c : α → ℂ} {v : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hv : Tendsto (fun n => c n • (a n - b n)) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (a n) - f (b n))) l (𝓝 (L v)) := by
  have ho : (fun n => f (a n) - f (b n) - L (a n - b n)) =o[l]
      (fun n => a n - b n) :=
    (hasStrictFDerivAt_iff_isLittleO.mp hf).comp_tendsto (ha.prodMk_nhds hb)
  have hs : (fun n => c n • (f (a n) - f (b n) - L (a n - b n))) =o[l]
      (fun n => c n • (a n - b n)) :=
    (isBigO_refl c l).smul_isLittleO ho
  have hz : Tendsto
      (fun n => c n • (f (a n) - f (b n) - L (a n - b n))) l (𝓝 0) :=
    (isLittleO_one_iff ℂ).mp (hs.trans_isBigO (hv.isBigO_one ℂ))
  have hL : Tendsto (fun n => L (c n • (a n - b n))) l (𝓝 (L v)) :=
    L.continuous.tendsto v |>.comp hv
  have hsum := hz.add hL
  have he : (fun n => c n • (f (a n) - f (b n) - L (a n - b n)) +
      L (c n • (a n - b n))) = (fun n => c n • (f (a n) - f (b n))) := by
    funext n
    rw [map_smul, smul_sub, sub_add_cancel]
  simpa only [he, zero_add] using hsum

end Wikipedia.HopfProblem.HolomorphicAutomorphismLinearization
