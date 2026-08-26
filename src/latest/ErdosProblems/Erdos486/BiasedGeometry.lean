import ErdosProblems.Erdos486.BiasedSkeleton
import ErdosProblems.Erdos486.BlockInterface

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! # Dyadic geometry supplied by the biased arithmetic skeleton -/

namespace Erdos486

/-- Any subset selector produces valid global dyadic geometry above an
arbitrary cutoff at least `400`.  The cutoff can therefore be enlarged until
the summable footprint tail is below the global error budget. -/
noncomputable def biasedGeometryAbove (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (selector : (j : ℕ) → ℕ → Finset (Fin (biasedK j))) :
    DyadicBlockGeometry where
  firstScale := firstScale
  endpoints := biasedEndpoints
  modulus j m := biasedModulus j (selector j m)
  endpoint_lower hj hm := by
    simpa [dyadicNat] using (biasedEndpoint_bounds (hfirst.trans hj) hm).1
  endpoint_upper hj hm := by
    simpa [dyadicNat] using (biasedEndpoint_bounds (hfirst.trans hj) hm).2
  modulus_pos _ _ := biasedModulus_pos _ _
  modulus_lower hj _ := by
    simpa [dyadicNat] using (biasedModulus_bounds (hfirst.trans hj) _).1
  modulus_upper hj _ := by
    simpa [dyadicNat] using (biasedModulus_bounds (hfirst.trans hj) _).2
  enough_endpoints hj := by
    simpa [dyadicNat] using biasedEndpoints_enough (hfirst.trans hj)

/-- The basic geometry with the explicit arithmetic cutoff `400`. -/
noncomputable def biasedGeometry
    (selector : (j : ℕ) → ℕ → Finset (Fin (biasedK j))) :
    DyadicBlockGeometry :=
  biasedGeometryAbove 400 le_rfl selector

end Erdos486
