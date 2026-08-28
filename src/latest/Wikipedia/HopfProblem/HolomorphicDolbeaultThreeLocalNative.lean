import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalNativeCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalGerm

/-!
# Local primitives of actual native three-dimensional `(0,1)` forms

The input is a smooth field of actual real continuous linear covectors on
the original model `ℂ × ComplexPlane₂`.  Anti-linearity and closedness are
the genuine differential identities.  The three-coordinate Cauchy–Green
primitive therefore gives equality of the full native differential, not
merely selected coefficients of a replacement model.
-/

noncomputable section

open Complex Filter Set
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- The genuine degree-one local Dolbeault lemma on the original complex
three-dimensional model.  Its primitive has the prescribed full actual
antiholomorphic differential as a germ. -/
theorem exists_native_primitive_germ {U : Set Model} (hU : IsOpen U)
    {a : Model → Model →L[ℝ] ℂ} (ha : ContDiffOn ℝ ∞ a U)
    (hanti : ∀ q ∈ U, a q ∈ antiCovectors)
    (hclosed : ∀ q ∈ U, ∀ v w : Model,
      dbar (fun y => a y w) q v = dbar (fun y => a y v) q w)
    {x : Model} (hx : x ∈ U) :
    ∃ u : Model → ℂ, ContDiff ℝ ∞ u ∧ dbar u =ᶠ[𝓝 x] a := by
  let V : Set Coordinates := nativeEquiv.symm ⁻¹' U
  let f : Fin 3 → Coordinates → ℂ :=
    fun i q => a (nativeEquiv.symm q) (nativeBasis i)
  have hV : IsOpen V := hU.preimage nativeEquiv.symm.continuous
  have hcoeff (i : Fin 3) :
      ContDiffOn ℝ ∞ (fun q : Model => a q (nativeBasis i)) U :=
    ha.clm_apply contDiffOn_const
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) V := by
    intro i
    exact contDiffOn_comp_nativeEquiv_symm_iff.mpr (hcoeff i)
  have hdiff (i : Fin 3) (q : Model) (hq : q ∈ U) :
      DifferentiableAt ℝ (fun r : Model => a r (nativeBasis i)) q :=
    ((hcoeff i).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hclosed' : IsClosedOn f V := by
    intro q hq i j
    have hi : coordinateDbar i (f j) q =
        nativeCoordinateDbar i (fun r : Model => a r (nativeBasis j))
          (nativeEquiv.symm q) :=
      coordinateDbar_comp_nativeEquiv_symm i
        (f := fun r : Model => a r (nativeBasis j)) (q := q)
        (hdiff j (nativeEquiv.symm q) hq)
    have hj : coordinateDbar j (f i) q =
        nativeCoordinateDbar j (fun r : Model => a r (nativeBasis i))
          (nativeEquiv.symm q) :=
      coordinateDbar_comp_nativeEquiv_symm j
        (f := fun r : Model => a r (nativeBasis i)) (q := q)
        (hdiff i (nativeEquiv.symm q) hq)
    exact hi.trans ((hclosed (nativeEquiv.symm q) hq
      (nativeBasis i) (nativeBasis j)).trans hj.symm)
  have hx' : nativeEquiv x ∈ V := by
    change nativeEquiv.symm (nativeEquiv x) ∈ U
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  obtain ⟨u, hu, he⟩ := exists_smooth_primitive_germ hV hf hclosed' hx'
  refine ⟨u ∘ nativeEquiv, contDiff_comp_nativeEquiv_iff.mpr hu, ?_⟩
  apply dbar_comp_nativeEquiv_eventuallyEq (hu.differentiable (by simp))
  · filter_upwards [hU.mem_nhds hx] with q hq
    exact hanti q hq
  · intro i
    exact he.mono fun q hq => hq i

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
