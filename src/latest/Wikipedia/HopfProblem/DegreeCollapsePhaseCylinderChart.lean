import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# A genuine transverse-and-phase change of full cylinder coordinates

An actual transverse partial diffeomorphism and a smooth scalar phase
give an actual full-cylinder partial diffeomorphism, with explicit inverse
and exact product domains. Its derivative preserves vertical velocity.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def phaseCylinderChart
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, Z × ℝ) (E × ℝ) (Z × ℝ) ∞ := by
  have hQ : ContDiffOn ℝ ∞ (fun p : E × ℝ => Q p.1) (Q.source ×ˢ univ) :=
    Q.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hQi : ContDiffOn ℝ ∞ (fun p : Z × ℝ => Q.symm p.1) (Q.target ×ˢ univ) :=
    Q.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  refine {
    toFun := fun p => (Q p.1, p.2 + v p.1)
    invFun := fun p => (Q.symm p.1, p.2 - v (Q.symm p.1))
    source := Q.source ×ˢ univ
    target := Q.target ×ˢ univ
    map_source' := fun p hp => ⟨Q.map_source' hp.1, mem_univ _⟩
    map_target' := fun p hp => ⟨Q.map_target' hp.1, mem_univ _⟩
    left_inv' := ?_
    right_inv' := ?_
    open_source := Q.open_source.prod isOpen_univ
    open_target := Q.open_target.prod isOpen_univ
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · intro p hp
    have hi : Q.symm (Q p.1) = p.1 := Q.left_inv' hp.1
    change (Q.symm (Q p.1), p.2 + v p.1 - v (Q.symm (Q p.1))) = p
    rw [hi, add_sub_cancel_right]
  · intro p hp
    have hi : Q (Q.symm p.1) = p.1 := Q.right_inv' hp.1
    change (Q (Q.symm p.1), p.2 - v (Q.symm p.1) + v (Q.symm p.1)) = p
    rw [hi, sub_add_cancel]
  · exact (hQ.prodMk (contDiff_snd.contDiffOn.add
      (hv.comp contDiff_fst).contDiffOn)).contMDiffOn
  · exact (hQi.prodMk (contDiff_snd.contDiffOn.sub
      (hv.contDiffOn.comp hQi (mapsTo_univ _ _)))).contMDiffOn

theorem phaseCylinderChart_apply
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) (p : E × ℝ) :
    phaseCylinderChart Q v hv p = (Q p.1, p.2 + v p.1) := rfl

theorem phaseCylinderChart_source
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    (phaseCylinderChart Q v hv).source = Q.source ×ˢ univ := rfl

theorem phaseCylinderChart_target
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    (phaseCylinderChart Q v hv).target = Q.target ×ˢ univ := rfl

theorem phaseCylinderChart_vertical
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) {p : E × ℝ}
    (hp : p ∈ (phaseCylinderChart Q v hv).source) :
    fderiv ℝ (phaseCylinderChart Q v hv) p (0, 1) = (0, 1) := by
  let R := phaseCylinderChart Q v hv
  have hdiff := (R.contMDiffOn_toFun.contDiffOn.contDiffAt
    (R.open_source.mem_nhds hp)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  have hdiff' : HasFDerivAt R (fderiv ℝ R p) (p.1, p.2 + 0) := by
    simpa only [add_zero, Prod.mk.eta] using hdiff.hasFDerivAt
  have hd := hdiff'.comp_hasDerivAt (0 : ℝ) hcurve
  have hd' : HasDerivAt (fun t : ℝ => (Q p.1, p.2 + t + v p.1))
      (fderiv ℝ R p (0, 1)) 0 := by
    convert! hd using 1
  have he : HasDerivAt (fun t : ℝ => (Q p.1, p.2 + t + v p.1)) (0, 1) 0 :=
    (hasDerivAt_const 0 (Q p.1)).prodMk
      (((hasDerivAt_id (0 : ℝ)).const_add p.2).add_const (v p.1))
  exact hd'.unique he

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
