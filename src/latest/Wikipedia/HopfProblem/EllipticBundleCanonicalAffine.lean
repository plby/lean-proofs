import Wikipedia.HopfProblem.EllipticSurfaces
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Determinant

/-!
# Actual derivatives of affine torus charts

A local inverse of a discrete-lattice quotient differs from a chosen lift
by a locally constant lattice vector. Consequently the derivative of an
affine map in the actual torus charts is its complex linear part. This is
proved for every iterate of the elliptic generator, not postulated as a
transition law for a separately defined bundle.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

section DiscreteQuotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L]

/-- Taking a local lattice-quotient lift does not change the derivative of
an actual covering lift. -/
theorem quotient_chart_hasFDerivAt_of_lift
    (f : E ⧸ L → E ⧸ L) (F : E → E)
    (hproj : ∀ y, L.mkQ (F y) = f (L.mkQ y))
    (b : E ⧸ L) (z : E) (D : E →L[ℂ] E)
    (hf : ContinuousAt f (L.mkQ z)) (hF : HasFDerivAt F D z)
    (hb : f (L.mkQ z) ∈ (DiscreteQuotient.chart L b).source) :
    HasFDerivAt (DiscreteQuotient.chart L b ∘ f ∘ L.mkQ) D z := by
  let d := DiscreteQuotient.chart L b (f (L.mkQ z)) - F z
  have hd : L.mkQ d = 0 := by
    change L.mkQ (DiscreteQuotient.chart L b (f (L.mkQ z)) - F z) = 0
    rw [map_sub, DiscreteQuotient.mkQ_chart L b _ hb, hproj, sub_self]
  have hnear : ∀ᶠ y in 𝓝 z, f (L.mkQ y) ∈ (DiscreteQuotient.chart L b).source :=
    (hf.comp L.continuous_mkQ.continuousAt)
      ((DiscreteQuotient.chart L b).open_source.mem_nhds hb)
  have he : DiscreteQuotient.chart L b ∘ f ∘ L.mkQ =ᶠ[𝓝 z] fun y => F y + d := by
    apply eventuallyEq_of_localHomeomorph_comp_eq (DiscreteQuotient.quotient_localHomeomorph L)
      ((((DiscreteQuotient.chart L b).continuousAt hb).comp hf).comp
        L.continuous_mkQ.continuousAt)
      (hF.continuousAt.add continuousAt_const)
    · dsimp [d]
      abel
    · filter_upwards [hnear] with y hy
      change L.mkQ (DiscreteQuotient.chart L b (f (L.mkQ y))) = L.mkQ (F y + d)
      rw [map_add, hd, add_zero, hproj, DiscreteQuotient.mkQ_chart L b _ hy]
  exact (hF.add_const d).congr_of_eventuallyEq he

end DiscreteQuotient

/-- The complex affine lift of the torus generator. -/
def affineLift (j : Kind) (p : FixedPeriod j) (v : Lattice) (z : ComplexPlane₂) :
    ComplexPlane₂ :=
  linearEquiv j p z + periodEquiv p.val ((1 / (j.order : ℝ)) • realCast v)

theorem affineLift_mkQ (j : Kind) (p : FixedPeriod j) (v : Lattice) (z : ComplexPlane₂) :
    p.val.lattice.mkQ (affineLift j p v z) =
      affineBiholomorph j p v (p.val.lattice.mkQ z) := by
  rw [affineLift, map_add, affineBiholomorph_apply, linearBiholomorph_mkQ]
  rfl

theorem affineLift_hasFDerivAt (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (z : ComplexPlane₂) :
    HasFDerivAt (affineLift j p v) (linearEquiv j p).toContinuousLinearMap z :=
  (linearEquiv j p).toContinuousLinearMap.hasFDerivAt.add_const _

theorem affineLift_iterate_hasFDerivAt (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (n : ℕ) (z : ComplexPlane₂) :
    HasFDerivAt (affineLift j p v)^[n]
      ((linearEquiv j p).toContinuousLinearMap ^ n) z := by
  induction n generalizing z with
  | zero => exact hasFDerivAt_id z
  | succ n ih =>
    rw [Function.iterate_succ', pow_succ']
    exact (affineLift_hasFDerivAt j p v _).comp z (ih z)

theorem affineLift_iterate_mkQ (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (n : ℕ) (z : ComplexPlane₂) :
    p.val.lattice.mkQ ((affineLift j p v)^[n] z) =
      (affineBiholomorph j p v)^[n] (p.val.lattice.mkQ z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', affineLift_mkQ, ih]

theorem affineAction_mkQ (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (z : ComplexPlane₂) :
    letI := affineAction j p v hv
    g • p.val.lattice.mkQ z =
      p.val.lattice.mkQ ((affineLift j p v)^[g.toAdd.val] z) := by
  let := affineAction j p v hv
  change (affinePermutation j p v ^ g.toAdd.val) (p.val.lattice.mkQ z) = _
  rw [Equiv.Perm.coe_pow]
  exact (affineLift_iterate_mkQ j p v g.toAdd.val z).symm

/-- In any pair of actual torus charts, a cyclic deck transformation has
the derivative given by the appropriate power of its linear monodromy. -/
theorem affineAction_chart_hasFDerivAt (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (a b : p.val.Torus)
    (z : ComplexPlane₂) :
    letI := affineAction j p v hv
    g • (chartAt ComplexPlane₂ a).symm z ∈ (chartAt ComplexPlane₂ b).source →
    HasFDerivAt (chartAt ComplexPlane₂ b ∘ (fun x : p.val.Torus => g • x) ∘
      (chartAt ComplexPlane₂ a).symm)
      ((linearEquiv j p).toContinuousLinearMap ^ g.toAdd.val) z := by
  let := affineAction j p v hv
  intro hb
  change g • (DiscreteQuotient.chart p.val.lattice a).symm z ∈
    (DiscreteQuotient.chart p.val.lattice b).source at hb
  rw [DiscreteQuotient.chart_symm] at hb
  change HasFDerivAt (DiscreteQuotient.chart p.val.lattice b ∘
    (fun x : p.val.Torus => g • x) ∘ (DiscreteQuotient.chart p.val.lattice a).symm) _ z
  rw [DiscreteQuotient.chart_symm]
  exact quotient_chart_hasFDerivAt_of_lift p.val.lattice _ _
    (fun y => (affineAction_mkQ j p v hv g y).symm) b z _
    (affineAction_holomorphic j p v hv g).continuous.continuousAt
    (affineLift_iterate_hasFDerivAt j p v g.toAdd.val z) hb

theorem affineAction_chart_det_fderiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (a b : p.val.Torus)
    (z : ComplexPlane₂) :
    letI := affineAction j p v hv
    g • (chartAt ComplexPlane₂ a).symm z ∈ (chartAt ComplexPlane₂ b).source →
    LinearMap.det (fderiv ℂ (chartAt ComplexPlane₂ b ∘
      (fun x : p.val.Torus => g • x) ∘ (chartAt ComplexPlane₂ a).symm) z).toLinearMap =
      (LinearMap.det (linearEquiv j p).toLinearMap) ^ g.toAdd.val := by
  let := affineAction j p v hv
  intro hb
  rw [(affineAction_chart_hasFDerivAt j p v hv g a b z hb).fderiv,
    ContinuousLinearMap.toLinearMap_pow, map_pow]
  rfl

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
