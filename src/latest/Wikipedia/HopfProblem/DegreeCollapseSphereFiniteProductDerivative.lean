import Wikipedia.HopfProblem.DegreeCollapseSphereProductLocalFormula

/-!
# Actual finite derivatives of the original sphere products

An inverse-chart square gives the finite map itself as a Euclidean germ.
Differentiating this germ retains the original source and target linear
coordinate equivalences. The suspension and smash derivatives are the
corresponding Cartesian block derivatives in those exact coordinates.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteProductDerivative

open NoExoticSixSphere SphereComposition CubicalSphereSuspension
open FiniteSphereProductCharts SphereFiniteRepresentative

section Coordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m n : ℕ}
  (f : C(Sphere m, Sphere n)) (g : E → F) (e : E ≃L[ℝ] V m) (d : F ≃L[ℝ] V n)
  (p : E)

theorem value_of_inverse_square
    (h : f ((chart m e).symm p) = (chart n d).symm (g p)) :
    value f (e p) = d (g p) := by
  have hh := congrArg (sphereProjection n) h
  change value f (e p) = sphereProjection n (point n (d (g p))) at hh
  rwa [projection_point] at hh

theorem value_eventuallyEq_of_inverse_square
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (g u))) :
    value f =ᶠ[𝓝 (e p)] (fun u ↦ d (g (e.symm u))) := by
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have hc : Tendsto e.symm (𝓝 (e p)) (𝓝 (e.symm (e p))) := e.symm.continuousAt
    rwa [ContinuousLinearEquiv.symm_apply_apply] at hc
  filter_upwards [h.comp_tendsto ht] with u hu
  have hh := value_of_inverse_square f g e d (e.symm u) hu
  rwa [ContinuousLinearEquiv.apply_symm_apply] at hh

theorem hasFDerivAt_of_inverse_square (G : E →L[ℝ] F) (hg : HasFDerivAt g G p)
    (h : (fun u ↦ f ((chart m e).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (chart n d).symm (g u))) :
    HasFDerivAt (value f)
      (d.toContinuousLinearMap.comp (G.comp e.symm.toContinuousLinearMap)) (e p) := by
  have hg' : HasFDerivAt g G (e.symm (e p)) := by
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  have hd := d.hasFDerivAt.comp (e p) (hg'.comp (e p) e.symm.hasFDerivAt)
  exact hd.congr_of_eventuallyEq (value_eventuallyEq_of_inverse_square f g e d p h)

end Coordinates

variable {m n : ℕ} (f : Based m n)

theorem value_product (p : V m × ℝ) (hb : f.val (point m p.1) ≠ spherePole n) :
    value (productBasedMap f).val (lineCoordinates m p) = lineCoordinates n (line f.val p) :=
  value_of_inverse_square (productBasedMap f).val (line f.val)
    (lineCoordinates m) (lineCoordinates n) p (SphereProductLocalFormula.line_formula f p hb)

theorem hasFDerivAt_product (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hb : f.val (point m p.1) ≠ spherePole n) :
    HasFDerivAt (value (productBasedMap f).val)
      ((lineCoordinates n).toContinuousLinearMap.comp
        (((fderiv ℝ (value f.val) p.1).prodMap (ContinuousLinearMap.id ℝ ℝ)).comp
          (lineCoordinates m).symm.toContinuousLinearMap)) (lineCoordinates m p) :=
  hasFDerivAt_of_inverse_square (productBasedMap f).val (line f.val)
    (lineCoordinates m) (lineCoordinates n) p _
    (HasFDerivAt.prodMap p
      ((value_contDiffAt f.val p.1 hf hb).differentiableAt (by simp)).hasFDerivAt
      (hasFDerivAt_id p.2)) (SphereProductLocalFormula.line_eventually f p hb)

theorem fderiv_product (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hb : f.val (point m p.1) ≠ spherePole n) :
    fderiv ℝ (value (productBasedMap f).val) (lineCoordinates m p) =
      (lineCoordinates n).toContinuousLinearMap.comp
        (((fderiv ℝ (value f.val) p.1).prodMap (ContinuousLinearMap.id ℝ ℝ)).comp
          (lineCoordinates m).symm.toContinuousLinearMap) :=
  (hasFDerivAt_product f p hf hb).fderiv

theorem value_square (p : V m × V m)
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    value (SphereSmash.squareMap f) (sumCoordinates m p) =
      sumCoordinates n (square f.val p) :=
  value_of_inverse_square (SphereSmash.squareMap f) (square f.val)
    (sumCoordinates m) (sumCoordinates n) p (SphereProductLocalFormula.square_formula f p hb hc)

theorem hasFDerivAt_square (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.2))
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    HasFDerivAt (value (SphereSmash.squareMap f))
      ((sumCoordinates n).toContinuousLinearMap.comp
        (((fderiv ℝ (value f.val) p.1).prodMap (fderiv ℝ (value f.val) p.2)).comp
          (sumCoordinates m).symm.toContinuousLinearMap)) (sumCoordinates m p) :=
  hasFDerivAt_of_inverse_square (SphereSmash.squareMap f) (square f.val)
    (sumCoordinates m) (sumCoordinates n) p _
    (HasFDerivAt.prodMap p
      ((value_contDiffAt f.val p.1 hf hb).differentiableAt (by simp)).hasFDerivAt
      ((value_contDiffAt f.val p.2 hg hc).differentiableAt (by simp)).hasFDerivAt)
    (SphereProductLocalFormula.square_eventually f p hb hc)

theorem fderiv_square (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.2))
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    fderiv ℝ (value (SphereSmash.squareMap f)) (sumCoordinates m p) =
      (sumCoordinates n).toContinuousLinearMap.comp
        (((fderiv ℝ (value f.val) p.1).prodMap (fderiv ℝ (value f.val) p.2)).comp
          (sumCoordinates m).symm.toContinuousLinearMap) :=
  (hasFDerivAt_square f p hf hg hb hc).fderiv

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteProductDerivative
