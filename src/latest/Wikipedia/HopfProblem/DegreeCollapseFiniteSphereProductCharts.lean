import Wikipedia.HopfProblem.DegreeCollapseProductSphereFiber
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphProduct

/-!
# Smooth finite charts for the original sphere product coordinates

Compose the existing stereographic chart with the actual continuous linear
product equivalence. Its inverse is exactly the finite part of the original
product-compactification homeomorphism. Both derivatives are bijective on
their actual domains. These charts will transfer product smoothness and
regularity to the existing sphere suspension and smash maps.
-/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FiniteSphereProductCharts

open NoExoticSixSphere

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def chart (n : ℕ) (e : E ≃L[ℝ] V n) :
    PartialDiffeomorph (𝓡 n) 𝓘(ℝ, E) (Sphere n) E ∞ :=
  (sphereProjectionDiffeomorph n).trans e.symm.toDiffeomorph.toPartialDiffeomorph

theorem chart_source (n : ℕ) (e : E ≃L[ℝ] V n) :
    (chart n e).source = {spherePole n}ᶜ := by
  ext x
  change (x ∈ (sphereProjection n).source ∧ sphereProjection n x ∈ (univ : Set (V n))) ↔ _
  rw [sphereProjection_source]
  simp only [mem_univ, and_true]

theorem chart_target (n : ℕ) (e : E ≃L[ℝ] V n) : (chart n e).target = univ := by
  ext x
  change (x ∈ (univ : Set E) ∧ e x ∈ (sphereProjection n).target) ↔ x ∈ univ
  rw [sphereProjection_target]
  simp only [mem_univ, and_self]

theorem chart_apply (n : ℕ) (e : E ≃L[ℝ] V n) (x : Sphere n) :
    chart n e x = e.symm (sphereProjection n x) := rfl

theorem chart_symm_apply (n : ℕ) (e : E ≃L[ℝ] V n) (p : E) :
    (chart n e).symm p = (sphereProjection n).symm (e p) := rfl

theorem chart_symm_coe (n : ℕ) (e : E ≃L[ℝ] V n) (p : E) :
    (chart n e).symm p = euclideanOnePointSphere n (↑(e p) : OnePoint (V n)) :=
  (euclideanOnePointSphere_coe n (e p)).symm

theorem chart_symm_ne_pole (n : ℕ) (e : E ≃L[ℝ] V n) (p : E) :
    (chart n e).symm p ≠ spherePole n := by
  intro h
  exact OnePoint.coe_ne_infty (e p) ((euclideanOnePointSphere n).injective
    (((chart_symm_coe n e p).symm.trans h).trans (euclideanOnePointSphere_infty n).symm))

theorem chart_right_inv (n : ℕ) (e : E ≃L[ℝ] V n) (p : E) :
    chart n e ((chart n e).symm p) = p :=
  (chart n e).right_inv (by rw [chart_target]; trivial)

theorem chart_contMDiffAt (n : ℕ) (e : E ≃L[ℝ] V n) {x : Sphere n}
    (hx : x ≠ spherePole n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (chart n e) x :=
  (chart n e).contMDiffOn_toFun.contMDiffAt ((chart n e).open_source.mem_nhds
    (by simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using hx))

theorem chart_symm_contMDiff (n : ℕ) (e : E ≃L[ℝ] V n) :
    ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞ (chart n e).symm := by
  have h := (chart n e).contMDiffOn_invFun
  rwa [chart_target, contMDiffOn_univ] at h

theorem chart_mfderiv_bijective (n : ℕ) (e : E ≃L[ℝ] V n) {x : Sphere n}
    (hx : x ≠ spherePole n) :
    Function.Bijective (mfderiv (𝓡 n) 𝓘(ℝ, E) (chart n e) x) := by
  have h : IsLocalDiffeomorphAt (𝓡 n) 𝓘(ℝ, E) ∞ (chart n e) x :=
    ⟨chart n e, by simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using hx,
      fun _ _ ↦ rfl⟩
  exact (h.mfderivToContinuousLinearEquiv (by simp)).bijective

theorem chart_symm_mfderiv_bijective (n : ℕ) (e : E ≃L[ℝ] V n) (p : E) :
    Function.Bijective (mfderiv 𝓘(ℝ, E) (𝓡 n) (chart n e).symm p) := by
  have h : IsLocalDiffeomorphAt 𝓘(ℝ, E) (𝓡 n) ∞ (chart n e).symm p :=
    ⟨(chart n e).symm, by change p ∈ (chart n e).target; rw [chart_target]; trivial,
      fun _ _ ↦ rfl⟩
  exact (h.mfderivToContinuousLinearEquiv (by simp)).bijective

def lineCoordinates (n : ℕ) : (V n × ℝ) ≃L[ℝ] V (n + 1) :=
  (ContinuousLinearEquiv.prodComm ℝ (V n) ℝ).trans (EuclideanProduct.coordinates n)

def sumCoordinates (n : ℕ) : (V n × V n) ≃L[ℝ] V (n + n) :=
  EuclideanSpace.finAddEquivProd.symm

def lineChart (n : ℕ) : PartialDiffeomorph (𝓡 (n + 1)) 𝓘(ℝ, V n × ℝ)
    (Sphere (n + 1)) (V n × ℝ) ∞ := chart (n + 1) (lineCoordinates n)

def pairChart (n : ℕ) : PartialDiffeomorph (𝓡 (n + n)) 𝓘(ℝ, V n × V n)
    (Sphere (n + n)) (V n × V n) ∞ := chart (n + n) (sumCoordinates n)

theorem lineChart_symm_coe (n : ℕ) (p : V n × ℝ) :
    (lineChart n).symm p = SuspensionProductComparison.productSphereHomeomorph n
      (↑p : OnePoint (V n × ℝ)) := by
  rw [lineChart, chart_symm_coe]
  rfl

theorem pairChart_symm_coe (n : ℕ) (p : V n × V n) :
    (pairChart n).symm p = JamesSphere.pairingHomeomorph n (↑p : OnePoint (V n × V n)) := by
  rw [pairChart, chart_symm_coe]
  rfl

theorem slice_finite (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    ProductSphereFiber.slice n x = (lineChart n).symm (sphereProjection n x, (0 : ℝ)) := by
  change SuspensionProductComparison.productSphereHomeomorph n
    (OnePointProduct.map ((euclideanOnePointSphere n).symm x, ↑(0 : ℝ))) = _
  rw [euclideanOnePointSphere_symm_of_ne n hx, OnePointProduct.map_coe]
  exact (lineChart_symm_coe n _).symm

theorem pairing_finite (n : ℕ) {x y : Sphere n} (hx : x ≠ spherePole n)
    (hy : y ≠ spherePole n) :
    JamesSphere.pairing n (x, y) =
      (pairChart n).symm (sphereProjection n x, sphereProjection n y) := by
  change JamesSphere.pairingHomeomorph n
    (OnePointProduct.map ((euclideanOnePointSphere n).symm x,
      (euclideanOnePointSphere n).symm y)) = _
  rw [euclideanOnePointSphere_symm_of_ne n hx, euclideanOnePointSphere_symm_of_ne n hy,
    OnePointProduct.map_coe]
  exact (pairChart_symm_coe n _).symm

end Wikipedia.HopfProblem.DegreeCollapse.FiniteSphereProductCharts
