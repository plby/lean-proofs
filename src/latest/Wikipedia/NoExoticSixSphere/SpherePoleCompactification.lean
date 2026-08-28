import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Smooth finite compactification charts with any specified sphere pole

The homeomorphism is obtained from the actual stereographic chart in the
existing sphere atlas. Infinity is the supplied pole, and finite zero is
its antipode. The finite-coordinate and smoothness formulas are explicit.
-/

noncomputable section

open Set Topology ChartedSpace IsManifold
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SpherePoleCompactification

variable {n : ℕ} (p : Sphere n)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def chart : OpenPartialHomeomorph (Sphere n) (EuclideanSpace ℝ (Fin n)) := stereographic' n p

theorem chart_source : (chart p).source = {p}ᶜ := stereographic'_source p

theorem chart_target : (chart p).target = univ := stereographic'_target p

theorem chart_mem_maximalAtlas : chart p ∈ maximalAtlas (𝓡 n) ∞ (Sphere n) := by
  apply subset_maximalAtlas
  exact ⟨p, rfl⟩

def chartDiffeomorph :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (EuclideanSpace ℝ (Fin n)) ∞ where
  toPartialEquiv := (chart p).toPartialEquiv
  open_source := (chart p).open_source
  open_target := (chart p).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (chart_mem_maximalAtlas p)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas p)

theorem range_chart_symm : range (chart p).symm = {p}ᶜ := by
  rw [← chart_source]
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact (chart p).map_target (by rw [chart_target]; trivial)
  · intro y hy
    exact ⟨chart p y, (chart p).left_inv hy⟩

def homeomorph : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ Sphere n :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p (chart p).symm
    ((chart p).symm.isOpenEmbedding (chart_target p)).isEmbedding (range_chart_symm p)

theorem homeomorph_infty : homeomorph p OnePoint.infty = p :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _

theorem homeomorph_coe (x : EuclideanSpace ℝ (Fin n)) :
    homeomorph p (x : OnePoint _) = (chart p).symm x :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ _

theorem chart_symm_zero : (chart p).symm 0 = -p :=
  EuclideanSphere.stereographic'_symm_zero p

theorem homeomorph_zero : homeomorph p ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) = -p := by
  rw [homeomorph_coe, chart_symm_zero]

theorem chart_antipode : chart p (-p) = 0 := by
  rw [← chart_symm_zero]
  exact (chart p).right_inv (by rw [chart_target]; trivial)

theorem homeomorph_symm_of_ne {y : Sphere n} (hy : y ≠ p) :
    (homeomorph p).symm y = (chart p y : OnePoint _) := by
  apply (homeomorph p).injective
  rw [Homeomorph.apply_symm_apply, homeomorph_coe]
  exact ((chart p).left_inv (by simpa only [chart_source,
    mem_compl_iff, mem_singleton_iff] using hy)).symm

theorem contMDiff_chart_symm : ContMDiff (𝓡 n) (𝓡 n) ∞ (chart p).symm := by
  have h := (chartDiffeomorph p).contMDiffOn_invFun
  change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chart p).symm (chart p).target at h
  rwa [chart_target, contMDiffOn_univ] at h

theorem chart_localDiffeomorph {y : Sphere n} (hy : y ≠ p) :
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (chart p) y :=
  ⟨chartDiffeomorph p, by
    change y ∈ (chart p).source
    simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using hy,
    fun _ _ ↦ rfl⟩

theorem chart_symm_localDiffeomorph (x : EuclideanSpace ℝ (Fin n)) :
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (chart p).symm x :=
  ⟨(chartDiffeomorph p).symm, by change x ∈ (chart p).target; rw [chart_target]; trivial,
    fun _ _ ↦ rfl⟩

theorem ne_neg : p ≠ -p := by
  intro h
  have hz : p.val = 0 := by
    ext i
    have hi : p.val i = -(p.val i) := congrArg (fun x : Sphere n ↦ x.val i) h
    exact CharZero.eq_neg_self_iff.mp hi
  have hn : ‖p.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

end NoExoticSixSphere.SpherePoleCompactification
