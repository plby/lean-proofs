import Wikipedia.NoExoticSixSphere.GenericLinearAvoidance
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover

/-!
# Actual secant and tangent families for linear compression

Both families live on open subsets of two copies of the original manifold
model. The secants exclude equal embedded points; the tangents exclude the
zero input vector. Smoothness and nonvanishing use the original embedding
and genuine partial-diffeomorphism charts.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.LinearProjection

open GLOrthonormalization ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

def chartMap (c : TargetChart n M) : Vector n → Vector e.ambientDimension :=
  e.toFun ∘ c.symm

theorem contDiffOn_chartMap (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartMap e c) c.target :=
  (e.smooth.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn

theorem chartDerivative_eq (c : TargetChart n M) {x : Vector n} (hx : x ∈ c.target) :
    fderiv ℝ (chartMap e c) x =
      (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun (c.symm x)).comp
        (mfderiv (𝓡 n) (𝓡 n) c.symm x) := by
  have hs := c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hx)
  have h := mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at h
  exact h

theorem chartDerivative_injective (c : TargetChart n M) {x : Vector n} (hx : x ∈ c.target) :
    Injective (fderiv ℝ (chartMap e c) x) := by
  have hl : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    ⟨c.symm, hx, fun _ _ ↦ rfl⟩
  have hi := (hl.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv (𝓡 n) (𝓡 n) c.symm x) at hi
  rw [chartDerivative_eq e c hx]
  exact (e.injective_mfderiv (c.symm x)).comp hi

def secant (c d : TargetChart n M) (q : Vector n × Vector n) : Vector e.ambientDimension :=
  chartMap e c q.1 - chartMap e d q.2

theorem contDiffOn_secant (c d : TargetChart n M) :
    ContDiffOn ℝ ∞ (secant e c d) (c.target ×ˢ d.target) :=
  ((contDiffOn_chartMap e c).comp contDiff_fst.contDiffOn (fun _ h ↦ h.1)).sub
    ((contDiffOn_chartMap e d).comp contDiff_snd.contDiffOn (fun _ h ↦ h.2))

def secantDomain (c d : TargetChart n M) : Opens (Vector n × Vector n) :=
  ⟨(c.target ×ˢ d.target) ∩ secant e c d ⁻¹' ({0}ᶜ : Set (Vector e.ambientDimension)),
    (contDiffOn_secant e c d).continuousOn.isOpen_inter_preimage
      (c.open_target.prod d.open_target) isClosed_singleton.isOpen_compl⟩

theorem secant_nonzero (c d : TargetChart n M) (q : Vector n × Vector n)
    (hq : q ∈ secantDomain e c d) : secant e c d q ≠ 0 := hq.2

def tangent (c : TargetChart n M) (q : Vector n × Vector n) : Vector e.ambientDimension :=
  fderiv ℝ (chartMap e c) q.1 q.2

def tangentDomain (c : TargetChart n M) : Opens (Vector n × Vector n) :=
  ⟨c.target ×ˢ ({0}ᶜ : Set (Vector n)), c.open_target.prod isClosed_singleton.isOpen_compl⟩

theorem contDiffOn_tangent (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (tangent e c) (tangentDomain c) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (chartMap e c)) c.target := by
    intro x hx
    exact (((contDiffOn_chartMap e c).contDiffAt (c.open_target.mem_nhds hx)).fderiv_right
      (by simp)).contDiffWithinAt
  exact (hD.comp contDiff_fst.contDiffOn (fun _ h ↦ h.1)).clm_apply contDiff_snd.contDiffOn

theorem tangent_nonzero (c : TargetChart n M) (q : Vector n × Vector n)
    (hq : q ∈ tangentDomain c) : tangent e c q ≠ 0 := by
  intro hz
  have hqzero : q.2 = 0 := (chartDerivative_injective e c hq.1)
    (hz.trans (map_zero (fderiv ℝ (chartMap e c) q.1)).symm)
  exact hq.2 hqzero

end NoExoticSixSphere.LinearProjection
