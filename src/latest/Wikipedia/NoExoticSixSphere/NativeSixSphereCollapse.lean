import Wikipedia.NoExoticSixSphere.StableSixSphereNativeLimit
import Wikipedia.NoExoticSixSphere.StableSixSphereCollapse

/-!
# The original framed collapse in the native sphere homotopy groups

The original collapse fixes the actual stereographic pole. Its genuine
cube-relative class therefore represents the same element of the native
suspension limit as the previously constructed sphere-map class. Equality
with the identity is equivalent both to a finite native identity witness
and to a finite ordinary suspension nullhomotopy of the original collapse.
These equivalences do not assert vanishing of the class.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

theorem reindex_pole {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (f : C(Sphere m, Sphere n)) (hp : f (spherePole m) = spherePole n) :
    reindex hm hn f (spherePole m') = spherePole n' := by
  subst m'
  subst n'
  exact hp

end NoExoticSixSphere.SphereMapSuspension

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open StableSixSphereMaps SmoothCube

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a) (hd : 8 ≤ e.ambientDimension)

theorem sixthStageMap_pole :
    d.sixthStageMap hd (spherePole (e.ambientDimension - 8 + 8)) =
      spherePole (e.ambientDimension - 8 + 2) := by
  apply SphereMapSuspension.reindex_pole (by omega) (by omega) d.sphereMap
  simpa only [sphereInfinity, euclideanOnePointSphere_infty] using d.sphereMap_infty

def nativeSixthStageClass : NativeStage (e.ambientDimension - 8) :=
  sphereClass ⟨d.sixthStageMap hd, d.sixthStageMap_pole hd⟩

theorem nativeStageEquiv_nativeSixthStageClass :
    nativeStageEquiv (e.ambientDimension - 8) (d.nativeSixthStageClass hd) =
      classOf (d.sixthStageMap hd) := nativeStageEquiv_sphereClass _

def nativeStableCollapse : NativeClass := nativeClassOf (d.nativeSixthStageClass hd)

theorem nativeClassEquiv_nativeStableCollapse :
    nativeClassEquiv (d.nativeStableCollapse hd) = d.sixthStableClass hd :=
  nativeClassEquiv_sphereClass ⟨d.sixthStageMap hd, d.sixthStageMap_pole hd⟩

theorem nativeStableCollapse_eq_identity_iff :
    d.nativeStableCollapse hd = nativeIdentityClass ↔
      d.sixthStableClass hd = nullClass := by
  rw [← nativeClassEquiv.injective.eq_iff, nativeClassEquiv_nativeStableCollapse,
    nativeClassEquiv_identity]

theorem nativeStableCollapse_eq_identity_iff_finite :
    d.nativeStableCollapse hd = nativeIdentityClass ↔
      ∃ (l : ℕ) (h : e.ambientDimension - 8 ≤ l),
        nativeTransition (e.ambientDimension - 8) l h (d.nativeSixthStageClass hd) = 1 :=
  nativeClassOf_eq_identity_iff _

theorem nativeStableCollapse_eq_identity_iff_nullhomotopic :
    d.nativeStableCollapse hd = nativeIdentityClass ↔
      ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic := by
  rw [d.nativeStableCollapse_eq_identity_iff, d.sixthStableClass_eq_null_iff]

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
