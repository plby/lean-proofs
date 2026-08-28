import Wikipedia.HopfProblem.DegreeCollapseMutualSheetUnit
import Wikipedia.HopfProblem.DegreeCollapseFramedCoreImmersion
import Wikipedia.HopfProblem.DegreeCollapseSurgeryFiniteRank
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyHomology

/-!
# A unit signed count constructs the actual framed dual used by surgery

Start with the original normalized attaching product and a full framed
face whose core is transverse to it. A unit actual signed count constructs
an ambient isotopy of the entire second face. Its endpoint meets the
unchanged attaching core at exactly one transverse pair. The checked
native surgery theorem then preserves two-connectivity and drops middle
rank. Existence of a pair with unit count is still a separate obligation.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedDual

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris OrbitPair.DeterminantSignCover

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (oS : Orientation (tangentBundleCore (𝓡 3) (Sphere 3)))
  (oM : Orientation (tangentBundleCore (𝓡 6) M))
  (K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6)
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

include A hR in
theorem attaching_smooth : ContMDiff (𝓡 3) (𝓡 6) ∞ f := by
  rw [← TraceBody.unitFace_coreMap_eq f A hR]
  exact FramedSurgery.contMDiff_coreMap (E := Vector 4) _

include A hR in
theorem attaching_injective : Injective f := by
  rw [← TraceBody.unitFace_coreMap_eq f A hR]
  exact FramedCore.injective_core _

include A hR in
theorem attaching_immersive (x : Sphere 3) : Injective (mfderiv (𝓡 3) (𝓡 6) f x) := by
  rw [← TraceBody.unitFace_coreMap_eq f A hR]
  exact FramedCore.injective_core_derivative _ x

theorem dual_good
    (ht : ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) B x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y))) :
    MutualSheets.Good (D := Vector 3) (E := Vector 6) f
      (FramedSurgery.coreMap (E := Vector 4) B) :=
  ⟨FramedSurgery.contMDiff_coreMap (E := Vector 4) B, FramedCore.injective_core B,
    FramedCore.injective_core_derivative B, ht⟩

def dualCount
    (ht : ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) B x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y))) : ℤ :=
  MutualSheets.signedCount oS oS oM K (FramedSurgery.coreMap (E := Vector 4) B) f
    (MutualSheets.finite_crossingPoints (by simp) (by simp)
      (attaching_smooth f A hR) (attaching_injective f A hR) (dual_good f B ht))

theorem exists_framed_single_dual_of_unit_count
    (ht : ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) B x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hcount : (dualCount oS oM K f A hR B ht).natAbs = 1) :
    ∃ ψ : Diffeomorph (𝓡 6) (𝓡 6) M M ∞, ∃ q u : Sphere 3,
      SupportedDiffeomorph.IsotopicToIdentity ψ ∧
      (FramedSurgery.coreMap (E := Vector 4) B).Homotopic
        (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) ∧
      (∀ x y, f x = FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ) y ↔
        x = q ∧ y = u) ∧
      Surjective ((mfderiv (𝓡 3) (𝓡 6) f q).coprod
        (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) u)) := by
  obtain ⟨ψ, F', u, q, hiso, heq, hgood, hcross⟩ :=
    MutualSheets.exists_single_crossing_of_unit_count oS oS oM K (by simp) (by simp)
      (FramedSurgery.coreMap (E := Vector 4) B) f (attaching_smooth f A hR)
      (attaching_injective f A hR) (attaching_immersive f A hR) (dual_good f B ht) hcount
  have he : F' = FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ) := by
    apply ContinuousMap.ext
    intro x
    exact heq x
  rw [he] at hgood hcross
  have hp : f q = FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ) u :=
    ((hcross u q).mpr ⟨rfl, rfl⟩).symm
  have hhom : (FramedSurgery.coreMap (E := Vector 4) B).Homotopic
      (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) :=
    hiso.comp_homotopic (FramedSurgery.coreMap (E := Vector 4) B)
  refine ⟨ψ, q, u, hiso, hhom, ?_, ?_⟩
  · intro x y
    exact eq_comm.trans ((hcross y x).trans and_comm)
  · let DF : Vector 3 →L[ℝ] Vector 6 :=
      mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) u
    let Df : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) f q
    exact TransverseCoordinates.surjective_coprod_swap DF Df (hgood.2.2.2 u q hp)

theorem compact_surgery_reduction_of_unit_count
    [Subsingleton (SingularHomology M 2)]
    (ht : ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) B x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hcount : (dualCount oS oM K f A hR B ht).natAbs = 1) :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      (∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x)) ∧
      Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
        Module.finrank ℤ (SingularHomology M 3) := by
  obtain ⟨ψ, q, u, _, _, hcross, htrans⟩ :=
    exists_framed_single_dual_of_unit_count oS oM K f A hR B ht hcount
  exact TraceBody.compact_dual_surgery_reduction f A hR (B.postcompose ψ) q u hcross htrans

end Wikipedia.HopfProblem.DegreeCollapse.FramedDual
