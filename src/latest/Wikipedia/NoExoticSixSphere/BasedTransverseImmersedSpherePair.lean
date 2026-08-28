import Wikipedia.NoExoticSixSphere.BasedImmersedSpherePairAtCenter
import Wikipedia.NoExoticSixSphere.ProtectedSphereIntersectionCutoff
import Wikipedia.NoExoticSixSphere.RelativeTransverseImmersedRepresentative

/-!
# Fully prepared transverse immersed representatives of arbitrary based pairs

Both original based homotopy classes are retained. The actual representatives
are smooth immersions, self-transverse and mutually transverse everywhere,
and their common center has exactly one preimage on each sphere. The local
crossing, global branch exclusion, cutoff, parameter, and slice are constructed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [T2Space M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_based_transverse_immersed_pair
    (f g : C(Sphere 3, M)) (hzero : f (sourceChart 0) = g (sourceChart 0)) :
    ∃ F G : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧
      ContMDiff (𝓡 3) (𝓡 6) ∞ G ∧ f.HomotopicRel F {sourceChart 0} ∧
      g.HomotopicRel G {sourceChart 0} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) F s)) ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) G s)) ∧
      NativeSphereSelfTransverse F ∧ NativeSphereSelfTransverse G ∧
      NativeSpherePairTransverse F G ∧ F (sourceChart 0) = G (sourceChart 0) ∧
      (∀ s, F s = F (sourceChart 0) → s = sourceChart 0) ∧
      (∀ s, G s = G (sourceChart 0) → s = sourceChart 0) := by
  obtain ⟨F, G, hF, hG, HF, HG, hFi, hGi, hFt, hGt, hFG0, hFGt, hFu, hGu⟩ :=
    e.exists_based_immersed_pair_transverse_at_center r f g hzero
  obtain ⟨χ, hχ, hn, hbound, hχ0, hprotected⟩ :=
    exists_protected_intersection_cutoff F G hF hG hFG0 hFu hGu hFGt
  have hm : ∀ x y, χ x = 0 → F x = G y → NativeSphereTransverseAt F G x y := by
    intro x y hx he
    obtain ⟨rfl, rfl⟩ := hprotected x y hx he
    exact hFGt
  obtain ⟨K, hK, HK, hKi, hKt, hKGt, _, ha⟩ :=
    e.exists_relative_immersed_representative_transverse_to r F G hF hG χ hχ hn hbound
      (fun x _ ↦ hFi x) (fun x y _ _ hne he ↦ hFt x y hne he) hm (F (sourceChart 0))
  have HK0 : F (sourceChart 0) = K (sourceChart 0) := HK.fst_eq_snd hχ0
  have HFK : F.HomotopicRel K {sourceChart 0} := by
    obtain ⟨H⟩ := HK
    refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
    intro u x hx
    rcases hx with rfl
    exact H.eq_fst u hχ0
  refine ⟨K, G, hK, hG, HF.trans HFK, HG, hKi, hGi, hKt, hGt, hKGt,
    HK0.symm.trans hFG0, ?_, hGu⟩
  intro x hx
  by_cases hχx : χ x = 0
  · exact hFu x ((HK.fst_eq_snd hχx).trans (hx.trans HK0.symm))
  · exact (ha x hχx (hx.trans HK0.symm)).elim

end NoExoticSixSphere.EuclideanEmbedding
