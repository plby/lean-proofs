import Wikipedia.NoExoticSixSphere.NativeSphereIntersectionCount
import Wikipedia.NoExoticSixSphere.GeometricIntersectionPinchGenericity
import Wikipedia.NoExoticSixSphere.BasedSphereMapSmoothing

/-!
# Geometric intersection additivity for native homotopy-group multiplication

The count is additive for the actual native cubical concatenation descended
to the original sphere. Flat based smooth representatives and a common
generic comparison map are constructed internally. The final statement
allows arbitrary continuous based inputs and an arbitrary continuous
comparison map. Its concatenation represents native third-homotopy-group
multiplication by the already checked class identity.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem concatenate_homotopicRel (f g F G : BasedMap 3 X x)
    (Hf : f.val.HomotopicRel F.val {spherePole 3})
    (Hg : g.val.HomotopicRel G.val {spherePole 3}) :
    (concatenate f g).val.HomotopicRel (concatenate F G).val {spherePole 3} := by
  apply (sphereClass_eq_iff (by decide : 0 < 3) _ _).mp
  rw [sphereClass_concatenate, sphereClass_concatenate]
  exact congrArg₂ (· * ·)
    ((sphereClass_eq_iff (by decide : 0 < 3) f F).mpr Hf)
    ((sphereClass_eq_iff (by decide : 0 < 3) g G).mpr Hg)

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections SmoothCube

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) {m : M}

theorem sphereIntersectionNumber_concatenate_of_flat (f g : BasedMap 3 M m)
    (k : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f.val) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g.val)
    (hk : ContMDiff (𝓡 3) (𝓡 6) ∞ k) (hm : m ∉ range k)
    (hfk : ∀ y z, f.val y = k z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f.val y).coprod (mfderiv (𝓡 3) (𝓡 6) k z)))
    (hgk : ∀ y z, g.val y = k z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g.val y).coprod (mfderiv (𝓡 3) (𝓡 6) k z)))
    {U : Set (Sphere 3)} (hU : IsOpen U) (hb : spherePole 3 ∈ U)
    (hfU : EqOn f.val (fun _ ↦ m) U) (hgU : EqOn g.val (fun _ ↦ m) U) :
    sphereIntersectionNumber e r (concatenate f g).val k =
      sphereIntersectionNumber e r f.val k + sphereIntersectionNumber e r g.val k := by
  have hP := contMDiff_concatenate f g hf hg hU hb hfU hgU
  have htP := transverse_concatenate f g k hf hg hm hfk hgk
  have hfinf := e.finite_transverse_sphere_pairs_of_retraction r f.val k hf hk hfk
  have hfing := e.finite_transverse_sphere_pairs_of_retraction r g.val k hg hk hgk
  rw [sphereIntersectionNumber_eq_parity e r (concatenate f g).val k hP hk htP,
    sphereIntersectionNumber_eq_parity e r f.val k hf hk hfk,
    sphereIntersectionNumber_eq_parity e r g.val k hg hk hgk]
  exact concatenate_parity f g k hm hfinf hfing

theorem sphereIntersectionNumber_concatenate (f g : BasedMap 3 M m) (k : C(Sphere 3, M)) :
    sphereIntersectionNumber e r (concatenate f g).val k =
      sphereIntersectionNumber e r f.val k + sphereIntersectionNumber e r g.val k := by
  obtain ⟨F₀, hF, HF, U, hU, hbU, hFU⟩ :=
    exists_smooth_flat_based_sphereMap (spherePole 3) f.val
  obtain ⟨G₀, hG, HG, V, hV, hbV, hGV⟩ :=
    exists_smooth_flat_based_sphereMap (spherePole 3) g.val
  let F : BasedMap 3 M m :=
    ⟨F₀, (HF.fst_eq_snd (mem_singleton _)).symm.trans f.property⟩
  let G : BasedMap 3 M m :=
    ⟨G₀, (HG.fst_eq_snd (mem_singleton _)).symm.trans g.property⟩
  have Hf : f.val.HomotopicRel F.val {spherePole 3} := HF
  have Hg : g.val.HomotopicRel G.val {spherePole 3} := HG
  obtain ⟨K, hK, HK, hmK, hKF, hKG⟩ :=
    e.exists_smooth_common_transverse_avoiding r k F₀ G₀ hF hG m
  have hfUV : EqOn F.val (fun _ ↦ m) (U ∩ V) :=
    fun y hy ↦ (hFU hy.1).trans f.property
  have hgUV : EqOn G.val (fun _ ↦ m) (U ∩ V) :=
    fun y hy ↦ (hGV hy.2).trans g.property
  have HP := concatenate_homotopicRel f g F G Hf Hg
  calc
    sphereIntersectionNumber e r (concatenate f g).val k =
        sphereIntersectionNumber e r (concatenate F G).val K :=
      sphereIntersectionNumber_homotopic e r _ _ k K HP.homotopic HK
    _ = sphereIntersectionNumber e r F.val K + sphereIntersectionNumber e r G.val K :=
      sphereIntersectionNumber_concatenate_of_flat e r F G K hF hG hK hmK
        (transverse_swap K F₀ hKF) (transverse_swap K G₀ hKG)
        (hU.inter hV) ⟨hbU, hbV⟩ hfUV hgUV
    _ = sphereIntersectionNumber e r f.val k + sphereIntersectionNumber e r g.val k :=
      congrArg₂ (· + ·)
        (sphereIntersectionNumber_homotopic e r f.val F.val k K Hf.homotopic HK).symm
        (sphereIntersectionNumber_homotopic e r g.val G.val k K Hg.homotopic HK).symm

end NoExoticSixSphere.EuclideanEmbedding
