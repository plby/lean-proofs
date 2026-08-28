import Wikipedia.NoExoticSixSphere.GeometricIntersectionPinch
import Wikipedia.NoExoticSixSphere.SphereLocalFlattening
import Wikipedia.NoExoticSixSphere.SpherePinchHomotopy

/-!
# Pinch additivity without a local-constancy hypothesis

Choose a small neighborhood of the common basepoint whose two images avoid
the compact comparison image. The constructed smooth local collapse fixes
the complement and stays in that neighborhood. It makes both input maps
constant near the basepoint without creating intersections or changing
their native differential at an intersection. The actual based homotopies
give a homotopy of the original pinch, so geometric homotopy invariance
removes the extra local-constancy hypothesis from the previous theorem.

Smoothness, transversality of the two input pairs, and avoidance of their
common base value remain explicit hypotheses.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFold

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem transverse_of_local_agreement (f F k : C(Sphere 3, M)) (U : Set (Sphere 3))
    (havoid : ∀ x ∈ U, F x ∉ range k)
    (heq : ∀ x ∉ U, (F : Sphere 3 → M) =ᶠ[𝓝 x] f)
    (ht : ∀ x y, f x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) k y))) :
    ∀ x y, F x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) k y)) := by
  intro x y hxy
  have hx : x ∉ U := fun h ↦ havoid x h ⟨y, hxy.symm⟩
  have he := heq x hx
  have hfxy : f x = k y := he.eq_of_nhds.symm.trans hxy
  change Surjective ((mfderiv (𝓡 3) (𝓡 6) F x : Vector 3 →L[ℝ] Vector 6).coprod
    (mfderiv (𝓡 3) (𝓡 6) k y : Vector 3 →L[ℝ] Vector 6))
  rw [he.mfderiv_eq]
  exact ht x y hfxy

end NoExoticSixSphere.SphereFold

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections SphereFold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

theorem sphereIntersectionNumber_pinch_of_transverse (v : Sphere 3)
    (f g k : C(Sphere 3, M)) (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hk : ContMDiff (𝓡 3) (𝓡 6) ∞ k) (hm : f (antipode v) ∉ range k)
    (hfk : ∀ x y, f x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) k y)))
    (hgk : ∀ x y, g x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) k y))) :
    sphereIntersectionNumber e r (pinch v f g hbase) k =
      sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  let U : Set (Sphere 3) := f ⁻¹' (range k)ᶜ ∩ g ⁻¹' (range k)ᶜ
  have hkc : IsClosed (range k) := (isCompact_range k.continuous).isClosed
  have hU : IsOpen U := (hkc.isOpen_compl.preimage f.continuous).inter
    (hkc.isOpen_compl.preimage g.continuous)
  have hbU : antipode v ∈ U := ⟨hm, by
    change g (antipode v) ∉ range k
    rwa [← hbase]⟩
  obtain ⟨F, hF, ⟨H⟩, hFU, hFid, W, hW, hbW, hFW⟩ :=
    SphereCap.exists_smooth_localFlattening (n := 3) (antipode v) hU hbU
  have HF : (ContinuousMap.id (Sphere 3)).HomotopicRel F {antipode v} :=
    ⟨{ toHomotopy := H.toHomotopy
       prop' := fun t x hx ↦ H.eq_fst t (Or.inr hx) }⟩
  have Hf : f.HomotopicRel (f.comp F) {antipode v} := HF.comp_continuousMap f
  have Hg : g.HomotopicRel (g.comp F) {antipode v} := HF.comp_continuousMap g
  have hFb : F (antipode v) = antipode v :=
    (HF.fst_eq_snd (mem_singleton _)).symm
  have hbase' : (f.comp F) (antipode v) = (g.comp F) (antipode v) := by
    change f (F (antipode v)) = g (F (antipode v))
    rw [hFb, hbase]
  have hm' : (f.comp F) (antipode v) ∉ range k := by
    change f (F (antipode v)) ∉ range k
    rwa [hFb]
  have hfk' := transverse_of_local_agreement f (f.comp F) k U
    (fun x hx ↦ (hFU hx).1)
    (fun x hx ↦ (hFid x hx).mono (fun y hy ↦ congrArg f hy)) hfk
  have hgk' := transverse_of_local_agreement g (g.comp F) k U
    (fun x hx ↦ (hFU hx).2)
    (fun x hx ↦ (hFid x hx).mono (fun y hy ↦ congrArg g hy)) hgk
  have hfW : EqOn (f.comp F) (fun _ ↦ f (antipode v)) W :=
    fun x hx ↦ congrArg f (hFW hx)
  have hgW : EqOn (g.comp F) (fun _ ↦ f (antipode v)) W :=
    fun x hx ↦ (congrArg g (hFW hx)).trans hbase.symm
  have HP := pinch_homotopic v f g (f.comp F) (g.comp F) hbase hbase' Hf Hg
  calc
    sphereIntersectionNumber e r (pinch v f g hbase) k =
        sphereIntersectionNumber e r (pinch v (f.comp F) (g.comp F) hbase') k :=
      sphereIntersectionNumber_homotopic e r _ _ k k HP (.refl k)
    _ = sphereIntersectionNumber e r (f.comp F) k +
        sphereIntersectionNumber e r (g.comp F) k :=
      sphereIntersectionNumber_pinch e r v (f.comp F) (g.comp F) k hbase'
        (hf.comp hF) (hg.comp hF) hk hm' hfk' hgk' (f (antipode v)) hW hbW hfW hgW
    _ = sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k :=
      congrArg₂ (· + ·)
        (sphereIntersectionNumber_homotopic e r f (f.comp F) k k Hf.homotopic (.refl k)).symm
        (sphereIntersectionNumber_homotopic e r g (g.comp F) k k Hg.homotopic (.refl k)).symm

end NoExoticSixSphere.EuclideanEmbedding
