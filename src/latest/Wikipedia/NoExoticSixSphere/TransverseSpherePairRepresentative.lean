import Wikipedia.NoExoticSixSphere.ManifoldTransverseRepresentative
import Wikipedia.NoExoticSixSphere.ManifoldIntersectionHomotopyParity
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing

/-!
# Actual transverse representatives of arbitrary continuous sphere-map pairs

Relative manifold smoothing and the proved generic perturbation construct
the representatives. The data retain both native smooth maps, genuine
homotopies from the original maps, native transversality, and finiteness of
the actual source-pair intersection set. No representative is supplied as
an unproved geometric assumption.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.MapIntersections

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

structure Representative (f g : C(Sphere 3, M)) where
  left : C(Sphere 3, M)
  right : C(Sphere 3, M)
  smooth_left : ContMDiff (𝓡 3) (𝓡 6) ∞ left
  smooth_right : ContMDiff (𝓡 3) (𝓡 6) ∞ right
  homotopic_left : f.Homotopic left
  homotopic_right : g.Homotopic right
  transverse : ∀ x y, left x = right y → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) left x).coprod (mfderiv (𝓡 3) (𝓡 6) right y))
  finite_pairs : (pairs left right).Finite

namespace Representative

variable {f g : C(Sphere 3, M)} (D : Representative f g)

def swap : Representative g f where
  left := D.right
  right := D.left
  smooth_left := D.smooth_right
  smooth_right := D.smooth_left
  homotopic_left := D.homotopic_right
  homotopic_right := D.homotopic_left
  transverse := by
    intro x y hxy
    let A : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) D.right x
    let B : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) D.left y
    have h : Surjective (B.coprod A) := D.transverse y x hxy.symm
    intro w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(v.2, v.1), ?_⟩
    change A v.2 + B v.1 = w
    rw [add_comm]
    exact hv
  finite_pairs := by
    let := D.finite_pairs.to_subtype
    exact finite_coe_iff.mp (Finite.of_equiv (pairs D.left D.right) (swapEquiv D.left D.right))

end Representative
end NoExoticSixSphere.MapIntersections

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem nonempty_intersectionRepresentative (f g : C(Sphere 3, M)) :
    Nonempty (Representative f g) := by
  obtain ⟨f', hf', Hf⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) f
  obtain ⟨g', hg', Hg⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) g
  obtain ⟨F, hF, HF, ht⟩ := e.exists_smooth_transverse_homotopic r f' g' hf' hg'
  have hfin : (pairs F g').Finite :=
    (e.intersectionParity_eq_of_smooth_families r (fun _ ↦ F) (fun _ ↦ g')
      (hF.comp contMDiff_snd) (hg'.comp contMDiff_snd) (fun _ _ ↦ ht)).1
  exact ⟨⟨F, g', hF, hg', Hf.trans HF, Hg, ht, hfin⟩⟩

def intersectionRepresentative (f g : C(Sphere 3, M)) : Representative f g :=
  Classical.choice (e.nonempty_intersectionRepresentative r f g)

end NoExoticSixSphere.EuclideanEmbedding
