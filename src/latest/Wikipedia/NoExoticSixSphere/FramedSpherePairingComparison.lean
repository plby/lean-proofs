import Wikipedia.NoExoticSixSphere.InternalSphereSmoothOpenTube
import Wikipedia.NoExoticSixSphere.SmoothSphereTubePairing
import Wikipedia.NoExoticSixSphere.GeometricIntersectionFundamentalClass
import Wikipedia.NoExoticSixSphere.SphereInternalNormalFrame

/-!
# Original cap and geometric pairings agree for a framed embedded first sphere

The smooth tube is constructed from the actual embedding, normal frame,
and tubular retraction. The proved local transverse contributions give
the original intersection count. Smoothing and a perturbation of only
the second map remove its smoothness and transversality assumptions.
Thus the two original pairings agree on this first sphere class and
every continuous second sphere class. Arbitrary immersed first classes
are not claimed to have embedded representatives here.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

attribute [local instance] SphereNormalCapNormalization.ambientDimension

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension) (r : TubularRetraction e)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)
  (m : M) [Subsingleton (π_ 2 M m)]

include r hi hC hd hiC hCr in
/-- Constructing the actual smooth tube identifies cap pairing with the transverse pair count. -/
theorem cap_pairing_eq_parity_of_framedSphere (g : C(Sphere 3, M))
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x y, f x = g y → Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) g y))) :
    MiddleCapEvaluation.pairing (E := Vector 6) m
      (modHomologyMap 2 (⟨f, hf.continuous⟩ : C(Sphere 3, M)) 3 (unitSphereModTopClass 2 2))
      (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) = MapIntersections.parity f g := by
  obtain ⟨Φ, hsource, hcore⟩ :=
    e.exists_internalSphereSmoothOpenTube f C r hf hi hC hd hiC hCr
  exact SmoothSphereTube.pairing_eq_intersection_parity Φ hsource f hcore g hf hg ht m

include hi hC hd hiC hCr in
/-- Perturbing only the second sphere retains the original framed embedded first sphere. -/
theorem cap_pairing_eq_intersectionNumber_of_framedSphere (g : C(Sphere 3, M)) :
    MiddleCapEvaluation.pairing (E := Vector 6) m
      (modHomologyMap 2 (⟨f, hf.continuous⟩ : C(Sphere 3, M)) 3 (unitSphereModTopClass 2 2))
      (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) =
      sphereIntersectionNumber e r (⟨f, hf.continuous⟩ : C(Sphere 3, M)) g := by
  let F : C(Sphere 3, M) := ⟨f, hf.continuous⟩
  obtain ⟨g₀, hg₀, Hg⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) g
  obtain ⟨G, hG, HG, hGF⟩ := e.exists_smooth_transverse_homotopic r g₀ F hg₀ hf
  have H := Hg.trans HG
  have ht : ∀ x y, f x = G y → Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) G y)) := by
    intro x y hxy
    exact SphereSumNeck.nativeSphereTransverseAt_swap (hGF y x hxy.symm)
  rw [modHomologyMap_homotopic 2 H 3]
  exact (cap_pairing_eq_parity_of_framedSphere e f C r hf hi hC hd hiC hCr m G hG ht).trans
    ((sphereIntersectionNumber_eq_parity e r F G hf hG ht).symm.trans
      (sphereIntersectionNumber_homotopic e r F F g G (.refl F) H).symm)

include hi hC hd hiC hCr in
/-- The two original homological pairings agree on this framed embedded first sphere class. -/
theorem cap_pairing_eq_geometric_of_framedSphere (g : C(Sphere 3, M)) :
    MiddleCapEvaluation.pairing (E := Vector 6) m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M)))
      (SixSphereMiddleParity.sphereClass g) =
    modTwoHomologyIntersection e r m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M)))
      (SixSphereMiddleParity.sphereClass g) :=
  (cap_pairing_eq_intersectionNumber_of_framedSphere e f C r hf hi hC hd hiC hCr m g).trans
    (modTwoHomologyIntersection_standardSphereClass e r m
      (⟨f, hf.continuous⟩ : C(Sphere 3, M)) g).symm

include hi hC hd hiC hCr in
/-- Native Hurewicz representatives extend the comparison to every second homology class. -/
theorem cap_pairing_eq_geometric_all_right_of_framedSphere (b : ModHomology 2 M 3) :
    MiddleCapEvaluation.pairing (E := Vector 6) m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M))) b =
    modTwoHomologyIntersection e r m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M))) b := by
  obtain ⟨g, hg⟩ := SmoothCube.modTwoSphereClass_surjective m b
  rw [SmoothCube.modTwoSphereClass_eq_standard g] at hg
  rw [← hg]
  exact cap_pairing_eq_geometric_of_framedSphere e f C r hf hi hC hd hiC hCr m g.val

include hi hd in
/-- Constructing the internal normal frame removes any separately supplied sphere-frame data. -/
theorem cap_pairing_eq_geometric_all_right_of_embedding
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (b : ModHomology 2 M 3) :
    MiddleCapEvaluation.pairing (E := Vector 6) m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M))) b =
    modTwoHomologyIntersection e r m
      (SixSphereMiddleParity.sphereClass (⟨f, hf.continuous⟩ : C(Sphere 3, M))) b := by
  obtain ⟨C', hC', hn, hr⟩ := exists_smooth_internalNormalFrame e f a hf hd
  have hiC' (s : Sphere 3) : Injective (C' s) := Stiefel.injective ⟨C' s, hn s⟩
  exact cap_pairing_eq_geometric_all_right_of_framedSphere e f C' r hf hi hC' hd hiC' hr m b

end NoExoticSixSphere.EuclideanEmbedding
