import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPathSpace
import Wikipedia.NoExoticSixSphere.PathSpaceTranslation
import Wikipedia.NoExoticSixSphere.ComplexStructureRankReduction

/-!
# From complex-structure vanishing to fixed-endpoint path-family vanishing

Translate an arbitrary path family to antipodal endpoints, deform it into
the actual minimum-path locus, and transfer a nullhomotopy of its complex-
structure family back through the path-space homeomorphism. The required
complex-structure nullhomotopy remains an explicit hypothesis here.
-/

open Module
open scoped ContDiff Manifold

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalExponential

variable {n : ℕ} {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I in
theorem pathFamily_nullhomotopic_of_complexStructures (a b : OrthogonalOperators n)
    (J₀ : OrthogonalComplexStructures.Space n) (x₀ : M) (hd : finrank ℝ B + 2 < n)
    (hnull : ∀ J : C(M, OrthogonalComplexStructures.Space n),
      ∃ K, J.Homotopic (ContinuousMap.const _ K)) (p : C(M, Path a b)) :
    ∃ γ, p.Homotopic (ContinuousMap.const _ γ) := by
  let b₀ : OrthogonalOperators n := exp (Real.pi • J₀.1)
  have hanti : ((1 : OrthogonalOperators n)⁻¹ * b₀).1.1 =
      -(1 : Vector n →L[ℝ] Vector n) := by
    simpa only [inv_one, one_mul] using OrthogonalComplexStructures.exp_pi J₀
  let e := PathFamilies.translationHomeomorph (p x₀) (minimumPathMap 1 b₀ hanti J₀)
  let P : C(M, Path (1 : OrthogonalOperators n) b₀) := (toContinuousMap e).comp p
  obtain ⟨J, ⟨F⟩⟩ := exists_minimumPathMap_representative (I := I) 1 b₀ hanti hd P
  obtain ⟨K, hJK⟩ := hnull J
  have hmin : ((minimumPathMap 1 b₀ hanti).comp J).Homotopic
      (ContinuousMap.const _ (minimumPathMap 1 b₀ hanti K)) := by
    simpa only [ContinuousMap.comp_const] using
      (ContinuousMap.Homotopic.refl (minimumPathMap 1 b₀ hanti)).comp hJK
  have hP : P.Homotopic (ContinuousMap.const _ (minimumPathMap 1 b₀ hanti K)) :=
    (show P.Homotopic ((minimumPathMap 1 b₀ hanti).comp J) from ⟨F.toHomotopy⟩).trans hmin
  have hback := (ContinuousMap.Homotopic.refl (toContinuousMap e.symm)).comp hP
  have hleft : (toContinuousMap e.symm).comp P = p := by
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply (p x)
  rw [hleft, ContinuousMap.comp_const] at hback
  exact ⟨e.symm (minimumPathMap 1 b₀ hanti K), hback⟩

theorem fourthSphere_pathFamily_sixteen_of_rankSix
    (h6 : ∀ J : C(Sphere 4, OrthogonalComplexStructures.Space 6),
      ∃ K, J.Homotopic (ContinuousMap.const _ K))
    (a b : OrthogonalOperators 16) (p : C(Sphere 4, Path a b)) :
    ∃ γ, p.Homotopic (ContinuousMap.const _ γ) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨J₀⟩ := OrthogonalComplexStructures.nonempty_even 8
  obtain ⟨x₀⟩ : Nonempty (Sphere 4) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  exact pathFamily_nullhomotopic_of_complexStructures (I := 𝓡 4) a b J₀ x₀
    (by norm_num) (OrthogonalComplexStructures.fourthSphereVanishing_sixteen_of_six h6) p

end NoExoticSixSphere.OrthogonalPolygon
