import Wikipedia.NoExoticSixSphere.PathFamilyCurrying
import Wikipedia.NoExoticSixSphere.MinimumPathHomotopyComparison

/-!
# The actual minimum-path map into the native orthogonal path space

The domain is the space of orthogonal complex structures and the target is
mathlib's `Path a b` with its compact-open topology. Relative representatives
and homotopy comparison are transferred from the checked path-family theorems.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalExponential

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def minimumPathMap (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    C(OrthogonalComplexStructures.Space n, Path a b) :=
  PathFamilies.curry (complexStructurePathFamily a (ContinuousMap.id _))
    (by
      intro J
      change a * exp ((0 : ℝ) • (Real.pi • J.1)) = a
      rw [zero_smul, exp_zero, mul_one])
    (by
      intro J
      change a * exp ((1 : ℝ) • (Real.pi • J.1)) = b
      rw [one_smul]
      exact complexStructure_endpoint a b hanti J)

theorem minimumPathMap_injective (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    Function.Injective (minimumPathMap a b hanti) := by
  intro J K h
  apply complexStructure_eq_of_paths a J K
  intro u
  exact congrArg (fun p : Path a b ↦ p u) h

theorem uncurry_minimumPathMap_comp (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J : C(X, OrthogonalComplexStructures.Space n)) :
    PathFamilies.uncurry ((minimumPathMap a b hanti).comp J) = complexStructurePathFamily a J := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem mem_minimumPathMap_range_iff (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n)) (p : Path a b) :
    p ∈ range (minimumPathMap a b hanti) ↔
      ∃ J : OrthogonalComplexStructures.Space n,
        ∀ u : unitInterval, p u = a * exp ((u : ℝ) • (Real.pi • J.1)) := by
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨J, fun _ ↦ rfl⟩
  · rintro ⟨J, hJ⟩
    refine ⟨J, Path.ext ?_⟩
    funext u
    exact (hJ u).symm

theorem minimumPathParameters_eq_preimage (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n)) (p : C(X, Path a b)) :
    minimumPathParameters (PathFamilies.uncurry p) a = p ⁻¹' range (minimumPathMap a b hanti) := by
  ext x
  exact (mem_minimumPathMap_range_iff a b hanti (p x)).symm

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_minimumPathMap_representative (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hd : finrank ℝ B + 2 < n) (p : C(M, Path a b)) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n),
      Nonempty (p.HomotopyRel ((minimumPathMap a b hanti).comp J)
        (p ⁻¹' range (minimumPathMap a b hanti))) := by
  obtain ⟨J, ⟨G⟩⟩ := exists_homotopy_to_minimum_path_family (I := I) a b hanti hd
    (PathFamilies.uncurry p) (PathFamilies.uncurry_zero p) (PathFamilies.uncurry_one p)
  rw [minimumPathParameters_eq_preimage a b hanti p] at G
  exact ⟨J, ⟨PathFamilies.curryHomotopy
    (G.cast rfl (uncurry_minimumPathMap_comp a b hanti J).symm)⟩⟩

theorem minimumPathMap_homotopicRel_iff (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hd : finrank ℝ B + 3 < n)
    (f g : C(M, OrthogonalComplexStructures.Space n)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((minimumPathMap a b hanti).comp f).HomotopyRel
        ((minimumPathMap a b hanti).comp g) S) := by
  have h := complexStructureHomotopicRel_iff_paths (I := I) a b hanti hd f g S
  rw [← uncurry_minimumPathMap_comp a b hanti f,
    ← uncurry_minimumPathMap_comp a b hanti g] at h
  exact h.trans (PathFamilies.homotopicRel_iff_uncurry
    ((minimumPathMap a b hanti).comp f) ((minimumPathMap a b hanti).comp g) S).symm

theorem exists_based_minimumPathMap_representative (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hd : finrank ℝ B + 2 < n) (x₀ : M) (J₀ : OrthogonalComplexStructures.Space n)
    (p : C(M, Path a b)) (hp : p x₀ = minimumPathMap a b hanti J₀) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n), J x₀ = J₀ ∧
      Nonempty (p.HomotopyRel ((minimumPathMap a b hanti).comp J) {x₀}) := by
  obtain ⟨J, ⟨G⟩⟩ := exists_minimumPathMap_representative (I := I) a b hanti hd p
  have hx : x₀ ∈ p ⁻¹' range (minimumPathMap a b hanti) := ⟨J₀, hp.symm⟩
  have hJ : J x₀ = J₀ := minimumPathMap_injective a b hanti
    ((G.fst_eq_snd hx).symm.trans hp)
  refine ⟨J, hJ, ⟨{ toHomotopy := G.toHomotopy, prop' := ?_ }⟩⟩
  intro r x hx'
  have he : x = x₀ := hx'
  subst x
  exact G.eq_fst r hx

end NoExoticSixSphere.OrthogonalPolygon
