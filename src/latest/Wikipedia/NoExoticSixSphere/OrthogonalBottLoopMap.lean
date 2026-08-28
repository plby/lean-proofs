import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPathSpace
import Wikipedia.NoExoticSixSphere.PathSpaceTranslation

/-!
# The first actual Bott map into the orthogonal loop space

Translate the reference minimum path to the constant loop by a pointwise
path-space homeomorphism. The resulting map is based at the chosen complex
structure. Relative representatives and homotopy comparison retain the
dimension bounds proved for minimum path families.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization

variable {n : ℕ}

noncomputable def bottLoopMap (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) :
    C(OrthogonalComplexStructures.Space n, Path a a) :=
  (toContinuousMap (PathFamilies.translationHomeomorph
    (minimumPathMap a b hanti J₀) (Path.refl a))).comp (minimumPathMap a b hanti)

theorem bottLoopMap_base (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) : bottLoopMap a b hanti J₀ J₀ = Path.refl a :=
  PathFamilies.translate_reference _ _

theorem bottLoopMap_injective (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) : Function.Injective (bottLoopMap a b hanti J₀) :=
  (PathFamilies.translationHomeomorph
    (minimumPathMap a b hanti J₀) (Path.refl a)).injective.comp (minimumPathMap_injective a b hanti)

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_bottLoopMap_representative (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : finrank ℝ B + 2 < n)
    (p : C(M, Path a a)) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n),
      Nonempty (p.HomotopyRel ((bottLoopMap a b hanti J₀).comp J)
        (p ⁻¹' range (bottLoopMap a b hanti J₀))) := by
  let e := PathFamilies.translationHomeomorph (minimumPathMap a b hanti J₀) (Path.refl a)
  let q := (toContinuousMap e.symm).comp p
  obtain ⟨J, ⟨G⟩⟩ := exists_minimumPathMap_representative (I := I) a b hanti hd q
  have hleft : (toContinuousMap e).comp q = p := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (p x)
  have hright : (toContinuousMap e).comp ((minimumPathMap a b hanti).comp J) =
      (bottLoopMap a b hanti J₀).comp J := rfl
  have hsets : q ⁻¹' range (minimumPathMap a b hanti) =
      p ⁻¹' range (bottLoopMap a b hanti J₀) := by
    ext x
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (congrArg e hK).trans (e.apply_symm_apply (p x))
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (e.symm_apply_apply (minimumPathMap a b hanti K)).symm.trans (congrArg e.symm hK)
  have G' := (G.compContinuousMap (toContinuousMap e)).cast hleft hright
  rw [hsets] at G'
  exact ⟨J, ⟨G'⟩⟩

theorem bottLoopMap_homotopicRel_iff (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : finrank ℝ B + 3 < n)
    (f g : C(M, OrthogonalComplexStructures.Space n)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((bottLoopMap a b hanti J₀).comp f).HomotopyRel
        ((bottLoopMap a b hanti J₀).comp g) S) :=
  (minimumPathMap_homotopicRel_iff (I := I) a b hanti hd f g S).trans
    (homotopicRel_iff_postcompose_homeomorph
      (PathFamilies.translationHomeomorph (minimumPathMap a b hanti J₀) (Path.refl a))
      ((minimumPathMap a b hanti).comp f) ((minimumPathMap a b hanti).comp g) S)

theorem exists_based_bottLoopMap_representative (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : finrank ℝ B + 2 < n)
    (x₀ : M) (p : C(M, Path a a)) (hp : p x₀ = Path.refl a) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n), J x₀ = J₀ ∧
      Nonempty (p.HomotopyRel ((bottLoopMap a b hanti J₀).comp J) {x₀}) := by
  obtain ⟨J, ⟨G⟩⟩ := exists_bottLoopMap_representative (I := I) a b hanti J₀ hd p
  have hx : x₀ ∈ p ⁻¹' range (bottLoopMap a b hanti J₀) :=
    ⟨J₀, (bottLoopMap_base a b hanti J₀).trans hp.symm⟩
  have hJ : J x₀ = J₀ := bottLoopMap_injective a b hanti J₀
    ((G.fst_eq_snd hx).symm.trans (hp.trans (bottLoopMap_base a b hanti J₀).symm))
  refine ⟨J, hJ, ⟨{ toHomotopy := G.toHomotopy, prop' := ?_ }⟩⟩
  intro r x hx'
  have he : x = x₀ := hx'
  subst x
  exact G.eq_fst r hx

end NoExoticSixSphere.OrthogonalPolygon
