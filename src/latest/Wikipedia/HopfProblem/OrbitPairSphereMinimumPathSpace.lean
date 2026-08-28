import Wikipedia.HopfProblem.OrbitPairSpherePathHomotopyComparison
import Wikipedia.HopfProblem.OrbitPairSphereMinimumSphere
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# The actual semicircle map into the native sphere path space

The target is mathlib's `Path a b`, with its compact-open topology. The source
is the actual unit tangent direction space, already identified with the standard
sphere of one lower dimension. Currying transfers the proved representative
and relative homotopy comparison theorems to this native path-space map.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereSemicircle

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def minimumPathMap (a b : Sphere n) (hanti : b.val = -a.val) : C(Direction a, Path a b) :=
  PathFamilies.curry (semicirclePathFamily a (ContinuousMap.id _))
    (semicirclePathFamily_zero a (ContinuousMap.id _))
    (semicirclePathFamily_one a b hanti (ContinuousMap.id _))

theorem minimumPathMap_injective (a b : Sphere n) (hanti : b.val = -a.val) :
    Function.Injective (minimumPathMap a b hanti) := by
  intro y z he
  apply direction_eq_of_paths a y z
  intro u
  exact congrArg (fun p : Path a b => (p u).val) he

theorem uncurry_minimumPathMap_comp (a b : Sphere n) (hanti : b.val = -a.val)
    (Y : C(X, Direction a)) :
    PathFamilies.uncurry ((minimumPathMap a b hanti).comp Y) = semicirclePathFamily a Y := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem mem_minimumPathMap_range_iff (a b : Sphere n) (hanti : b.val = -a.val) (p : Path a b) :
    p ∈ range (minimumPathMap a b hanti) ↔ ∃ y : Direction a,
      ∀ u : unitInterval, (p u).val = SphereGreatCircle.curve a.val y.val Real.pi u := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun _ => rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Path.ext ?_⟩
    funext u
    exact Subtype.ext (hy u).symm

theorem minimumPathParameters_eq_preimage (a b : Sphere n) (hanti : b.val = -a.val)
    (p : C(X, Path a b)) :
    minimumPathParameters a (PathFamilies.uncurry p) = p ⁻¹' range (minimumPathMap a b hanti) := by
  ext x
  exact (mem_minimumPathMap_range_iff a b hanti (p x)).symm

def minimumSpherePathMap {n : ℕ} (a b : Sphere (n + 1)) (hanti : b.val = -a.val) :
    C(Sphere n, Path a b) :=
  (minimumPathMap a b hanti).comp
    ((directionSphereHomeomorph a).symm : C(Sphere n, Direction a))

theorem minimumSpherePathMap_injective {n : ℕ} (a b : Sphere (n + 1))
    (hanti : b.val = -a.val) : Function.Injective (minimumSpherePathMap a b hanti) :=
  (minimumPathMap_injective a b hanti).comp (directionSphereHomeomorph a).symm.injective

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_minimumPathMap_representative (a b : Sphere n) (hanti : b.val = -a.val)
    (hd : finrank ℝ B + 2 < 2 * n) (p : C(M, Path a b)) :
    ∃ Y : C(M, Direction a), Nonempty (p.HomotopyRel ((minimumPathMap a b hanti).comp Y)
      (p ⁻¹' range (minimumPathMap a b hanti))) := by
  obtain ⟨Y, ⟨G⟩⟩ := exists_continuous_path_deformation (I := I) a b hanti
    (PathFamilies.uncurry p) (PathFamilies.uncurry_zero p) (PathFamilies.uncurry_one p) hd
  rw [minimumPathParameters_eq_preimage a b hanti p] at G
  exact ⟨Y, ⟨PathFamilies.curryHomotopy
    (G.cast rfl (uncurry_minimumPathMap_comp a b hanti Y).symm)⟩⟩

theorem minimumPathMap_homotopicRel_iff (a b : Sphere n) (hanti : b.val = -a.val)
    (hd : finrank ℝ B + 3 < 2 * n) (f g : C(M, Direction a)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((minimumPathMap a b hanti).comp f).HomotopyRel
        ((minimumPathMap a b hanti).comp g) S) := by
  have h := directionHomotopicRel_iff_paths (I := I) a b hanti hd f g S
  rw [← uncurry_minimumPathMap_comp a b hanti f,
    ← uncurry_minimumPathMap_comp a b hanti g] at h
  exact h.trans (PathFamilies.homotopicRel_iff_uncurry
    ((minimumPathMap a b hanti).comp f) ((minimumPathMap a b hanti).comp g) S).symm

theorem exists_based_minimumPathMap_representative (a b : Sphere n) (hanti : b.val = -a.val)
    (hd : finrank ℝ B + 2 < 2 * n) (x₀ : M) (y₀ : Direction a)
    (p : C(M, Path a b)) (hp : p x₀ = minimumPathMap a b hanti y₀) :
    ∃ Y : C(M, Direction a), Y x₀ = y₀ ∧
      Nonempty (p.HomotopyRel ((minimumPathMap a b hanti).comp Y) {x₀}) := by
  obtain ⟨Y, ⟨G⟩⟩ := exists_minimumPathMap_representative (I := I) a b hanti hd p
  have hx : x₀ ∈ p ⁻¹' range (minimumPathMap a b hanti) := ⟨y₀, hp.symm⟩
  have hY : Y x₀ = y₀ := minimumPathMap_injective a b hanti
    ((G.fst_eq_snd hx).symm.trans hp)
  refine ⟨Y, hY, ⟨{ toHomotopy := G.toHomotopy, prop' := ?_ }⟩⟩
  intro t x hx'
  have he : x = x₀ := hx'
  subst x
  exact G.eq_fst t hx

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
