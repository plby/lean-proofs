import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPathDeformation
import Wikipedia.NoExoticSixSphere.CircleHomotopyParameter
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Relative homotopy reflection for the minimum rotation family

Extend the homotopy parameter over the circle and apply the actual relative
path deformation. The endpoint fibers and protected parameters are already
minimum rotations, so their unique midpoint parameters remain fixed.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization ComplexStructures

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

theorem negative_antipodal (a : ComplexStructures.Space n) :
    (Cayley.relative a (negative a)).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  rw [Cayley.relative, toSymplectic_inv, toSymplectic_mul_self, antipode_operator]

noncomputable def rotationPathHomotopy (a : ComplexStructures.Space n)
    (f g : C(M, AnticommutingStructures.Space a)) (S : Set M) (F : f.HomotopyRel g S) :
    (rotationPathFamily f).HomotopyRel (rotationPathFamily g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} where
  toContinuousMap := (rotationPathFamily F.toContinuousMap).comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  map_zero_left z := by
    change AnticommutingStructures.rotation (F (0, z.2)) ((z.1 : ℝ) * Real.pi) =
      AnticommutingStructures.rotation (f z.2) ((z.1 : ℝ) * Real.pi)
    rw [F.apply_zero]
  map_one_left z := by
    change AnticommutingStructures.rotation (F (1, z.2)) ((z.1 : ℝ) * Real.pi) =
      AnticommutingStructures.rotation (g z.2) ((z.1 : ℝ) * Real.pi)
    rw [F.apply_one]
  prop' r z hz := by
    rcases z with ⟨t, x⟩
    change AnticommutingStructures.rotation (F (r, x)) ((t : ℝ) * Real.pi) =
      AnticommutingStructures.rotation (f x) ((t : ℝ) * Real.pi)
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      change AnticommutingStructures.rotation (F (r, x)) ((0 : ℝ) * Real.pi) =
        AnticommutingStructures.rotation (f x) ((0 : ℝ) * Real.pi)
      rw [zero_mul, AnticommutingStructures.rotation_zero, AnticommutingStructures.rotation_zero]
    · change t = 1 at ht
      subst t
      change AnticommutingStructures.rotation (F (r, x)) ((1 : ℝ) * Real.pi) =
        AnticommutingStructures.rotation (f x) ((1 : ℝ) * Real.pi)
      rw [one_mul, AnticommutingStructures.rotation_pi, AnticommutingStructures.rotation_pi]
    · rw [F.eq_fst r hx]

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem nonempty_rotationHomotopyRel_of_paths (a : ComplexStructures.Space n)
    (hd : finrank ℝ B + 1 < n) (f g : C(M, AnticommutingStructures.Space a)) (S : Set M)
    (F : (rotationPathFamily f).HomotopyRel (rotationPathFamily g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) : Nonempty (f.HomotopyRel g S) := by
  let P : C(unitInterval × (Circle × M), ComplexStructures.Space n) := F.toContinuousMap.comp {
    toFun z := (CircleHomotopyParameter.height z.2.1, (z.1, z.2.2))
    continuous_toFun :=
      (CircleHomotopyParameter.height.continuous.comp
        (continuous_fst.comp continuous_snd)).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  have hPa (z : Circle × M) : P (0, z) = a := by
    have he := F.eq_fst (CircleHomotopyParameter.height z.1)
      (show ((0 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from Or.inl rfl)
    change P (0, z) = AnticommutingStructures.rotation (f z.2) ((0 : ℝ) * Real.pi) at he
    simpa only [zero_mul, AnticommutingStructures.rotation_zero] using he
  have hPb (z : Circle × M) : P (1, z) = negative a := by
    have he := F.eq_fst (CircleHomotopyParameter.height z.1)
      (show ((1 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from
        Or.inr (Or.inl rfl))
    change P (1, z) = AnticommutingStructures.rotation (f z.2) ((1 : ℝ) * Real.pi) at he
    simpa only [one_mul, AnticommutingStructures.rotation_pi] using he
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 1) × B) < n := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  obtain ⟨J, ⟨G⟩⟩ := exists_homotopy_to_minimum_path_family (I := (𝓡 1).prod I)
    a (negative a) (negative_antipodal a) hdim P hPa hPb
  have hfixed (z : Circle × M) (K : AnticommutingStructures.Space a)
      (hK : ∀ u : unitInterval, P (u, z) =
        AnticommutingStructures.rotation K ((u : ℝ) * Real.pi)) : J z = K := by
    apply rotation_eq_of_paths
    intro u
    have he := G.fst_eq_snd
      (show (u, z) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ minimumPathParameters P a} from
        Or.inr (Or.inr ⟨K, hK⟩))
    exact he.symm.trans (hK u)
  refine ⟨{
    toContinuousMap := CircleHomotopyParameter.restrict J
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    change J (CircleHomotopyParameter.semicircle 0, x) = f x
    rw [CircleHomotopyParameter.semicircle_zero]
    apply hfixed (1, x) (f x)
    intro u
    change F (CircleHomotopyParameter.height 1, (u, x)) = _
    rw [CircleHomotopyParameter.height_one, F.apply_zero]
    rfl
  · intro x
    change J (CircleHomotopyParameter.semicircle 1, x) = g x
    rw [CircleHomotopyParameter.semicircle_one]
    apply hfixed (-1, x) (g x)
    intro u
    change F (CircleHomotopyParameter.height (-1), (u, x)) = _
    rw [CircleHomotopyParameter.height_neg_one, F.apply_one]
    rfl
  · intro t x hx
    change J (CircleHomotopyParameter.semicircle t, x) = f x
    apply hfixed (CircleHomotopyParameter.semicircle t, x) (f x)
    intro u
    exact F.eq_fst _ (Or.inr (Or.inr hx))

theorem rotationHomotopicRel_iff_paths (a : ComplexStructures.Space n)
    (hd : finrank ℝ B + 1 < n) (f g : C(M, AnticommutingStructures.Space a)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty ((rotationPathFamily f).HomotopyRel (rotationPathFamily g)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨rotationPathHomotopy a f g S F⟩
  · rintro ⟨F⟩
    exact nonempty_rotationHomotopyRel_of_paths (I := I) a hd f g S F

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
