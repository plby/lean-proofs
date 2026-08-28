import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPathDeformation
import Wikipedia.NoExoticSixSphere.CircleHomotopyParameter
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Relative homotopy comparison for minimum exponential path families

An arbitrary continuous path-family homotopy is extended over the circle,
then deformed into minimum paths. The endpoint fibers and every protected
parameter are already minima, so they remain fixed. A minimum path determines
its complex structure at half time, giving the relative homotopy in the
complex-structure space. No polygon mesh or energy assumptions remain.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization Exponential

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

noncomputable def complexStructurePathHomotopy
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (f g : C(M, ComplexStructures.Space n)) (S : Set M)
    (F : f.HomotopyRel g S) :
    (complexStructurePathFamily a f).HomotopyRel (complexStructurePathFamily a g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} where
  toContinuousMap := (complexStructurePathFamily a F.toContinuousMap).comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  map_zero_left z := by
    change a * exp ((z.1 : ℝ) • (Real.pi • (F (0, z.2)).1)) =
      a * exp ((z.1 : ℝ) • (Real.pi • (f z.2).1))
    rw [F.apply_zero]
  map_one_left z := by
    change a * exp ((z.1 : ℝ) • (Real.pi • (F (1, z.2)).1)) =
      a * exp ((z.1 : ℝ) • (Real.pi • (g z.2).1))
    rw [F.apply_one]
  prop' r z hz := by
    rcases z with ⟨t, x⟩
    change a * exp ((t : ℝ) • (Real.pi • (F (r, x)).1)) =
      a * exp ((t : ℝ) • (Real.pi • (f x).1))
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      change a * exp ((0 : ℝ) • (Real.pi • (F (r, x)).1)) =
        a * exp ((0 : ℝ) • (Real.pi • (f x).1))
      simp only [zero_smul, exp_zero]
    · change t = 1 at ht
      subst t
      change a * exp ((1 : ℝ) • (Real.pi • (F (r, x)).1)) =
        a * exp ((1 : ℝ) • (Real.pi • (f x).1))
      simp only [one_smul]
      rw [complexStructure_endpoint a b hanti, complexStructure_endpoint a b hanti]
    · rw [F.eq_fst r hx]

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem nonempty_complexStructureHomotopyRel_of_paths
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hd : finrank ℝ B + 1 < n)
    (f g : C(M, ComplexStructures.Space n)) (S : Set M)
    (F : (complexStructurePathFamily a f).HomotopyRel (complexStructurePathFamily a g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) : Nonempty (f.HomotopyRel g S) := by
  let P : C(unitInterval × (Circle × M), symplecticSubgroup n) := F.toContinuousMap.comp {
    toFun z := (CircleHomotopyParameter.height z.2.1, (z.1, z.2.2))
    continuous_toFun :=
      (CircleHomotopyParameter.height.continuous.comp
        (continuous_fst.comp continuous_snd)).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  have hPa (z : Circle × M) : P (0, z) = a := by
    have he := F.eq_fst (CircleHomotopyParameter.height z.1)
      (show ((0 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from Or.inl rfl)
    change P (0, z) = a * exp ((0 : ℝ) • (Real.pi • (f z.2).1)) at he
    simpa only [zero_smul, exp_zero, mul_one] using he
  have hPb (z : Circle × M) : P (1, z) = b := by
    have he := F.eq_fst (CircleHomotopyParameter.height z.1)
      (show ((1 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from
        Or.inr (Or.inl rfl))
    change P (1, z) = a * exp ((1 : ℝ) • (Real.pi • (f z.2).1)) at he
    simpa only [one_smul, complexStructure_endpoint a b hanti] using he
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 1) × B) < n := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  obtain ⟨J, ⟨G⟩⟩ := exists_homotopy_to_minimum_path_family (I := (𝓡 1).prod I)
    a b hanti hdim P hPa hPb
  have hfixed (z : Circle × M) (K : ComplexStructures.Space n)
      (hK : ∀ u : unitInterval, P (u, z) = a * exp ((u : ℝ) • (Real.pi • K.1))) :
      J z = K := by
    apply complexStructure_eq_of_paths a
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

theorem complexStructureHomotopicRel_iff_paths
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hd : finrank ℝ B + 1 < n)
    (f g : C(M, ComplexStructures.Space n)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty ((complexStructurePathFamily a f).HomotopyRel (complexStructurePathFamily a g)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨complexStructurePathHomotopy a b hanti f g S F⟩
  · rintro ⟨F⟩
    exact nonempty_complexStructureHomotopyRel_of_paths (I := I) a b hanti hd f g S F

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
