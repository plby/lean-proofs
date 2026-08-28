import Wikipedia.HopfProblem.OrbitPairSphereContinuousPathDeformation
import Wikipedia.NoExoticSixSphere.CircleHomotopyParameter
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Relative homotopy comparison for semicircle path families

Extend an interval homotopy over a circle parameter, then apply the proved
continuous path deformation. Endpoint fibers and protected parameters are
already semicircles and remain fixed. Evaluation at half time recovers their
unit tangent directions, giving a relative homotopy in the direction sphere.
No polygon, mesh, energy, or smoothness hypothesis on the path homotopy remains.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereSemicircle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

theorem direction_eq_of_paths (a : Sphere n) (y z : Direction a)
    (h : ∀ u : unitInterval, SphereGreatCircle.curve a.val y.val Real.pi u =
      SphereGreatCircle.curve a.val z.val Real.pi u) : y = z := by
  apply Subtype.ext
  have he := h ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
  simpa only [SphereGreatCircle.curve, mul_one_div, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_smul, one_smul, zero_add] using he

def directionPathHomotopy (a : Sphere n) (f g : C(M, Direction a))
    (S : Set M) (F : f.HomotopyRel g S) :
    (semicirclePathFamily a f).HomotopyRel (semicirclePathFamily a g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} where
  toContinuousMap := (semicirclePathFamily a F.toContinuousMap).comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  map_zero_left z := by
    apply Subtype.ext
    change SphereGreatCircle.curve a.val (F (0, z.2)).val Real.pi z.1 =
      SphereGreatCircle.curve a.val (f z.2).val Real.pi z.1
    rw [F.apply_zero]
  map_one_left z := by
    apply Subtype.ext
    change SphereGreatCircle.curve a.val (F (1, z.2)).val Real.pi z.1 =
      SphereGreatCircle.curve a.val (g z.2).val Real.pi z.1
    rw [F.apply_one]
  prop' r z hz := by
    rcases z with ⟨t, x⟩
    apply Subtype.ext
    change SphereGreatCircle.curve a.val (F (r, x)).val Real.pi t =
      SphereGreatCircle.curve a.val (f x).val Real.pi t
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      change SphereGreatCircle.curve a.val (F (r, x)).val Real.pi 0 =
        SphereGreatCircle.curve a.val (f x).val Real.pi 0
      rw [SphereGreatCircle.curve_zero, SphereGreatCircle.curve_zero]
    · change t = 1 at ht
      subst t
      change SphereGreatCircle.curve a.val (F (r, x)).val Real.pi 1 =
        SphereGreatCircle.curve a.val (f x).val Real.pi 1
      rw [SphereGreatCircle.curve_pi_one, SphereGreatCircle.curve_pi_one]
    · have he : F (r, x) = f x := F.eq_fst r hx
      rw [he]

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem nonempty_directionHomotopyRel_of_paths (a b : Sphere n) (hanti : b.val = -a.val)
    (hd : finrank ℝ B + 3 < 2 * n) (f g : C(M, Direction a)) (S : Set M)
    (F : (semicirclePathFamily a f).HomotopyRel (semicirclePathFamily a g)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) : Nonempty (f.HomotopyRel g S) := by
  let P : C(unitInterval × (Circle × M), Sphere n) := F.toContinuousMap.comp {
    toFun z := (CircleHomotopyParameter.height z.2.1, (z.1, z.2.2))
    continuous_toFun :=
      (CircleHomotopyParameter.height.continuous.comp
        (continuous_fst.comp continuous_snd)).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  have hPa (z : Circle × M) : P (0, z) = a := by
    have he : P (0, z) = semicirclePathFamily a f (0, z.2) :=
      F.eq_fst (CircleHomotopyParameter.height z.1)
        (show ((0 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from Or.inl rfl)
    exact he.trans (semicirclePathFamily_zero a f z.2)
  have hPb (z : Circle × M) : P (1, z) = b := by
    have he : P (1, z) = semicirclePathFamily a f (1, z.2) :=
      F.eq_fst (CircleHomotopyParameter.height z.1)
        (show ((1 : unitInterval), z.2) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S} from
          Or.inr (Or.inl rfl))
    exact he.trans (semicirclePathFamily_one a b hanti f z.2)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 1) × B) + 2 < 2 * n := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  obtain ⟨J, ⟨G⟩⟩ := exists_continuous_path_deformation (I := (𝓡 1).prod I)
    a b hanti P hPa hPb hdim
  have hfixed (z : Circle × M) (y : Direction a)
      (hy : ∀ u : unitInterval, (P (u, z)).val = SphereGreatCircle.curve a.val y.val Real.pi u) :
      J z = y := by
    apply direction_eq_of_paths a
    intro u
    have he := G.fst_eq_snd
      (show (u, z) ∈ {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ minimumPathParameters a P} from
        Or.inr (Or.inr ⟨y, hy⟩))
    exact (congrArg Subtype.val he).symm.trans (hy u)
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
    change (F (CircleHomotopyParameter.height 1, (u, x))).val = _
    rw [CircleHomotopyParameter.height_one, F.apply_zero]
    rfl
  · intro x
    change J (CircleHomotopyParameter.semicircle 1, x) = g x
    rw [CircleHomotopyParameter.semicircle_one]
    apply hfixed (-1, x) (g x)
    intro u
    change (F (CircleHomotopyParameter.height (-1), (u, x))).val = _
    rw [CircleHomotopyParameter.height_neg_one, F.apply_one]
    rfl
  · intro t x hx
    change J (CircleHomotopyParameter.semicircle t, x) = f x
    apply hfixed (CircleHomotopyParameter.semicircle t, x) (f x)
    intro u
    exact congrArg Subtype.val (F.eq_fst _ (Or.inr (Or.inr hx)))

theorem directionHomotopicRel_iff_paths (a b : Sphere n) (hanti : b.val = -a.val)
    (hd : finrank ℝ B + 3 < 2 * n) (f g : C(M, Direction a)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty ((semicirclePathFamily a f).HomotopyRel (semicirclePathFamily a g)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨directionPathHomotopy a f g S F⟩
  · rintro ⟨F⟩
    exact nonempty_directionHomotopyRel_of_paths (I := I) a b hanti hd f g S F

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
