import Wikipedia.NoExoticSixSphere.RoundDiskCubicalSuspension
import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange
import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality
import Wikipedia.HopfProblem.OrbitPairHigherHomotopyHomeomorph

/-!
# The original round-disk boundary homomorphism is cubical suspension

The explicit segment family is curried in the native path space and
then uncurried on native cubes. The constructed target homeomorphism
identifies this homomorphism with the original cubical suspension.
Its stable-range bijectivity therefore follows for the actual map.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.RoundDiskCubicalSuspension

open RoundDiskBoundarySegments

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y]
  (f : C(Disk (E := E), Y)) (z : Y)
  (hbase : ∀ x, f x = z ↔ x.val ∈ sphere (0 : E) 1)
  {n : ℕ} (e : Sphere n ≃ₜ Boundary (E := E))

include hbase in
theorem evaluation_zero (s : Sphere n) : evaluation f e (0, s) = z := by
  change f (point (e (spherePole n)) (0, e s)) = z
  rw [point_zero]
  exact (hbase _).mpr (e s).property

include hbase in
theorem evaluation_one (s : Sphere n) : evaluation f e (1, s) = z := by
  change f (point (e (spherePole n)) (1, e s)) = z
  rw [point_one]
  exact (hbase _).mpr (e (spherePole n)).property

def loops : C(Sphere n, Path z z) :=
  PathFamilies.curry (evaluation f e) (evaluation_zero f z hbase e) (evaluation_one f z hbase e)

theorem loops_pole : loops f z hbase e (spherePole n) = Path.refl z := by
  apply Path.ext
  funext t
  change f (point (e (spherePole n)) (t, e (spherePole n))) = z
  rw [point_base]
  exact (hbase _).mpr (e (spherePole n)).property

def hom (d : ℕ) [NeZero d] :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d z).toMonoidHom.comp
    (HigherHomotopy.mapMonoidHom (N := Fin d) (loops f z hbase e) (loops_pole f z hbase e))

def genLoop {d : ℕ} (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    GenLoop (Fin (d + 1)) Y z :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (loops f z hbase e) (loops_pole f z hbase e) p)

theorem hom_mk (d : ℕ) [NeZero d] (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    hom f z hbase e d (Quotient.mk _ p) = Quotient.mk _ (genLoop f z hbase e p) := rfl

variable [T2Space Y]
  (hfiber : ∀ x y, f x = f y → f x = z ∨ x = y)
  (hsurj : Function.Surjective f)

theorem hom_eq_postcompose (d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    hom f z hbase e d c =
      HigherHomotopy.map (N := Fin (d + 1))
        (homeomorph f z hbase hfiber hsurj e : C(Sphere (n + 1), Y))
        (homeomorph_pole f z hbase hfiber hsurj e) (CubicalSphereSuspension.hom d n c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun r : GenLoop (Fin (d + 1)) Y z ↦
    (Quotient.mk _ r : π_ (d + 1) Y z))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact (homeomorph_evaluation f z hbase hfiber hsurj e (u 0, p.val (Fin.tail u))).symm

include hfiber hsurj in
theorem hom_bijective (d : ℕ) [NeZero d] (hd : d + 3 < 2 * (n + 1)) :
    Function.Bijective (hom f z hbase e d) := by
  let H : C(Sphere (n + 1), Y) := homeomorph f z hbase hfiber hsurj e
  have he₀ : Function.Bijective
      (HigherHomotopy.map (N := Fin (d + 1)) H (y := spherePole (n + 1)) rfl) :=
    (HigherHomotopyCoordinates.homeomorphEquiv (Fin (d + 1))
      (homeomorph f z hbase hfiber hsurj e) (spherePole (n + 1))).bijective
  have he : Function.Bijective (HigherHomotopy.map (N := Fin (d + 1)) H
      (homeomorph_pole f z hbase hfiber hsurj e)) :=
    (NativeHomotopyTargetEquality.map_bijective_iff (d + 1) H
      (homeomorph_pole f z hbase hfiber hsurj e)).mpr he₀
  have hf : (hom f z hbase e d : _ → _) =
      HigherHomotopy.map (N := Fin (d + 1)) H (homeomorph_pole f z hbase hfiber hsurj e) ∘
        CubicalSphereSuspension.hom d n :=
    funext (hom_eq_postcompose f z hbase e hfiber hsurj d)
  rw [hf]
  exact he.comp (CubicalSphereSuspension.hom_bijective hd)

end NoExoticSixSphere.RoundDiskCubicalSuspension
