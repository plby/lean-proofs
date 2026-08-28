import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionTwo
import Wikipedia.HopfProblem.ThirdHurewiczIso
import Wikipedia.HopfProblem.ThirdHurewiczNaturality

/-!
# Actual fiber projection in higher homotopy and third homology

The native fiber sequence gives projection bijectivity in every positive
degree when the two adjacent target groups vanish. In degree three, the
actual third Hurewicz isomorphism transfers this to third homology after
the required second-homotopy vanishing is proved for the source and fiber.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair.HomotopyFiber

namespace NoExoticSixSphere.HomotopyFiberConnectivity

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem projection_pi_bijective (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ d Y (f x))] [Subsingleton (π_ (d + 1) Y (f x))] :
    Function.Bijective (HigherHomotopy.map (N := Fin d)
      (projection f (f x)) (y := basepoint f x) rfl) := by
  constructor
  · change Function.Injective (HigherHomotopy.mapMonoidHom (N := Fin d)
      (projection f (f x)) (y := basepoint f x) rfl)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← boundary_range_eq_projection_ker d f x]
    apply MonoidHom.range_eq_bot_iff.mpr
    ext c
    exact (congrArg (boundaryHom d f x) (Subsingleton.elim c 1)).trans (map_one _)
  · intro c
    exact (map_eq_const_iff_exists_fiber_class f x c).mp (Subsingleton.elim _ _)

theorem map_injective_of_fiber_subsingleton (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ d (Space f (f x)) (basepoint f x))] :
    Function.Injective (HigherHomotopy.map (N := Fin d) f (y := x) rfl) := by
  change Function.Injective (HigherHomotopy.mapMonoidHom (N := Fin d) f (y := x) rfl)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← projection_range_eq_ker]
  apply MonoidHom.range_eq_bot_iff.mpr
  ext c
  exact (congrArg (HigherHomotopy.mapMonoidHom (N := Fin d)
    (projection f (f x)) (projection_basepoint f x)) (Subsingleton.elim c 1)).trans (map_one _)

variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
  (f : C(X, Y)) (x : X) [Subsingleton (π_ 2 X x)]
  [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
  [Subsingleton (π_ 4 Y (f x))]

theorem projection_homologyThree_bijective :
    Function.Bijective (singularHomologyMap (projection f (f x)) 3) := by
  have hs : Function.Surjective (HigherHomotopy.map (N := Fin 2) f (y := x) rfl) :=
    fun c ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩
  let := simplyConnectedSpace f x hs
  let : Subsingleton (π_ 2 X ((projection f (f x)) (basepoint f x))) :=
    inferInstanceAs (Subsingleton (π_ 2 X x))
  let : Subsingleton (π_ 2 (Space f (f x)) (basepoint f x)) :=
    (projection_pi_bijective 2 f x).injective.subsingleton
  let p := projection f (f x)
  let z := basepoint f x
  let : Subsingleton (π_ 2 X (p z)) := inferInstanceAs (Subsingleton (π_ 2 X x))
  have he : HigherHomotopy.map (N := Fin 3) p (y := z) rfl =
      ThirdHurewicz.homotopyMap p z := by
    funext c
    refine Quotient.inductionOn c fun q ↦ ?_
    rfl
  have hP : Function.Bijective (ThirdHurewicz.homotopyMap p z) := by
    rw [← he]
    exact projection_pi_bijective 3 f x
  have hx : Function.Bijective (ThirdHurewicz.hurewiczFunction z) :=
    (ThirdHurewicz.hurewiczPi3Equiv z).bijective
  have hy : Function.Bijective (ThirdHurewicz.hurewiczFunction (p z)) :=
    (ThirdHurewicz.hurewiczPi3Equiv (p z)).bijective
  have hn : ThirdHurewicz.hurewiczFunction (p z) ∘ ThirdHurewicz.homotopyMap p z =
      singularHomologyMap p 3 ∘ ThirdHurewicz.hurewiczFunction z :=
    funext (fun c ↦ (ThirdHurewicz.hurewiczFunction_natural p z c).symm)
  have hb := hy.comp hP
  rw [hn] at hb
  exact (Function.Bijective.of_comp_iff (singularHomologyMap p 3) hx).mp hb

end NoExoticSixSphere.HomotopyFiberConnectivity
