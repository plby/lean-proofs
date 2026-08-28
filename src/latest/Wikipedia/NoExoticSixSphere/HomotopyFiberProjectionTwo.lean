import Wikipedia.NoExoticSixSphere.HomotopyFiberConnectivity
import Wikipedia.NoExoticSixSphere.HomologyEquivalencePiTwo

/-!
# Projection is an isomorphism when the target has no second or third homotopy

The original fiber exact sequence proves bijectivity on native second
homotopy. For simply connected source and target, the checked natural
second Hurewicz isomorphisms transfer it to the actual second homology map.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair.HomotopyFiber

namespace NoExoticSixSphere.HomotopyFiberConnectivity

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (x : X)
  [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]

theorem projection_piTwo_bijective :
    Function.Bijective (HigherHomotopy.map (N := Fin 2)
      (projection f (f x)) (y := basepoint f x) rfl) := by
  constructor
  · change Function.Injective (HigherHomotopy.mapMonoidHom (N := Fin 2)
      (projection f (f x)) (y := basepoint f x) rfl)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← boundary_range_eq_projection_ker 2 f x]
    apply MonoidHom.range_eq_bot_iff.mpr
    ext c
    exact (congrArg (boundaryHom 2 f x) (Subsingleton.elim c 1)).trans (map_one _)
  · intro c
    exact (map_eq_const_iff_exists_fiber_class f x c).mp (Subsingleton.elim _ _)

theorem projection_homologyTwo_bijective [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    Function.Bijective (singularHomologyMap (projection f (f x)) 2) := by
  have hs : Function.Surjective (HigherHomotopy.map (N := Fin 2) f (y := x) rfl) :=
    fun c ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩
  let := simplyConnectedSpace f x hs
  let p := projection f (f x)
  let z := basepoint f x
  have he : HigherHomotopy.map (N := Fin 2) p (y := z) rfl =
      SecondHurewicz.homotopyMap p z := by
    funext c
    refine Quotient.inductionOn c fun q ↦ ?_
    rfl
  have hP : Function.Bijective (SecondHurewicz.homotopyMap p z) := by
    rw [← he]
    exact projection_piTwo_bijective f x
  have hx : Function.Bijective (SecondHurewicz.hurewiczFunction z) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv z).bijective
  have hy : Function.Bijective (SecondHurewicz.hurewiczFunction (p z)) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv (p z)).bijective
  have hn : SecondHurewicz.hurewiczFunction (p z) ∘ SecondHurewicz.homotopyMap p z =
      singularHomologyMap p 2 ∘ SecondHurewicz.hurewiczFunction z :=
    funext (fun c ↦ (SecondHurewicz.hurewiczFunction_natural p z c).symm)
  have hb := hy.comp hP
  rw [hn] at hb
  exact (Function.Bijective.of_comp_iff (singularHomologyMap p 2) hx).mp hb

end NoExoticSixSphere.HomotopyFiberConnectivity
