import Wikipedia.HopfProblem.SecondHurewiczSimplyConnected
import Wikipedia.HopfProblem.SecondHurewiczNaturality

/-!
# Homology isomorphisms induce second homotopy isomorphisms

For simply connected spaces, the naturality square of the proved second
Hurewicz isomorphisms conjugates the actual homology map to the actual
native second-homotopy map. No higher Whitehead theorem is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.HomologyEquivalence

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]

theorem piTwo_bijective (f : C(X, Y))
    (h : Function.Bijective (singularHomologyMap f 2)) (x : X) :
    Function.Bijective (SecondHurewicz.homotopyMap f x) := by
  have hx : Function.Bijective (SecondHurewicz.hurewiczFunction x) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).bijective
  have hy : Function.Bijective (SecondHurewicz.hurewiczFunction (f x)) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv (f x)).bijective
  have hn : SecondHurewicz.hurewiczFunction (f x) ∘ SecondHurewicz.homotopyMap f x =
      singularHomologyMap f 2 ∘ SecondHurewicz.hurewiczFunction x :=
    funext (fun a ↦ (SecondHurewicz.hurewiczFunction_natural f x a).symm)
  have hb := h.comp hx
  rw [← hn] at hb
  exact (Function.Bijective.of_comp_iff' hy (SecondHurewicz.homotopyMap f x)).mp hb

end NoExoticSixSphere.HomologyEquivalence
