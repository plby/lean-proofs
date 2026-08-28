import Wikipedia.HopfProblem.DegreeCollapseMiddleIntersectionMatrix
import Wikipedia.HopfProblem.DegreeCollapseFiniteDualFamily

/-!
# Nondegeneracy of the actual middle pairing from native Morse geometry

The smooth descending and ascending sphere classes have identity pairing.
The same Morse system bounds the actual mod-two homology dimension by their
number. Thus they give bases of the original homology object and prove its
geometric pairing nondegenerate. No duality theorem is supplied as a premise.
-/

noncomputable section

open Set Function Classical
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare
open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

open SingularMayerVietoris SphereHomologyCoefficients
attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : e.TubularRetraction)
  (m : M) [hπ₂ : Subsingleton (π_ 2 M m)]

namespace SeparatedSystem.SmoothMiddleFamilies

variable [Nonempty M] {D : SeparatedSystem (Vector 6) M} (F : D.SmoothMiddleFamilies)

def descendingModTwoBasis : (D.MiddleLabel → ZMod 2) ≃ₗ[ZMod 2] ModHomology 2 M 3 := by
  let _ : Fintype D.MiddleLabel := Fintype.ofFinite _
  let _ : Module.Finite (ZMod 2) (ModHomology 2 M 3) := D.middle_modTwo_finite m
  exact FiniteDualFamily.familyEquiv (e.modTwoHomologyIntersection r m)
    (fun p => SixSphereMiddleParity.sphereClass (F.descending p))
    (fun p => SixSphereMiddleParity.sphereClass (F.ascending p))
    (fun p q => by
      by_cases h : p = q
      · simpa only [if_pos h] using F.homologyIntersectionMatrix e r m p q
      · simpa only [if_neg h] using F.homologyIntersectionMatrix e r m p q)
    (by simpa only [Nat.card_eq_fintype_card] using D.middle_modTwo_finrank_le m)

include F in
theorem modTwo_nondegenerate : (e.modTwoHomologyIntersection r m).Nondegenerate := by
  let _ : Fintype D.MiddleLabel := Fintype.ofFinite _
  let _ : Module.Finite (ZMod 2) (ModHomology 2 M 3) := D.middle_modTwo_finite m
  exact FiniteDualFamily.nondegenerate (e.modTwoHomologyIntersection r m)
    (fun p => SixSphereMiddleParity.sphereClass (F.descending p))
    (fun p => SixSphereMiddleParity.sphereClass (F.ascending p))
    (fun p q => by
      by_cases h : p = q
      · simpa only [if_pos h] using F.homologyIntersectionMatrix e r m p q
      · simpa only [if_neg h] using F.homologyIntersectionMatrix e r m p q)
    (by simpa only [Nat.card_eq_fintype_card] using D.middle_modTwo_finrank_le m)

include e r m hπ₂ F in
theorem middle_modTwo_finrank :
    Module.finrank (ZMod 2) (ModHomology 2 M 3) = Nat.card D.MiddleLabel := by
  let _ : Fintype D.MiddleLabel := Fintype.ofFinite _
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    (F.descendingModTwoBasis e r m).finrank_eq.symm

end SeparatedSystem.SmoothMiddleFamilies

theorem modTwoIntersection_nondegenerate :
    (e.modTwoHomologyIntersection r m).Nondegenerate := by
  let _ : Nonempty M := ⟨m⟩
  let _ : Subsingleton (SingularHomology M 2) := TwoConnectedCoefficients.secondHomology_subsingleton m
  obtain ⟨D⟩ := nonempty_separatedSystem (Vector 6) M (by simp [GLOrthonormalization.Vector])
  obtain ⟨F⟩ := D.nonempty_smoothMiddleFamilies
  exact F.modTwo_nondegenerate e r m

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
