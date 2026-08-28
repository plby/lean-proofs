import Wikipedia.HopfProblem.DegreeCollapseSevenShrunkEvenTwists
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryConnectivity
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryFourthHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenAmbientFiniteHomology

/-!
# Connectivity and fourth homology of each actual shrunk even twist

The original old half is unchanged by the positive radial scaling and
orthogonal twist. Hence every constructed member preserves its simple
connectivity and zero H2. When the actual new H3 is finite, zero original
H4 is preserved too. No reflected presentation of the new space is used.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.ShrunkEvenTwist

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris FramedAttachingProduct UnitSurgery ExteriorTwist

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f} {v : Sphere 3} {j : ℤ}
  (Q : ShrunkEvenTwist A v j) (hA : A.radius = 2) (T : TimeData A)

theorem low_connectivity [SimplyConnectedSpace (OldPositiveHalf A T)]
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 2)] :
    SimplyConnectedSpace
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) ∧
    Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 2) := by
  let : SimplyConnectedSpace (OldPositiveHalf Q.twisted (Q.twistedTimeData hA T)) :=
    inferInstanceAs (SimplyConnectedSpace (OldPositiveHalf A T))
  let : Subsingleton (SingularHomology (OldPositiveHalf Q.twisted (Q.twistedTimeData hA T)) 2) :=
    inferInstanceAs (Subsingleton (SingularHomology (OldPositiveHalf A T) 2))
  exact ⟨positiveHalf_simplyConnected Q.twisted Q.twisted_radius (Q.twistedTimeData hA T),
    positiveHalf_second_homology Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)⟩

theorem fourth_homology_of_finite
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    [Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3)] :
    Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 4) := by
  let : Subsingleton (SingularHomology (OldPositiveHalf Q.twisted (Q.twistedTimeData hA T)) 4) :=
    inferInstanceAs (Subsingleton (SingularHomology (OldPositiveHalf A T) 4))
  exact positiveHalf_fourth_homology_of_finite
    Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)

theorem target_third_finite_of_half [Finite (SingularHomology M 3)]
    [Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3)] :
    Finite (SingularHomology (Target Q.twisted Q.twisted_radius) 3) :=
  FramedAttachingProduct.UnitSurgery.target_third_finite_of_half
    Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.ShrunkEvenTwist
