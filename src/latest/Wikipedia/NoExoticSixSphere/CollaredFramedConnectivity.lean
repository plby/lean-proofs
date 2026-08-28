import Wikipedia.NoExoticSixSphere.CollaredZeroFramedPath
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneBothHalves
import Wikipedia.HopfProblem.FirstHurewiczEquivalence

/-!
# Two-connected native fillings with a full induced boundary-frame comparison

The actual component selection, both fundamental-group surgery paths, and
both second-homology surgery paths now retain a single endpoint stabilized
framed diffeomorphism of the native zero boundaries. No initial half
connectivity, middle-homology vanishing, or prescribed frame comparison is
assumed. The original induced zero frame is compared with the final induced
zero frame by constructed constant ambient and normal isometries.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredFramedConnectivity

open GLOrthonormalization Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 2)]

omit [Subsingleton (SingularHomology B 2)] in
theorem firstHomology_subsingleton (b : B) : Subsingleton (SingularHomology B 1) := by
  let : Subsingleton (FundamentalGroup B b) := inferInstance
  let : Subsingleton (Abelianization (FundamentalGroup B b)) := by
    change Subsingleton ((FundamentalGroup B b) ⧸ commutator (FundamentalGroup B b))
    exact (QuotientGroup.mk_surjective).subsingleton
  let : Subsingleton (FirstHurewicz.AbelianPi1 B b) := by
    change Subsingleton (Additive (Abelianization (FundamentalGroup B b)))
    infer_instance
  exact (FirstHurewicz.firstHurewiczEquiv b).symm.injective.subsingleton

theorem exists_twoConnected_state (S : LowCollaredSevenState B) (b : B) :
    ∃ V : LowCollaredSevenState B,
      SimplyConnectedSpace V.PositiveHalf ∧ SimplyConnectedSpace V.NegativeHalf ∧
      Subsingleton (SingularHomology V.PositiveHalf 2) ∧
      Subsingleton (SingularHomology V.NegativeHalf 2) ∧
      (∀ w : V.PositiveHalf, Subsingleton (π_ 2 V.PositiveHalf w)) ∧
      Nonempty (CollaredZero.Comparison S V b) := by
  let : Subsingleton (SingularHomology B 1) := firstHomology_subsingleton b
  let C := S.component b
  let : PathConnectedSpace C.Space := S.component_pathConnected b
  obtain ⟨P, Q, hCP, hPQ, hQP, hQN⟩ := C.exists_simplyConnected_both_halves_of_connected
  let := hQP
  let := hQN
  obtain ⟨R, V, hQR, hRV, hVP, hVN, hVP2, hVN2⟩ := Q.exists_h2_zero_both_halves
  let := hVP
  let := hVN
  let := hVP2
  let := hVN2
  refine ⟨V, hVP, hVN, hVP2, hVN2, ?_, ?_⟩
  · intro w
    exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv w).injective.subsingleton
  · obtain ⟨F⟩ := CollaredZero.comparison_after_reversed_path hCP hPQ b
    obtain ⟨G⟩ := CollaredZero.comparison_after_reversed_path hQR hRV b
    exact ⟨CollaredZero.comparisonTrans (CollaredZero.componentComparisonSymm S b)
      (CollaredZero.comparisonTrans F G)⟩

end NoExoticSixSphere.CollaredFramedConnectivity
