import ErdosProblems.Erdos237
import ErdosProblems.Erdos237.MaynardBridge
import ErdosProblems.Erdos237.DyadicLattice
import ErdosProblems.Erdos237.SieveDecomposition
import ErdosProblems.Erdos237.SieveS1Limit
import ErdosProblems.Erdos237.YSharpBounds
import BoundedGaps.Proof.MainTheorem

#print axioms Erdos237.exists_card_eq_same_residue
#print axioms Erdos237.reflected_isAdmissible
#print axioms Erdos237.chen_ding_of_qualitative
#print axioms Erdos237.erdos_237_of_qualitative
#print axioms Erdos237.prime_shifts_of_normalized_asymptotics
#print axioms Erdos237.qualitativePrimeTuples_of_positiveSieveExcess
#print axioms Erdos237.half_le_product_mass_below_cutoff
#print axioms Erdos237.dyadic_box_ratio_gt
#print axioms Erdos237.exists_dyadic_box_ratio_gt
#print axioms Erdos237.tendsto_dyadic_independent_box_mass
#print axioms Erdos237.abs_sieveWeightSum_sub_yDiagonal_le
#print axioms Erdos237.tendsto_normalized_collision_mass
#print axioms Erdos237.tendsto_normalized_s1_cross
#print axioms Erdos237.tendsto_dyadicY_diagonal
#print axioms Erdos237.tendsto_normalized_coefficient_mass
#print axioms Erdos237.tendsto_sieveWeightSum_of_yDiagonal
#print axioms Erdos237.tendsto_dyadic_sieveWeightSum
#print axioms Erdos237.abs_coefficientFromY_le_sharp_log
#print axioms Erdos237.tendsto_normalized_s2_cross
#print axioms Erdos237.tendsto_normalized_s2Diagonal_sub_fiberDiagonal
#print axioms Erdos237.extraCoordinate_sum_le_fiberDiagonal
#print axioms Erdos237.exists_dyadic_s2Fiber_lower_sequence
#print axioms Erdos237.exists_dyadic_s2Arithmetic_lower_sequence
#print axioms Erdos237.tendsto_normalized_s2YError
#print axioms Erdos237.tendsto_shiftedPrimeFactor
#print axioms Erdos237.qualitativePrimeTuples_unconditional
#print axioms Erdos237.chen_ding_theorem
#print axioms BoundedGaps.unconditional_boundedGapsStatement
#print axioms Erdos237.erdos_237

-- Confirm the extracted definition still has exactly the challenge's body.
example (A : Set ℕ) (n : ℕ) : Erdos237.repCount A n =
    Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime} := rfl

-- An explicit hypothesis is not a proof of QualitativePrimeTuples.
#check Erdos237.erdos_237_of_qualitative
#check BoundedGaps.Maynard.engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt
