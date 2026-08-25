import ErdosProblems.Erdos237
import ErdosProblems.Erdos237b
import ErdosProblems.Erdos237b.MaynardBridge
import ErdosProblems.Erdos237b.DyadicLattice
import ErdosProblems.Erdos237b.SieveDecomposition
import ErdosProblems.Erdos237b.SieveS1Limit
import ErdosProblems.Erdos237b.YSharpBounds
import BoundedGaps.Proof.MainTheorem

#print axioms maynard_tao
#print axioms MaynardTao.natural_maynard_tao
#print axioms MaynardTao.maynard_tao
#print axioms Erdos237.chen_ding_theorem
#print axioms Erdos237.erdos_237

#print axioms Erdos237b.exists_card_eq_same_residue
#print axioms Erdos237b.reflected_isAdmissible
#print axioms Erdos237b.chen_ding_of_qualitative
#print axioms Erdos237b.erdos_237_of_qualitative
#print axioms Erdos237b.prime_shifts_of_normalized_asymptotics
#print axioms Erdos237b.qualitativePrimeTuples_of_positiveSieveExcess
#print axioms Erdos237b.half_le_product_mass_below_cutoff
#print axioms Erdos237b.dyadic_box_ratio_gt
#print axioms Erdos237b.exists_dyadic_box_ratio_gt
#print axioms Erdos237b.tendsto_dyadic_independent_box_mass
#print axioms Erdos237b.abs_sieveWeightSum_sub_yDiagonal_le
#print axioms Erdos237b.tendsto_normalized_collision_mass
#print axioms Erdos237b.tendsto_normalized_s1_cross
#print axioms Erdos237b.tendsto_dyadicY_diagonal
#print axioms Erdos237b.tendsto_normalized_coefficient_mass
#print axioms Erdos237b.tendsto_sieveWeightSum_of_yDiagonal
#print axioms Erdos237b.tendsto_dyadic_sieveWeightSum
#print axioms Erdos237b.abs_coefficientFromY_le_sharp_log
#print axioms Erdos237b.tendsto_normalized_s2_cross
#print axioms Erdos237b.tendsto_normalized_s2Diagonal_sub_fiberDiagonal
#print axioms Erdos237b.extraCoordinate_sum_le_fiberDiagonal
#print axioms Erdos237b.exists_dyadic_s2Fiber_lower_sequence
#print axioms Erdos237b.exists_dyadic_s2Arithmetic_lower_sequence
#print axioms Erdos237b.tendsto_normalized_s2YError
#print axioms Erdos237b.tendsto_shiftedPrimeFactor
#print axioms Erdos237b.qualitativePrimeTuples_unconditional
#print axioms Erdos237b.chen_ding_theorem
#print axioms BoundedGaps.unconditional_boundedGapsStatement
#print axioms Erdos237b.erdos_237

-- Confirm the extracted definition still has exactly the challenge's body.
example (A : Set ℕ) (n : ℕ) : Erdos237b.repCount A n =
    Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime} := rfl

-- An explicit hypothesis is not a proof of QualitativePrimeTuples.
#check Erdos237b.erdos_237_of_qualitative
#check BoundedGaps.Maynard.engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt

-- Both routes count exactly the same representations.
example (A : Set ℕ) (n : ℕ) : Erdos237.repCount A n = Erdos237b.repCount A n := rfl

-- The public Maynard–Tao statement retains all original hypotheses and quantifiers.
example (m : ℕ) (hm : 2 ≤ m) (B : Finset ℤ)
    (hB : Admissible B)
    (hk : Real.exp (8 * m + 4) < B.card * Real.log B.card) :
    ∀ N : ℕ, ∃ n : ℤ, N < n ∧
      m ≤ (B.filter (fun b ↦ (n + b).natAbs.Prime)).card :=
  maynard_tao m hm B hB hk
