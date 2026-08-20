/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.ClaimOne
import ErdosProblems.Erdos518.LowMu
import ErdosProblems.Erdos518.SmallCases
import ErdosProblems.Erdos518.TripleCover
import ErdosProblems.Erdos518.TripleFreeConcrete
import ErdosProblems.Erdos518.NoEdgeAllHigh
import ErdosProblems.Erdos518.HighFinal

/-!
# Excluding normalized counterexamples to Erdős Problem 518

This file joins the small-parameter, low-maximum-degree, and high-maximum-degree
branches of the Chen--Chen argument.  Its conclusion is the exact structural input
needed by the outer strong induction in `MainInduction`.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

namespace Configuration

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance noConfigurationDecidableEq : DecidableEq V := Classical.decEq V

/-- Every normalized minimal-counterexample configuration is impossible. -/
theorem impossible (C : Configuration V) : False := by
  have hY1 : C.Y1.Nonempty := C.Y1_nonempty
  have hY0 : C.Y0.Nonempty := C.Y0_nonempty
  by_cases hcOne : C.c = 1
  · have hwlo : 1 ≤ C.w := by
      have := C.w_ge_c
      omega
    have hrhi : C.r ≤ 2 := by
      have := C.r_le_two_mul_c
      omega
    exact c_one_impossible hwlo C.w_le_r_sub_two hrhi
  have hcTwo : 2 ≤ C.c := by
    have := C.one_le_c
    omega
  have hwTwo : C.w + 2 ≤ C.r := by
    have := C.w_le_r_sub_two
    have := C.w_ge_c
    omega
  have hmu : C.mu ≤ C.r - 2 :=
    C.mu_le_r_sub_two_of_bounds hY1 hY0 hcTwo hwTwo
  by_cases hcSmall : C.c ≤ 3
  · exact C.small_c_impossible_of_mu_le hcSmall hmu
  have hc : 4 ≤ C.c := by omega
  have hkey : C.a0 + ceilHalf C.a1 = C.c := C.claim_one hc
  by_cases hlow : 2 * C.mu ≤ C.r
  · exact C.lowMu_impossible_of_key hc hkey.symm hlow
  have hhigh : C.r + 1 ≤ 2 * C.mu := by omega
  let H := C.blueTripleHypergraph
  have hUniform : IsThreeUniformOn H C.Y1 := by
    intro T hT
    exact C.blueTripleHypergraph_threeUniform hT
  have hred :
      HighMuReductionData H C.Y1 C.blueDegreeToX C.r C.a0 C.a1 C.c C.w := by
    apply highMu_structural_reduction
    · exact C.a1_eq_card_Y1.symm
    · exact hUniform
    · exact C.exists_mem_Y1_blueDegreeToX_eq_mu hY1
    · exact C.r_le_two_mul_c
    · exact hhigh
    · exact hkey.symm
    · exact C.w_eq_a0_add_a1
    · intro hodd
      exact C.blueTripleHypergraph_eq_empty_of_odd hkey hodd
    · intro heven
      exact C.blueTripleHypergraph_matching_of_even hkey heven
    · intro S hSY1 hfree s hs hshigh
      have htripleFree : C.TripleFreeOn S :=
        (C.tripleFreeOn_iff_no_blueTriple_edge hSY1).2 hfree
      exact C.tripleFree_estimate_concrete hSY1 hs htripleFree hshigh
    · exact C.no_blueTripleHyperedge_contains_all_high hc hkey hhigh
  exact C.highMu_final_contradiction hc hUniform hred

end Configuration

/-- There is no normalized counterexample on any finite vertex type. -/
theorem configuration_impossible {V : Type u} [Fintype V]
    (C : Configuration V) : False :=
  C.impossible

end Erdos518
