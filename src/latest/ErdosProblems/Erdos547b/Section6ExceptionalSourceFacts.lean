/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Section6PrunedPreExceptional
import ErdosProblems.Erdos547b.Claim615RichExceptionalFullFiberForcing

/-!
# Source-only facts for the two Section 6 exceptional branches

The roots selected by the degree-form package provide nonnegative density
rows and reduced-graph adjacency for every positive entry.  This file turns
those facts into the two source records consumed by the complete-fiber
Claim-6.15 constructors.  Host cleaning is deliberately left to the later
online package: source roots and embedding roots are independent.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoSection6ExceptionalSourceFacts

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication

universe u v w

variable {TreeVertex : Type u} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
variable {globalRoot : TreeVertex} {small : ℕ}
variable {V : Type v} {I : Type w}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment V I)
variable (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable {beta : ℚ} {reducedK : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota)
    (claim61Miss beta reducedK))
variable (density : EvenPadding I → EvenPadding I → ℝ)
variable {N nTree targetB error : ℝ}
variable {lowerV1 upperV1 upperV2 : ℕ}
variable
  (F : PreExceptionalFacts Pcluster Gdegree threshold quota R Q density N
    nTree targetB error lowerV1 upperV1 upperV2)
variable {L : Finset (EvenPadding I)} {eta0 cap : ℝ}
variable {count cardBound : ℕ}
variable
  (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)

/-- The fixed Section 6 hierarchy absorbs the two embedding reserves and
three regularity losses inside one exceptional-density gap. -/
theorem exceptional_charge_le_eta
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4) :
    2 * (embeddingGamma beta : ℝ) +
        3 * (regularityEpsilon beta : ℝ) ≤ (eta beta : ℝ) := by
  have hs0 : (0 : ℝ) ≤ (sigma beta : ℝ) := by
    exact_mod_cast (sigma_pos hbeta).le
  have hs1 : (sigma beta : ℝ) ≤ 1 / 1000 :=
    sigma_le_one_div hbeta hbetaOne
  have hsEta : (sigma beta : ℝ) ≤ (eta beta : ℝ) :=
    (sigma_le_fourthRootD hbeta hbetaOne).trans <| by
      have h := fourthRootD_le_eta_div_1000 hbeta hbetaOne
      have heta0 : (0 : ℝ) ≤ (eta beta : ℝ) := by
        exact_mod_cast (eta_pos hbeta).le
      linarith
  have hgamma0 : (0 : ℝ) ≤ (embeddingGamma beta : ℝ) := by
    exact_mod_cast (embeddingGamma_pos hbeta).le
  have hgamma : (embeddingGamma beta : ℝ) ≤ (eta beta : ℝ) / 1000 := by
    rw [embeddingGamma]
    push_cast
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hepsilon : (regularityEpsilon beta : ℝ) ≤
      (embeddingGamma beta : ℝ) / 1000 := by
    rw [regularityEpsilon_cast_eq]
    simp only [reducedDensity]
    push_cast
    nlinarith [mul_nonneg hgamma0 (sub_nonneg.mpr hs1)]
  have heta0 : (0 : ℝ) < (eta beta : ℝ) := by
    exact_mod_cast eta_pos hbeta
  nlinarith

include F

/-- The larger endpoint of an unbalanced exceptional edge has source density
at least the exceptional cutoff. -/
theorem exceptionalHighDensity_ge
    (E0 : SelectedExceptionalEdges Q density L eta0 .unbalanced count)
    (e : K0 Q density E0) :
    eta0 ≤ exceptionalHighDensity Q density E0 e := by
  have hlow : 0 ≤ exceptionalLowDensity Q density E0 e := by
    exact PreExceptionalFacts.A_density_nonneg F _
  have hgap := exceptionalGap Q density E0 e
  linarith

/-- The degree-form source rows supply the complete source-only threshold
record for every selected unbalanced exceptional family. -/
theorem physicalThresholdSourceFacts
    (E0 : SelectedExceptionalEdges Q density L eta0 .unbalanced count)
    {ratio gamma epsilon : ℝ}
    (hratio0 : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hgamma0 : 0 ≤ gamma) (hepsilon0 : 0 ≤ epsilon)
    (heta0 : 0 < eta0) (hgamma : gamma ≤ eta0)
    (hcharge : 2 * gamma + 3 * epsilon ≤ eta0)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)) :
    PhysicalThresholdSourceFacts (small := small) (ratio := ratio)
      Q density E0 Mb gamma epsilon := by
  have hratioOne : ratio < 1 := hratioHalf.trans_lt (by norm_num)
  have hfactor : 0 ≤ ratio / (1 - ratio) :=
    div_nonneg hratio0 (sub_nonneg.mpr hratioOne.le)
  refine {
    ratio_nonneg := hratio0
    ratio_le_half := hratioHalf
    N_pos := PreExceptionalFacts.N_pos F
    gamma_nonneg := hgamma0
    epsilon_nonneg := hepsilon0
    rounding := hround
    eta_pos := heta0
    row_A_nonneg := PreExceptionalFacts.A_density_nonneg F
    adj_A := PreExceptionalFacts.density_adj_A F
    adj_B := PreExceptionalFacts.density_adj_B F
    exceptional_target_nonneg := ?_
    exceptional_high_nonneg := ?_
  }
  · intro e
    have hlow : 0 ≤ exceptionalLowDensity Q density E0 e :=
      PreExceptionalFacts.A_density_nonneg F _
    have hhigh : eta0 ≤ exceptionalHighDensity Q density E0 e :=
      exceptionalHighDensity_ge Pcluster Gdegree threshold quota R Q density F E0 e
    have hgap : 0 ≤ exceptionalHighDensity Q density E0 e -
        exceptionalLowDensity Q density E0 e :=
      sub_nonneg.mpr (exceptionalLowDensity_le_highDensity Q density E0 e)
    have hbonus : 0 ≤ ratio / (1 - ratio) *
        (exceptionalHighDensity Q density E0 e -
          exceptionalLowDensity Q density E0 e) :=
      mul_nonneg hfactor hgap
    have hbase : 0 ≤ exceptionalLowDensity Q density E0 e +
        exceptionalHighDensity Q density E0 e - 2 * gamma - 3 * epsilon := by
      linarith
    unfold exceptionalPartTwoTarget
    exact add_nonneg (mul_nonneg hbase (PreExceptionalFacts.N_pos F).le)
      (mul_nonneg hbonus (PreExceptionalFacts.N_pos F).le)
  · intro e
    have hhigh : eta0 ≤ exceptionalHighDensity Q density E0 e :=
      exceptionalHighDensity_ge Pcluster Gdegree threshold quota R Q density F E0 e
    exact mul_nonneg (by linarith) (PreExceptionalFacts.N_pos F).le

/-- The same source rows give the simpler nonextreme/Appendix source record.
No exceptional capacity inequality is needed in this branch. -/
theorem physicalPartThreeRootSourceFacts
    (E0 : SelectedExceptionalEdges Q density L eta0 .nonextreme count)
    {gamma epsilon : ℝ}
    (hgamma0 : 0 ≤ gamma) (hepsilon0 : 0 ≤ epsilon)
    (heta0 : 0 < eta0)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)) :
    PhysicalPartThreeRootSourceFacts (small := small)
      Q density E0 Mb gamma epsilon where
  N_pos := PreExceptionalFacts.N_pos F
  gamma_nonneg := hgamma0
  epsilon_nonneg := hepsilon0
  rounding := hround
  eta_pos := heta0
  adj_A := PreExceptionalFacts.density_adj_A F
  adj_B := PreExceptionalFacts.density_adj_B F

end Erdos547b.ZhaoSection6ExceptionalSourceFacts

#print axioms Erdos547b.ZhaoSection6ExceptionalSourceFacts.exceptionalHighDensity_ge
#print axioms Erdos547b.ZhaoSection6ExceptionalSourceFacts.physicalThresholdSourceFacts
#print axioms Erdos547b.ZhaoSection6ExceptionalSourceFacts.physicalPartThreeRootSourceFacts
