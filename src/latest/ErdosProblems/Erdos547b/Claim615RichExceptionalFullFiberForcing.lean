/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichThresholdOnlinePackage
import ErdosProblems.Erdos547b.Claim615RichPartThreeMixedOnlinePackage

/-!
# Exceptional-family forcing from state-independent full-fiber facts

This is the source-faithful Claim-6.15 boundary.  Both source selections,
both integral packings, and both synchronized online realizations are invoked
internally.  The public records contain only source, regular-pair, cleaning,
and complete-fiber inequalities; they contain no copy, embedding,
continuation, containment conclusion, or recursive online state.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoClaim615RichGlobalThresholdApplication
open Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts
open Erdos547b.ZhaoClaim615RichRootSideOnlineRealization
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichExceptionalForcing
open Erdos547b.ZhaoClaim615RichThresholdOnlinePackage
open Erdos547b.ZhaoClaim615RichPartThreeMixedOnlinePackage
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}
variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
variable {L : Finset (EvenPadding I)} {eta0 N targetB cap : ℝ}
variable {count cardBound : ℕ}
variable (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)
variable {targetU slackU targetP slackP ratio gammaU epsilonU : ℝ}

/-- The source/live-host facts for one selected unbalanced exceptional family.
All source-selection parameters are fixed outside this record. -/
structure UnbalancedFullFiberFacts
    (hT : T.IsTree)
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (target slack : ℕ) (ratio gamma epsilon : ℝ)
    (G : SimpleGraph Bv) [DecidableRel G.Adj] : Type (max u v w) where
  rootRho : ℝ
  rootDensity : ℝ
  pairRealization : ReducedPairRealization Pcluster R G rootRho rootDensity
  source : PhysicalThresholdSourceFacts (small := small) (ratio := ratio)
    Q sourceDensity E0 Mb gamma epsilon
  packing : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
    PhysicalThresholdPackingFacts
      (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon)
  host : ThresholdOnlineHostFacts (target := target) (slack := slack)
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT G
    rootRho rootDensity (H := pairRealization) (Fsource := source)

/-- Realize one unbalanced source record as the package used by exceptional
forcing. -/
theorem UnbalancedFullFiberFacts.toPackage
    (hT : T.IsTree)
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (Ghost : SimpleGraph (Fin (2 * n - 2))) [DecidableRel Ghost.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun x ↦ n - 1 ≤ Ghost.degree x))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta Ghost)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    (hcard : 3 ≤ Fintype.card V)
    (horder : Fintype.card V - 1 ≤ n - 1)
    (hnotContained : ¬T.IsContained Ghost)
    (target slack : ℕ) (ratio : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N) (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * ratio) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts)
    (gamma epsilon : ℝ)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (D : UnbalancedFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity Mb P hT E0 target slack ratio gamma epsilon G) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  exact exists_thresholdOnlinePackage_of_claim6_10_fullFiberFacts Pcluster
    Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT hn beta Ghost
    hlarge hnotEC1 hnumeric hcard horder hnotContained hratio hratioHalf hN
    hslack hbranchSmall hthreshold D.packing hdisjoint G D.rootRho
    D.rootDensity D.pairRealization D.source D.host

/-- The source/live-host facts for one selected nonextreme exceptional family.
Claim 6.8 and the physical packing are run by `toPackage`. -/
structure NonextremeFullFiberFacts
    (hT : T.IsTree)
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (target slack : ℕ) (gamma epsilon : ℝ)
    (G : SimpleGraph Bv) [DecidableRel G.Adj] : Type (max u v w) where
  cap0 : K0 Q sourceDensity E0 → ℕ
  rootRho : ℝ
  rootDensity : ℝ
  rootRho_nonneg : 0 ≤ rootRho
  pairRealization : ReducedPairRealization Pcluster R G rootRho rootDensity
  source : PhysicalPartThreeRootSourceFacts (small := small)
    Q sourceDensity E0 Mb gamma epsilon
  packing : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
    PartThreePackingFacts (P := P) (S := S)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (cap0 := cap0) (gamma := gamma) (epsilon := epsilon)
  host : PartThreeMixedOnlineHostFacts (target := target) (slack := slack)
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT cap0
    gamma epsilon G rootRho rootDensity rootRho_nonneg
    (H := pairRealization) (Fsource := source)

/-- Realize one nonextreme source record as the package used by exceptional
forcing. -/
theorem NonextremeFullFiberFacts.toPackage
    (hT : T.IsTree)
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n)
    (target slack : ℕ)
    (htarget : (target : ℝ) < (n : ℝ) / 2 - 12 * Real.sqrt d * n)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (gamma epsilon : ℝ)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (D : NonextremeFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity Mb P hT E0 target slack gamma epsilon G) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  exact exists_partThreeOnlinePackage_of_claim6_8_mixedFamilyFacts Pcluster
    Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT d hd n hcardT
    horiginalLeaves hhierarchyF hhierarchyA htarget hslack hbranchSmall
    hdisjoint D.cap0 gamma epsilon D.packing G D.rootRho D.rootDensity
    D.rootRho_nonneg D.pairRealization D.source D.host

/-- Contrapositive Claim 6.15 with both exceptional cases constructed from
state-independent full-fiber facts. -/
theorem exceptionalAway_families_lt_of_fullFiberFacts
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A0 B0 : EvenPadding I) (hA : A0 = Sum.inl Q.A)
    (hL : L = padFinset
      (largeClustersAtLeast Pcluster Gdegree threshold quota))
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hT : T.IsTree)
    {nU kU : ℕ} (hnU : 2 ≤ nU)
    (Ghost : SimpleGraph (Fin (2 * nU - 2))) [DecidableRel Ghost.Adj]
    (hlarge : nU - 1 ≤
      #(Finset.univ.filter fun x ↦ nU - 1 ≤ Ghost.degree x))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta Ghost)
    (hnumeric : (2 * kU * ((nU - 1 : ℕ) : ℚ)) ≤
      beta * ((nU - 1 : ℕ) : ℚ) * ((nU - 1 : ℕ) : ℚ))
    (hcard : 3 ≤ Fintype.card V)
    (horder : Fintype.card V - 1 ≤ nU - 1)
    (hnotContainedGhost : ¬T.IsContained Ghost)
    (targetU slackU : ℕ) (ratio : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N) (hslackU : 0 < slackU)
    (hbranchSmallU : ∀ j, (branchForest P).branches.size j ≤ slackU)
    (hthreshold : ((Fintype.card V - (kU + 1) : ℕ) : ℝ) ≤
      (1 - 2 * ratio) *
          ((branchMass P (halfBranches P) : ℝ) - targetU) -
        2 * P.numParts)
    (gammaU epsilonU : ℝ)
    (d : ℝ) (hd : 0 ≤ d) (nP : ℕ)
    (hcardT : Fintype.card V = nP + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * nP)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * nP)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * nP)
    (targetP slackP : ℕ)
    (htargetP : (targetP : ℝ) <
      (nP : ℝ) / 2 - 12 * Real.sqrt d * nP)
    (hslackP : 0 < slackP)
    (hbranchSmallP : ∀ j, (branchForest P).branches.size j ≤ slackP)
    (gammaP epsilonP : ℝ)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (unbalanced : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .unbalanced
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      UnbalancedFullFiberFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity Mb P hT E0 targetU slackU ratio gammaU epsilonU G)
    (nonextreme : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .nonextreme
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      NonextremeFullFiberFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity Mb P hT E0 targetP slackP gammaP epsilonP G)
    (hnot : ¬T.IsContained G) :
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A0 B0)
      (fun e c ↦ sourceDensity A0
        (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .unbalanced).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK ∧
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A0 B0)
      (fun e c ↦ sourceDensity A0
        (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .nonextreme).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK := by
  apply exceptionalAway_families_lt_of_onlinePackages Pcluster Gdegree
    threshold quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A0 B0
    hA hL Mb hMbCard hT
  · intro E0 hdisjoint
    exact (unbalanced E0).toPackage Pcluster Gdegree threshold quota R miss Q
      sourceDensity Mb P hT E0 hnU beta Ghost hlarge hnotEC1 hnumeric hcard
      horder hnotContainedGhost targetU slackU ratio hratio hratioHalf hN
      hslackU hbranchSmallU hthreshold gammaU epsilonU hdisjoint G
  · intro E0 hdisjoint
    exact (nonextreme E0).toPackage Pcluster Gdegree threshold quota R miss Q
      sourceDensity Mb P hT E0 d hd nP hcardT horiginalLeaves hhierarchyF
      hhierarchyA targetP slackP htargetP hslackP hbranchSmallP gammaP epsilonP
      hdisjoint G
  · exact hnot

end Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing

#print axioms Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing.UnbalancedFullFiberFacts.toPackage
#print axioms Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing.NonextremeFullFiberFacts.toPackage
#print axioms Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing.exceptionalAway_families_lt_of_fullFiberFacts
