/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberScalarApplication

/-!
# Exceptional-family forcing through the checked physical plan

This module is the cardinality bridge between the exceptional edge filters
used in Lemma 6.11 / Claim 6.18 and the checked physical Claim-6.15 backend.
The package below contains only source allocations, regular-pair data, and
scalar inequalities.  A large exceptional family selects a literal
submatching disjoint from the preliminary reserved matching; the cut-aware
coordinate theorem then returns the actual tree containment.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalForcing

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
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
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable (G : SimpleGraph Bv) [DecidableRel G.Adj]

/-- All non-result data required by the checked physical Claim-6.15
endpoint.  In particular, this structure has no copy, containment,
continuation, or online-state-success field. -/
structure FixedPhysicalApplicationPackage
    (hT : T.IsTree) : Type (max u v w) where
  available : Finset (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
  target : ℕ
  slack : ℕ
  selected : SelectedF0 P available target slack
  cap0 : K0 Q sourceDensity E0 → ℕ
  cap1 : K1 Q sourceDensity E0 Mb → ℕ
  capb : Kb Q sourceDensity Mb → ℕ
  allocation : PhysicalSourceAllocationWith Q sourceDensity P selected E0 Mb
    cap0 cap1 capb
  small_pos : 1 ≤ small
  available_half : available ⊆ halfBranches P
  rootRho : ℝ
  rootDensity : ℝ
  removalBudget : ℝ
  pairRealization : ReducedPairRealization Pcluster R G rootRho rootDensity
  plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P selected cap0 cap1 capb allocation rootRho
      rootDensity removalBudget
  commonCard : ℕ
  globalFacts : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R
    miss Q P hT rootRho rootDensity removalBudget commonCard

/-- A checked package yields the literal containment once the exceptional and
reserved physical edge families are disjoint. -/
theorem FixedPhysicalApplicationPackage.isContained
    {hT : T.IsTree}
    (D : FixedPhysicalApplicationPackage Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P G hT)
    (hdisjoint : Disjoint E0.selected Mb.selected) :
    T.IsContained G := by
  exact isContained_of_physicalFiberPlanScalarFacts Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb hT P D.small_pos D.selected D.allocation
      D.available_half hdisjoint G D.rootRho D.rootDensity D.removalBudget
      D.plan D.pairRealization D.commonCard D.globalFacts

/-- The exceptional filter after deleting the matching edges incident with
the two distinguished clusters. -/
def exceptionalAwayFamily {E : Type*} [DecidableEq E]
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta0 : ℝ) :
    ExceptionalCase → Finset E
  | .unbalanced => unbalancedEdges M density eta0
  | .nonextreme => nonextremeEdges M density eta0

/-- Deleting distinguished incident edges can only shrink either exceptional
filter. -/
theorem exceptionalAwayFamily_subset_exceptionalFamily
    (A B : EvenPadding I) (L : Finset (EvenPadding I)) (eta0 : ℝ)
    (hA : A = Sum.inl Q.A) :
    exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A B)
      (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
      eta0 which ⊆
      exceptionalFamily Q sourceDensity L eta0 which := by
  subst A
  cases which with
  | unbalanced =>
      intro e he
      change e ∈ unbalancedEdges
        (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
          Q.claim67.M L (Sum.inl Q.A) B)
        (fun e c ↦ sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta0 at he
      change e ∈ unbalancedEdges (allMatchingEdges Q.claim67.M)
        (fun e c ↦ sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta0
      rw [mem_unbalancedEdges] at he ⊢
      exact ⟨Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished_subset
        Q.claim67.M L (Sum.inl Q.A) B he.1, he.2⟩
  | nonextreme =>
      intro e he
      change e ∈ nonextremeEdges
        (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
          Q.claim67.M L (Sum.inl Q.A) B)
        (fun e c ↦ sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta0 at he
      change e ∈ nonextremeEdges (allMatchingEdges Q.claim67.M)
        (fun e c ↦ sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta0
      rw [mem_nonextremeEdges] at he ⊢
      exact ⟨Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished_subset
        Q.claim67.M L (Sum.inl Q.A) B he.1, he.2⟩

/-- A large away-family selects the exact half-scale exceptional matching,
avoids the preliminary reserve, and realizes any checked physical package.
This is the oracle-free cardinality core of Claim 6.15. -/
theorem isContained_of_largeExceptionalAway
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A B : EvenPadding I) (hA : A = Sum.inl Q.A)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hlarge : (eta beta : ℝ) * reducedK ≤
      (#(exceptionalAwayFamily
        (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
          Q.claim67.M L A B)
        (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
        (eta beta : ℝ) which) : ℝ))
    (hT : T.IsTree)
    (packages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) which
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT)) :
    T.IsContained G := by
  have hfamily : (eta beta : ℝ) * reducedK ≤
      (#(exceptionalFamily Q sourceDensity L (eta beta : ℝ) which) : ℝ) := by
    calc
      (eta beta : ℝ) * reducedK ≤
          (#(exceptionalAwayFamily
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M L A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M L e c))
            (eta beta : ℝ) which) : ℝ) := hlarge
      _ ≤ (#(exceptionalFamily Q sourceDensity L (eta beta : ℝ)
          which) : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (exceptionalAwayFamily_subset_exceptionalFamily
            (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R)
            (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
            (which := which) (A := A) (B := B) (L := L)
            (eta0 := (eta beta : ℝ)) hA)
  obtain ⟨⟨E0, hdisjoint⟩⟩ :=
    exists_eventualHalfSelectedExceptionalEdges_avoiding Q sourceDensity
      hbeta hbetaOne hreducedK L which Mb.selected hfamily hMbCard
  obtain ⟨D⟩ := packages E0 hdisjoint
  exact FixedPhysicalApplicationPackage.isContained
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) (P := P)
    (G := G) D hdisjoint

/-- Both exceptional alternatives furnish the containment-forcing callback
used by the oracle-free Lemma-6.11 contrapositive. -/
theorem exceptionalAway_large_forces_containment
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A B : EvenPadding I) (hA : A = Sum.inl Q.A)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hT : T.IsTree)
    (unbalancedPackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .unbalanced
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (nonextremePackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .nonextreme
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (hlarge :
      (eta beta : ℝ) * reducedK ≤
          (#(exceptionalAwayFamily
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M L A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M L e c))
            (eta beta : ℝ) .unbalanced) : ℝ) ∨
        (eta beta : ℝ) * reducedK ≤
          (#(exceptionalAwayFamily
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M L A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M L e c))
            (eta beta : ℝ) .nonextreme) : ℝ)) :
    T.IsContained G := by
  rcases hlarge with hlarge | hlarge
  · exact isContained_of_largeExceptionalAway Pcluster Gdegree threshold
      quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A B hA Mb
      hMbCard hlarge hT unbalancedPackages
  · exact isContained_of_largeExceptionalAway Pcluster Gdegree threshold
      quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A B hA Mb
      hMbCard hlarge hT nonextremePackages

/-- Contrapositive form consumed by the rich Lemma-6.11 construction: under
actual noncontainment, both away-families lie below the paper's exceptional
threshold. -/
theorem exceptionalAway_families_lt_of_physicalPackages
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A B : EvenPadding I) (hA : A = Sum.inl Q.A)
    (hL : L = padFinset
      (largeClustersAtLeast Pcluster Gdegree threshold quota))
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hT : T.IsTree)
    (unbalancedPackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .unbalanced
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (nonextremePackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .nonextreme
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (hnot : ¬ T.IsContained G) :
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A B)
      (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .unbalanced).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK ∧
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A B)
      (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .nonextreme).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK := by
  subst L
  have hforce :
      (eta beta : ℝ) * reducedK ≤
          ((unbalancedEdges
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) e c))
            (eta beta : ℝ)).card : ℝ) ∨
        (eta beta : ℝ) * reducedK ≤
          ((nonextremeEdges
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) e c))
            (eta beta : ℝ)).card : ℝ) → T.IsContained G := by
    intro hlarge
    apply exceptionalAway_large_forces_containment Pcluster Gdegree threshold
      quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A B hA Mb
      hMbCard hT unbalancedPackages nonextremePackages
    simpa only [exceptionalAwayFamily] using hlarge
  have hsmall :=
    Erdos547b.ZhaoRichClaim61Lemma611.exceptional_families_away_lt_of_not_contained
      T G Q.claim67 A B sourceDensity (eta beta : ℝ) (reducedK : ℝ)
        hforce hnot
  simpa only [exceptionalAwayFamily] using hsmall

end Erdos547b.ZhaoClaim615RichExceptionalForcing

#print axioms Erdos547b.ZhaoClaim615RichExceptionalForcing.isContained_of_largeExceptionalAway
#print axioms Erdos547b.ZhaoClaim615RichExceptionalForcing.exceptionalAway_large_forces_containment
#print axioms Erdos547b.ZhaoClaim615RichExceptionalForcing.exceptionalAway_families_lt_of_physicalPackages
