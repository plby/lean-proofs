/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61Numerics
import ErdosProblems.Erdos547b.Claim61RichFull
import ErdosProblems.Erdos547b.DegreeFormQuantitative

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoStabilityPropertyRichEntry

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoClaim61Numerics
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoPrunedReducedLargeEdges

/-- Numeric degree-form entry to the corrected quantitative Claim 6.1.
All premises are explicit hierarchy inequalities.  The non-EC1 result keeps
the adjacent rich clusters, their exact high-degree reservoirs, their
membership in the Claim-6.7 set `O`, and the padded certificate. -/
theorem pruned_degreeForm_ec1_or_richClaim61_of_error_capacities
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (quota c : ℕ) (hquota : 0 < quota)
    (hdensitySlots :
      (((2 * (quota - 1) * W.clusterSize : ℕ) : ℚ)) <
        d * (W.clusterSize : ℚ) * (W.clusterSize : ℚ))
    (hc : c ≤ paddedHalf {Q // Q ∈ W.partition.parts})
    (hdegreeCapacity :
      W.clusterSize + 2 * W.loss + W.exceptional.card ≤
        2 * c * W.clusterSize)
    (hcardCapacity :
      W.clusterSize + 2 *
          (Fintype.card {Q // Q ∈ W.partition.parts} * (quota - 1)) +
          W.exceptional.card ≤
        2 * c * W.clusterSize)
    (hthree :
      3 * (W.exceptional.card + W.loss +
        Fintype.card {Q // Q ∈ W.partition.parts} * (quota - 1)) ≤
        n - 1)
    (herror :
      (((3 * (n - 1) *
        (W.exceptional.card + W.loss +
          Fintype.card {Q // Q ∈ W.partition.parts} *
            (quota - 1)) : ℕ) : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let H := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
    let R : SimpleGraph ι :=
      regularityReducedGraph H (fun i : ι => i.1) ε d
    let L := largeClustersAtLeast P G (n - 1) quota
    ZhaoExtremalCaseOne α G ∨
      Nonempty (RichClaim61Certificate P G (n - 1) quota R L
        (2 * c + 1)) := by
  classical
  let ι := {Q // Q ∈ W.partition.parts}
  let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
    partitionAssignment W.exceptional W.partition
  let richError := nonLargeHighError P G (n - 1) quota
  let richCap := Fintype.card ι * (quota - 1)
  have hrichle : richError ≤ richCap := by
    exact nonLargeHighError_le_card_mul P G (n - 1) quota
  have hcardCapacityExact :
      W.clusterSize + 2 * richError + W.exceptional.card ≤
        2 * c * W.clusterSize := by
    have hcap : W.clusterSize + 2 * richCap + W.exceptional.card ≤
        2 * c * W.clusterSize := by
      simpa only [richCap, ι] using hcardCapacity
    omega
  have hthreeExact :
      3 * (W.exceptional.card + W.loss + richError) ≤ n - 1 := by
    have hcap : 3 * (W.exceptional.card + W.loss + richCap) ≤ n - 1 := by
      simpa only [richCap, ι] using hthree
    omega
  have herrorExact :
      (((3 * (n - 1) * (W.exceptional.card + W.loss + richError) : ℕ) : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) := by
    have hnat :
        3 * (n - 1) * (W.exceptional.card + W.loss + richError) ≤
          3 * (n - 1) * (W.exceptional.card + W.loss + richCap) := by
      exact Nat.mul_le_mul_left (3 * (n - 1)) (by omega)
    have hcast :
        (((3 * (n - 1) * (W.exceptional.card + W.loss + richError) : ℕ) : ℕ) : ℚ) ≤
          (((3 * (n - 1) * (W.exceptional.card + W.loss + richCap) : ℕ) : ℕ) : ℚ) := by
      exact_mod_cast hnat
    exact hcast.trans (by simpa only [richCap, ι] using herror)
  have hhost := exceptional_add_clusters_eq_host W
  have hhost' : W.exceptional.card + Fintype.card ι * W.clusterSize =
      2 * (n - 1) := by
    have hhost'' : W.exceptional.card + Fintype.card ι * W.clusterSize =
        2 * n - 2 := by
      simpa [ι] using hhost
    omega
  have hsmallDegree : W.exceptional.card + W.loss ≤ n - 1 := by
    have := hthreeExact
    omega
  have hsmallCard : W.exceptional.card + richError ≤ n - 1 := by
    have := hthreeExact
    omega
  have hRichPositive : W.exceptional.card + richError < n - 1 := by
    have hqpos : 0 < n - 1 := by omega
    have := hthreeExact
    omega
  have hdegreeScale :
      (paddedHalf ι - c) * W.clusterSize ≤
        (n - 1 - W.loss) - W.exceptional.card :=
    claim67_scale_of_capacity ι (n - 1) W.exceptional.card W.loss
      W.clusterSize c hhost' hsmallDegree hc hdegreeCapacity
  have hcardScale :
      (paddedHalf ι - c) * W.clusterSize ≤
        n - 1 - W.exceptional.card - richError :=
    claim67_card_scale_of_rich_error ι (n - 1) W.exceptional.card
      richError W.clusterSize c hhost' hsmallCard hc (by
        exact hcardCapacityExact)
  have hEC1numeric :
      (1 - α) * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) ≤
        (((n - 1 - W.exceptional.card - richError) *
          (n - 1 - W.loss) -
          2 * (n - 1) * (W.exceptional.card + W.loss + richError) : ℕ) : ℚ) :=
    ec1_numeric_of_rich_error α (n - 1) W.exceptional.card W.loss richError
      hthreeExact
      herrorExact
  apply claim6_1_rich_full G W hn
  · simpa only [highDegreeVertices] using hlarge
  · exact hquota
  · exact W.clusterSize_pos
  · exact hdensitySlots
  · simpa only [richError, nonLargeHighError, P, ι] using hRichPositive
  · simpa only [ι] using hdegreeScale
  · simpa only [richError, nonLargeHighError, P, ι] using hcardScale
  · simpa only [richError, nonLargeHighError, P, ι] using hEC1numeric

end Erdos547b.ZhaoStabilityPropertyRichEntry
