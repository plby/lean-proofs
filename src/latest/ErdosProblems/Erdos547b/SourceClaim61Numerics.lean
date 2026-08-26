/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61Numerics
import ErdosProblems.Erdos547b.Claim61PairPrunedFull
import ErdosProblems.Erdos547b.Section6RichHierarchy

/-!
# Source-scale large-cluster counting and integer capacities

The two-pass count in `(LC-bootstrap)` of `tex/547.tex` retains the number
of nonlarge clusters. This permits the defect `ceil (4 * sqrt d * k)`;
using the total number of clusters throughout loses this source margin.
-/

noncomputable section

namespace Erdos547b.ZhaoSourceClaim61Numerics

open Erdos547b.ZhaoClaim61Numerics Erdos547b.ZhaoEvenReducedPadding

/-- A second use of the high-vertex count improves the discarded-vertex
estimate from `4 * sigma * q` to `3 * sigma * q`. -/
theorem nonlarge_error_bootstrap
    (q E Q L m u : ℕ) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (hL : L ≤ Q) (hhost : E + Q * m = 2 * q)
    (hhigh : q ≤ E + L * m + (Q - L) * u)
    (hquota : (u : ℝ) ≤ 2 * sigma * m) :
    (((Q - L) * u : ℕ) : ℝ) ≤ 3 * sigma * q := by
  let R := (Q - L) * u
  have hhostR : (E : ℝ) + (Q : ℝ) * m = 2 * q := by exact_mod_cast hhost
  have hhighR : (q : ℝ) ≤ E + (L : ℝ) * m + (R : ℝ) := by
    exact_mod_cast hhigh
  have hQm : (Q : ℝ) * m ≤ 2 * q := by linarith
  have hcoarse : (R : ℝ) ≤ 4 * sigma * q := by
    calc
      (R : ℝ) ≤ (Q : ℝ) * u := by
        exact_mod_cast Nat.mul_le_mul_right u (Nat.sub_le Q L)
      _ ≤ (Q : ℝ) * (2 * sigma * m) :=
        mul_le_mul_of_nonneg_left hquota (by positivity)
      _ = (2 * sigma) * ((Q : ℝ) * m) := by ring
      _ ≤ (2 * sigma) * (2 * q) :=
        mul_le_mul_of_nonneg_left hQm (by positivity)
      _ = 4 * sigma * q := by ring
  have hnonlarge : ((Q - L : ℕ) : ℝ) * m ≤ (q : ℝ) + R := by
    rw [Nat.cast_sub hL]
    nlinarith only [hhostR, hhighR]
  have hsharp : (R : ℝ) ≤ 2 * sigma * ((q : ℝ) + R) := by
    calc
      (R : ℝ) = ((Q - L : ℕ) : ℝ) * u := by simp only [R, Nat.cast_mul]
      _ ≤ ((Q - L : ℕ) : ℝ) * (2 * sigma * m) :=
        mul_le_mul_of_nonneg_left hquota (by positivity)
      _ = (2 * sigma) * (((Q - L : ℕ) : ℝ) * m) := by ring
      _ ≤ (2 * sigma) * ((q : ℝ) + R) :=
        mul_le_mul_of_nonneg_left hnonlarge (by positivity)
  have hcoarseMul := mul_le_mul_of_nonneg_left hcoarse (show 0 ≤ 2 * sigma by positivity)
  have hsmallMul := mul_le_mul_of_nonneg_right hsigmaSmall
    (show 0 ≤ sigma * q by positivity)
  change (R : ℝ) ≤ _
  nlinarith only [hsharp, hcoarseMul, hsmallMul,
    show 0 ≤ sigma * q by positivity]

/-- Zhao's rounded reduced-degree defect. -/
def matchingDefect (sigma : ℝ) (k : ℕ) : ℕ := ⌈4 * sigma * k⌉₊

theorem matchingDefect_le {sigma : ℝ} (hsigma : sigma ≤ 1 / 16) (k : ℕ) :
    matchingDefect sigma k ≤ k := by
  apply Nat.ceil_le.mpr
  have h := mul_le_mul_of_nonneg_right hsigma (show (0 : ℝ) ≤ k by positivity)
  nlinarith only [h, show (0 : ℝ) ≤ k by positivity]

/-- Sufficient real scale estimates imply all four integral gates for the
rich Claim-6.1 constructor. No density/reservoir separation is assumed. -/
theorem rounded_capacity_gates
    (q E loss Q R m k : ℕ) (sigma : ℝ) (α : ℚ)
    (hsigma : 0 ≤ sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (hhost : E + Q * m = 2 * q) (hpad : Q ≤ 2 * k)
    (hE : (E : ℝ) ≤ sigma * q / 4)
    (hloss : (loss : ℝ) ≤ sigma * q / 4)
    (hR : (R : ℝ) ≤ 3 * sigma * q)
    (hm : (m : ℝ) ≤ sigma * q)
    (hα : 11 * sigma ≤ (α : ℝ)) :
    m + 2 * loss + E ≤ 2 * matchingDefect sigma k * m ∧
      m + 2 * R + E ≤ 2 * matchingDefect sigma k * m ∧
      3 * (E + loss + R) ≤ q ∧
      ((3 * q * (E + loss + R) : ℕ) : ℚ) ≤ α * (q : ℚ) * q := by
  have hhostR : (E : ℝ) + (Q : ℝ) * m = 2 * q := by exact_mod_cast hhost
  have hpadMul : (Q : ℝ) * m ≤ (2 : ℝ) * k * m := by
    exact_mod_cast Nat.mul_le_mul_right m hpad
  have hcover : (q : ℝ) ≤ (k : ℝ) * m + E / 2 := by
    linarith only [hhostR, hpadMul]
  have hceil : 4 * sigma * k ≤ (matchingDefect sigma k : ℝ) := Nat.le_ceil _
  have hceilMul := mul_le_mul_of_nonneg_right hceil
    (show (0 : ℝ) ≤ 2 * m by positivity)
  have hcoverMul := mul_le_mul_of_nonneg_left hcover
    (show 0 ≤ 8 * sigma by positivity)
  have hEMul := mul_le_mul_of_nonneg_left hE (show 0 ≤ 4 * sigma by positivity)
  have hsmallMul := mul_le_mul_of_nonneg_right hsigmaSmall
    (show 0 ≤ sigma * q by positivity)
  have hnonneg : 0 ≤ sigma * q := by positivity
  have hcapacity : (m : ℝ) + 2 * R + E ≤
      2 * (matchingDefect sigma k : ℝ) * m := by
    nlinarith only [hceilMul, hcoverMul, hEMul, hsmallMul, hnonneg, hm, hR, hE]
  have hdegree : (m : ℝ) + 2 * loss + E ≤
      2 * (matchingDefect sigma k : ℝ) * m := by
    nlinarith only [hceilMul, hcoverMul, hEMul, hsmallMul, hnonneg, hm, hloss, hE]
  have hb : (E : ℝ) + loss + R ≤ (7 / 2 : ℝ) * sigma * q := by
    linarith only [hE, hloss, hR]
  have hsmallq := mul_le_mul_of_nonneg_right hsigmaSmall
    (show (0 : ℝ) ≤ q by positivity)
  have hthree : (3 : ℝ) * (E + loss + R) ≤ q := by
    nlinarith only [hb, hsmallq, show (0 : ℝ) ≤ q by positivity]
  have hαq := mul_le_mul_of_nonneg_right hα (show (0 : ℝ) ≤ q by positivity)
  have hthreeα : (3 : ℝ) * (E + loss + R) ≤ (α : ℝ) * q := by
    nlinarith only [hb, hαq, hnonneg]
  have hfinal : (3 : ℝ) * q * (E + loss + R) ≤ (α : ℝ) * q * q := by
    have h := mul_le_mul_of_nonneg_left hthreeα (show (0 : ℝ) ≤ q by positivity)
    nlinarith only [h]
  exact ⟨by exact_mod_cast hdegree, by exact_mod_cast hcapacity,
    by exact_mod_cast hthree, by exact_mod_cast hfinal⟩

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoPrunedReducedLargeEdges
open Erdos547b.ZhaoSection6RichHierarchy Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoClaim61PairPrunedFull

/-- The sharpened count for an actual degree-form partition and the
upward-rounded reservoir quota. -/
theorem degreeForm_nonlarge_error_le
    {n m₀ M : ℕ} {ε d : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16) :
    (nonLargeHighError (partitionAssignment W.exceptional W.partition)
      G (n - 1) (richQuota sigma W.clusterSize) : ℝ) ≤
        3 * sigma * (n - 1 : ℕ) := by
  classical
  let ι := {Q // Q ∈ W.partition.parts}
  let P := partitionAssignment W.exceptional W.partition
  let quota := richQuota sigma W.clusterSize
  let L := largeClustersAtLeast P G (n - 1) quota
  have hquota : 0 < quota := richQuota_pos hsigma W.clusterSize_pos
  have hcluster : ∀ i : ι, (clusterVertices P i).card ≤ W.clusterSize := by
    intro i
    rw [clusterVertices_partitionAssignment W.exceptional W.partition i]
    exact (W.equal_clusters i.1 i.2).le
  have hhost : W.exceptional.card + Fintype.card ι * W.clusterSize =
      2 * (n - 1) := by
    have h := exceptional_add_clusters_eq_host W
    have hnsub : 2 * n - 2 = 2 * (n - 1) := by omega
    simpa [ι, hnsub] using h
  have hhigh : n - 1 ≤ W.exceptional.card + L.card * W.clusterSize +
      (Fintype.card ι - L.card) * (quota - 1) := by
    have h := hlarge.trans (highDegree_card_le_exceptional_add_large_small
      P G (n - 1) quota W.clusterSize hquota hcluster)
    simpa only [P, exceptionalVertices_partitionAssignment] using h
  exact nonlarge_error_bootstrap (n - 1) W.exceptional.card (Fintype.card ι)
    L.card W.clusterSize (quota - 1) sigma hsigma.le hsigmaSmall
    (Finset.card_le_univ L) hhost hhigh
    (richQuota_sub_one_cast_lt hsigma W.clusterSize_pos).le

/-- The source-scale constructor now requires just the cleanup and cluster
size bounds. The high-vertex error and every integer gate are derived from
the actual degree-form witness, including the sharp two-pass count. -/
theorem pairPruned_rich_entry
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (hE : (W.exceptional.card : ℝ) ≤ sigma * (n - 1 : ℕ) / 4)
    (hloss : (W.loss : ℝ) ≤ sigma * (n - 1 : ℕ) / 4)
    (hm : (W.clusterSize : ℝ) ≤ sigma * (n - 1 : ℕ))
    (hα : 11 * sigma ≤ (α : ℝ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P := partitionAssignment W.exceptional W.partition
    let quota := richQuota sigma W.clusterSize
    let L := largeClustersAtLeast P G (n - 1) quota
    let R := pruneSmallEdges
      (regularityReducedGraph (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
        (fun i : ι => i.1) ε d) (L : Set ι)
    ZhaoExtremalCaseOne α G ∨
      Nonempty (RichClaim61Certificate P G (n - 1) quota R L
        (2 * matchingDefect sigma (paddedHalf ι) + 1)) := by
  classical
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let P := partitionAssignment W.exceptional W.partition
  let quota := richQuota sigma W.clusterSize
  let L := largeClustersAtLeast P G (n - 1) quota
  let richError := (Fintype.card ι - L.card) * (quota - 1)
  let c := matchingDefect sigma (paddedHalf ι)
  have hquota : 0 < quota := richQuota_pos hsigma W.clusterSize_pos
  have hhost : W.exceptional.card + Fintype.card ι * W.clusterSize =
      2 * (n - 1) := by
    have h := exceptional_add_clusters_eq_host W
    have hnsub : 2 * n - 2 = 2 * (n - 1) := by omega
    simpa [ι, hnsub] using h
  have herror : (richError : ℝ) ≤ 3 * sigma * (n - 1 : ℕ) :=
    degreeForm_nonlarge_error_le G W hn hlarge sigma hsigma hsigmaSmall
  obtain ⟨hdegreeCap, hcardCap, hthree, herrorCap⟩ :=
    rounded_capacity_gates (n - 1) W.exceptional.card W.loss (Fintype.card ι)
      richError W.clusterSize (paddedHalf ι) sigma α hsigma.le hsigmaSmall
      hhost (card_le_paddedCard ι) hE hloss herror hm hα
  have hc : c ≤ paddedHalf ι := matchingDefect_le hsigmaSmall _
  have hRichPositive : W.exceptional.card + richError < n - 1 := by omega
  have hdegreeScale := claim67_scale_of_capacity ι (n - 1)
    W.exceptional.card W.loss W.clusterSize c hhost (by omega) hc hdegreeCap
  have hcardScale := claim67_card_scale_of_rich_error ι (n - 1)
    W.exceptional.card richError W.clusterSize c hhost (by omega) hc hcardCap
  have hEC1 := ec1_numeric_of_rich_error α (n - 1) W.exceptional.card
    W.loss richError hthree herrorCap
  exact claim6_1_rich_pairPruned_full G W hn hlarge quota c hquota
    W.clusterSize_pos hRichPositive hdegreeScale hcardScale hEC1

end Erdos547b.ZhaoSourceClaim61Numerics

#print axioms Erdos547b.ZhaoSourceClaim61Numerics.nonlarge_error_bootstrap
#print axioms Erdos547b.ZhaoSourceClaim61Numerics.matchingDefect_le
#print axioms Erdos547b.ZhaoSourceClaim61Numerics.rounded_capacity_gates
#print axioms Erdos547b.ZhaoSourceClaim61Numerics.degreeForm_nonlarge_error_le
#print axioms Erdos547b.ZhaoSourceClaim61Numerics.pairPruned_rich_entry
