/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.ForestPartitionEventualHierarchy
import ErdosProblems.Erdos547b.Section6EventualParameters

/-!
# An explicit tree-order threshold for the Section 6 hierarchy

The degree-form threshold controls the host.  The additional threshold in
this file controls the number of components of the Zhao forest partition.
It is deliberately kept separate, since the final eventual statement may
take the maximum of both bounds.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSection6EventualTreeParameters

open Erdos547b.TreePartition
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoSection6EventualParameters

/-- The tree components used inside one regular pair must be smaller than the
later reduced-graph scales from Claims 6.16 and 6.17.  Dividing the regularity
error by a bound for the number of degree-form clusters makes every component
negligible compared with the actual cluster size. -/
def treeRho (β : ℚ) : ℚ :=
  regularityEpsilon β /
    (100 * (degreeFormBound (regularityEpsilon β) (section6M₀ β) + 1))

/-- Downward-rounded component scale for the Zhao forest partition. -/
def treeScale (β : ℚ) (n : ℕ) : ℕ :=
  lowerScale ((treeRho β : ℝ) * n)

theorem treeRho_pos {β : ℚ} (hβ0 : 0 < β) : 0 < treeRho β := by
  simp only [treeRho]
  positivity [regularityEpsilon_pos hβ0]

theorem treeRho_le_one {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) : treeRho β ≤ 1 := by
  have hεlt : (regularityEpsilon β : ℝ) < 1 := by
    have hεd := regularityEpsilon_lt_reducedDensity hβ0 hβ1
    have hσ := sigma_le_one_div hβ0 hβ1
    have hd : (reducedDensity β : ℝ) = 5 * (sigma β : ℝ) := by
      simp only [reducedDensity]
      push_cast
      rfl
    rw [hd] at hεd
    linarith
  let M := degreeFormBound (regularityEpsilon β) (section6M₀ β)
  have hM : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hden : (1 : ℝ) ≤
      100 * ((M + 1 : ℕ) : ℝ) := by nlinarith
  have hdenPos : (0 : ℝ) <
      100 * ((M + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) hden
  have hcast : (treeRho β : ℝ) =
      (regularityEpsilon β : ℝ) /
        (100 * ((M + 1 : ℕ) : ℝ)) := by
    simp only [treeRho, M]
    push_cast
    rfl
  have hreal : (treeRho β : ℝ) ≤ 1 := by
    rw [hcast]
    exact (div_le_one hdenPos).2 (hεlt.le.trans hden)
  exact_mod_cast hreal

/-- Above this order the product `treeRho * sigma * n` is larger than the coarse
constant used in the partition-count estimate. -/
def section6TreeN₀ (β : ℚ) : ℕ :=
  upperScale
      (13 / ((treeRho β : ℝ) * (sigma β : ℝ))) + 1

theorem treeRho_mul_sigma_mul_order_gt_twelve
    {β : ℚ} (hβ0 : 0 < β) {n : ℕ}
    (hn : section6TreeN₀ β ≤ n) :
    12 < (treeRho β : ℝ) * (sigma β : ℝ) * n := by
  have hrho : (0 : ℝ) < (treeRho β : ℝ) := by
    exact_mod_cast treeRho_pos hβ0
  have hsigma : (0 : ℝ) < (sigma β : ℝ) := by
    exact_mod_cast sigma_pos hβ0
  let a : ℝ := (treeRho β : ℝ) * (sigma β : ℝ)
  have ha : 0 < a := mul_pos hrho hsigma
  have hceil : 13 / a ≤ (upperScale (13 / a) : ℝ) :=
    le_upperScale_cast _
  have hnNat : upperScale (13 / a) + 1 ≤ n := by
    simpa only [section6TreeN₀, a] using hn
  have hnReal : (upperScale (13 / a) : ℝ) + 1 ≤ n := by
    exact_mod_cast hnNat
  have hthirteen : 13 < a * n := by
    have hdiv : 13 / a < (n : ℝ) := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hdiv
  simpa only [a] using hthirteen.trans' (by norm_num : (12 : ℝ) < 13)

/-- The component scale is small relative to every cluster returned by the
degree-form witness.  This is the exact rounding inequality consumed by the
three physical source-orientation constructors in Claim 6.15. -/
theorem treeScale_rounding_le_degreeFormCluster
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hN : section6N₀ β ≤ 2 * n)
    (hnTree : section6TreeN₀ β ≤ n) :
    (2 : ℝ) + 3 * treeScale β n ≤
      3 * ((regularityEpsilon β : ℝ) * W.clusterSize) := by
  let M := degreeFormBound (regularityEpsilon β) (section6M₀ β)
  have hnpos : 0 < n := by
    have hleft : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhost : 0 < 2 * n := hleft.trans_le W.five_ordinaryParts_le_host
    omega
  have hε0 : (0 : ℝ) < (regularityEpsilon β : ℝ) := by
    exact_mod_cast regularityEpsilon_pos hβ0
  have hσ0 : (0 : ℝ) ≤ (sigma β : ℝ) := by
    exact_mod_cast (sigma_pos hβ0).le
  have hσ1 : (sigma β : ℝ) ≤ 1 :=
    (sigma_le_one_div hβ0 hβ1).trans (by norm_num)
  have hE := (degreeForm_exceptional_and_loss_small hβ0 hβ1 W hN).1
  have hElt : (W.exceptional.card : ℝ) < n := by
    have hσ := sigma_le_one_div hβ0 hβ1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    calc
      (W.exceptional.card : ℝ) < (sigma β : ℝ) * (2 * n) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hE
      _ ≤ (1 / 1000 : ℝ) * (2 * n) :=
        mul_le_mul_of_nonneg_right hσ (by positivity)
      _ < n := by nlinarith
  have hhost := exceptional_add_clusters_eq_host W
  have hparts : n ≤ W.partition.parts.card * W.clusterSize := by
    have hEltNat : W.exceptional.card < n := by exact_mod_cast hElt
    omega
  have hpartsM : W.partition.parts.card ≤ M :=
    W.cleaned_le_ordinary.trans W.upper_parts
  have hnMNat : n ≤ M * W.clusterSize :=
    hparts.trans (Nat.mul_le_mul_right W.clusterSize hpartsM)
  have hnM : (n : ℝ) ≤ (M : ℝ) * W.clusterSize := by
    exact_mod_cast hnMNat
  have hMstep : (M : ℝ) ≤ (M + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ M
  have hdenPos : (0 : ℝ) < 100 * ((M + 1 : ℕ) : ℝ) := by positivity
  have htreeRho : (treeRho β : ℝ) =
      (regularityEpsilon β : ℝ) /
        (100 * ((M + 1 : ℕ) : ℝ)) := by
    simp only [treeRho, M]
    push_cast
    rfl
  have htreeMul : (treeRho β : ℝ) * n ≤
      (regularityEpsilon β : ℝ) * W.clusterSize / 100 := by
    rw [htreeRho, div_mul_eq_mul_div, div_le_iff₀ hdenPos]
    calc
      (regularityEpsilon β : ℝ) * n ≤
          (regularityEpsilon β : ℝ) *
            ((M : ℝ) * W.clusterSize) :=
        mul_le_mul_of_nonneg_left hnM hε0.le
      _ ≤ (regularityEpsilon β : ℝ) *
          (((M + 1 : ℕ) : ℝ) * W.clusterSize) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hMstep (by positivity)) hε0.le
      _ = ((regularityEpsilon β : ℝ) * W.clusterSize / 100) *
          (100 * ((M + 1 : ℕ) : ℝ)) := by ring
  have hscaleUpper : (treeScale β n : ℝ) ≤
      (treeRho β : ℝ) * n := by
    simpa only [treeScale] using
      (lowerScale_cast_le
        (mul_nonneg (by exact_mod_cast (treeRho_pos hβ0).le)
          (by positivity : (0 : ℝ) ≤ n)))
  have hscale : (treeScale β n : ℝ) ≤
      (regularityEpsilon β : ℝ) * W.clusterSize / 100 :=
    hscaleUpper.trans htreeMul
  have hproduct := treeRho_mul_sigma_mul_order_gt_twelve hβ0 hnTree
  have hproductUpper :
      (treeRho β : ℝ) * (sigma β : ℝ) * n ≤
        (regularityEpsilon β : ℝ) * W.clusterSize / 100 := by
    calc
      (treeRho β : ℝ) * (sigma β : ℝ) * n =
          (sigma β : ℝ) * ((treeRho β : ℝ) * n) := by ring
      _ ≤ 1 * ((regularityEpsilon β : ℝ) * W.clusterSize / 100) :=
        mul_le_mul hσ1 htreeMul
          (mul_nonneg
            (by exact_mod_cast (treeRho_pos hβ0).le)
            (by positivity : (0 : ℝ) ≤ n))
          (by norm_num)
      _ = (regularityEpsilon β : ℝ) * W.clusterSize / 100 := by ring
  have hlarge : 12 <
      (regularityEpsilon β : ℝ) * W.clusterSize / 100 :=
    hproduct.trans_le hproductUpper
  nlinarith

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V}

/-- The literal hierarchy premises used by Claims 6.8 and 6.10, specialized
to the cluster-compatible tree component scale. -/
theorem eventual_partition_hierarchy
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {n : ℕ} (hn : section6TreeN₀ β ≤ n) (hnOne : 1 ≤ n)
    (hcard : Fintype.card V = n + 1)
    (P : ZhaoForestPartition T globalRoot (treeScale β n)) :
    2 * (P.numParts : ℝ) < 1 + (sigma β : ℝ) * n ∧
      3 * (P.numParts : ℝ) < 1 + 2 * (sigma β : ℝ) * n := by
  have hrho : (0 : ℝ) < (treeRho β : ℝ) := by
    exact_mod_cast treeRho_pos hβ0
  have hrhoOne : (treeRho β : ℝ) ≤ 1 := by
    exact_mod_cast treeRho_le_one hβ0 hβ1
  have hsigma : (0 : ℝ) ≤ (sigma β : ℝ) := by
    exact_mod_cast (sigma_pos hβ0).le
  simpa only [treeScale] using
    (eventual_hierarchy_bounds (treeRho β : ℝ) (sigma β : ℝ)
      hrho hrhoOne hsigma n hnOne hcard P
        (treeRho_mul_sigma_mul_order_gt_twelve hβ0 hn))

end Erdos547b.ZhaoSection6EventualTreeParameters

#print axioms Erdos547b.ZhaoSection6EventualTreeParameters.treeRho_mul_sigma_mul_order_gt_twelve
#print axioms Erdos547b.ZhaoSection6EventualTreeParameters.treeScale_rounding_le_degreeFormCluster
#print axioms Erdos547b.ZhaoSection6EventualTreeParameters.eventual_partition_hierarchy
