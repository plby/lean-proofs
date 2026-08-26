/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceBalancedForestMass
import ErdosProblems.Erdos547b.Claim610HostEmbedding
import ErdosProblems.Erdos547b.SourceDegreeFormRootRows

/-!
# Source balanced mass from a non-EC1 host

The nonleaf core has the actual integer scale floor(alpha*q/4).
The source schedule pays its rounding and the partition-root loss.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceBalancedMassFromHost

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceBalancedForestMass Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoClaim610HostEmbedding Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem root_loss_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (count : ℕ) (hcount : (count : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    3 * (count : ℝ) ≤ (α : ℝ) / 16 * q := by
  subst hostN
  obtain ⟨_, _, hσ, hd, he, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have heα : 48 * epsilon α ≤ α := by linarith only [hσ, hd, he, sq_nonneg (fourthRoot α)]
  have heαR : (48 : ℝ) * (epsilon α : ℝ) ≤ (α : ℝ) := by exact_mod_cast heα
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hd1R : (degreeError α : ℝ) ≤ 1 := by exact_mod_cast hd1
  have hdq := mul_le_mul_of_nonneg_right hd1R (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hNq : (W.clusterSize : ℝ) ≤ q := by nlinarith only [hN, hdq, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have heps : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hcountq := hcount.trans (mul_le_mul_of_nonneg_left hNq heps)
  have heαq := mul_le_mul_of_nonneg_right heαR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hcountq, heαq]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {n : ℕ} (H : SimpleGraph (Fin (2 * n - 2))) [DecidableRel H.Adj]

theorem leaf_bound_of_not_contained
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hn : 3 ≤ n)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hT : T.IsTree) (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H) :
    ((graphLeaves T).card : ℝ) < (1 - (α : ℝ) / 4) * (n - 1 : ℕ) + 1 := by
  let q := n - 1
  let k : ℕ := ⌊α * (q : ℚ) / 4⌋₊
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg _
  have hk : (k : ℚ) ≤ α * (q : ℚ) / 4 := Nat.floor_le (by positivity)
  have haQ := mul_le_mul_of_nonneg_right hα1 hqQ
  have hkqQ : (k : ℚ) ≤ q := by nlinarith only [hk, haQ, hqQ]
  have hkq : k ≤ q := by exact_mod_cast hkqQ
  have h2k : 2 * (k : ℚ) ≤ α * q := by nlinarith only [hk, mul_nonneg hα.le hqQ]
  have hnum : 2 * (k : ℚ) * q ≤ α * q * q := mul_le_mul_of_nonneg_right h2k hqQ
  have hleafNat := card_graphLeaves_lt_sub_of_not_isContained (n := n) (k := k)
    (by omega) α H hlarge hnotEC1 hnum T hT
    (by omega) (by rw [hcard]) hnot
  rw [hcard] at hleafNat
  have hsub : n - (k + 1) = q - k := by dsimp only [q]; omega
  rw [hsub] at hleafNat
  have hleafR : ((graphLeaves T).card : ℝ) < ((q - k : ℕ) : ℝ) := by exact_mod_cast hleafNat
  rw [Nat.cast_sub hkq] at hleafR
  have hfloor : α * (q : ℚ) / 4 < (k : ℚ) + 1 := Nat.lt_floor_add_one _
  have hfloorQ : α * (q : ℚ) < 4 * ((k : ℚ) + 1) := by linarith only [hfloor]
  have hfloorR : (α : ℝ) * q < 4 * ((k : ℝ) + 1) := by exact_mod_cast hfloorQ
  nlinarith only [hleafR, hfloorR]

theorem exists_balancedSide_mass_of_notEC1
    (Z : Witness α (n - 1) M H) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (horder : orderThreshold α M ≤ n - 1)
    (hlarge : n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ H.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne α H)
    (hT : T.IsTree) (hcard : Fintype.card U = n) (hnot : ¬T.IsContained H)
    {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * Z.clusterSize) :
    ∃ s : Fin 2, (α : ℝ) / 32 * (n - 1 : ℕ) <
      (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ) := by
  have hn : 3 ≤ n := by
    have hh := Z.five_ordinaryParts_le_host
    have hp := Z.ordinaryParts_pos
    omega
  have hleaf := leaf_bound_of_not_contained H hα hα1 hn hlarge hnotEC1 hT hcard hnot
  have hroot := root_loss_margin Z hα hα1 (by omega) horder P.numParts hroots
  have hcard' : Fintype.card U = (n - 1) + 1 := by omega
  have ha : (0 : ℝ) < α := by exact_mod_cast hα
  have ha4Q : 4 * α ≤ 1 := by linarith only [hα1]
  have ha4 : (4 : ℝ) * (α : ℝ) ≤ 1 := by exact_mod_cast ha4Q
  have hmass := balanced_mass_gt_of_leaf_bound P hcard' ((α : ℝ) / 16)
    (by positivity) (by linarith only [ha4]) hroot (by nlinarith only [hleaf])
  obtain ⟨s, hs⟩ := exists_balancedSide_mass_gt P ((α : ℝ) / 16) hmass
  refine ⟨s, ?_⟩
  convert hs using 1
  ring

end Erdos547b.ZhaoSourceBalancedMassFromHost

#print axioms Erdos547b.ZhaoSourceBalancedMassFromHost.root_loss_margin
#print axioms Erdos547b.ZhaoSourceBalancedMassFromHost.leaf_bound_of_not_contained
#print axioms Erdos547b.ZhaoSourceBalancedMassFromHost.exists_balancedSide_mass_of_notEC1
