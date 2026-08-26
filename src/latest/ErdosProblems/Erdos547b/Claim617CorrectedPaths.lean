/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617CleanLoss

/-! Corrected component-rooted source package for Zhao Claim 6.17. -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617CorrectedPaths

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617RootPaths
open Erdos547b.ZhaoClaim617CutRootPaths
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim617CleanLoss

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

structure CorrectedPathPackage (T : SimpleGraph V) (q : ℕ) where
  family : PendantRootTwoPathFamily T
  enough : q ≤ family.middles.card
  coreRoot : {x // x ∉ (family.select enough).middleSet}
  coreTree : (family.select enough).core.IsTree

noncomputable def corrected_package_of_branch_masses
    (hT : T.IsTree)
    (P : ZhaoForestPartition T globalRoot small)
    (lower bad parentBound q : ℕ)
    (hclaim68 : lower ≤ nontrivialHalfMass P)
    (hclaim616 : largeHalfMass P ≤ bad)
    (hparents : (partitionParents P).card ≤ parentBound)
    (hhierarchy : bad + 2 * (q + parentBound) ≤ lower) :
    CorrectedPathPackage T q := by
  let hq : q ≤ (middles P).card :=
    pathCount_le_of_branch_masses P lower bad parentBound q hclaim68
      hclaim616 hparents
      (sizeTwoBranches_card_le_middles_add_parents P) hhierarchy
  exact
    { family := pendantFamily P
      enough := hq
      coreRoot := selectedCoreRoot P hT hq
      coreTree := selectedCore_isTree P hT hq }

/-- Source-faithful specialization: Claim 6.8 supplies the whole major-half
mass, Claim 6.16 controls the large branches, and the clean-loss injection
constructs the reserved component-rooted two-paths. -/
noncomputable def corrected_package_of_claim68_claim616
    (hT : T.IsTree)
    (P : ZhaoForestPartition T globalRoot small)
    (d : ℝ) (hd : 0 ≤ d) (n lower bad parentBound q : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n)
    (hlower : (lower : ℝ) ≤
      (n : ℝ) / 2 - 12 * Real.sqrt d * n)
    (hclaim616 : largeHalfMass P ≤ bad)
    (hparents : (partitionParents P).card ≤ parentBound)
    (hhierarchy : bad + 2 * (q + parentBound) ≤ lower) :
    CorrectedPathPackage T q := by
  have hmassReal : (lower : ℝ) < (nontrivialHalfMass P : ℝ) :=
    lt_of_le_of_lt hlower
      (claim6_8_nontrivialHalfMass_lower P d hd n hcardT
        horiginalLeaves hhierarchyF hhierarchyA)
  have hmass : lower ≤ nontrivialHalfMass P := by
    have : lower < nontrivialHalfMass P := by exact_mod_cast hmassReal
    omega
  exact corrected_package_of_branch_masses hT P lower bad parentBound q
    hmass hclaim616 hparents hhierarchy

theorem corrected_path_count
    (P : ZhaoForestPartition T globalRoot small)
    (lower bad parentBound q : ℕ)
    (hclaim68 : lower ≤ nontrivialHalfMass P)
    (hclaim616 : largeHalfMass P ≤ bad)
    (hparents : (partitionParents P).card ≤ parentBound)
    (hhierarchy : bad + 2 * (q + parentBound) ≤ lower) :
    q ≤ (middles P).card :=
  pathCount_le_of_branch_masses P lower bad parentBound q hclaim68
    hclaim616 hparents
    (sizeTwoBranches_card_le_middles_add_parents P) hhierarchy

end Erdos547b.ZhaoClaim617CorrectedPaths

#print axioms Erdos547b.ZhaoClaim617CorrectedPaths.corrected_package_of_branch_masses
