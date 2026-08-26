/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceSelection

/-!
# The Claim 6.8 mass bound as a Lemma 6.15 source selector

This file records the definitional identification between the nontrivial
major-branch mass used in Lemma 6.15 and the canonical Claim 6.8 mass.  It
then packages the already proved real Claim 6.8 lower bound as the finite
first-threshold selector needed in the nonextreme case of Lemma 6.15.

There is no host graph or embedding conclusion in this module.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615SourceMass

open Finset SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The source family called `F̃_a` in Lemma 6.15 is literally the
nontrivial-half mass occurring in the branch form of Claim 6.8. -/
@[simp] theorem branchMass_nontrivialMajorBranches
    (P : ZhaoForestPartition T globalRoot small) :
    branchMass P (nontrivialMajorBranches P) = nontrivialHalfMass P := by
  rfl

/-- Claim 6.8 supplies the source selector required by the nonextreme case of
Lemma 6.15 whenever the desired threshold lies below Zhao's displayed real
lower bound. -/
theorem exists_nontrivialSelectedF0_of_claim6_8
    (P : ZhaoForestPartition T globalRoot small)
    (d : ℝ) (hd : 0 ≤ d) (n target slack : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n)
    (htarget : (target : ℝ) < (n : ℝ) / 2 - 12 * Real.sqrt d * n)
    (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack) :
    Nonempty (SelectedF0 P (nontrivialMajorBranches P) target slack) := by
  have hmassReal : (target : ℝ) < (nontrivialHalfMass P : ℝ) :=
    htarget.trans (claim6_8_nontrivialHalfMass_lower P d hd n hcardT
      horiginalLeaves hhierarchyF hhierarchyA)
  have hmass : target ≤ branchMass P (nontrivialMajorBranches P) := by
    rw [branchMass_nontrivialMajorBranches]
    exact_mod_cast hmassReal.le
  exact exists_nontrivialSelectedF0 P target slack hslack hsmall hmass

end Erdos547b.ZhaoClaim615SourceMass

#print axioms Erdos547b.ZhaoClaim615SourceMass.branchMass_nontrivialMajorBranches
#print axioms Erdos547b.ZhaoClaim615SourceMass.exists_nontrivialSelectedF0_of_claim6_8
