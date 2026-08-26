/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyAllocationAdvance
import ErdosProblems.Erdos547b.SourceCapacityFamilyPacking

/-!
# Full actual family successor from the concrete source capacity budget

The source ledger constructs the current packing. All graph copies and
the new active reservation are then constructed, including empty current
fibers and terminal reservations. No future-root realization is assumed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyBudgetAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceCapacityFamilyAllocationAdvance Erdos547b.ZhaoSourceCapacityFamilyPacking
open Erdos547b.ZhaoSourceCapacityOwnerAdvance Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

theorem exists_familyAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
    (hbranch : ∀ i ∈ family, kind.BranchValid F i)
    (hedge : ∀ e ∈ all, edgeValid W Q S C kind e)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : all ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : FamilyState W Q S C F owner kind all family rootImage n.val)
    (globalCount : ℕ)
    (hbudget : family ≠ [] → mass (fun i => (F.size i : ℝ)) family ≤
      (∑ e ∈ all, capacity W Q S C kind e) -
        (freshBranchBound α W.clusterSize : ℝ) * all.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (z : Fin hostN)
    (hactive : requirementGood W Q S C (activeRequirement W Q S C F owner kind A.active) z)
    (bad : Finset (MatchingEdge Q.claim67.M))
    (hbad : bad ⊆ A.unusedEdges W Q S C F owner kind)
    (hcount : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount)
    (hgood : ∀ e ∈ A.unusedEdges W Q S C F owner kind \ bad,
      requirementGood W Q S C (initialRequirement W Q kind e) z) :
    ∃ D : FamilyState W Q S C F owner kind all family (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, (D.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i hi := by
  have heligible : ∀ x, A.active = some x → (∃ i ∈ x.source.items, owner i = n) →
      requirementGood W Q S C (x.source.requirement W Q S C F owner kind x.copyPrefix) z := by
    intro x hx _
    simpa only [hx, activeRequirement] using hactive
  by_cases hcurrent : ∃ i ∈ A.remaining, owner i = n
  · have hfamily : family ≠ [] := by
      intro hnil
      obtain ⟨i, hi, _⟩ := hcurrent
      have hm : i ∈ family := A.flatten ▸ List.mem_append_right _ hi
      rw [hnil] at hm
      exact List.not_mem_nil hm
    obtain ⟨R, ⟨P⟩⟩ := exists_currentOwnerPacking W Q S C kind F owner hα hC hkind hedge hsmall
      rootImage n A hcurrent globalCount (hbudget hfamily) bad hbad hcount
    let bins := capacityBins W Q S C kind all (A.reservedEdges W Q S C F owner kind) bad
    have hbin (e : MatchingEdge Q.claim67.M) (he : e ∈ bins) :
        e ∈ A.unusedEdges W Q S C F owner kind \ bad ∧
          (freshBranchBound α W.clusterSize : ℝ) < capacity W Q S C kind e :=
      (mem_capacityBins W Q S C kind all (A.reservedEdges W Q S C F owner kind) bad e).mp he
    apply exists_familyAdvance_withPacking W Q S C F owner kind rootImage n A
      hα hα1 hhost horder hC hkind z hcurrent heligible R bins P hbranch hsmall
    · intro e he
      exact (Finset.mem_sdiff.mp (hbin e (List.mem_toFinset.mp he)).1).1
    · intro e he
      exact haway (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hbin e he).1).1).1
    · intro e he
      exact hedge e (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hbin e he).1).1).1
    · exact fun e he => (hbin e he).2
    · exact fun e he => hgood e (hbin e he).1
  · obtain ⟨D, _, _, _, _, _, hcopies⟩ := exists_familyAdvance_noAllocation W Q S C F owner kind
      hα hα1 hhost horder hkind rootImage n A z (fun i hi he => hcurrent ⟨i, hi, he⟩) heligible
    exact ⟨D, hcopies⟩

end Erdos547b.ZhaoSourceCapacityFamilyBudgetAdvance

#print axioms Erdos547b.ZhaoSourceCapacityFamilyBudgetAdvance.exists_familyAdvance
