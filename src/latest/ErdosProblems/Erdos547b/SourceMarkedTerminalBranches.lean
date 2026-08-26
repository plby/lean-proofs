/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedTerminalSeparation

/-!
# The terminal combined branch embedding

The four membership cases use the checked marked and ordinary separation
lemmas. Root separation follows from the actual cluster supports.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourcePrivateGroupSeparation
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoStability
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceGlobalPrefixState (reservoir_disjoint_edgeWhole)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family r)

theorem PrefixState.terminalBranch_injective (hCV1 : C ⊆ O.D.V1)
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2)) :
    Function.Injective (fun x : Σ i : Fin b, Fin (F.size i) =>
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover x.1 (owner x.1).isLt x.2) := by
  rintro ⟨i, a⟩ ⟨j, d⟩ heq
  change A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a =
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt d at heq
  by_cases hij : i = j
  · subst j
    have had := (A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt).injective heq
    subst d
    rfl
  exfalso
  by_cases hi : i ∈ selected
  · by_cases hj : j ∈ selected
    · exact A.marked_copies_ne W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i j hi hj hij a d heq
    · exact A.mixed_copies_ne W Q S O P F owner marks selected rootSide kinds allocation family locate hcover hCV1 hresidual i j hi hj a d heq
  · by_cases hj : j ∈ selected
    · exact A.mixed_copies_ne W Q S O P F owner marks selected rootSide kinds allocation family locate hcover hCV1 hresidual j i hj hi d a heq.symm
    · exact A.ordinary_copies_ne W Q S O P F owner marks selected rootSide kinds allocation family locate hcover hdisjoint i j hi hj hij a d heq

def PrefixState.terminalBranchEmbedding (hCV1 : C ⊆ O.D.V1)
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2)) :
    F.Embedding (embeddingHost W) where
  copy i := A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt
  injective := A.terminalBranch_injective W Q S O P F owner marks selected rootSide kinds allocation family locate hcover hCV1 hresidual hdisjoint

theorem PrefixState.root_ne_branchCopy (hCV1 : C ⊆ O.D.V1)
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (u : Fin r) (i : Fin b) (a : Fin (F.size i)) :
    A.ordinary.rootImage u ≠ A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a := by
  intro heq
  have hr := A.ordinary.root_mem u u.isLt
  by_cases hi : i ∈ selected
  · let himem : i ∈ ownerPrefix selected owner r := Finset.mem_filter.mpr ⟨hi, (owner i).isLt⟩
    let x := A.marked.group ⟨i, himem⟩
    have ha : A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a ∈
        P.support W Q S O x := by
      rw [A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt hi]
      exact A.marked_copy_mem_support W Q S O P F owner marks selected rootSide kinds allocation family i himem a
    exact Finset.disjoint_left.mp (reservoir_disjoint_group W Q S O P hCV1 (rootSide u) x) hr (heq.symm ▸ ha)
  · obtain ⟨e, he, c, ha⟩ := A.ordinary_branch_support W Q S F owner O P marks selected rootSide kinds allocation family locate hcover
      i hi (owner i).isLt a
    exact Finset.disjoint_left.mp (reservoir_disjoint_edgeWhole W Q (rootSide u) e (haway _ _ he) c) hr (heq.symm ▸ ha)

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.terminalBranchEmbedding
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.root_ne_branchCopy
