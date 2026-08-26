/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGlobalBranchImage

/-!
# Global injectivity and root separation at the terminal prefix

The literal branch copies are injective within one family and occupy
disjoint matching supports across different families. Their images avoid
the two root reservoirs because all assigned edges avoid those clusters.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceGlobalPrefixState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceReservationFamilyState Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootSide : Fin r → Fin 2)
variable (all : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (A : PrefixState W Q S F owner rootSide all family r)

theorem PrefixState.terminalBranch_injective
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (all x.1 x.2) (all y.1 y.2)) :
    Function.Injective (fun x : Σ i : Fin b, Fin (F.size i) =>
      A.branchCopy W Q S F owner rootSide all family locate hcover x.1 (owner x.1).isLt x.2) := by
  rintro ⟨i, a⟩ ⟨j, d⟩ heq
  change A.branchCopy W Q S F owner rootSide all family locate hcover i (owner i).isLt a =
    A.branchCopy W Q S F owner rootSide all family locate hcover j (owner j).isLt d at heq
  by_cases hij : i = j
  · subst j
    have had : a = d := (A.branchCopy W Q S F owner rootSide all family locate hcover i (owner i).isLt).injective heq
    subst d
    rfl
  exfalso
  by_cases hloc : locate i = locate j
  · have hfst := congrArg Prod.fst hloc
    have hsnd := congrArg Prod.snd hloc
    change (locate i).1 = (locate j).1 at hfst
    change (locate i).2 = (locate j).2 at hsnd
    let E := (A.families (locate j).1 (locate j).2).currentPlacement W Q S
      (rootCluster W Q (locate j).1) F owner
    have hiMem : i ∈ (family (locate j).1 (locate j).2).toFinset.filter (fun i => (owner i).val < r) := by
      refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ?_, (owner i).isLt⟩
      simpa only [hfst, hsnd] using hcover i
    have hjMem : j ∈ (family (locate j).1 (locate j).2).toFinset.filter (fun i => (owner i).val < r) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover j), (owner j).isLt⟩
    have heq' : E.forestCopy.componentCopy i hiMem a = E.forestCopy.componentCopy j hjMem d := by
      let eval : {p : Fin 2 × Fin k // i ∈ (family p.1 p.2).toFinset.filter (fun i => (owner i).val < r)} →
          Fin hostN := fun p =>
        ((A.families p.1.1 p.1.2).currentPlacement W Q S
          (rootCluster W Q p.1.1) F owner).forestCopy.componentCopy i p.2 a
      have hindices : (⟨locate i, Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr (hcover i), (owner i).isLt⟩⟩ :
          {p : Fin 2 × Fin k // i ∈ (family p.1 p.2).toFinset.filter (fun i => (owner i).val < r)}) =
          ⟨locate j, hiMem⟩ := Subtype.ext hloc
      have hconvert := congrArg eval hindices
      exact hconvert.symm.trans heq
    exact Set.disjoint_left.mp (E.forestCopy.disjoint_ranges i hiMem j hjMem hij)
      ⟨a, rfl⟩ ⟨d, heq'.symm⟩
  · let e := A.branchEdge W Q S F owner rootSide all family locate hcover i (owner i).isLt
    let f := A.branchEdge W Q S F owner rootSide all family locate hcover j (owner j).isLt
    have he := A.branchEdge_mem W Q S F owner rootSide all family locate hcover i (owner i).isLt
    have hf := A.branchEdge_mem W Q S F owner rootSide all family locate hcover j (owner j).isLt
    have hef : e ≠ f := by
      intro h
      change A.branchEdge W Q S F owner rootSide all family locate hcover i (owner i).isLt =
        A.branchEdge W Q S F owner rootSide all family locate hcover j (owner j).isLt at h
      exact Finset.disjoint_left.mp (hdisjoint (locate i) (locate j) hloc) he (h.symm ▸ hf)
    have ha := (Finset.mem_sdiff.mp (A.branchCopy_side W Q S F owner rootSide all family locate hcover
      i (owner i).isLt a)).1
    have hd := (Finset.mem_sdiff.mp (A.branchCopy_side W Q S F owner rootSide all family locate hcover
      j (owner j).isLt d)).1
    exact Finset.disjoint_left.mp (edgeWhole_cross_disjoint W Q e f hef _ _) ha (heq.symm ▸ hd)

def PrefixState.terminalBranchEmbedding
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (all x.1 x.2) (all y.1 y.2)) :
    F.Embedding (embeddingHost W) where
  copy i := A.branchCopy W Q S F owner rootSide all family locate hcover i (owner i).isLt
  injective := A.terminalBranch_injective W Q S F owner rootSide all family locate hcover hdisjoint

omit S F owner rootSide all family locate hcover A in
theorem reservoir_disjoint_edgeWhole (s : Fin 2) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (c : Fin 2) :
    Disjoint (reservoir W Q s) (edgeWhole W Q e c) := by
  have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B) he c
  have hne : Sum.inl (rootCluster W Q s) ≠ edgeVertex W Q e c := by
    rcases rootCluster_cases W Q s with hA | hB
    · rw [hA]
      exact hn.1.symm
    · rw [hB]
      exact hn.2.symm
  have hd : Disjoint (clusterVertices (assignment W) (rootCluster W Q s)) (edgeWhole W Q e c) := by
    have h := clusterVertices_disjoint (padAssignment (assignment W)) hne
    simpa only [clusterVertices_padAssignment, padCluster, edgeWhole] using h
  exact hd.mono (reservoir_subset W Q s) (Finset.Subset.refl _)

theorem PrefixState.root_ne_branchCopy
    (haway : ∀ s j, all s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (u : Fin r) (i : Fin b) (a : Fin (F.size i)) :
    A.rootImage u ≠ A.branchCopy W Q S F owner rootSide all family locate hcover i (owner i).isLt a := by
  intro heq
  have hr := A.root_mem u u.isLt
  have hb := (Finset.mem_sdiff.mp (A.branchCopy_side W Q S F owner rootSide all family locate hcover
    i (owner i).isLt a)).1
  have he := haway (locate i).1 (locate i).2
    (A.branchEdge_mem W Q S F owner rootSide all family locate hcover i (owner i).isLt)
  exact Finset.disjoint_left.mp (reservoir_disjoint_edgeWhole W Q (rootSide u) _ he _) hr (heq.symm ▸ hb)

end Erdos547b.ZhaoSourceGlobalPrefixState

#print axioms Erdos547b.ZhaoSourceGlobalPrefixState.PrefixState.terminalBranchEmbedding
#print axioms Erdos547b.ZhaoSourceGlobalPrefixState.reservoir_disjoint_edgeWhole
#print axioms Erdos547b.ZhaoSourceGlobalPrefixState.PrefixState.root_ne_branchCopy
