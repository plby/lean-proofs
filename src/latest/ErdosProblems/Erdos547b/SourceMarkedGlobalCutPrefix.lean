/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedCutCoordinates

/-!
# Finite cut-prefix induction with actual ordinary and marked branch images

The source cut parents are earlier coordinates. Selected-branch parents are
required to be prescribed marks, while ordinary parents use rooted colour.
Each step constructs the new cut edge and preserves every previous edge.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceMarkedOwnerAdvance
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner CutSource)

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
variable (L : CutSource F owner rootSide locate)

structure CutPrefixState (stage : ℕ) where
  state : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family stage
  cut_adj : ∀ i (hi : i.val ≠ 0) (hstage : i.val < stage),
    (embeddingHost W).Adj
      (state.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover
        (L.parent i hi) ((L.before i hi).trans hstage))
      (state.ordinary.rootImage i)

def emptyCutPrefixState
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    CutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L 0 where
  state := emptyPrefixState W Q S O P F owner marks selected rootSide kinds allocation family hnd hordered
  cut_adj := by omega

variable (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
variable (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hC : 0 < C.card)
variable (hkind : ∀ s j, (kinds s j).Valid α)
variable (hdisjoint : ∀ s, Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)))
variable (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
variable (hselectedSide : ∀ i ∈ selected, rootSide (owner i) = 0)
variable (hselectedLocate : ∀ i ∈ selected, (locate i).1 = 0)
variable (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid F i)
variable (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
variable (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
variable (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
variable (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
variable (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.size i : ℝ)) (family s j) ≤
  (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
    (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
    4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
variable (hselectedSize : ∀ i ∈ selected, 3 ≤ F.size i)
variable (hmarks : (∑ i ∈ selected, ((marks i).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
variable (hselectedMass : (∑ i ∈ selected, (F.size i : ℝ)) ≤
  (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
variable (hcolor : ∀ i ∈ selected, ∀ a ∈ marks i, (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
variable (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
variable (hparentMarked : ∀ i hi, coordinateMarked F marks selected (L.parent i hi))

include hα hα1 hhost horder hk hCV1 hC hkind hdisjoint hside hselectedSide hselectedLocate
  hbranch hedge hsmall haway globalCount hglobal hbudget hselectedSize hmarks hselectedMass hcolor hroots hparentMarked

theorem exists_cutPrefixAdvance (n : Fin r)
    (A : CutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L n.val) :
    Nonempty (CutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L (n.val + 1)) := by
  let poolParent : Option (Fin hostN) := if hn : n.val = 0 then none else
    some (A.state.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover
      (L.parent n hn) (L.before n hn))
  have hparent : ∀ v, poolParent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)).card := by
    intro v hv
    by_cases hn : n.val = 0
    · simp only [poolParent, dif_pos hn] at hv
      cases hv
    · have heq := Option.some.inj (show some
          (A.state.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover
            (L.parent n hn) (L.before n hn)) = some v from by
          simpa only [poolParent, dif_neg hn] using hv)
      have hd := A.state.coordinateImage_degree F owner marks selected W Q S O P rootSide kinds allocation family locate hcover
        hselectedLocate (L.parent n hn) (L.before n hn) (L.color n hn) (hparentMarked n hn)
      rw [L.side n hn, heq] at hd
      exact hd
  obtain ⟨z, D, hroot, hAdj, hcopies, hmarkedCopies, _⟩ := exists_prefixAdvance W Q S O P F owner marks selected
    rootSide kinds allocation family hα hα1 hhost horder hk hCV1 hC hkind hdisjoint hside hselectedSide
    n A.state hbranch hedge hsmall haway globalCount hglobal hbudget hselectedSize hmarks hselectedMass hcolor hroots
    poolParent hparent
  have hbefore (i : Fin r) (hi : i.val < n.val) : D.ordinary.rootImage i = A.state.ordinary.rootImage i := by
    rw [hroot]
    exact Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.state.ordinary.rootImage
  have hcoord (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < n.val) :
      D.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover x
          (Nat.lt_succ_of_lt hx) =
        A.state.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover x hx :=
    A.state.coordinateImage_preserved F owner marks selected W Q S O P rootSide kinds allocation family locate hcover
      D hbefore hcopies hmarkedCopies x hx
  refine ⟨⟨D, ?_⟩⟩
  intro i hi histage
  by_cases hin : i = n
  · subst i
    rw [hcoord (L.parent n hi) (L.before n hi), hroot, Function.update_self]
    apply hAdj
    simp only [poolParent, dif_neg hi]
  · have hv : i.val ≠ n.val := fun h => hin (Fin.ext h)
    have hib : i.val < n.val := by omega
    rw [hcoord (L.parent i hi) ((L.before i hi).trans hib), hbefore i hib]
    exact A.cut_adj i hi hib

theorem exists_terminalCutPrefix
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    Nonempty (CutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L r) := by
  have hstates : ∀ n : ℕ, n ≤ r →
      Nonempty (CutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L n) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨emptyCutPrefixState W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L hnd hordered⟩
    | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        obtain ⟨A⟩ := ih (Nat.le_of_lt hnr)
        exact exists_cutPrefixAdvance W Q S O P F owner marks selected rootSide kinds allocation family locate hcover L
          hα hα1 hhost horder hk hCV1 hC hkind hdisjoint hside hselectedSide hselectedLocate
          hbranch hedge hsmall haway globalCount hglobal hbudget hselectedSize hmarks hselectedMass hcolor hroots
          hparentMarked ⟨n, hnr⟩ A
  exact hstates r le_rfl

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.emptyCutPrefixState
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.exists_cutPrefixAdvance
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.exists_terminalCutPrefix
