/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityCutCoordinates

/-!
# Capacity-aware cut-prefix induction through every source root

The next parent is the actual image of its earlier source coordinate.
The successor constructs its cut edge and preserves all previous edges.
Finite induction produces a terminal state from source-only data and the
concrete family budgets, with no future graph-realization callback.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (L : CutSource F owner rootSide locate)

structure CutPrefixState (stage : ℕ) where
  state : PrefixState W Q S F owner rootSide kinds allocation family stage
  cut_adj : ∀ i (hi : i.val ≠ 0) (hstage : i.val < stage),
    (embeddingHost W).Adj
      (state.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover (L.parent i hi)
        ((L.before i hi).trans hstage))
      (state.rootImage i)

def emptyCutPrefixState
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    CutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L 0 where
  state := emptyPrefixState W Q S F owner rootSide kinds allocation family hnd hordered (fun _ => S.zA)
  cut_adj := by omega

variable (hα : 0 < α) (hα1 : α ≤ 1 / 4)
variable (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
variable (hkind : ∀ s j, (kinds s j).Valid α)
variable (hdisjoint : ∀ s, Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)))
variable (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
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
variable (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)

include hα hα1 hhost horder hk hkind hdisjoint hside hbranch hedge hsmall haway globalCount hglobal hbudget hroots

theorem exists_cutPrefixAdvance (n : Fin r)
    (A : CutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L n.val) :
    Nonempty (CutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L (n.val + 1)) := by
  let poolParent : Option (Fin hostN) := if hn : n.val = 0 then none else
    some (A.state.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover
      (L.parent n hn) (L.before n hn))
  have hparent : ∀ v, poolParent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)) : ℝ) := by
    intro v hv
    by_cases hn : n.val = 0
    · simp only [poolParent, dif_pos hn] at hv
      cases hv
    · have heq := Option.some.inj (show some
          (A.state.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover
            (L.parent n hn) (L.before n hn)) = some v from by
          simpa only [poolParent, dif_neg hn] using hv)
      have hd := A.state.coordinateImage_degree F owner W Q S rootSide kinds allocation family locate hcover
        (L.parent n hn) (L.before n hn) (L.color n hn)
      rw [L.side n hn, heq] at hd
      exact hd
  obtain ⟨z, D, hroot, hAdj, hcopies⟩ := exists_prefixAdvance W Q S F owner rootSide kinds allocation family
    hα hα1 hhost horder hk hkind hdisjoint hside n A.state hbranch hedge hsmall haway
    globalCount hglobal hbudget hroots poolParent hparent
  have hbefore (i : Fin r) (hi : i.val < n.val) : D.rootImage i = A.state.rootImage i := by
    rw [hroot]
    exact Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.state.rootImage
  have hcoord (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < n.val) :
      D.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover x (Nat.lt_succ_of_lt hx) =
        A.state.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover x hx :=
    A.state.coordinateImage_preserved F owner W Q S rootSide kinds allocation family locate hcover D hbefore hcopies x hx
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
    Nonempty (CutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L r) := by
  have hstates : ∀ n : ℕ, n ≤ r →
      Nonempty (CutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L n) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨emptyCutPrefixState W Q S F owner rootSide kinds allocation family locate hcover L hnd hordered⟩
    | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        obtain ⟨A⟩ := ih (Nat.le_of_lt hnr)
        exact exists_cutPrefixAdvance W Q S F owner rootSide kinds allocation family locate hcover L
          hα hα1 hhost horder hk hkind hdisjoint hside hbranch hedge hsmall haway
          globalCount hglobal hbudget hroots ⟨n, hnr⟩ A
  exact hstates r le_rfl

end Erdos547b.ZhaoSourceCapacityGlobalPrefix

#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.emptyCutPrefixState
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.exists_cutPrefixAdvance
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.exists_terminalCutPrefix
