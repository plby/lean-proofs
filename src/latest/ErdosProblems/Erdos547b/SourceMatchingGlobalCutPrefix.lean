/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingCutCoordinates

/-!
# Cut-aware global prefix induction

Every cut parent is evaluated at its already constructed source coordinate.
The actual successor obtains the new cut edge and preserves all previous
ones by root and branch image equalities. Finite induction gives a terminal
cut-aware state from source-only finite data and scalar capacity bounds.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoSourceFamilyOwnerAdvance
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceGlobalPrefixState (CutSource CutCoordinate coordinateOwner)
open Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootSide : Fin r → Fin 2)
variable (all : Fin 2 → Fin k → Finset (MatchingEdge P))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (avoid : Fin 2 → Finset (Fin hostN))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (L : CutSource F owner rootSide locate)

structure CutPrefixState (stage : ℕ) where
  state : PrefixState W Q S P F owner rootSide all family avoid stage
  cut_adj : ∀ i (hi : i.val ≠ 0) (hstage : i.val < stage),
    (embeddingHost W).Adj
      (state.coordinateImage F owner W Q S P rootSide all family avoid locate hcover (L.parent i hi)
        ((L.before i hi).trans hstage))
      (state.rootImage i)

def emptyCutPrefixState (hP : P.IsMatching)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    CutPrefixState W Q S P F owner rootSide all family avoid locate hcover L 0 where
  state := emptyPrefixState W Q S P F owner rootSide all family avoid hP hnd hordered (fun _ => S.zA)
  cut_adj := by omega

variable (hα : 0 < α) (hα1 : α ≤ 1 / 4)
variable (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
variable (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
variable (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
variable (haway : ∀ s j, all s j ⊆ edgesAwayFromDistinguished P
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
variable (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (all s)).card ≤ globalCount)
variable (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.size i : ℝ)) (family s j) ≤
  (∑ e ∈ all s j, capacity W Q P S (rootCluster W Q s) e) -
    (freshBranchBound α W.clusterSize : ℝ) * (all s j).card -
    4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
variable (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
variable (havoid : ∀ s, ((avoid s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize)

include hα hα1 hhost horder hk hside hsmall haway globalCount hglobal hbudget hroots havoid

/-- Advance the cut-aware state using only the earlier actual parent image.
Every old cut adjacency is preserved, not assumed again for the new state. -/
theorem exists_cutPrefixAdvance (n : Fin r)
    (A : CutPrefixState W Q S P F owner rootSide all family avoid locate hcover L n.val) :
    Nonempty (CutPrefixState W Q S P F owner rootSide all family avoid locate hcover L (n.val + 1)) := by
  let poolParent : Option (Fin hostN) := if hn : n.val = 0 then none else
    some (A.state.coordinateImage F owner W Q S P rootSide all family avoid locate hcover
      (L.parent n hn) (L.before n hn))
  have hparent : ∀ v, poolParent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)) : ℝ) := by
    intro v hv
    by_cases hn : n.val = 0
    · simp only [poolParent, dif_pos hn] at hv
      cases hv
    · have heq := Option.some.inj (show some
          (A.state.coordinateImage F owner W Q S P rootSide all family avoid locate hcover
            (L.parent n hn) (L.before n hn)) = some v from by
          simpa only [poolParent, dif_neg hn] using hv)
      have hd := A.state.coordinateImage_degree F owner W Q S P rootSide all family avoid locate hcover
        (L.parent n hn) (L.before n hn) (L.color n hn)
      rw [L.side n hn, heq] at hd
      exact hd
  obtain ⟨z, D, hroot, hAdj, hcopies⟩ := exists_prefixAdvance W Q S P F owner rootSide all family avoid
    hα hα1 hhost horder hk hside n A.state hsmall haway globalCount hglobal hbudget hroots havoid
    poolParent hparent
  have hbefore (i : Fin r) (hi : i.val < n.val) : D.rootImage i = A.state.rootImage i := by
    rw [hroot]
    exact Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.state.rootImage
  have hcoord (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < n.val) :
      D.coordinateImage F owner W Q S P rootSide all family avoid locate hcover x (Nat.lt_succ_of_lt hx) =
        A.state.coordinateImage F owner W Q S P rootSide all family avoid locate hcover x hx :=
    A.state.coordinateImage_preserved F owner W Q S P rootSide all family avoid locate hcover D hbefore hcopies x hx
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

/-- Actual finite induction through every root. The only hypotheses are
finite source layout/parent data and the verified source-scale budgets. -/
theorem exists_terminalCutPrefix (hP : P.IsMatching)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    Nonempty (CutPrefixState W Q S P F owner rootSide all family avoid locate hcover L r) := by
  have hstates : ∀ n : ℕ, n ≤ r →
      Nonempty (CutPrefixState W Q S P F owner rootSide all family avoid locate hcover L n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨emptyCutPrefixState W Q S P F owner rootSide all family avoid locate hcover L hP hnd hordered⟩
    | succ n ih =>
      intro hn
      have hnr : n < r := by omega
      obtain ⟨A⟩ := ih (Nat.le_of_lt hnr)
      exact exists_cutPrefixAdvance W Q S P F owner rootSide all family avoid locate hcover L
        hα hα1 hhost horder hk hside hsmall haway globalCount hglobal hbudget hroots havoid ⟨n, hnr⟩ A
  exact hstates r le_rfl

end Erdos547b.ZhaoSourceMatchingGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.emptyCutPrefixState
#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.exists_cutPrefixAdvance
#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.exists_terminalCutPrefix
