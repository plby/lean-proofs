/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingBranchImage
import ErdosProblems.Erdos547b.SourceCutCoordinates

/-!
# Source-only cut coordinates and their actual host images

A cut parent is either an earlier component root or an original branch
vertex of rooted colour zero. Source side compatibility gives its actual
reservoir degree, and prefix preservation keeps the same host image.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoSourceFamilyOwnerAdvance
open Erdos547b.ZhaoSourceMatchingFamilyState
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule

variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner coordinateSide coordinateColor CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)
variable (rootSide : Fin r → Fin 2)
variable (all : Fin 2 → Fin k → Finset (MatchingEdge P))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (avoid : Fin 2 → Finset (Fin hostN))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S P F owner rootSide all family avoid stage)

def PrefixState.coordinateImage (x : CutCoordinate F r)
    (hx : (coordinateOwner F owner x).val < stage) : Fin hostN :=
  match x with
  | Sum.inl i => A.rootImage i
  | Sum.inr a => A.branchCopy W Q S P F owner rootSide all family avoid locate hcover a.1 hx a.2

theorem PrefixState.coordinateImage_degree (x : CutCoordinate F r)
    (hx : (coordinateOwner F owner x).val < stage) (hcolor : coordinateColor F x) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q (coordinateSide F rootSide locate x)).filter ((embeddingHost W).Adj
        (A.coordinateImage F owner W Q S P rootSide all family avoid locate hcover x hx))) : ℝ) := by
  cases x with
  | inl i => exact A.root_degree i hx
  | inr a =>
    exact A.branch_rootColor_degree W Q S P F owner rootSide all family avoid locate hcover a.1 hx a.2 hcolor

theorem PrefixState.coordinateImage_preserved
    (D : PrefixState W Q S P F owner rootSide all family avoid (stage + 1))
    (hroots : ∀ i : Fin r, i.val < stage → D.rootImage i = A.rootImage i)
    (hcopies : ∀ s j i hi,
      ((D.families s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ stage) (family s j) hi) =
        ((A.families s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i hi)
    (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < stage) :
    D.coordinateImage F owner W Q S P rootSide all family avoid locate hcover x (Nat.lt_succ_of_lt hx) =
      A.coordinateImage F owner W Q S P rootSide all family avoid locate hcover x hx := by
  cases x with
  | inl i => exact hroots i hx
  | inr a =>
    exact congrArg (fun f : (F.tree a.1).Copy (embeddingHost W) => f a.2)
      (A.branchCopy_preserved W Q S P F owner rootSide all family avoid locate hcover D hcopies a.1 hx)

end Erdos547b.ZhaoSourceMatchingGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.PrefixState.coordinateImage_degree
#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.PrefixState.coordinateImage_preserved
