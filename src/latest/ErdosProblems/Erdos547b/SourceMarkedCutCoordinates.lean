/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedBranchImage
import ErdosProblems.Erdos547b.SourceCutCoordinates

/-!
# Cut-coordinate images in the combined ordinary/marked prefix

Selected-branch parents must be actual prescribed marks. Root and ordinary
branch parents use the existing stronger reservoir-degree guarantees.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedOwnerAdvance
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner coordinateSide coordinateColor CutSource)
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))

def coordinateMarked (x : CutCoordinate F r) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr a => a.1 ∈ selected → a.2 ∈ marks a.1

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family stage)

def PrefixState.coordinateImage (x : CutCoordinate F r)
    (hx : (coordinateOwner F owner x).val < stage) : Fin hostN :=
  match x with
  | Sum.inl i => A.ordinary.rootImage i
  | Sum.inr a => A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover a.1 hx a.2

theorem PrefixState.coordinateImage_degree
    (hselectedLocate : ∀ i ∈ selected, (locate i).1 = 0)
    (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < stage)
    (hcolor : coordinateColor F x) (hmark : coordinateMarked F marks selected x) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      ((reservoir W Q (coordinateSide F rootSide locate x)).filter ((embeddingHost W).Adj
        (A.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover x hx))).card := by
  cases x with
  | inl i => exact A.ordinary.root_degree i hx
  | inr a =>
      exact A.branchCopy_degree W Q S O P F owner marks selected rootSide kinds allocation family locate hcover
        hselectedLocate a.1 hx a.2 hcolor hmark

theorem PrefixState.coordinateImage_preserved
    (D : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family (stage + 1))
    (hroots : ∀ i : Fin r, i.val < stage → D.ordinary.rootImage i = A.ordinary.rootImage i)
    (hcopies : ∀ s j i hi,
      ((D.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ stage) (family s j) hi) =
        ((A.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi)
    (hmarked : ∀ i (hi : i ∈ ownerPrefix selected owner stage), D.marked.forestCopy.componentCopy i
      (ownerPrefix_mono selected owner (Nat.le_succ stage) hi) = A.marked.forestCopy.componentCopy i hi)
    (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < stage) :
    D.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover x (Nat.lt_succ_of_lt hx) =
      A.coordinateImage F owner marks selected W Q S O P rootSide kinds allocation family locate hcover x hx := by
  cases x with
  | inl i => exact hroots i hx
  | inr a =>
      exact congrArg (fun f : (F.tree a.1).Copy (embeddingHost W) => f a.2)
        (A.branchCopy_preserved W Q S O P F owner marks selected rootSide kinds allocation family locate hcover
          D hcopies hmarked a.1 hx)

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.coordinateImage_degree
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.coordinateImage_preserved
