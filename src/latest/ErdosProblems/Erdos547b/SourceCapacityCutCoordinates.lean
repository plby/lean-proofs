/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityBranchImage
import ErdosProblems.Erdos547b.SourceCutCoordinates

/-!
# Existing source cut coordinates in capacity-aware host prefixes

Reuse the source-only parent coordinates unchanged. Their actual images
have the necessary reservoir degree and remain fixed through a successor.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner coordinateSide coordinateColor CutSource)
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S F owner rootSide kinds allocation family stage)

def PrefixState.coordinateImage (x : CutCoordinate F r)
    (hx : (coordinateOwner F owner x).val < stage) : Fin hostN :=
  match x with
  | Sum.inl i => A.rootImage i
  | Sum.inr a => A.branchCopy W Q S F owner rootSide kinds allocation family locate hcover a.1 hx a.2

theorem PrefixState.coordinateImage_degree (x : CutCoordinate F r)
    (hx : (coordinateOwner F owner x).val < stage) (hcolor : coordinateColor F x) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q (coordinateSide F rootSide locate x)).filter ((embeddingHost W).Adj
        (A.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover x hx))) : ℝ) := by
  cases x with
  | inl i => exact A.root_degree i hx
  | inr a =>
      exact A.branch_rootColor_degree W Q S F owner rootSide kinds allocation family locate hcover a.1 hx a.2 hcolor

theorem PrefixState.coordinateImage_preserved
    (D : PrefixState W Q S F owner rootSide kinds allocation family (stage + 1))
    (hroots : ∀ i : Fin r, i.val < stage → D.rootImage i = A.rootImage i)
    (hcopies : ∀ s j i hi,
      ((D.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ stage) (family s j) hi) =
        ((A.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi)
    (x : CutCoordinate F r) (hx : (coordinateOwner F owner x).val < stage) :
    D.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover x (Nat.lt_succ_of_lt hx) =
      A.coordinateImage F owner W Q S rootSide kinds allocation family locate hcover x hx := by
  cases x with
  | inl i => exact hroots i hx
  | inr a =>
      exact congrArg (fun f : (F.tree a.1).Copy (embeddingHost W) => f a.2)
        (A.branchCopy_preserved W Q S F owner rootSide kinds allocation family locate hcover D hcopies a.1 hx)

end Erdos547b.ZhaoSourceCapacityGlobalPrefix

#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.coordinateImage_degree
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.coordinateImage_preserved
