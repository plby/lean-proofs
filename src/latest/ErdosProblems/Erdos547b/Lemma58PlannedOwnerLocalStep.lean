/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CanonicalThresholdStep

/-!
# Plan-certified local owner steps

Besides constructing the local dynamic embedding, these source-data cases
certify that its branch-root and coordinate sides belong to the target plan
which was cleaned before any roots were chosen.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58PlannedOwnerLocalStep

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58CanonicalThresholdStep

universe v

/-- A realized local batch together with the side-plan facts needed by the
global synchronized invariant. -/
structure PlannedLocalRealization
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (live : Fin 2 → Finset B)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2)) where
  orient : Fin b → Fin 2 ≃ Fin 2
  embedding : Nonempty
    (DynamicAttachedForestEmbedding F G externalParent orient live)
  root_side_mem : ∀ i,
    branchRootSide F orient i ∈ rootAllowed i
  coordinate_side_mem : ∀ i a,
    orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) ∈
      coordinateAllowed ⟨i, a⟩

/-- The three source-faithful local cases, augmented only by membership in a
precomputed finite side plan.  No embedding or continuation is a field. -/
inductive PlannedOwnerLocalStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2)) :
    Type (max 0 v)
  | threshold
      (D : ActualThresholdStepData
        F G externalParent whole live rho density)
      (hroot : ∀ i,
        branchRootSide F
          (canonicalStepOrientation F G externalParent whole live rho density
            D) i ∈ rootAllowed i)
      (hcoordinate : ∀ i a,
        (canonicalStepOrientation F G externalParent whole live rho density D)
            i ((F.isTree i).coloringTwoOfVert (F.root i) a) ∈
          coordinateAllowed ⟨i, a⟩) :
      PlannedOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed
  | appendix
      (D : AppendixStepData F G externalParent whole live rho density)
      (hroot : ∀ i c, c ∈ rootAllowed i)
      (hcoordinate : ∀ i a c, c ∈ coordinateAllowed ⟨i, a⟩) :
      PlannedOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed
  | reindexedAppendix
      (D : ReindexedAppendixStepData F G externalParent whole live rho density)
      (hroot : ∀ i c, c ∈ rootAllowed i)
      (hcoordinate : ∀ i a c, c ∈ coordinateAllowed ⟨i, a⟩) :
      PlannedOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed
  | empty (D : EmptyStepData F) :
      PlannedOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed
  | fixed
      {orient : Fin b → Fin 2 ≃ Fin 2}
      (D : FixedOrientationStepData
        F G externalParent orient whole live rho density)
      (hroot : ∀ i, branchRootSide F orient i ∈ rootAllowed i)
      (hcoordinate : ∀ i a,
        orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) ∈
          coordinateAllowed ⟨i, a⟩) :
      PlannedOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed

/-- Forget the side-plan certificate while retaining the deterministic local
source datum. -/
noncomputable def PlannedOwnerLocalStepData.toOwnerLocalStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2))
    (D : PlannedOwnerLocalStepData F G externalParent whole live rho density
      rootAllowed coordinateAllowed) :
    OwnerLocalStepData F G externalParent whole live rho density := by
  cases D with
  | threshold D _ _ => exact OwnerLocalStepData.threshold D
  | appendix D _ _ => exact OwnerLocalStepData.appendix D
  | reindexedAppendix D _ _ => exact OwnerLocalStepData.reindexedAppendix D
  | empty D => exact OwnerLocalStepData.empty D
  | @fixed orient D _ _ => exact OwnerLocalStepData.fixed D

/-- The deterministic forgotten orientation respects the planned root
sides. -/
theorem PlannedOwnerLocalStepData.orientation_root_side_mem
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2))
    (D : PlannedOwnerLocalStepData F G externalParent whole live rho density
      rootAllowed coordinateAllowed) (i : Fin b) :
    branchRootSide F
        ((D.toOwnerLocalStepData F G externalParent whole live rho density
          rootAllowed coordinateAllowed).orientation F G externalParent whole
            live rho density) i ∈ rootAllowed i := by
  cases D with
  | threshold D hroot _ =>
      simpa only [toOwnerLocalStepData, OwnerLocalStepData.orientation,
        canonicalStepOrientation] using hroot i
  | appendix D hroot _ => exact hroot i _
  | reindexedAppendix D hroot _ => exact hroot i _
  | empty D =>
      exfalso
      have hi := i.isLt
      have hb := D.card_eq_zero
      omega
  | fixed D hroot _ => exact hroot i

/-- The deterministic forgotten orientation respects the planned coordinate
sides. -/
theorem PlannedOwnerLocalStepData.orientation_coordinate_side_mem
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2))
    (D : PlannedOwnerLocalStepData F G externalParent whole live rho density
      rootAllowed coordinateAllowed) (i : Fin b) (a : Fin (F.size i)) :
    (D.toOwnerLocalStepData F G externalParent whole live rho density
        rootAllowed coordinateAllowed).orientation F G externalParent whole
          live rho density i
        ((F.isTree i).coloringTwoOfVert (F.root i) a) ∈
      coordinateAllowed ⟨i, a⟩ := by
  cases D with
  | threshold D _ hcoordinate =>
      simpa only [toOwnerLocalStepData, OwnerLocalStepData.orientation,
        canonicalStepOrientation] using hcoordinate i a
  | appendix D _ hcoordinate => exact hcoordinate i a _
  | reindexedAppendix D _ hcoordinate => exact hcoordinate i a _
  | empty D =>
      exfalso
      have hi := i.isLt
      have hb := D.card_eq_zero
      omega
  | fixed D _ hcoordinate => exact hcoordinate i a

/-- Realize a plan-certified source datum. -/
theorem PlannedOwnerLocalStepData.realize
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ i, Fin (F.size i)) → Finset (Fin 2))
    (D : PlannedOwnerLocalStepData F G externalParent whole live rho density
      rootAllowed coordinateAllowed) :
    Nonempty (PlannedLocalRealization F G externalParent live rootAllowed
      coordinateAllowed) := by
  cases D with
  | threshold D hroot hcoordinate =>
      exact ⟨{
        orient := canonicalStepOrientation F G externalParent whole live rho
          density D
        embedding :=
          Erdos547b.ZhaoLemma58CanonicalThresholdStep.ActualThresholdStepData.realize_canonical
            F G externalParent whole live rho density D
        root_side_mem := hroot
        coordinate_side_mem := hcoordinate }⟩
  | appendix D hroot hcoordinate =>
      obtain ⟨orient, E⟩ := D.realize F G externalParent whole live rho density
      exact ⟨{
        orient := orient
        embedding := E
        root_side_mem := fun i ↦ hroot i _
        coordinate_side_mem := fun i a ↦ hcoordinate i a _ }⟩
  | reindexedAppendix D hroot hcoordinate =>
      obtain ⟨orient, E⟩ := D.realize F G externalParent whole live rho density
      exact ⟨{
        orient := orient
        embedding := E
        root_side_mem := fun i ↦ hroot i _
        coordinate_side_mem := fun i a ↦ hcoordinate i a _ }⟩
  | empty D =>
      exact ⟨{
        orient := D.orientation
        embedding := D.realize F G externalParent live
        root_side_mem := fun i ↦ False.elim (by
          have hi := i.isLt
          have hb := D.card_eq_zero
          omega)
        coordinate_side_mem := fun i ↦ False.elim (by
          have hi := i.isLt
          have hb := D.card_eq_zero
          omega) }⟩
  | fixed D hroot hcoordinate =>
      exact ⟨{
        orient := _
        embedding := D.realize F G externalParent _ whole live rho density
        root_side_mem := hroot
        coordinate_side_mem := hcoordinate }⟩

end Erdos547b.ZhaoLemma58PlannedOwnerLocalStep

#print axioms Erdos547b.ZhaoLemma58PlannedOwnerLocalStep.PlannedOwnerLocalStepData.realize
