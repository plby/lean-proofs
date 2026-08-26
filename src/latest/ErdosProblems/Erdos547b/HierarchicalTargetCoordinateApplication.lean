/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetUnifiedApplication
import ErdosProblems.Erdos547b.HierarchicalTargetCoordinateCleaning

/-!
# One-shot target-relative realization with endpoint-side occupancy

This is the cut-aware, side-sensitive graph endpoint for the concrete
Claim-6.16 layout.  It chooses the global original root, performs the same
target-relative cleaning as the unified backend, and realizes the complete
hierarchy using exact coordinate-side loads plus one small-component carry.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateApplication

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinateRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateCleaning
open Erdos547b.ZhaoHierarchicalRootReservoir
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateCleaning.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {s : ℕ} {B : Type u}

/-- Coordinate-sensitive counterpart of
`exists_targetUnifiedHierarchyEmbedding`. -/
theorem exists_targetCoordinateHierarchyEmbedding
    {RootSlot Pool : Type*} [DecidableEq Pool]
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho density : ℝ) (small : ℕ)
    (sourceWhole sourceRaw : Finset B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B)
    (poolCapacity : Pool → ℕ)
    (removalBudget : ℝ)
    (hsegmentSmall : ∀ i, F.segments.size i ≤ small)
    (hsourceSubset : sourceRaw ⊆ sourceWhole)
    (hsourceLarge : rho * #sourceWhole ≤ #sourceRaw)
    (hrootRawSubset : ∀ i,
      rootRaw (rootSlot i) ⊆ rootWhole (rootSlot i))
    (hinteriorRawSubset : ∀ i a,
      rootRaw (interiorSlot i a) ⊆ rootWhole (interiorSlot i a))
    (hrootRawLarge : ∀ i,
      rho * #(rootWhole (rootSlot i)) ≤ #(rootRaw (rootSlot i)))
    (hinteriorRawLarge : ∀ i a,
      rho * #(rootWhole (interiorSlot i a)) ≤
        #(rootRaw (interiorSlot i a)))
    (hdirectUniform : ∀ i, F.parent i = Sum.inl 0 →
      G.IsUniform rho sourceWhole (rootWhole (rootSlot i)))
    (hdirectDensity : ∀ i, F.parent i = Sum.inl 0 →
      density ≤ G.edgeDensity sourceWhole (rootWhole (rootSlot i)))
    (hattachUniform : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) j a)
        (rootWhole (rootSlot i)))
    (hattachDensity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      density ≤ G.edgeDensity
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) j a)
        (rootWhole (rootSlot i)))
    (hinternalUniform : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) i a)
        (rootWhole (interiorSlot i b)))
    (hinternalDensity : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      density ≤ G.edgeDensity
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) i a)
        (rootWhole (interiorSlot i b)))
    (hpoolLoad : ∀ p,
      coordinatePoolLoad F (fun i ↦ slotPool (rootSlot i))
          (fun i a ↦ slotPool (interiorSlot i a)) p ≤ poolCapacity p)
    (hremoval : ∀ i a,
      coordinateRemovalBudget F rho rootSlot rootWhole
          (fun i a ↦ rootWhole (interiorSlot i a)) i a ≤ removalBudget)
    (hrootCapacity : ∀ i,
      (poolCapacity (slotPool (rootSlot i)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) * #(rootRaw (rootSlot i)))
    (hinteriorCapacity : ∀ i a,
      (poolCapacity (slotPool (interiorSlot i a)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) * #(rootRaw (interiorSlot i a)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
          (rho * #sourceWhole) < #sourceRaw)
    (hrootRawDisjoint : ∀ i j,
      slotPool (rootSlot i) ≠ slotPool (rootSlot j) →
      Disjoint (rootRaw (rootSlot i)) (rootRaw (rootSlot j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      slotPool (interiorSlot i a) ≠ slotPool (interiorSlot j b) →
      Disjoint (rootRaw (interiorSlot i a))
        (rootRaw (interiorSlot j b)))
    (hrootInteriorRawDisjoint : ∀ i j a,
      slotPool (rootSlot i) ≠ slotPool (interiorSlot j a) →
      Disjoint (rootRaw (rootSlot i))
        (rootRaw (interiorSlot j a))) :
    ∃ z ∈ sourceRaw,
      Nonempty (HierarchicalCandidateEmbedding F G (fun _ ↦ z)
        (targetRootCandidate F G rho rootSlot rootWhole rootRaw
          (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) {z})
        (targetInteriorCandidate F G rho rootSlot rootWhole rootRaw
          (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) {z})) := by
  classical
  let interiorWhole : (i : Fin s) → Fin (F.segments.size i) → Finset B :=
    fun i a ↦ rootWhole (interiorSlot i a)
  let interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B :=
    fun i a ↦ rootRaw (interiorSlot i a)
  let rootPool : Fin s → Pool := fun i ↦ slotPool (rootSlot i)
  let interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool :=
    fun i a ↦ slotPool (interiorSlot i a)
  have hcoordinateSubset : ∀ i a,
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootRaw interiorRaw i a ⊆
        ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole interiorWhole i a := by
    intro i a
    by_cases ha : a = F.segments.root i
    · subst a
      simpa [ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
        using hrootRawSubset i
    · simpa [ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate,
        interiorRaw, interiorWhole, ha] using hinteriorRawSubset i a
  have hcoordinateLarge : ∀ i a,
      rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootWhole interiorWhole i a) ≤
        #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootSlot rootRaw interiorRaw i a) := by
    intro i a
    by_cases ha : a = F.segments.root i
    · subst a
      simpa [ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
        using hrootRawLarge i
    · simpa [ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate,
        interiorRaw, interiorWhole, ha] using hinteriorRawLarge i a
  obtain ⟨z, hzRaw, hzDirect⟩ :=
    exists_oneRootImage_in_targetReservoir F G rho sourceWhole sourceRaw
      rootSlot rootWhole rootRaw hsourceSubset hsourceLarge hdirectUniform
      (fun i _ ↦ hrootRawSubset i) (fun i _ ↦ hrootRawLarge i) hbadBudget
  let originalImage : Fin 1 → B := fun _ ↦ z
  have horiginalInjective : Function.Injective originalImage := by
    intro q q' _
    exact Subsingleton.elim q q'
  have hremoved : ∀ i a,
      (#(targetCoordinateRemoved F G rho rootSlot rootWhole rootRaw
        interiorWhole interiorRaw i a) : ℝ) ≤
        coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole i a := by
    intro i a
    simp only [coordinateRemovalBudget]
    apply card_targetCoordinateRemoved_le F G rho rootSlot rootWhole rootRaw
      interiorWhole interiorRaw i a (hcoordinateSubset i a)
      (hcoordinateLarge i a)
    · intro t ht
      exact hattachUniform t i a (Finset.mem_filter.mp ht).2
    · intro t _
      exact hrootRawSubset t
    · intro t _
      exact hrootRawLarge t
    · intro b hb
      exact hinternalUniform i a b (Finset.mem_filter.mp hb).2.1
        (Finset.mem_filter.mp hb).2.2
    · intro b _
      exact hinteriorRawSubset i b
    · intro b _
      exact hinteriorRawLarge i b
  have hremovedUnion : ∀ i a,
      (#(targetCoordinateRemoved F G rho rootSlot rootWhole rootRaw
          interiorWhole interiorRaw i a ∪ {z}) : ℝ) ≤ removalBudget + 1 := by
    intro i a
    have h := card_targetCoordinateRemoved_union_le F G rho rootSlot rootWhole
      rootRaw interiorWhole interiorRaw {z} i a (hremoved i a)
    calc
      (#(targetCoordinateRemoved F G rho rootSlot rootWhole rootRaw
          interiorWhole interiorRaw i a ∪ {z}) : ℝ) ≤
          coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole i a + 1 := by
        simpa [coordinateRemovalBudget] using h
      _ ≤ removalBudget + 1 := by
        simpa [add_comm] using add_le_add_right (hremoval i a) 1
  have hinteriorRemoved : ∀ i a, a ≠ F.segments.root i →
      (#(targetInteriorRemoved F G rho rootSlot rootWhole rootRaw
          interiorWhole interiorRaw {z} i a) : ℝ) ≤ removalBudget + 1 := by
    intro i a ha
    have h := card_targetInteriorRemoved_le F G rho rootSlot rootWhole rootRaw
      interiorWhole interiorRaw {z} i a ha (hremoved i a)
    calc
      (#(targetInteriorRemoved F G rho rootSlot rootWhole rootRaw
          interiorWhole interiorRaw {z} i a) : ℝ) ≤
          coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole i a + 1 := by
        simpa [coordinateRemovalBudget] using h
      _ ≤ removalBudget + 1 := by
        simpa [add_comm] using add_le_add_right (hremoval i a) 1
  have hrootLoad (i : Fin s) :
      coordinatePoolLoad F rootPool interiorPool (rootPool i) ≤
        poolCapacity (rootPool i) := hpoolLoad (rootPool i)
  have hinteriorLoad (i : Fin s) (a : Fin (F.segments.size i)) :
      coordinatePoolLoad F rootPool interiorPool (interiorPool i a) ≤
        poolCapacity (interiorPool i a) := hpoolLoad (interiorPool i a)
  let system := targetCoordinateCleanedRegularSystem F G rho originalImage
    small rootSlot rootPool interiorPool rootWhole rootRaw interiorWhole
    interiorRaw {z}
    (by intro _ hz; simpa [originalImage] using hz)
    hsegmentSmall
    (by
      intro i q hp
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      have hloadReal :
          (coordinatePoolLoad F rootPool interiorPool (rootPool i) +
              small + 1 : ℝ) ≤
            (poolCapacity (rootPool i) + small + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right
          (Nat.add_le_add_right (hrootLoad i) small) 1
      have hdensity0 :
          (density - rho) * #(rootRaw (rootSlot i)) ≤
            (G.edgeDensity sourceWhole (rootWhole (rootSlot i)) - rho) *
              #(rootRaw (rootSlot i)) :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_right (hdirectDensity i hp) rho) (by positivity)
      have htail :
          (poolCapacity (rootPool i) + small + 1 : ℝ) +
              (removalBudget + 1) ≤
            #((rootRaw (rootSlot i)).filter (G.Adj (originalImage 0))) := by
        simpa only [rootPool, originalImage, add_assoc] using
          ((hrootCapacity i).trans (hdensity0.trans (hzDirect i hp)))
      exact (add_le_add hloadReal
        (hremovedUnion i (F.segments.root i))).trans htail)
    (by
      intro i j a hp
      have hloadReal :
          (coordinatePoolLoad F rootPool interiorPool (rootPool i) +
              small + 1 : ℝ) ≤
            (poolCapacity (rootPool i) + small + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right
          (Nat.add_le_add_right (hrootLoad i) small) 1
      have hdensity0 :
          (density - rho) * #(rootRaw (rootSlot i)) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole j a)
              (rootWhole (rootSlot i)) - rho) * #(rootRaw (rootSlot i)) :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_right (hattachDensity i j a hp) rho) (by positivity)
      have htail :
          (poolCapacity (rootPool i) + small + 1 : ℝ) +
              (removalBudget + 1) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole j a)
              (rootWhole (rootSlot i)) - rho) * #(rootRaw (rootSlot i)) := by
        simpa [rootPool, interiorPool, interiorWhole, interiorRaw, add_assoc] using
          ((hrootCapacity i).trans hdensity0)
      exact (add_le_add hloadReal
        (hremovedUnion i (F.segments.root i))).trans htail)
    (by
      intro i a b hab hb
      have hloadReal :
          (coordinatePoolLoad F rootPool interiorPool (interiorPool i b) +
              small + 1 : ℝ) ≤
            (poolCapacity (interiorPool i b) + small + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right
          (Nat.add_le_add_right (hinteriorLoad i b) small) 1
      have hdensity0 :
          (density - rho) * #(rootRaw (interiorSlot i b)) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole i a)
              (rootWhole (interiorSlot i b)) - rho) *
                #(rootRaw (interiorSlot i b)) :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_right (hinternalDensity i a b hab hb) rho) (by positivity)
      have htail :
          (poolCapacity (interiorPool i b) + small + 1 : ℝ) +
              (removalBudget + 1) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole i a)
              (rootWhole (interiorSlot i b)) - rho) *
                #(rootRaw (interiorSlot i b)) := by
        simpa [rootPool, interiorPool, interiorWhole, interiorRaw, add_assoc] using
          ((hinteriorCapacity i b).trans hdensity0)
      exact (add_le_add hloadReal (hinteriorRemoved i b hb)).trans htail)
    horiginalInjective
    (by intro i j hp; exact hrootRawDisjoint i j hp)
    (by intro i a j b hp; exact hinteriorRawDisjoint i a j b hp)
    (by intro i j a hp; exact hrootInteriorRawDisjoint i j a hp)
  refine ⟨z, hzRaw, ?_⟩
  exact exists_hierarchicalCoordinateRegularEmbedding F G originalImage small
    rootPool interiorPool
    (targetRootCandidate F G rho rootSlot rootWhole rootRaw interiorWhole
      interiorRaw {z})
    (targetInteriorCandidate F G rho rootSlot rootWhole rootRaw interiorWhole
      interiorRaw {z}) system

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateApplication

#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateApplication.HierarchicalSegmentForest.exists_targetCoordinateHierarchyEmbedding
