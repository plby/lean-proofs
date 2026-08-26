/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetRemovalBounds
import ErdosProblems.Erdos547b.HierarchicalRootReservoir

/-!
# One-shot target-relative hierarchical realization

This is the graph-side endpoint consumed by the concrete Section 6 host
layouts.  Its inputs are whole regular pairs, quantitative raw reservoirs,
one physical-pool load bound, and scalar capacity inequalities.  It chooses
the original root inside its actual reservoir, performs all target-relative
cleaning, and returns an actual copy of the hierarchy.  In particular no
`CleanedRegularSystem`, pointwise candidate-degree oracle, or source copy is
an input.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalCanonical
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular
open Erdos547b.ZhaoHierarchicalRootReservoir
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {s : ℕ} {B : Type u}

/-- The literal regularity loss attached to one already embedded hierarchy
coordinate. -/
def coordinateRemovalBudget
    {RootSlot : Type*}
    [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (rho : ℝ)
    (rootSlot : Fin s → RootSlot)
    (rootWhole : RootSlot → Finset B)
    (interiorWhole : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : ℝ :=
  (∑ _t ∈ childSegments F i a,
      rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootSlot rootWhole interiorWhole i a)) +
    ∑ _b ∈ internalTargets F i a,
      rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootSlot rootWhole interiorWhole i a)

/-- A one-shot target-relative realization.  The `slotPool` equality for
interior coordinates says precisely that both endpoint sides of one assigned
matching edge are charged to the same physical pool. -/
theorem exists_targetUnifiedHierarchyEmbedding
    {RootSlot Pool : Type*} [DecidableEq Pool]
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B)
    (poolCapacity : Pool → ℕ)
    (removalBudget : ℝ)
    (hinteriorPool : ∀ i a,
      slotPool (interiorSlot i a) =
        slotPool (interiorSlot i (F.segments.root i)))
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
      poolLoad F (fun i ↦ slotPool (rootSlot i))
          (fun i ↦ slotPool (interiorSlot i (F.segments.root i))) p ≤
        poolCapacity p)
    (hremoval : ∀ i a,
      coordinateRemovalBudget F rho rootSlot rootWhole
          (fun i a ↦ rootWhole (interiorSlot i a)) i a ≤
        removalBudget)
    (hrootCapacity : ∀ i,
      (poolCapacity (slotPool (rootSlot i)) + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(rootRaw (rootSlot i)))
    (hinteriorCapacity : ∀ i a,
      (poolCapacity (slotPool (interiorSlot i a)) + 1 : ℝ) +
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
  let interiorPool : Fin s → Pool := fun i ↦
    slotPool (interiorSlot i (F.segments.root i))
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
      (fun i _ ↦ hrootRawSubset i)
      (fun i _ ↦ hrootRawLarge i) hbadBudget
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
    · intro t _ht
      exact hrootRawSubset t
    · intro t _ht
      exact hrootRawLarge t
    · intro b hb
      exact hinternalUniform i a b (Finset.mem_filter.mp hb).2.1
        (Finset.mem_filter.mp hb).2.2
    · intro b _hb
      exact hinteriorRawSubset i b
    · intro b _hb
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
      poolLoad F rootPool interiorPool (rootPool i) ≤
        poolCapacity (rootPool i) := by
    exact hpoolLoad (rootPool i)
  have hinteriorLoad (i : Fin s) :
      poolLoad F rootPool interiorPool (interiorPool i) ≤
        poolCapacity (interiorPool i) := by
    exact hpoolLoad (interiorPool i)
  let system := targetUnifiedCleanedRegularSystem F G rho originalImage
    rootSlot rootPool interiorPool rootWhole rootRaw interiorWhole interiorRaw {z}
    (by
      intro _ hz
      simpa [originalImage] using hz)
    (by
      intro i q hp
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      have hloadReal :
          (poolLoad F rootPool interiorPool (rootPool i) + 1 : ℝ) ≤
            (poolCapacity (rootPool i) + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (hrootLoad i) 1
      have hcap0 := hrootCapacity i
      have hdensity0 :
          (density - rho) * #(rootRaw (rootSlot i)) ≤
            (G.edgeDensity sourceWhole (rootWhole (rootSlot i)) - rho) *
              #(rootRaw (rootSlot i)) :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_right (hdirectDensity i hp) rho) (by positivity)
      have htail :
          (poolCapacity (rootPool i) + 1 : ℝ) + (removalBudget + 1) ≤
            #((rootRaw (rootSlot i)).filter (G.Adj (originalImage 0))) := by
        simpa only [rootPool, originalImage, add_assoc] using
          (hcap0.trans (hdensity0.trans (hzDirect i hp)))
      exact (add_le_add hloadReal
        (hremovedUnion i (F.segments.root i))).trans htail)
    (by
      intro i j a hp
      have hloadReal :
          (poolLoad F rootPool interiorPool (rootPool i) + 1 : ℝ) ≤
            (poolCapacity (rootPool i) + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (hrootLoad i) 1
      have hcap0 := hrootCapacity i
      have hdensity0 :
          (density - rho) * #(rootRaw (rootSlot i)) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole j a)
              (rootWhole (rootSlot i)) - rho) *
                #(rootRaw (rootSlot i)) :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_right (hattachDensity i j a hp) rho) (by positivity)
      have htail :
          (poolCapacity (rootPool i) + 1 : ℝ) + (removalBudget + 1) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole j a)
              (rootWhole (rootSlot i)) - rho) * #(rootRaw (rootSlot i)) := by
        simpa [rootPool, interiorPool, interiorWhole, interiorRaw, add_assoc] using
          (hcap0.trans hdensity0)
      exact (add_le_add hloadReal
        (hremovedUnion i (F.segments.root i))).trans htail)
    (by
      intro i a b hab hb
      have hloadReal :
          (poolLoad F rootPool interiorPool (interiorPool i) + 1 : ℝ) ≤
            (poolCapacity (interiorPool i) + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (hinteriorLoad i) 1
      have hpoolSlot : slotPool (interiorSlot i b) = interiorPool i :=
        hinteriorPool i b
      have hcap0 := hinteriorCapacity i b
      rw [hpoolSlot] at hcap0
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
          (poolCapacity (interiorPool i) + 1 : ℝ) + (removalBudget + 1) ≤
            (G.edgeDensity
              (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
                F rootSlot rootWhole interiorWhole i a)
              (rootWhole (interiorSlot i b)) - rho) *
                #(rootRaw (interiorSlot i b)) := by
        simpa [rootPool, interiorPool, interiorWhole, interiorRaw, add_assoc] using
          (hcap0.trans hdensity0)
      exact (add_le_add hloadReal (hinteriorRemoved i b hb)).trans htail)
    horiginalInjective
    (by
      intro i j hp
      exact hrootRawDisjoint i j hp)
    (by
      intro i a j b hp
      apply hinteriorRawDisjoint i a j b
      intro heq
      apply hp
      simpa [interiorPool, hinteriorPool i a, hinteriorPool j b] using heq)
    (by
      intro i j a hp
      apply hrootInteriorRawDisjoint i j a
      intro heq
      apply hp
      simpa [rootPool, interiorPool, hinteriorPool j a] using heq)
  refine ⟨z, hzRaw, ?_⟩
  exact exists_hierarchicalUnifiedRegularEmbedding F G originalImage rootPool
    interiorPool
    (targetRootCandidate F G rho rootSlot rootWhole rootRaw interiorWhole
      interiorRaw {z})
    (targetInteriorCandidate F G rho rootSlot rootWhole rootRaw interiorWhole
      interiorRaw {z}) system

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication

#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest.exists_targetUnifiedHierarchyEmbedding
