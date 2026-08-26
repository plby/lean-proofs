/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedHistoryStep

/-!
# Literal marked partial branch placements

Insertion preserves every old source-index copy and its group assignment.
Only marked vertices, not all vertices of the root colour, are required to
have the permanent A-reservoir reconnection degree.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedBranchPlacement

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ForestMatching
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b : ℕ} (F : OrderedRootedForest b) (marks : ∀ i, Finset (Fin (F.size i)))

structure Placement (selected : Finset (Fin b)) (parent : Fin b → Fin hostN) where
  group : {i // i ∈ selected} → {c // c ∈ C}
  forestCopy : OrderedForestCopy selected (fun i => Fin (F.size i)) F.tree (embeddingHost W)
  attach : ∀ i hi, (embeddingHost W).Adj (parent i) (forestCopy.componentCopy i hi (F.root i))
  marked : ∀ i hi a, a ∈ insert (F.root i) (marks i) →
    forestCopy.componentCopy i hi a ∈ whole W (P.center (group ⟨i, hi⟩)) ∧
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (Q.A₀.filter ((embeddingHost W).Adj (forestCopy.componentCopy i hi a))).card
  other : ∀ i hi a, a ≠ F.root i → a ∉ marks i →
    forestCopy.componentCopy i hi a ∈ P.pairs W Q S O (group ⟨i, hi⟩)

variable {selected : Finset (Fin b)} {parent : Fin b → Fin hostN}

def Placement.used (E : Placement W Q S O P F marks selected parent) : Finset (Fin hostN) :=
  Finset.univ.biUnion fun i : {i // i ∈ selected} => Finset.univ.image (E.forestCopy.componentCopy i.1 i.2)

theorem Placement.copy_mem_used (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (hi : i ∈ selected) (a : Fin (F.size i)) :
    E.forestCopy.componentCopy i hi a ∈ E.used W Q S O P F marks := by
  exact Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

def Placement.empty (parent : Fin b → Fin hostN) : Placement W Q S O P F marks ∅ parent where
  group i := (Finset.notMem_empty _ i.2).elim
  forestCopy := {
    componentCopy := fun _ hi => (Finset.notMem_empty _ hi).elim
    disjoint_ranges := fun _ hi => (Finset.notMem_empty _ hi).elim }
  attach _ hi := (Finset.notMem_empty _ hi).elim
  marked _ hi := (Finset.notMem_empty _ hi).elim
  other _ hi := (Finset.notMem_empty _ hi).elim

def Placement.reparent (E : Placement W Q S O P F marks selected parent)
    (parent' : Fin b → Fin hostN) (hagrees : ∀ i ∈ selected, parent' i = parent i) :
    Placement W Q S O P F marks selected parent' where
  group := E.group
  forestCopy := E.forestCopy
  attach i hi := by rw [hagrees i hi]; exact E.attach i hi
  marked := E.marked
  other := E.other

private def insertCopy (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (f : (F.tree i).Copy (embeddingHost W)) :
    ∀ j, j ∈ insert i selected → (F.tree j).Copy (embeddingHost W) := fun j hj =>
  if hs : j ∈ selected then E.forestCopy.componentCopy j hs
  else ((Finset.mem_insert.mp hj).resolve_right hs).symm ▸ f

private theorem insertCopy_old (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (f : (F.tree i).Copy (embeddingHost W)) (j : Fin b) (hj : j ∈ selected) :
    insertCopy W Q S O P F marks E i f j (Finset.mem_insert_of_mem hj) = E.forestCopy.componentCopy j hj := by
  simp only [insertCopy, dif_pos hj]

private theorem insertCopy_new (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (hi : i ∉ selected) (f : (F.tree i).Copy (embeddingHost W)) :
    insertCopy W Q S O P F marks E i f i (Finset.mem_insert_self _ _) = f := by
  simp only [insertCopy, dif_neg hi]

def Placement.appendBranch (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (hi : i ∉ selected) (x : {c // c ∈ C}) (f : (F.tree i).Copy (embeddingHost W))
    (hattach : (embeddingHost W).Adj (parent i) (f (F.root i)))
    (hfresh : ∀ a, f a ∉ E.used W Q S O P F marks)
    (hmarked : ∀ a ∈ insert (F.root i) (marks i), f a ∈ whole W (P.center x) ∧
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (Q.A₀.filter ((embeddingHost W).Adj (f a))).card)
    (hother : ∀ a, a ≠ F.root i → a ∉ marks i → f a ∈ P.pairs W Q S O x) :
    Placement W Q S O P F marks (insert i selected) parent := by
  let group : {j // j ∈ insert i selected} → {c // c ∈ C} :=
    fun j => if hj : j.1 ∈ selected then E.group ⟨j.1, hj⟩ else x
  have hdisjoint (j : Fin b) (hj : j ∈ selected) :
      Disjoint (Set.range (E.forestCopy.componentCopy j hj : Fin (F.size j) → Fin hostN))
        (Set.range (f : Fin (F.size i) → Fin hostN)) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨a, rfl⟩ ⟨d, hd⟩
    apply hfresh d
    rw [hd]
    exact E.copy_mem_used W Q S O P F marks j hj a
  refine {
    group := group
    forestCopy := {
      componentCopy := insertCopy W Q S O P F marks E i f
      disjoint_ranges := ?_ }
    attach := ?_
    marked := ?_
    other := ?_ }
  · intro j hj k hk hjk
    by_cases hjs : j ∈ selected
    · by_cases hks : k ∈ selected
      · simpa only [insertCopy_old W Q S O P F marks E i f j hjs,
          insertCopy_old W Q S O P F marks E i f k hks] using E.forestCopy.disjoint_ranges j hjs k hks hjk
      · have hki : k = i := (Finset.mem_insert.mp hk).resolve_right hks
        subst k
        simpa only [insertCopy_old W Q S O P F marks E i f j hjs,
          insertCopy_new W Q S O P F marks E i hi f] using hdisjoint j hjs
    · have hji : j = i := (Finset.mem_insert.mp hj).resolve_right hjs
      subst j
      have hks : k ∈ selected := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
      simpa only [insertCopy_old W Q S O P F marks E i f k hks,
        insertCopy_new W Q S O P F marks E i hi f] using (hdisjoint k hks).symm
  · intro j hj
    by_cases hjs : j ∈ selected
    · simpa only [insertCopy_old W Q S O P F marks E i f j hjs] using E.attach j hjs
    · have hji : j = i := (Finset.mem_insert.mp hj).resolve_right hjs
      subst j
      simpa only [insertCopy_new W Q S O P F marks E i hi f] using hattach
  · intro j hj a ha
    by_cases hjs : j ∈ selected
    · simpa only [insertCopy_old W Q S O P F marks E i f j hjs, group, dif_pos hjs] using E.marked j hjs a ha
    · have hji : j = i := (Finset.mem_insert.mp hj).resolve_right hjs
      subst j
      simpa only [insertCopy_new W Q S O P F marks E i hi f, group, dif_neg hi] using hmarked a ha
  · intro j hj a har ham
    by_cases hjs : j ∈ selected
    · simpa only [insertCopy_old W Q S O P F marks E i f j hjs, group, dif_pos hjs] using E.other j hjs a har ham
    · have hji : j = i := (Finset.mem_insert.mp hj).resolve_right hjs
      subst j
      simpa only [insertCopy_new W Q S O P F marks E i hi f, group, dif_neg hi] using hother a har ham

theorem Placement.appendBranch_preserves_copy (E : Placement W Q S O P F marks selected parent)
    (i : Fin b) (hi : i ∉ selected) (x : {c // c ∈ C}) (f : (F.tree i).Copy (embeddingHost W))
    (hattach : (embeddingHost W).Adj (parent i) (f (F.root i)))
    (hfresh : ∀ a, f a ∉ E.used W Q S O P F marks)
    (hmarked : ∀ a ∈ insert (F.root i) (marks i), f a ∈ whole W (P.center x) ∧
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (Q.A₀.filter ((embeddingHost W).Adj (f a))).card)
    (hother : ∀ a, a ≠ F.root i → a ∉ marks i → f a ∈ P.pairs W Q S O x)
    (j : Fin b) (hj : j ∈ selected) :
    (E.appendBranch W Q S O P F marks i hi x f hattach hfresh hmarked hother).forestCopy.componentCopy j
      (Finset.mem_insert_of_mem hj) = E.forestCopy.componentCopy j hj :=
  insertCopy_old W Q S O P F marks E i f j hj

variable (E : Placement W Q S O P F marks selected parent)
variable (i : Fin b) (hi : i ∉ selected) (x : {c // c ∈ C}) (f : (F.tree i).Copy (embeddingHost W))
variable (hattach : (embeddingHost W).Adj (parent i) (f (F.root i)))
variable (hfresh : ∀ a, f a ∉ E.used W Q S O P F marks)
variable (hmarked : ∀ a ∈ insert (F.root i) (marks i), f a ∈ whole W (P.center x) ∧
  ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
    (Q.A₀.filter ((embeddingHost W).Adj (f a))).card)
variable (hother : ∀ a, a ≠ F.root i → a ∉ marks i → f a ∈ P.pairs W Q S O x)

theorem Placement.appendBranch_new_copy :
    (E.appendBranch W Q S O P F marks i hi x f hattach hfresh hmarked hother).forestCopy.componentCopy i
      (Finset.mem_insert_self _ _) = f :=
  insertCopy_new W Q S O P F marks E i hi f

theorem Placement.appendBranch_preserves_group (j : Fin b) (hj : j ∈ selected) :
    (E.appendBranch W Q S O P F marks i hi x f hattach hfresh hmarked hother).group
      ⟨j, Finset.mem_insert_of_mem hj⟩ = E.group ⟨j, hj⟩ := by
  simp only [Placement.appendBranch, dif_pos hj]

theorem Placement.appendBranch_new_group :
    (E.appendBranch W Q S O P F marks i hi x f hattach hfresh hmarked hother).group
      ⟨i, Finset.mem_insert_self _ _⟩ = x := by
  simp only [Placement.appendBranch, dif_neg hi]

end Erdos547b.ZhaoSourceMarkedBranchPlacement

#print axioms Erdos547b.ZhaoSourceMarkedBranchPlacement.Placement.appendBranch
#print axioms Erdos547b.ZhaoSourceMarkedBranchPlacement.Placement.appendBranch_preserves_copy
#print axioms Erdos547b.ZhaoSourceMarkedBranchPlacement.Placement.appendBranch_preserves_group
