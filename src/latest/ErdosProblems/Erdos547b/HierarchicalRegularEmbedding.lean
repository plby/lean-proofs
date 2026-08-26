/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalOnlineCandidates

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalRegular

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline

universe u

namespace HierarchicalSegmentForest

variable {r s c k : ℕ} {B : Type u} {RootGroup : Type*}

/-- Raw regular-pair side containing a source coordinate.  Segment roots use
their assigned cluster; all other coordinates use their assigned matching
side. -/
def rawCandidate [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (rootGroup : Fin s → RootGroup)
    (rootRaw : RootGroup → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  if a = F.segments.root i then rootRaw (rootGroup i) else interiorRaw i a

/-- Removing an explicit exceptional/occupied set from a raw target costs at
most its cardinality.  This is the non-regular part of every capacity check. -/
theorem card_neighbors_sdiff_ge_of_real
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (Y removed : Finset B) (z : B) (n : ℕ)
    (hcap : (n : ℝ) + #removed ≤ (#(Y.filter (G.Adj z)) : ℝ)) :
    n ≤ #((Y \ removed).filter (G.Adj z)) := by
  have hcapNat : n + #removed ≤ #(Y.filter (G.Adj z)) := by
    exact_mod_cast hcap
  exact card_neighbors_cleaned_ge G Y removed z n hcapNat

/-- A member of a genuinely cleaned regular-pair side has the required
degree after the explicit target removals, provided the aggregate capacity
inequality holds. -/
theorem card_neighbors_sdiff_ge_of_mem_cleaned
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (X Y removed : Finset B) (z : B) (n : ℕ)
    (hz : z ∈ cleanedSide G rho X Y)
    (hcap : (n : ℝ) + #removed ≤
      (G.edgeDensity X Y - rho) * #Y) :
    n ≤ #((Y \ removed).filter (G.Adj z)) := by
  have hz' : z ∈ X \ atypicalVertices G rho X Y := by
    simpa [cleanedSide] using hz
  have hzX := (Finset.mem_sdiff.mp hz').1
  have hzNot := (Finset.mem_sdiff.mp hz').2
  have hzDeg : (G.edgeDensity X Y - rho) * (#Y : ℝ) ≤
      (#(Y.filter (G.Adj z)) : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply hzNot
    simpa [atypicalVertices, hzX, hlt]
  exact card_neighbors_sdiff_ge_of_real G Y removed z n (hcap.trans hzDeg)

/-- Source-shaped data for a hierarchical special-set realization.  The
regularity argument which constructs this record has already removed its bad
vertices.  Consequently the realization only needs the resulting *real raw
degree* lower bounds; it does not falsely require the possibly much smaller
target reservoir itself to form a uniform pair.

This separation is important in Section 6: regularity of a whole pair
`X--A` bounds the vertices of `X` which have low degree into a large target
`A₀ ⊆ A`, even though `X--A₀` need not satisfy the same uniformity
parameter. -/
structure CleanedRegularSystem [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin s → Fin c) (group : Fin s → Fin k)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    where
  rootRaw : Fin c → Finset B
  interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B
  rootRemoved : Fin s → Finset B
  interiorRemoved : (i : Fin s) → Fin (F.segments.size i) → Finset B
  rootCandidate_eq : ∀ i,
    rootCandidate i = rootRaw (rootGroup i) \ rootRemoved i
  interiorCandidate_eq : ∀ i a,
    interiorCandidate i a = interiorRaw i a \ interiorRemoved i a
  attach_original_capacity : ∀ i q, F.parent i = Sum.inl q →
    (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
        rootGroup (rootGroup i) + 1 : ℝ) +
        #(rootRemoved i) ≤
      (#((rootRaw (rootGroup i)).filter (G.Adj (originalImage q))) : ℝ)
  attach_source_degree : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    ∀ z ∈ ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate
        F rootCandidate interiorCandidate j a,
    (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
        rootGroup (rootGroup i) + 1 : ℝ) +
        #(rootRemoved i) ≤
      (#((rootRaw (rootGroup i)).filter (G.Adj z)) : ℝ)
  internal_source_degree : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i → ∀ z ∈
      ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate
        F rootCandidate interiorCandidate i a,
    (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.interiorLoad
        F group (group i) + 1 : ℝ) +
        #(interiorRemoved i b) ≤
      (#((interiorRaw i b).filter (G.Adj z)) : ℝ)
  original_injective : Function.Injective originalImage
  original_outside_root : ∀ q i, originalImage q ∉ rootCandidate i
  original_outside_interior : ∀ q i a,
    originalImage q ∉ interiorCandidate i a
  root_disjoint : ∀ i j, rootGroup i ≠ rootGroup j →
    Disjoint (rootCandidate i) (rootCandidate j)
  interior_disjoint : ∀ i a j b, group i ≠ group j →
    Disjoint (interiorCandidate i a) (interiorCandidate j b)
  root_interior_disjoint : ∀ i j a,
    Disjoint (rootCandidate i) (interiorCandidate j a)

/-- Public no-degree-oracle endpoint for the hierarchical arbitrary-special
realization.  It consumes the degree certificates produced from actual
regular pairs and aggregate capacities, and returns an actual source copy
with every parent edge restored. -/
theorem exists_hierarchicalRegularEmbedding
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin s → Fin c) (group : Fin s → Fin k)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (S : CleanedRegularSystem F G rho originalImage rootGroup group
      rootCandidate interiorCandidate) :
    Nonempty
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.HierarchicalCandidateEmbedding
        F G originalImage rootCandidate interiorCandidate) := by
  classical
  apply ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding
    F G originalImage rootGroup group rootCandidate interiorCandidate
    S.original_injective S.original_outside_root S.original_outside_interior
    S.root_disjoint S.interior_disjoint S.root_interior_disjoint
  · intro i q hp
    rw [S.rootCandidate_eq i]
    exact card_neighbors_sdiff_ge_of_real G (S.rootRaw (rootGroup i))
      (S.rootRemoved i) (originalImage q)
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
        rootGroup (rootGroup i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.attach_original_capacity i q hp)
  · intro i j a hp z hz
    rw [S.rootCandidate_eq i]
    exact card_neighbors_sdiff_ge_of_real G
      (S.rootRaw (rootGroup i)) (S.rootRemoved i) z
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
        rootGroup (rootGroup i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.attach_source_degree i j a hp z hz)
  · intro i a b hab hb z hz
    rw [S.interiorCandidate_eq i b]
    exact card_neighbors_sdiff_ge_of_real G
      (S.interiorRaw i b) (S.interiorRemoved i b) z
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.interiorLoad
        F group (group i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.internal_source_degree i a b hab hb z hz)

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalRegular

#print axioms Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.exists_hierarchicalRegularEmbedding
