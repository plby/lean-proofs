import ErdosProblems.Erdos920.DStarProjective
import ErdosProblems.Erdos920.TupleBound

/-!
# Forward-independent tuples as projective container histories

The projective `D*` vertices are incident ordered pairs.  A tuple is written
chronologically in `RamseyPackaging`, whereas the container tree stores the
newest pair at the head of its history.  This file proves that reversing and
forgetting the incidence proofs identifies the two finite collections
exactly.
-/

open scoped LinearAlgebra.Projectivization

namespace Erdos920.TupleHistory

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

variable {q t m : ℕ} [Fact q.Prime]

abbrev P (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)
abbrev V (q t : ℕ) [Fact q.Prime] := ProjectiveDStar.Vertex q t

local instance orthogonalDecidable :
    DecidableRel (@Projective.Orthogonal (ZMod q) _ (t + 1)) :=
  Classical.decRel _

noncomputable local instance pointFintype : Fintype (P q t) :=
  Fintype.ofFinite _

local instance pointDecidableEq : DecidableEq (P q t) :=
  Classical.decEq _

/-- The ambient finset of incident projective pairs. -/
def incidentPairs : Finset (P q t × P q t) :=
  Finset.univ.filter fun p ↦ Projective.Orthogonal p.1 p.2

@[simp] theorem mem_incidentPairs_iff (p : P q t × P q t) :
    p ∈ (incidentPairs : Finset (P q t × P q t)) ↔
      Projective.Orthogonal p.1 p.2 := by
  simp [incidentPairs]

/-- Forget the incidence proof carried by a projective `D*` vertex. -/
def vertexPair (u : V q t) : P q t × P q t :=
  (ProjectiveDStar.leftPoint u, ProjectiveDStar.rightPoint u)

@[simp] theorem vertexPair_fst (u : V q t) :
    (vertexPair u).1 = ProjectiveDStar.leftPoint u := rfl

@[simp] theorem vertexPair_snd (u : V q t) :
    (vertexPair u).2 = ProjectiveDStar.rightPoint u := rfl

/-- Forget the proof of incidence in every coordinate of a tuple. -/
def pairTuple (x : Fin m → V q t) : Fin m → P q t × P q t :=
  fun i ↦ vertexPair (x i)

/-- Chronological tuples become newest-first container histories. -/
def pairHistory (x : Fin m → V q t) : List (P q t × P q t) :=
  TupleBound.tupleHistory (pairTuple x)

@[simp] theorem length_pairHistory (x : Fin m → V q t) :
    (pairHistory x).length = m := by
  simp [pairHistory]

theorem vertexPair_injective :
    Function.Injective (@vertexPair q t _) := by
  intro u v huv
  exact Subtype.ext huv

theorem pairTuple_injective :
    Function.Injective
      (pairTuple : (Fin m → V q t) → (Fin m → P q t × P q t)) := by
  intro x y hxy
  funext i
  exact vertexPair_injective (congrFun hxy i)

theorem pairHistory_injective :
    Function.Injective
      (pairHistory : (Fin m → V q t) → List (P q t × P q t)) := by
  intro x y hxy
  apply pairTuple_injective
  exact TupleBound.tupleHistory_injective hxy

private theorem ofFn_get_cast {alpha : Type*} (xs : List alpha) {n : ℕ}
    (h : n = xs.length) :
    List.ofFn (fun i : Fin n ↦ xs.get (Fin.cast h i)) = xs := by
  subst n
  simp

/-! ## Logical identification -/

/-- Adding a concrete projective vertex to a reverse history is equivalent
to requiring that no old vertex has a `D*` arc to it. -/
theorem canExtend_vertexPair_iff (new : V q t) (old : List (V q t)) :
    Container.CanExtend Projective.Orthogonal
        (vertexPair new)
        (old.map vertexPair) ↔
      ∀ u ∈ old, ¬ ProjectiveDStar.Arc u new := by
  constructor
  · intro h u hu harc
    rcases h with ⟨_inc, hcompat⟩
    rcases harc with ⟨huv, hvu⟩
    apply hvu
    apply hcompat (vertexPair u)
    · exact List.mem_map.mpr ⟨u, hu, rfl⟩
    · exact huv
  · intro h
    refine ⟨ProjectiveDStar.incident new, ?_⟩
    intro p hp holdnew
    rcases List.mem_map.mp hp with ⟨u, hu, rfl⟩
    by_contra hnewold
    exact h u hu ⟨holdnew, hnewold⟩

/-- Consistent newest-first histories are the same thing as chronological
lists with no arc from an earlier entry to a later entry. -/
theorem consistent_map_iff_pairwise_reverse (xs : List (V q t)) :
    Container.Consistent Projective.Orthogonal
        (xs.map vertexPair) ↔
      xs.reverse.Pairwise (fun old new ↦ ¬ ProjectiveDStar.Arc old new) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, Container.consistent_cons_iff, ih,
        canExtend_vertexPair_iff]
      simp only [List.reverse_cons]
      rw [List.pairwise_append]
      simp

/-- The tuple predicate used by `forwardIndependentTupleCount` is literally
container consistency after reversing chronology and forgetting proofs. -/
theorem isForwardIndependent_iff_consistent (x : Fin m → V q t) :
    (ProjectiveDStar.digraph q t).IsForwardIndependent x ↔
      Container.Consistent Projective.Orthogonal (pairHistory x) := by
  rw [pairHistory, TupleBound.tupleHistory]
  have hmap : List.ofFn (pairTuple x) =
      (List.ofFn x).map vertexPair := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, ← List.map_reverse, consistent_map_iff_pairwise_reverse]
  simp only [List.reverse_reverse]
  rw [List.pairwise_ofFn]
  rfl

/-- Every entry of a pair history is incident. -/
theorem pairHistory_mem_incidentPairs (x : Fin m → V q t) :
    ∀ p ∈ pairHistory x,
      p ∈ (incidentPairs : Finset (P q t × P q t)) := by
  intro p hp
  have hp' : p ∈ List.ofFn (pairTuple x) := by
    simpa [pairHistory, TupleBound.tupleHistory] using hp
  rcases List.mem_ofFn.mp hp' with ⟨i, rfl⟩
  exact (mem_incidentPairs_iff _).2 (ProjectiveDStar.incident (x i))

/-- Exact path characterization for the concrete incident-pair child tree. -/
theorem isPath_pairHistory_iff (x : Fin m → V q t) :
    MarkedTree.IsPath
        (TupleBound.consistentChildren incidentPairs Projective.Orthogonal)
        (pairHistory x) ↔
      (ProjectiveDStar.digraph q t).IsForwardIndependent x := by
  rw [TupleBound.isPath_consistentChildren_iff,
    ← isForwardIndependent_iff_consistent]
  exact and_iff_left (pairHistory_mem_incidentPairs x)

/-! ## Exact equality of the finite counts -/

/-- The concrete finset counted by `forwardIndependentTupleCount`. -/
def forwardIndependentTuples : Finset (Fin m → V q t) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      (ProjectiveDStar.digraph q t).IsForwardIndependent x

@[simp] theorem mem_forwardIndependentTuples_iff (x : Fin m → V q t) :
    x ∈ (forwardIndependentTuples : Finset (Fin m → V q t)) ↔
      (ProjectiveDStar.digraph q t).IsForwardIndependent x := by
  simp [forwardIndependentTuples]

theorem card_forwardIndependentTuples :
    (forwardIndependentTuples : Finset (Fin m → V q t)).card =
      @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m := by
  simp [forwardIndependentTuples, Digraph.forwardIndependentTupleCount]

/-- The image of all forward-independent tuples under the history map.
This form is useful even when a downstream argument only needs an injection. -/
def forwardHistories : Finset (List (P q t × P q t)) :=
  by
    classical
    exact (forwardIndependentTuples (q := q) (t := t) (m := m)).image pairHistory

theorem card_forwardHistories :
    (forwardHistories (q := q) (t := t) (m := m)).card =
      @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m := by
  rw [forwardHistories, Finset.card_image_iff.mpr]
  · exact card_forwardIndependentTuples
  · exact pairHistory_injective.injOn

/-- Membership in the history image has an intrinsic characterization. -/
theorem mem_forwardHistories_iff (xs : List (P q t × P q t)) :
    xs ∈ (forwardHistories (q := q) (t := t) (m := m) :
        Finset (List (P q t × P q t))) ↔
      Container.Consistent Projective.Orthogonal xs ∧
      xs.length = m ∧
      ∀ p ∈ xs, p ∈ (incidentPairs : Finset (P q t × P q t)) := by
  constructor
  · intro hxs
    rw [forwardHistories] at hxs
    rcases Finset.mem_image.mp hxs with ⟨x, hx, rfl⟩
    exact ⟨(isForwardIndependent_iff_consistent x).1
        ((mem_forwardIndependentTuples_iff x).1 hx),
      length_pairHistory x, pairHistory_mem_incidentPairs x⟩
  · rintro ⟨hconsistent, hlen, hinc⟩
    have hrev : m = xs.reverse.length := by
      calc
        m = xs.length := hlen.symm
        _ = xs.reverse.length := by simp
    let x : Fin m → V q t := fun i ↦
      ⟨xs.reverse.get (Fin.cast hrev i), (mem_incidentPairs_iff _).1
        (hinc _ (List.mem_reverse.mp
          (List.get_mem xs.reverse (Fin.cast hrev i))))⟩
    have hhistory : pairHistory x = xs := by
      apply List.reverse_injective
      simp only [pairHistory, TupleBound.tupleHistory, List.reverse_reverse]
      change List.ofFn (fun i : Fin m ↦
        xs.reverse.get (Fin.cast hrev i)) = xs.reverse
      exact ofFn_get_cast xs.reverse hrev
    rw [forwardHistories]
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hhistory⟩
    rw [mem_forwardIndependentTuples_iff,
      isForwardIndependent_iff_consistent, hhistory]
    exact hconsistent

/-- For any marking, `Container.allPaths` is exactly the image of the
forward-independent tuples.  The marking is irrelevant because `allPaths`
imposes only the path and length conditions. -/
theorem forwardHistories_eq_allPaths
    (marked : List (P q t × P q t) → (P q t × P q t) → Bool) :
    forwardHistories (q := q) (t := t) (m := m) = Container.allPaths
      (TupleBound.consistentChildren
        (incidentPairs (q := q) (t := t)) Projective.Orthogonal)
      marked m := by
  ext xs
  rw [mem_forwardHistories_iff, Container.mem_allPaths_iff,
    TupleBound.isPath_consistentChildren_iff]
  aesop

/-- Exact equality between Bradač's forward-tuple count and the number of
length-`m` paths in the incident-pair container tree. -/
theorem forwardIndependentTupleCount_eq_card_allPaths
    (marked : List (P q t × P q t) → (P q t × P q t) → Bool) :
    @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m =
      (Container.allPaths
        (TupleBound.consistentChildren
          (incidentPairs (q := q) (t := t)) Projective.Orthogonal)
        marked m).card := by
  rw [← card_forwardHistories, forwardHistories_eq_allPaths marked]

end

end Erdos920.TupleHistory
