/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Decomposition
import ErdosProblems.Erdos163.Embedding
import Mathlib.Data.Prod.Lex

/-!
# Ordered occupied parts of the target graph

The part of a target vertex records its geometric pruning layer and one
proper colour.  We retain only occupied pairs.  A lexicographic order on
vertices, with the original vertex as a final tie-breaker, makes every edge
point from an earlier part to a later part exactly as required by the greedy
embedding theorem.
-/

open Finset

namespace Erdos163
namespace TargetParts

noncomputable section

abbrev PartKey (n d : ℕ) := Fin (n + 1) × Fin (d + 1)

instance partKeyLinearOrder (n d : ℕ) : LinearOrder (PartKey n d) :=
  LinearOrder.lift' toLex (fun _ _ h => h)

def boundedKey {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) (x : Fin n) : PartKey n d :=
  (layer x, c x)

def OccupiedPart {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) :=
  {p : PartKey n d // ∃ x, boundedKey layer c x = p}

instance {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) : Fintype (OccupiedPart layer c) :=
  Fintype.ofFinset
    (Finset.univ.filter fun p : PartKey n d => ∃ x, boundedKey layer c x = p)
    (by
      intro p
      constructor
      · intro hp
        exact (Finset.mem_filter.mp hp).2
      · intro hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)

instance {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) : LinearOrder (OccupiedPart layer c) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

def part {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) (x : Fin n) : OccupiedPart layer c :=
  ⟨boundedKey layer c x, ⟨x, rfl⟩⟩

def layerOf {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} (p : OccupiedPart layer c) : ℕ :=
  p.1.1.1

def colorOf {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} (p : OccupiedPart layer c) : Fin (d + 1) :=
  p.1.2

@[simp] theorem layerOf_part {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) (x : Fin n) :
    layerOf (part layer c x) = (layer x).1 := rfl

@[simp] theorem colorOf_part {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) (x : Fin n) :
    colorOf (part layer c x) = c x := rfl

def vertexOrder {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) : LinearOrder (Fin n) :=
  LinearOrder.lift'
    (fun x => toLex (part layer c x, x))
    (fun _ _ h => congrArg (fun z => (ofLex z).2) h)

theorem part_ne_of_color_ne {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) {x y : Fin n} (h : c x ≠ c y) :
    part layer c x ≠ part layer c y := by
  intro heq
  exact h <| by simpa using congrArg colorOf heq

theorem vertex_lt_iff_part_lt_of_ne
    {n d : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) {x y : Fin n}
    (hne : part layer c x ≠ part layer c y) :
    @LT.lt (Fin n) (vertexOrder layer c).toLT x y ↔
      part layer c x < part layer c y := by
  change Prod.Lex (· < ·) (· < ·)
      (part layer c x, x) (part layer c y, y) ↔ _
  rw [Prod.lex_iff]
  constructor
  · rintro (h | ⟨heq, -⟩)
    · exact h
    · exact (hne heq).elim
  · exact Or.inl

theorem layer_le_of_part_lt
    {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} {p q : OccupiedPart layer c}
    (h : p < q) : layerOf p ≤ layerOf q := by
  change Prod.Lex (· < ·) (· < ·) p.1 q.1 at h
  rw [Prod.lex_iff] at h
  rcases h with h | ⟨heq, h⟩
  · exact h.le
  · exact le_of_eq (congrArg Fin.val heq)

theorem forwardNeighbors_subset_ge_layer
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hcolor : ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y)
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (x : Fin n) :
    letI := vertexOrder layer c
    RandomGreedy.forwardNeighbors H x ⊆
      Finset.univ.filter fun y =>
        H.Adj x y ∧ Decomposition.layerIndex H d x ≤
          Decomposition.layerIndex H d y := by
  let := vertexOrder layer c
  intro y hy
  have hyAdj : H.Adj x y := (Finset.mem_filter.mp hy).2.1
  have hyLt : @LT.lt (Fin n) (vertexOrder layer c).toLT x y := by
    exact (Finset.mem_filter.mp hy).2.2
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ y, hyAdj, ?_⟩
  have hp : part layer c x < part layer c y :=
    (vertex_lt_iff_part_lt_of_ne layer c
      (part_ne_of_color_ne layer c (hcolor hyAdj))).mp hyLt
  have hpLayer := layer_le_of_part_lt hp
  simpa only [layerOf_part, hlayer] using hpLayer

theorem forwardNeighbors_card_le
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hcolor : ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y)
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (x : Fin n) :
    letI := vertexOrder layer c
    (RandomGreedy.forwardNeighbors H x).card ≤
      4 * d := by
  let := vertexOrder layer c
  exact (Finset.card_le_card
    (forwardNeighbors_subset_ge_layer H layer c hcolor hlayer x)).trans
      (Nat.le_of_lt (Decomposition.card_forward_neighbors_lt H hd hdeg x))

theorem partVertices_subset_level
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (x : Fin n) :
    RandomGreedy.partVertices (part layer c) x ⊆
      Decomposition.levels H d (layer x).1 := by
  intro y hy
  have hpartEq := (Finset.mem_filter.mp hy).2
  have hlayEq : (layer y).1 = (layer x).1 := by
    simpa using congrArg layerOf hpartEq
  have hyLevel := Decomposition.mem_levels_layerIndex H hd hdeg y
  rw [← hlayer y, hlayEq] at hyLevel
  exact hyLevel

theorem pow_mul_partVertices_card_le
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (x : Fin n) :
    2 ^ (layer x).1 * (RandomGreedy.partVertices (part layer c) x).card ≤ n := by
  calc
    2 ^ (layer x).1 * (RandomGreedy.partVertices (part layer c) x).card ≤
        2 ^ (layer x).1 * (Decomposition.levels H d (layer x).1).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card
        (partVertices_subset_level H hd hdeg layer c hlayer x))
    _ ≤ Fintype.card (Fin n) :=
      Decomposition.pow_mul_card_levels_le H hd hdeg (layer x).1
    _ = n := Fintype.card_fin n

end
end TargetParts
end Erdos163
