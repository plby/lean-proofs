/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Basic
import Mathlib

/-!
# Erdős Problem 163: geometric decomposition of a degenerate target

This file proves the deterministic target-graph preparation used in Lee's
embedding argument.  Repeatedly retain the vertices having at least `4*d`
neighbors in the current set.  Degeneracy and the handshaking identity imply
that the retained set has at most half the vertices.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace Decomposition

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Degree of `x` into the finite vertex set `S`. -/
def degreeIn (H : SimpleGraph α) [DecidableRel H.Adj]
    (S : Finset α) (x : α) : ℕ :=
  (S.filter fun y => H.Adj x y).card

@[simp] theorem degreeIn_empty (H : SimpleGraph α) [DecidableRel H.Adj] (x : α) :
    degreeIn H ∅ x = 0 := by
  simp [degreeIn]

theorem degreeIn_mono (H : SimpleGraph α) [DecidableRel H.Adj]
    {S T : Finset α} (hST : S ⊆ T) (x : α) :
    degreeIn H S x ≤ degreeIn H T x := by
  exact card_le_card (filter_subset_filter _ hST)

/-- The induced-graph degree is the elementary filtered degree used in the
definition of degeneracy. -/
theorem degree_induce_finset (H : SimpleGraph α) [DecidableRel H.Adj]
    (S : Finset α) (x : S) :
    (H.induce (S : Set α)).degree x = degreeIn H S x := by
  classical
  unfold SimpleGraph.degree SimpleGraph.neighborFinset degreeIn
  rw [Set.toFinset_card, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun y => ⟨y.1.1, Finset.mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y =>
        ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩, (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun y => by ext; rfl }

/-- Removing one vertex from an induced graph gives the induced graph on the
erased finset, up to the canonical equivalence of the two nested subtypes. -/
noncomputable def eraseInduceIso (H : SimpleGraph α) [DecidableRel H.Adj]
    (S : Finset α) {x : α} (hx : x ∈ S) :
    (H.induce (S : Set α)).induce ({(⟨x, hx⟩ : S)}ᶜ) ≃g
      H.induce ((S.erase x : Finset α) : Set α) where
  toEquiv :=
    { toFun := fun y => ⟨y.1.1, by
        have hyS : y.1.1 ∈ S := y.1.2
        have hyx : y.1.1 ≠ x := by
          intro h
          apply y.2
          simpa [Set.mem_singleton_iff, Subtype.ext_iff] using h
        exact Finset.mem_erase.mpr ⟨hyx, hyS⟩⟩
      invFun := fun y => ⟨⟨y.1, (Finset.mem_erase.mp y.2).2⟩, by
        have hyx : y.1 ≠ x := (Finset.mem_erase.mp y.2).1
        simpa [Set.mem_singleton_iff, Subtype.ext_iff] using hyx⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun y => by ext; rfl }
  map_rel_iff' := by
    intro a b
    rfl

/-- A `d`-degenerate graph has at most `d|S|` edges in every induced vertex
set `S`. -/
theorem card_induced_edges_le (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (hdeg : IsDegenerateAtMost H d) (S : Finset α) :
    #(H.induce (S : Set α)).edgeFinset ≤ d * S.card := by
  classical
  exact Finset.strongInduction
    (p := fun S => #(H.induce (S : Set α)).edgeFinset ≤ d * S.card)
    (fun S ih => by
      by_cases hS : S.Nonempty
      · obtain ⟨x, hxS, hxdeg⟩ := hdeg S hS
        let K := H.induce (S : Set α)
        let xs : S := ⟨x, hxS⟩
        have hdegree : K.degree xs ≤ d := by
          change (H.induce (S : Set α)).degree xs ≤ d
          rw [degree_induce_finset]
          unfold degreeIn
          change #(@Finset.filter α (fun y => H.Adj x y)
            (fun y => Classical.propDecidable (H.Adj x y)) S) ≤ d at hxdeg
          have hfilter :
              S.filter (fun y => H.Adj x y) =
                @Finset.filter α (fun y => H.Adj x y)
                  (fun y => Classical.propDecidable (H.Adj x y)) S := by
            ext y
            simp
          rw [hfilter]
          exact hxdeg
        have hdel :
            #(K.induce ({xs}ᶜ : Set S)).edgeFinset =
              #K.edgeFinset - K.degree xs := by
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet]
        have hiso :
            #(K.induce ({xs}ᶜ : Set S)).edgeFinset =
              #(H.induce ((S.erase x : Finset α) : Set α)).edgeFinset := by
          exact (eraseInduceIso H S hxS).card_edgeFinset_eq
        have hrest :
            #(H.induce ((S.erase x : Finset α) : Set α)).edgeFinset ≤
              d * (S.erase x).card :=
          ih (S.erase x) (Finset.erase_ssubset hxS)
        have hdegree_edges : K.degree xs ≤ #K.edgeFinset :=
          K.degree_le_card_edgeFinset xs
        have hsplit :
            #K.edgeFinset =
              #(H.induce ((S.erase x : Finset α) : Set α)).edgeFinset + K.degree xs := by
          rw [← hiso, hdel, Nat.sub_add_cancel hdegree_edges]
        change #K.edgeFinset ≤ d * S.card
        rw [hsplit]
        calc
          #(H.induce ((S.erase x : Finset α) : Set α)).edgeFinset + K.degree xs
              ≤ d * (S.erase x).card + d := Nat.add_le_add hrest hdegree
          _ = d * S.card := by
            rw [← Finset.card_erase_add_one hxS, Nat.mul_add]
            simp
      · simp only [Finset.not_nonempty_iff_eq_empty] at hS
        subst S
        change #(H.induce (∅ : Set α)).edgeFinset ≤ d * #(∅ : Finset α)
        have hempty : (H.induce (∅ : Set α)).edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ a b => simp
        rw [hempty]
        simp) S

/-- Handshaking on an induced finset, stated using `degreeIn`. -/
theorem sum_degreeIn_eq_twice_edges (H : SimpleGraph α) [DecidableRel H.Adj]
    (S : Finset α) :
    ∑ x ∈ S, degreeIn H S x = 2 * #(H.induce (S : Set α)).edgeFinset := by
  classical
  rw [← (H.induce (S : Set α)).sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x hx
  exact (degree_induce_finset H S x).symm

/-- Consequently, the degree sum in every vertex subset is at most
`2*d*|S|`. -/
theorem sum_degreeIn_le (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (hdeg : IsDegenerateAtMost H d) (S : Finset α) :
    ∑ x ∈ S, degreeIn H S x ≤ 2 * d * S.card := by
  rw [sum_degreeIn_eq_twice_edges]
  calc
    2 * #(H.induce (S : Set α)).edgeFinset ≤ 2 * (d * S.card) :=
      Nat.mul_le_mul_left 2 (card_induced_edges_le H d hdeg S)
    _ = 2 * d * S.card := by simp [Nat.mul_assoc]

/-- Vertices whose current internal degree is at least `4*d`. -/
def high (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (S : Finset α) : Finset α :=
  S.filter fun x => 4 * d ≤ degreeIn H S x

theorem high_subset (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (S : Finset α) : high H d S ⊆ S :=
  filter_subset _ _

/-- At least half the current vertices disappear at each high-degree pruning
step. -/
theorem twice_card_high_le (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (S : Finset α) :
    2 * (high H d S).card ≤ S.card := by
  classical
  have hlocal : ∀ x ∈ high H d S, 4 * d ≤ degreeIn H S x := by
    simpa [high] using fun x (hx : x ∈ high H d S) => hx
  have hsum_low :
      4 * d * (high H d S).card ≤ ∑ x ∈ S, degreeIn H S x := by
    calc
      4 * d * (high H d S).card =
          ∑ x ∈ high H d S, 4 * d := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ ∑ x ∈ high H d S, degreeIn H S x :=
        Finset.sum_le_sum hlocal
      _ ≤ ∑ x ∈ S, degreeIn H S x :=
        Finset.sum_le_sum_of_subset_of_nonneg (high_subset H d S) (fun _ _ _ => by omega)
  have hbound := hsum_low.trans (sum_degreeIn_le H d hdeg S)
  have hfour :
      4 * d * (high H d S).card =
        (2 * d) * (2 * (high H d S).card) := by ring
  rw [hfour] at hbound
  exact Nat.le_of_mul_le_mul_left hbound (by omega)

/-- The nested filtration obtained by repeatedly retaining the high-degree
vertices. -/
def levels (H : SimpleGraph α) [DecidableRel H.Adj] (d : ℕ) : ℕ → Finset α
  | 0 => Finset.univ
  | i + 1 => high H d (levels H d i)

@[simp] theorem levels_zero (H : SimpleGraph α) [DecidableRel H.Adj] (d : ℕ) :
    levels H d 0 = Finset.univ := rfl

@[simp] theorem levels_succ (H : SimpleGraph α) [DecidableRel H.Adj]
    (d i : ℕ) : levels H d (i + 1) = high H d (levels H d i) := rfl

theorem levels_antitone (H : SimpleGraph α) [DecidableRel H.Adj] (d i : ℕ) :
    levels H d (i + 1) ⊆ levels H d i :=
  high_subset H d _

theorem twice_card_levels_succ_le (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (i : ℕ) :
    2 * (levels H d (i + 1)).card ≤ (levels H d i).card := by
  exact twice_card_high_le H hd hdeg _

/-- Quantitative geometric decay of the filtration. -/
theorem pow_mul_card_levels_le (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (i : ℕ) :
    2 ^ i * (levels H d i).card ≤ Fintype.card α := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc
        2 ^ (i + 1) * (levels H d (i + 1)).card =
            2 ^ i * (2 * (levels H d (i + 1)).card) := by ring
        _ ≤ 2 ^ i * (levels H d i).card :=
          Nat.mul_le_mul_left _ (twice_card_levels_succ_le H hd hdeg i)
        _ ≤ Fintype.card α := ih

/-- Later filtration levels are contained in earlier ones. -/
theorem levels_subset_of_le (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) {i j : ℕ} (hij : i ≤ j) : levels H d j ⊆ levels H d i := by
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j hij ih => exact (levels_antitone H d j).trans ih

/-- The filtration is empty by the ambient cardinality index. -/
theorem levels_card_eq_empty (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) :
    levels H d (Fintype.card α) = ∅ := by
  rw [← Finset.card_eq_zero]
  by_contra hcard
  have hpos : 1 ≤ (levels H d (Fintype.card α)).card :=
    Nat.one_le_iff_ne_zero.mpr hcard
  have hdecay := pow_mul_card_levels_le H hd hdeg (Fintype.card α)
  have hpow : 2 ^ Fintype.card α ≤ Fintype.card α := by
    calc
      2 ^ Fintype.card α = 2 ^ Fintype.card α * 1 := by simp
      _ ≤ 2 ^ Fintype.card α * (levels H d (Fintype.card α)).card :=
        Nat.mul_le_mul_left _ hpos
      _ ≤ Fintype.card α := hdecay
  exact Nat.not_le_of_lt (Fintype.card α).lt_two_pow_self hpow

/-- The bounded search used to assign a pruning layer always has a witness. -/
theorem layerSearch_exists (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (x : α) :
    ∃ i, i = Fintype.card α ∨ x ∉ levels H d (i + 1) :=
  ⟨Fintype.card α, Or.inl rfl⟩

/-- First pruning step at which a vertex disappears, with the ambient
cardinality as a bounded-search sentinel. -/
noncomputable def layerIndex (H : SimpleGraph α) [DecidableRel H.Adj]
    (d : ℕ) (x : α) : ℕ :=
  Nat.find (layerSearch_exists H d x)

theorem exists_not_mem_levels_succ (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (x : α) :
    ∃ i, x ∉ levels H d (i + 1) := by
  refine ⟨Fintype.card α, ?_⟩
  intro hx
  have hsub := levels_subset_of_le H d (Nat.le_succ (Fintype.card α)) hx
  rw [levels_card_eq_empty H hd hdeg] at hsub
  simpa using hsub

theorem layerIndex_spec (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (x : α) :
    x ∉ levels H d (layerIndex H d x + 1) := by
  rcases Nat.find_spec (layerSearch_exists H d x) with hsentinel | hexit
  · rw [layerIndex, hsentinel]
    intro hx
    have hsub := levels_subset_of_le H d (Nat.le_succ (Fintype.card α)) hx
    rw [levels_card_eq_empty H hd hdeg] at hsub
    simpa using hsub
  · exact hexit

theorem layerIndex_le_card (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (x : α) :
    layerIndex H d x ≤ Fintype.card α := by
  exact Nat.find_min' (layerSearch_exists H d x) (Or.inl rfl)

theorem mem_levels_layerIndex (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (x : α) :
    x ∈ levels H d (layerIndex H d x) := by
  let hsearch := layerSearch_exists H d x
  change x ∈ levels H d (Nat.find hsearch)
  cases hfind : Nat.find hsearch with
  | zero => simp
  | succ i =>
      have hi : i < Nat.find hsearch := by omega
      have hmin := Nat.find_min hsearch hi
      exact Classical.not_not.mp (fun hnot => hmin (Or.inr hnot))

/-- A vertex has fewer than `4*d` neighbors whose layer is no earlier than
its own layer.  This is the forward-degree property used by the embedding
algorithm. -/
theorem card_forward_neighbors_lt (H : SimpleGraph α) [DecidableRel H.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d) (x : α) :
    (Finset.univ.filter fun y =>
      H.Adj x y ∧ layerIndex H d x ≤ layerIndex H d y).card < 4 * d := by
  classical
  let i := layerIndex H d x
  have hxi : x ∈ levels H d i := mem_levels_layerIndex H hd hdeg x
  have hxnext : x ∉ levels H d (i + 1) := layerIndex_spec H hd hdeg x
  have hxlow : degreeIn H (levels H d i) x < 4 * d := by
    rw [levels_succ, high] at hxnext
    simp only [Finset.mem_filter, hxi, true_and] at hxnext
    exact Nat.lt_of_not_ge hxnext
  have hsub :
      (Finset.univ.filter fun y => H.Adj x y ∧ i ≤ layerIndex H d y) ⊆
        (levels H d i).filter fun y => H.Adj x y := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hylayer := mem_levels_layerIndex H hd hdeg y
    have hyi := levels_subset_of_le H d hy.2 hylayer
    exact Finset.mem_filter.mpr ⟨hyi, hy.1⟩
  exact (Finset.card_le_card hsub).trans_lt hxlow

end Decomposition
end Erdos163
