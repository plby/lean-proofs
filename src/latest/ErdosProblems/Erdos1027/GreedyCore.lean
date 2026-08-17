/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Prod.Lex

/-!
# The finite greedy recolouring kernel

This file isolates the deterministic part of the Duraj--Gutowski--Kozik
random-greedy recolouring.  Once the initial colouring and the random
priorities have been fixed, ties are broken by a linear order on the vertices.

The selected vertices form a transversal of all initially monochromatic
edges.  Moreover, every selected vertex has a *reason edge*: an initially
monochromatic edge on which it is the largest-priority vertex and the only
selected vertex.  The proof below is a finite greedy proof.  It repeatedly
chooses an unhit edge whose key-maximum is as small as possible, selects that
maximum, and removes the edges which it hits.

Empty initially monochromatic edges have to be excluded: no set can intersect
an empty edge.  In the application to Problem 1027 all edges have the same
positive cardinality.
-/

namespace Erdos1027.GreedyCore

open Finset

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

/-- The priority key.  Its second coordinate breaks priority ties. -/
def key {α : Type*} (priority : α → ℕ) (v : α) : ℕ ×ₗ α :=
  toLex (priority v, v)

/-- `v` is the (unique) largest-key vertex of `E`. -/
def IsKeyMaximum {α : Type*} [LinearOrder α]
    (priority : α → ℕ) (E : Finset α) (v : α) : Prop :=
  v ∈ E ∧ ∀ w ∈ E, key priority w ≤ key priority v

/-- An edge is monochromatic in the initial Boolean colouring. -/
def InitiallyMonochromatic {α : Type*} [DecidableEq α]
    (initial : α → Bool) (E : Finset α) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, initial x = initial y

lemma key_injective {α : Type*} (priority : α → ℕ) :
    Function.Injective (key priority) := by
  intro x y h
  exact congrArg (fun q : ℕ ×ₗ α ↦ (ofLex q).2) h

/-- Every nonempty finite edge has a key-maximum. -/
lemma exists_keyMaximum {α : Type*} [LinearOrder α]
    (priority : α → ℕ) {E : Finset α} (hE : E.Nonempty) :
    ∃ v, IsKeyMaximum priority E v := by
  obtain ⟨v, hvE, hv⟩ := Finset.exists_max_image E (key priority) hE
  exact ⟨v, hvE, hv⟩

/-- All pairs consisting of an edge and its key-maximum.  The redundant
`biUnion` factor gives a finite ambient set of possible second coordinates. -/
private noncomputable def topPairs {α : Type*} [LinearOrder α]
    (priority : α → ℕ) (G : Hypergraph α) : Finset (Finset α × α) := by
  classical
  exact (G.product (G.biUnion id)).filter fun q ↦
    IsKeyMaximum priority q.1 q.2

private lemma mem_topPairs {α : Type*} [LinearOrder α]
    {priority : α → ℕ} {G : Hypergraph α} {E : Finset α} {v : α} :
    (E, v) ∈ topPairs priority G ↔ E ∈ G ∧ IsKeyMaximum priority E v := by
  classical
  constructor
  · intro h
    unfold topPairs at h
    obtain ⟨hprod, hmax⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_product.mp hprod).1, hmax⟩
  · rintro ⟨hEG, hmax⟩
    unfold topPairs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hEG, ?_⟩, hmax⟩
    exact Finset.mem_biUnion.mpr ⟨E, hEG, hmax.1⟩

private lemma topPairs_nonempty {α : Type*} [LinearOrder α]
    (priority : α → ℕ) {G : Hypergraph α} (hG : G.Nonempty)
    (hne : ∀ E ∈ G, E.Nonempty) :
    (topPairs priority G).Nonempty := by
  obtain ⟨E, hEG⟩ := hG
  obtain ⟨v, hmax⟩ := exists_keyMaximum priority (hne E hEG)
  exact ⟨(E, v), mem_topPairs.mpr ⟨hEG, hmax⟩⟩

/-- The abstract finite greedy transversal lemma.

It is stated for an arbitrary family `G`; in the recolouring application `G`
is the subfamily of initially monochromatic edges. -/
theorem exists_greedyTransversal {α : Type*} [LinearOrder α]
    (G : Hypergraph α) (priority : α → ℕ)
    (hne : ∀ E ∈ G, E.Nonempty) :
    ∃ S : Finset α,
      (∀ v ∈ S, ∃ E ∈ G,
        IsKeyMaximum priority E v ∧ E ∩ S = {v}) ∧
      (∀ E ∈ G, (E ∩ S).Nonempty) := by
  classical
  generalize hn : G.card = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hG0 : G = ∅
      · subst G
        exact ⟨∅, by simp⟩
      · have hG : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hG0
        obtain ⟨q, hq, hqmin⟩ :=
          Finset.exists_min_image (topPairs priority G)
            (fun q ↦ key priority q.2) (topPairs_nonempty priority hG hne)
        rcases q with ⟨E₀, v⟩
        have hE₀ : E₀ ∈ G := (mem_topPairs.mp hq).1
        have hmax₀ : IsKeyMaximum priority E₀ v := (mem_topPairs.mp hq).2
        let G' : Hypergraph α := G.filter fun E ↦ v ∉ E
        have hG'sub : G' ⊆ G := Finset.filter_subset _ _
        have hG'ne : G' ≠ G := by
          intro heq
          have : E₀ ∈ G' := heq.symm ▸ hE₀
          exact (Finset.mem_filter.mp this).2 hmax₀.1
        have hG'ss : G' ⊂ G :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hG'sub, hG'ne⟩
        have hG'card : G'.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hG'ss
        have hne' : ∀ E ∈ G', E.Nonempty := by
          intro E hE
          exact hne E (hG'sub hE)
        obtain ⟨S', hreason', hhit'⟩ := ih G'.card hG'card G' hne' rfl
        have hvS' : v ∉ S' := by
          intro hv
          obtain ⟨F, hFG', hmaxF, -⟩ := hreason' v hv
          exact (Finset.mem_filter.mp hFG').2 hmaxF.1
        have hE₀S' : Disjoint E₀ S' := by
          rw [Finset.disjoint_left]
          intro w hwE₀ hwS'
          obtain ⟨F, hFG', hmaxF, -⟩ := hreason' w hwS'
          have hFG : F ∈ G := hG'sub hFG'
          have hpairF : (F, w) ∈ topPairs priority G :=
            mem_topPairs.mpr ⟨hFG, hmaxF⟩
          have hvw : key priority v ≤ key priority w := hqmin (F, w) hpairF
          have hwv : key priority w ≤ key priority v := hmax₀.2 w hwE₀
          have hw_eq_v : w = v :=
            key_injective priority (le_antisymm hwv hvw)
          subst w
          exact hvS' hwS'
        refine ⟨insert v S', ?_, ?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwS'
          · refine ⟨E₀, hE₀, hmax₀, ?_⟩
            ext x
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hxE₀, rfl | hxS'⟩
              · rfl
              · exact (Finset.disjoint_left.mp hE₀S' hxE₀ hxS').elim
            · rintro rfl
              exact ⟨hmax₀.1, Or.inl rfl⟩
          · obtain ⟨F, hFG', hmaxF, hFS'⟩ := hreason' w hwS'
            refine ⟨F, hG'sub hFG', hmaxF, ?_⟩
            have hvF : v ∉ F := (Finset.mem_filter.mp hFG').2
            rw [Finset.inter_insert_of_notMem hvF, hFS']
        · intro E hEG
          by_cases hvE : v ∈ E
          · exact ⟨v, Finset.mem_inter.mpr ⟨hvE, Finset.mem_insert_self _ _⟩⟩
          · have hEG' : E ∈ G' := Finset.mem_filter.mpr ⟨hEG, hvE⟩
            obtain ⟨w, hw⟩ := hhit' E hEG'
            exact ⟨w, Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hw).1,
                Finset.mem_insert_of_mem (Finset.mem_inter.mp hw).2⟩⟩

/-- The deterministic flip-set conclusion used in random-greedy recolouring.

Every selected vertex has an initially monochromatic reason edge on which it
is the key-maximum and the sole selected vertex, and every initially
monochromatic edge is hit. -/
theorem exists_flipSet {α : Type*} [LinearOrder α]
    (H : Hypergraph α) (initial : α → Bool) (priority : α → ℕ)
    (hne : ∀ E ∈ H, InitiallyMonochromatic initial E → E.Nonempty) :
    ∃ S : Finset α,
      (∀ v ∈ S, ∃ E ∈ H,
        InitiallyMonochromatic initial E ∧
        IsKeyMaximum priority E v ∧ E ∩ S = {v}) ∧
      (∀ E ∈ H, InitiallyMonochromatic initial E → (E ∩ S).Nonempty) := by
  classical
  let G : Hypergraph α := H.filter (InitiallyMonochromatic initial)
  have hneG : ∀ E ∈ G, E.Nonempty := by
    intro E hEG
    obtain ⟨hEH, hmono⟩ := Finset.mem_filter.mp hEG
    exact hne E hEH hmono
  obtain ⟨S, hreason, hhit⟩ := exists_greedyTransversal G priority hneG
  refine ⟨S, ?_, ?_⟩
  · intro v hv
    obtain ⟨E, hEG, hmax, hsingle⟩ := hreason v hv
    obtain ⟨hEH, hmono⟩ := Finset.mem_filter.mp hEG
    exact ⟨E, hEH, hmono, hmax, hsingle⟩
  · intro E hEH hmono
    exact hhit E (Finset.mem_filter.mpr ⟨hEH, hmono⟩)

end Erdos1027.GreedyCore
