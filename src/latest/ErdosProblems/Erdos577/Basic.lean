import Mathlib

/-!
# Four-cycle packings for Erdős Problem 577

The cycles are copies, not induced embeddings, of Mathlib's four-cycle.
A packing uses one injective map from `Fin k × Fin 4`, so distinctness
within cycles and disjointness between cycles are both explicit.
-/

namespace Erdos577

open Finset Function
open scoped BigOperators

variable {V W : Type*}

/-- An ordinary, not necessarily induced, cycle on four distinct vertices. -/
abbrev Quadrilateral (G : SimpleGraph V) := (SimpleGraph.cycleGraph 4).Copy G

lemma cycleGraph_four_adj_iff (i j : Fin 4) :
    (SimpleGraph.cycleGraph 4).Adj i j ↔ i = j + 1 ∨ j = i + 1 := by
  rw [SimpleGraph.cycleGraph_adj]
  simp only [sub_eq_iff_eq_add']

namespace Quadrilateral

/-- Construct a graph copy from an injective cyclically adjacent tuple. -/
def ofEdges {G : SimpleGraph V} (v : Fin 4 ↪ V)
    (h : ∀ i, G.Adj (v i) (v (i + 1))) : Quadrilateral G where
  toHom := {
    toFun := v
    map_rel' := by
      intro i j hij
      rcases (cycleGraph_four_adj_iff i j).mp hij with hij | hij
      · subst i
        exact (h j).symm
      · subst j
        exact h i }
  injective' := v.injective

lemma adjacent {G : SimpleGraph V} (q : Quadrilateral G) (i : Fin 4) :
    G.Adj (q i) (q (i + 1)) :=
  q.toHom.map_rel' ((cycleGraph_four_adj_iff i (i + 1)).mpr (Or.inr rfl))

/-- An explicit ordered witness, useful for the local exchange lemmas. -/
def ofVertices {G : SimpleGraph V} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eab : G.Adj a b) (ebc : G.Adj b c) (ecd : G.Adj c d) (eda : G.Adj d a) :
    Quadrilateral G :=
  ofEdges {
    toFun := ![a, b, c, d]
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all } (by
    intro i
    change G.Adj (![a, b, c, d] i) (![a, b, c, d] (i + 1))
    fin_cases i <;> simp_all)

variable [DecidableEq V]

/-- The four vertices of a quadrilateral. -/
def support {G : SimpleGraph V} (q : Quadrilateral G) : Finset V :=
  univ.image q

@[simp] lemma mem_support {G : SimpleGraph V} (q : Quadrilateral G) (v : V) :
    v ∈ q.support ↔ ∃ i, q i = v := by
  simp [support]

@[simp] lemma card_support {G : SimpleGraph V} (q : Quadrilateral G) :
    q.support.card = 4 := by
  have hinj : Injective (q : Fin 4 → V) := q.injective
  rw [support, card_image_of_injective _ hinj]
  simp

end Quadrilateral

/-- A family of `k` pairwise vertex-disjoint cycles of exactly length four. -/
structure Packing (G : SimpleGraph V) (k : ℕ) where
  vertices : Fin k × Fin 4 ↪ V
  adjacent : ∀ i j, G.Adj (vertices (i, j)) (vertices (i, j + 1))

/-- The exact packing conclusion, with no degree or cardinality hidden in it. -/
def HasPacking (G : SimpleGraph V) (k : ℕ) : Prop := Nonempty (Packing G k)

namespace Packing

variable {G H : SimpleGraph V} {k : ℕ}

/-- Recover each individual Mathlib graph copy from a packing. -/
def cycle (p : Packing G k) (i : Fin k) : Quadrilateral G :=
  Quadrilateral.ofEdges {
    toFun := fun j ↦ p.vertices (i, j)
    inj' := fun _ _ h ↦ (Prod.mk.inj (p.vertices.injective h)).2 }
    (p.adjacent i)

/-- Adding graph edges preserves a packing and its actual vertices. -/
def mono (p : Packing G k) (hGH : G ≤ H) : Packing H k where
  vertices := p.vertices
  adjacent i j := hGH (p.adjacent i j)

/-- The empty packing exists on every vertex type, including an empty one. -/
def zero (G : SimpleGraph V) : Packing G 0 where
  vertices := {
    toFun := fun p ↦ p.1.elim0
    inj' := fun p _ _ ↦ p.1.elim0 }
  adjacent i := i.elim0

/-- One four-cycle is a packing with one member. -/
def one (q : Quadrilateral G) : Packing G 1 where
  vertices := {
    toFun := fun p ↦ q p.2
    inj' := by
      intro p s h
      exact Prod.ext (Subsingleton.elim _ _) (q.injective h) }
  adjacent _ j := q.adjacent j

variable [DecidableEq V]

/-- All vertices used by the packing. -/
def support (p : Packing G k) : Finset V := univ.image p.vertices

@[simp] lemma card_support (p : Packing G k) : p.support.card = 4 * k := by
  rw [support, card_image_of_injective _ p.vertices.injective]
  simp [Nat.mul_comm]

lemma disjoint_cycles (p : Packing G k) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (p.cycle i).support (p.cycle j).support := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨a, ha⟩ := (Quadrilateral.mem_support _ _).mp hi
  obtain ⟨b, hb⟩ := (Quadrilateral.mem_support _ _).mp hj
  have he : p.vertices (i, a) = p.vertices (j, b) := ha.trans hb.symm
  exact hij (Prod.mk.inj (p.vertices.injective he)).1

lemma support_eq_univ [Fintype V] (p : Packing G k)
    (hcard : Fintype.card V = 4 * k) : p.support = univ := by
  apply Finset.eq_of_subset_of_card_le (subset_univ _)
  simp [hcard]

end Packing

lemma hasPacking_zero (G : SimpleGraph V) : HasPacking G 0 := ⟨Packing.zero G⟩

lemma hasPacking_mono {G H : SimpleGraph V} {k : ℕ}
    (hGH : G ≤ H) (h : HasPacking G k) : HasPacking H k := by
  obtain ⟨p⟩ := h
  exact ⟨p.mono hGH⟩

section FourVertices

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The four-vertex base case, proved by the two possible neighbors of a nonedge. -/
theorem quadrilateral_of_card_four (hcard : Fintype.card V = 4)
    (hdeg : ∀ v, 2 ≤ G.degree v) : Nonempty (Quadrilateral G) := by
  classical
  by_cases hcomplete : ∀ a b : V, a ≠ b → G.Adj a b
  · let e : Fin 4 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨Quadrilateral.ofEdges e.toEmbedding ?_⟩
    intro i
    apply hcomplete
    intro h
    have hi : i = i + 1 := e.injective h
    fin_cases i <;> simp at hi
  · push Not at hcomplete
    obtain ⟨u, v, huv, hnot⟩ := hcomplete
    let s : Finset V := univ \ {u, v}
    have hs : s.card = 2 := by
      simp [s, card_sdiff_of_subset (subset_univ _), huv, hcard]
    have hNu : G.neighborFinset u ⊆ s := by
      intro w hw
      have hadj : G.Adj u w := (G.mem_neighborFinset _ _).mp hw
      simp only [s, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact G.irrefl hadj
      · exact hnot hadj
    have hNv : G.neighborFinset v ⊆ s := by
      intro w hw
      have hadj : G.Adj v w := (G.mem_neighborFinset _ _).mp hw
      simp only [s, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact hnot hadj.symm
      · exact G.irrefl hadj
    have heu : G.neighborFinset u = s :=
      eq_of_subset_of_card_le hNu (by rw [hs]; exact hdeg u)
    have hev : G.neighborFinset v = s :=
      eq_of_subset_of_card_le hNv (by rw [hs]; exact hdeg v)
    obtain ⟨a, b, hab, hsab⟩ := card_eq_two.mp hs
    have ha : a ∈ s := by simp [hsab]
    have hb : b ∈ s := by simp [hsab]
    have hau : a ≠ u := by
      have := (mem_sdiff.mp ha).2
      simp only [mem_insert, mem_singleton, not_or] at this
      exact this.1
    have hbu : b ≠ u := by
      have := (mem_sdiff.mp hb).2
      simp only [mem_insert, mem_singleton, not_or] at this
      exact this.1
    have hav : a ≠ v := by
      have := (mem_sdiff.mp ha).2
      simp only [mem_insert, mem_singleton, not_or] at this
      exact this.2
    have hbv : b ≠ v := by
      have := (mem_sdiff.mp hb).2
      simp only [mem_insert, mem_singleton, not_or] at this
      exact this.2
    have eua : G.Adj u a := (G.mem_neighborFinset _ _).mp (heu.symm ▸ ha)
    have eub : G.Adj u b := (G.mem_neighborFinset _ _).mp (heu.symm ▸ hb)
    have eva : G.Adj v a := (G.mem_neighborFinset _ _).mp (hev.symm ▸ ha)
    have evb : G.Adj v b := (G.mem_neighborFinset _ _).mp (hev.symm ▸ hb)
    exact ⟨Quadrilateral.ofVertices u a v b hau.symm huv hbu.symm hav hab hbv.symm
      eua eva.symm evb eub.symm⟩

theorem hasPacking_one (hcard : Fintype.card V = 4)
    (hdeg : ∀ v, 2 ≤ G.degree v) : HasPacking G 1 := by
  obtain ⟨q⟩ := quadrilateral_of_card_four G hcard hdeg
  exact ⟨Packing.one q⟩

end FourVertices

end Erdos577
