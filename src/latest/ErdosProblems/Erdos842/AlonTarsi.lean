import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The Alon--Tarsi step for Erdős Problem 842

This file isolates the algebraic part of the cycle-plus-triangles argument.  An
edge occurrence has a tail and a head; distinct occurrences are deliberately
not quotiented, so the construction also applies when a Hamiltonian-cycle edge
coincides with a triangle edge.

The main result, `coloring_of_coeff_ne_zero`, says that a suitable nonzero
top-degree coefficient of the indexed graph polynomial produces a coloring of
the simple support with three colors.  The difficult parity argument proving
that the coefficient in the cycle-plus-triangles case is nonzero belongs in a
separate file.
-/

open scoped BigOperators

namespace Erdos842

open Finsupp MvPolynomial

universe u v

section Definitions

variable {V : Type u} {A : Type v}

/-- The graph polynomial of a family of directed edge occurrences. -/
noncomputable def occurrencePolynomial [Fintype A] (tail head : A → V) : MvPolynomial V ℤ :=
  ∏ a : A, (X (tail a) - X (head a))

/-- The simple graph supported by a family of directed edge occurrences.

`SimpleGraph.fromRel` both symmetrizes the relation and removes loops. -/
def occurrenceSupport (tail head : A → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ ∃ a, tail a = x ∧ head a = y

/-- The exponent which assigns exponent two to every vertex. -/
noncomputable def centralExponent [Fintype V] [DecidableEq V] : V →₀ ℕ :=
  ∑ x : V, single x 2

@[simp]
theorem centralExponent_apply [Fintype V] [DecidableEq V] (x : V) :
    centralExponent (V := V) x = 2 := by
  simp [centralExponent]

theorem centralExponent_degree [Fintype V] [DecidableEq V] :
    (centralExponent (V := V)).degree = 2 * Fintype.card V := by
  rw [Finsupp.degree_eq_sum]
  simp [centralExponent_apply, mul_comm]

@[simp]
theorem occurrenceSupport_adj (tail head : A → V) (x y : V) :
    (occurrenceSupport tail head).Adj x y ↔
      x ≠ y ∧
        ((∃ a, tail a = x ∧ head a = y) ∨
          ∃ a, tail a = y ∧ head a = x) := by
  simp [occurrenceSupport, SimpleGraph.fromRel_adj]

theorem occurrenceSupport_adj_of_occurrence (tail head : A → V) (a : A)
    (hne : tail a ≠ head a) :
    (occurrenceSupport tail head).Adj (tail a) (head a) := by
  rw [occurrenceSupport_adj]
  exact ⟨hne, Or.inl ⟨a, rfl, rfl⟩⟩

end Definitions

section PolynomialFacts

variable {V : Type u} {A : Type v} [Fintype A]

@[simp]
theorem eval_occurrencePolynomial (tail head : A → V) (color : V → ℤ) :
    eval color (occurrencePolynomial tail head) =
      ∏ a : A, (color (tail a) - color (head a)) := by
  simp [occurrencePolynomial]

theorem occurrencePolynomial_totalDegree_le_card (tail head : A → V) :
    (occurrencePolynomial tail head).totalDegree ≤ Fintype.card A := by
  classical
  calc
    (occurrencePolynomial tail head).totalDegree ≤
        ∑ a ∈ Finset.univ, (X (tail a) - X (head a) : MvPolynomial V ℤ).totalDegree := by
          simpa only [occurrencePolynomial] using
            MvPolynomial.totalDegree_finsetProd Finset.univ
              (fun a ↦ (X (tail a) - X (head a) : MvPolynomial V ℤ))
    _ ≤ ∑ _a : A, 1 := by
      apply Finset.sum_le_sum
      intro a _
      simpa using
        (MvPolynomial.totalDegree_sub
          (X (tail a) : MvPolynomial V ℤ) (X (head a) : MvPolynomial V ℤ))
    _ = Fintype.card A := by simp

theorem degree_le_totalDegree_of_coeff_ne_zero {p : MvPolynomial V ℤ} {t : V →₀ ℕ}
    (ht : p.coeff t ≠ 0) : t.degree ≤ p.totalDegree := by
  classical
  rw [Finsupp.degree_apply]
  exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr ht)

theorem occurrencePolynomial_totalDegree_eq_degree
    (tail head : A → V) (t : V →₀ ℕ)
    (hdegree : t.degree = Fintype.card A)
    (hcoeff : (occurrencePolynomial tail head).coeff t ≠ 0) :
    (occurrencePolynomial tail head).totalDegree = t.degree := by
  apply Nat.le_antisymm
  · simpa only [hdegree] using occurrencePolynomial_totalDegree_le_card tail head
  · exact degree_le_totalDegree_of_coeff_ne_zero hcoeff

theorem endpoint_ne_of_eval_occurrencePolynomial_ne_zero
    (tail head : A → V) (color : V → ℤ)
    (hcolor : eval color (occurrencePolynomial tail head) ≠ 0) (a : A) :
    color (tail a) ≠ color (head a) := by
  intro h
  apply hcolor
  rw [eval_occurrencePolynomial]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [h]

theorem eval_occurrencePolynomial_ne_zero_iff
    (tail head : A → V) (color : V → ℤ) :
    eval color (occurrencePolynomial tail head) ≠ 0 ↔
      ∀ a, color (tail a) ≠ color (head a) := by
  constructor
  · exact fun h a ↦ endpoint_ne_of_eval_occurrencePolynomial_ne_zero tail head color h a
  · intro h
    rw [eval_occurrencePolynomial, Finset.prod_ne_zero_iff]
    intro a _
    exact sub_ne_zero.mpr (h a)

end PolynomialFacts

section Nullstellensatz

variable {V : Type u} {A : Type v}
variable [Fintype V] [Fintype A]

/-- A nonzero top-degree coefficient with every exponent below three gives a
three-coloring of the simple support of the edge occurrences. -/
theorem coloring_of_coeff_ne_zero
    (tail head : A → V) (t : V →₀ ℕ)
    (hdegree : t.degree = Fintype.card A)
    (hexponent : ∀ x, t x < 3)
    (hcoeff : (occurrencePolynomial tail head).coeff t ≠ 0) :
    (occurrenceSupport tail head).Colorable 3 := by
  classical
  let palette : Finset ℤ := {0, 1, 2}
  have palette_card : palette.card = 3 := by
    simp [palette]
  let paletteEquiv : palette ≃ Fin 3 := palette.equivFinOfCardEq palette_card
  have htotal : (occurrencePolynomial tail head).totalDegree = t.degree :=
    occurrencePolynomial_totalDegree_eq_degree tail head t hdegree hcoeff
  obtain ⟨color, color_mem, color_ne⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      (occurrencePolynomial tail head) t hcoeff htotal (fun _ ↦ palette) (by
        intro x
        simp [palette, hexponent x])
  let finiteColor : V → Fin 3 := fun x ↦ paletteEquiv ⟨color x, color_mem x⟩
  refine ⟨SimpleGraph.Coloring.mk finiteColor ?_⟩
  intro x y hxy
  rw [occurrenceSupport_adj] at hxy
  obtain ⟨_, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩ := hxy
  · subst x
    subst y
    intro h
    have hsubtype :
        (⟨color (tail a), color_mem (tail a)⟩ : palette) =
          ⟨color (head a), color_mem (head a)⟩ := paletteEquiv.injective h
    exact (endpoint_ne_of_eval_occurrencePolynomial_ne_zero tail head color color_ne a)
      (congrArg Subtype.val hsubtype)
  · subst x
    subst y
    intro h
    have hsubtype :
        (⟨color (head a), color_mem (head a)⟩ : palette) =
          ⟨color (tail a), color_mem (tail a)⟩ := paletteEquiv.injective h
    exact (endpoint_ne_of_eval_occurrencePolynomial_ne_zero tail head color color_ne a)
      (congrArg Subtype.val hsubtype).symm

/-- Central-coefficient specialization of `coloring_of_coeff_ne_zero` for a
two-outgoing-occurrences-per-vertex family. -/
theorem coloring_of_centralCoeff_ne_zero
    [DecidableEq V]
    (tail head : A → V)
    (hcard : Fintype.card A = 2 * Fintype.card V)
    (hcoeff :
      (occurrencePolynomial tail head).coeff (centralExponent (V := V)) ≠ 0) :
    (occurrenceSupport tail head).Colorable 3 := by
  apply coloring_of_coeff_ne_zero tail head (centralExponent (V := V))
  · rw [centralExponent_degree, hcard]
  · intro x
    simp
  · exact hcoeff

/-- Any simple graph contained in the occurrence support inherits the
three-coloring supplied by the nonzero coefficient. -/
theorem subgraph_colorable_of_coeff_ne_zero
    (G : SimpleGraph V) (tail head : A → V) (t : V →₀ ℕ)
    (hG : G ≤ occurrenceSupport tail head)
    (hdegree : t.degree = Fintype.card A)
    (hexponent : ∀ x, t x < 3)
    (hcoeff : (occurrencePolynomial tail head).coeff t ≠ 0) :
    G.Colorable 3 :=
  SimpleGraph.Colorable.mono_left hG
    (coloring_of_coeff_ne_zero tail head t hdegree hexponent hcoeff)

end Nullstellensatz

end Erdos842
