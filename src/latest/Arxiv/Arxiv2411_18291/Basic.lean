import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Hypergraphs, clique decompositions, and integral decompositions

Definitions from Sections 1 and 3 of Peter Keevash, *A short proof of the
existence of designs*, arXiv:2411.18291.

An `r`-graph on `V` is a finite set of `r`-element subsets of `V`. A clique
is represented by its vertex set. `IsDecomposition` requires its incidence
vector to equal the graph's characteristic vector, with integer coefficients;
it does not assume the existence of a design.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

/-- The `k`-element subsets of a vertex type. -/
abbrev Block (V : Type*) (k : ℕ) := {s : Finset V // s.card = k}

/-- An `r`-uniform hypergraph on `V`, identified with its edge set. -/
abbrev Hypergraph (V : Type*) (r : ℕ) := Finset (Block V r)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- The complete `r`-graph. -/
def complete (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : Hypergraph V r :=
  univ

/-- The edges of the complete `r`-graph on the vertex set `Q`. -/
def cliqueEdges (r : ℕ) (Q : Block V q) : Hypergraph V r :=
  univ.filter fun e => e.val ⊆ Q.val

@[simp] theorem mem_cliqueEdges (e : Block V r) (Q : Block V q) :
    e ∈ cliqueEdges r Q ↔ e.val ⊆ Q.val := by
  simp [cliqueEdges]

/-- The integer characteristic vector of a finite set. -/
def indicator {α : Type*} [DecidableEq α] (s : Finset α) (a : α) : ℤ :=
  if a ∈ s then 1 else 0

@[simp] theorem indicator_empty {α : Type*} [DecidableEq α] :
    indicator (∅ : Finset α) = 0 := by
  funext a
  simp [indicator]

@[simp] theorem indicator_apply_of_mem {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (h : a ∈ s) : indicator s a = 1 := if_pos h

@[simp] theorem indicator_apply_of_notMem {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (h : a ∉ s) : indicator s a = 0 := if_neg h

theorem indicator_union {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : Disjoint s t) : indicator (s ∪ t) = indicator s + indicator t := by
  funext a
  have ha : a ∈ s → a ∉ t := fun hs ht => Finset.disjoint_left.mp h hs ht
  simp only [indicator, Pi.add_apply, mem_union]
  split_ifs <;> simp_all

theorem indicator_sdiff {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : t ⊆ s) : indicator (s \ t) = indicator s - indicator t := by
  funext a
  have ha : a ∈ t → a ∈ s := fun ht => h ht
  simp only [indicator, Pi.sub_apply, mem_sdiff]
  split_ifs <;> simp_all

/-- The clique-to-edge incidence operator `∂`, with coefficients in an
arbitrary additive commutative monoid. -/
def boundary {R : Type*} [AddCommMonoid R] (r : ℕ)
    (Φ : Block V q → R) (e : Block V r) : R :=
  ∑ Q, if e.val ⊆ Q.val then Φ Q else 0

@[simp] theorem boundary_zero {R : Type*} [AddCommMonoid R] :
    boundary (V := V) (q := q) r (0 : Block V q → R) = 0 := by
  funext e
  simp [boundary]

@[simp] theorem boundary_add {R : Type*} [AddCommMonoid R]
    (Φ Ψ : Block V q → R) :
    boundary r (Φ + Ψ) = boundary r Φ + boundary r Ψ := by
  funext e
  simp only [boundary, Pi.add_apply]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro Q _
  split_ifs <;> simp

@[simp] theorem boundary_neg {R : Type*} [AddCommGroup R]
    (Φ : Block V q → R) : boundary r (-Φ) = -boundary r Φ := by
  funext e
  simp only [boundary, Pi.neg_apply]
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro Q _
  split_ifs <;> simp

@[simp] theorem boundary_sub {R : Type*} [AddCommGroup R]
    (Φ Ψ : Block V q → R) :
    boundary r (Φ - Ψ) = boundary r Φ - boundary r Ψ := by
  simp only [sub_eq_add_neg, boundary_add, boundary_neg]

/-- Signed edge vectors in the integer image of the incidence operator. -/
def IntegrallyDecomposable (q : ℕ) (J : Block V r → ℤ) : Prop :=
  ∃ Φ : Block V q → ℤ, boundary r Φ = J

/-- The paper's definition of `K_q^r`-divisibility. The witnessing cliques may
use any vertices in the ambient complete graph. -/
def Divisible (q : ℕ) (G : Hypergraph V r) : Prop :=
  IntegrallyDecomposable q (indicator G)

/-- A true clique decomposition uses a set of cliques, each with coefficient
one, and covers every edge of `G` exactly once and all other edges zero times. -/
def IsDecomposition (G : Hypergraph V r) (D : Finset (Block V q)) : Prop :=
  boundary r (indicator D) = indicator G

/-- Existence of a true `K_q^r`-decomposition. -/
def HasDecomposition (q : ℕ) (G : Hypergraph V r) : Prop :=
  ∃ D : Finset (Block V q), IsDecomposition G D

theorem IntegrallyDecomposable.zero :
    IntegrallyDecomposable (V := V) (r := r) q 0 :=
  ⟨0, boundary_zero⟩

theorem IntegrallyDecomposable.add {J K : Block V r → ℤ}
    (hJ : IntegrallyDecomposable q J) (hK : IntegrallyDecomposable q K) :
    IntegrallyDecomposable q (J + K) := by
  obtain ⟨Φ, rfl⟩ := hJ
  obtain ⟨Ψ, rfl⟩ := hK
  exact ⟨Φ + Ψ, boundary_add Φ Ψ⟩

theorem IntegrallyDecomposable.sub {J K : Block V r → ℤ}
    (hJ : IntegrallyDecomposable q J) (hK : IntegrallyDecomposable q K) :
    IntegrallyDecomposable q (J - K) := by
  obtain ⟨Φ, rfl⟩ := hJ
  obtain ⟨Ψ, rfl⟩ := hK
  exact ⟨Φ - Ψ, boundary_sub Φ Ψ⟩

theorem Divisible.empty : Divisible (V := V) (r := r) q ∅ := by
  simpa [Divisible] using (IntegrallyDecomposable.zero (V := V) (r := r) (q := q))

theorem Divisible.union {G H : Hypergraph V r} (hG : Divisible q G)
    (hH : Divisible q H) (h : Disjoint G H) : Divisible q (G ∪ H) := by
  simpa [Divisible, indicator_union h] using hG.add hH

theorem Divisible.sdiff {G H : Hypergraph V r} (hG : Divisible q G)
    (hH : Divisible q H) (h : H ⊆ G) : Divisible q (G \ H) := by
  simpa [Divisible, indicator_sdiff h] using hG.sub hH

theorem IsDecomposition.divisible {G : Hypergraph V r} {D : Finset (Block V q)}
    (h : IsDecomposition G D) : Divisible q G := ⟨indicator D, h⟩

theorem HasDecomposition.divisible {G : Hypergraph V r}
    (h : HasDecomposition q G) : Divisible q G := by
  obtain ⟨D, hD⟩ := h
  exact hD.divisible

theorem boundary_indicator (D : Finset (Block V q)) (e : Block V r) :
    boundary r (indicator D) e = ((D.filter fun Q => e.val ⊆ Q.val).card : ℤ) := by
  simp only [boundary, indicator, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext Q
  simp [and_comm]

/-- A direct cardinality characterization of the incidence-vector definition. -/
theorem isDecomposition_iff (G : Hypergraph V r) (D : Finset (Block V q)) :
    IsDecomposition G D ↔
      ∀ e : Block V r,
        (D.filter fun Q => e.val ⊆ Q.val).card = if e ∈ G then 1 else 0 := by
  simp only [IsDecomposition, funext_iff, boundary_indicator, indicator]
  constructor <;> intro h e <;> specialize h e
  · split_ifs at h ⊢ <;> exact_mod_cast h
  · split_ifs at h ⊢ <;> exact_mod_cast h

end Arxiv2411_18291
