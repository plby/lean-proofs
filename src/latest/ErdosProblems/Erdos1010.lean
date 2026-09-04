/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import ErdosProblems.Erdos1010.Counting
import ErdosProblems.Erdos1010.Odd

/-!
# Erdős Problem 1010

The detailed mathematical proof and the formalization plan are in
`tex/1010.tex`. The proof uses finite maximum-cut charge bounds for even
orders and a leaf-switching/deletion reduction for odd orders. The public
theorem `erdos_1010` is at the end of this file. Sound counting and arithmetic
from the earlier development are preserved below; the invalid Goodman-based
lower-bound inference is not used.
-/

open Finset

namespace Erdos1010

noncomputable section

/-! ## Finite-sum and vertex-deletion infrastructure -/

lemma int_sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    (∑ i, z i) ^ 2 ≤ Fintype.card ι * ∑ i, (z i) ^ 2 := by
  simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := z))

/-! ## Goodman's three-vertex double count -/

/-- A mixed wedge consists of a centre, a neighbor in `G`, and a neighbor
of the centre in the complementary graph. -/
def mixedWedges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Σ _ : V, V × V) :=
  Finset.univ.sigma fun v ↦ G.neighborFinset v ×ˢ Gᶜ.neighborFinset v

/-- The unordered three-set supporting a mixed wedge. -/
def wedgeSupport {V : Type*} [DecidableEq V] (w : Σ _ : V, V × V) : Finset V :=
  insert w.1 (insert w.2.1 {w.2.2})

lemma card_mixedWedges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (mixedWedges G).card =
      ∑ v : V, G.degree v * (Fintype.card V - 1 - G.degree v) := by
  classical
  simp [mixedWedges, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.degree_compl]

lemma wedgeSupport_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w : Σ _ : V, V × V}
    (hw : w ∈ mixedWedges G) : (wedgeSupport w).card = 3 := by
  rcases w with ⟨v, u, z⟩
  simp only [mixedWedges, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_product, SimpleGraph.mem_neighborFinset] at hw
  have hwz : ¬G.Adj v z := (show v ≠ z ∧ ¬G.Adj v z by simpa using hw.2).2
  have hvu : v ≠ u := hw.1.ne
  have hvz : v ≠ z := hw.2.ne
  have huz : u ≠ z := by
    intro h
    subst z
    exact hwz hw.1
  simp [wedgeSupport, hvu, hvz, huz]

/-- The three-sets which are triangles in neither `G` nor its complement. -/
def mixedTriples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.powersetCard 3 \ (G.cliqueFinset 3 ∪ Gᶜ.cliqueFinset 3)

lemma wedgeSupport_mem_mixedTriples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w : Σ _ : V, V × V}
    (hw : w ∈ mixedWedges G) : wedgeSupport w ∈ mixedTriples G := by
  have hcard := wedgeSupport_card G hw
  rcases w with ⟨v, u, z⟩
  simp only [mixedWedges, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_product, SimpleGraph.mem_neighborFinset] at hw
  have hwz : ¬G.Adj v z := (show v ≠ z ∧ ¬G.Adj v z by simpa using hw.2).2
  rw [mixedTriples, Finset.mem_sdiff]
  constructor
  · simpa [Finset.mem_powersetCard] using hcard
  rw [Finset.mem_union, not_or]
  constructor
  · intro hcl
    have h := (SimpleGraph.mem_cliqueFinset_iff.mp hcl).isClique
    exact hwz (h (by simp [wedgeSupport]) (by simp [wedgeSupport]) (by
      exact hw.2.ne))
  · intro hcl
    have h := (SimpleGraph.mem_cliqueFinset_iff.mp hcl).isClique
    have hc := h (by simp [wedgeSupport]) (by simp [wedgeSupport]) hw.1.ne
    have hn : ¬G.Adj v u := (show v ≠ u ∧ ¬G.Adj v u by simpa using hc).2
    exact hn hw.1

def wedgesOver {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Finset (Σ _ : V, V × V) :=
  (mixedWedges G).filter fun w ↦ wedgeSupport w = s

private lemma support_eq_triple_iff {V : Type*} [DecidableEq V]
    {v u z a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    wedgeSupport ⟨v, u, z⟩ = {a, b, c} ↔
      (v = a ∧ u = b ∧ z = c) ∨ (v = a ∧ u = c ∧ z = b) ∨
      (v = b ∧ u = a ∧ z = c) ∨ (v = b ∧ u = c ∧ z = a) ∨
      (v = c ∧ u = a ∧ z = b) ∨ (v = c ∧ u = b ∧ z = a) := by
  constructor
  · intro h
    have hv : v = a ∨ v = b ∨ v = c := by
      have : v ∈ ({a, b, c} : Finset V) := by rw [← h]; simp [wedgeSupport]
      simpa using this
    have hu : u = a ∨ u = b ∨ u = c := by
      have : u ∈ ({a, b, c} : Finset V) := by rw [← h]; simp [wedgeSupport]
      simpa using this
    have hz : z = a ∨ z = b ∨ z = c := by
      have : z ∈ ({a, b, c} : Finset V) := by rw [← h]; simp [wedgeSupport]
      simpa using this
    have hcard : ({v, u, z} : Finset V).card = 3 := by
      change (wedgeSupport ⟨v, u, z⟩).card = 3
      rw [h]
      simp [hab, hac, hbc]
    have hvu : v ≠ u := by
      intro hvu
      subst u
      have hle : ({v, v, z} : Finset V).card ≤ 2 := by
        simpa using Finset.card_le_two (a := v) (b := z)
      omega
    have hvz : v ≠ z := by
      intro hvz
      subst z
      have hle : ({v, u, v} : Finset V).card ≤ 2 := by
        simpa using Finset.card_le_two (a := u) (b := v)
      omega
    have huz : u ≠ z := by
      intro huz
      subst z
      have hle : ({v, u, u} : Finset V).card ≤ 2 := by
        simpa using Finset.card_le_two (a := v) (b := u)
      omega
    rcases hv with rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;>
      simp_all [wedgeSupport]
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      ext x <;> simp [wedgeSupport] <;> aesop

lemma card_wedgesOver_of_mem_mixedTriples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    (hs : s ∈ mixedTriples G) : (wedgesOver G s).card = 2 := by
  have hscard : s.card = 3 := by
    have hs' := hs
    rw [mixedTriples, Finset.mem_sdiff] at hs'
    simpa [Finset.mem_powersetCard] using hs'.1
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hscard
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  by_cases eab : G.Adj a b <;> by_cases eac : G.Adj a c <;>
      by_cases ebc : G.Adj b c
  · exfalso
    have hs' := hs
    rw [mixedTriples, Finset.mem_sdiff, Finset.mem_union, not_or] at hs'
    exact hs'.2.1 (by
      rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
      exact ⟨eab, eac, ebc⟩)
  · have heq : wedgesOver G {a, b, c} = {⟨b, a, c⟩, ⟨c, a, b⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      constructor
      · rintro ⟨⟨hvu, hvz, hvnz⟩, hp⟩
        rcases hp with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          simp_all [SimpleGraph.adj_comm]
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          simp_all [SimpleGraph.adj_comm] <;> aesop
    rw [heq]
    simp [hbc]
  · have heq : wedgesOver G {a, b, c} = {⟨a, b, c⟩, ⟨c, b, a⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      aesop (add simp [eab, eac, ebc, SimpleGraph.adj_comm])
    rw [heq]
    simp [hac]
  · have heq : wedgesOver G {a, b, c} = {⟨a, b, c⟩, ⟨b, a, c⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      aesop (add simp [eab, eac, ebc, SimpleGraph.adj_comm])
    rw [heq]
    simp [hab]
  · have heq : wedgesOver G {a, b, c} = {⟨a, c, b⟩, ⟨b, c, a⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      aesop (add simp [eab, eac, ebc, SimpleGraph.adj_comm])
    rw [heq]
    simp [hab]
  · have heq : wedgesOver G {a, b, c} = {⟨a, c, b⟩, ⟨c, a, b⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      aesop (add simp [eab, eac, ebc, SimpleGraph.adj_comm])
    rw [heq]
    simp [hac]
  · have heq : wedgesOver G {a, b, c} = {⟨b, c, a⟩, ⟨c, b, a⟩} := by
      apply Finset.ext
      rintro ⟨v, u, z⟩
      simp only [wedgesOver, Finset.mem_filter, mixedWedges, Finset.mem_sigma,
        Finset.mem_univ, true_and, Finset.mem_product, SimpleGraph.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, Sigma.mk.injEq]
      rw [support_eq_triple_iff hab hac hbc]
      aesop (add simp [eab, eac, ebc, SimpleGraph.adj_comm])
    rw [heq]
    simp [hbc]
  · exfalso
    have hs' := hs
    rw [mixedTriples, Finset.mem_sdiff, Finset.mem_union, not_or] at hs'
    exact hs'.2.2 (by
      rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
      simp [eab, eac, ebc, hab, hac, hbc])

lemma card_mixedWedges_eq_two_mul_mixedTriples {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (mixedWedges G).card = 2 * (mixedTriples G).card := by
  classical
  have hfiber : (mixedWedges G).card =
      ∑ s : Finset V, (wedgesOver G s).card := by
    simpa [wedgesOver] using
      (Finset.sum_fiberwise (mixedWedges G) wedgeSupport (fun _ ↦ (1 : ℕ))).symm
  rw [hfiber]
  calc
    ∑ s : Finset V, (wedgesOver G s).card =
        ∑ s : Finset V, if s ∈ mixedTriples G then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hsm : s ∈ mixedTriples G
          · simp [hsm, card_wedgesOver_of_mem_mixedTriples G hsm]
          · have hz : wedgesOver G s = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro w hw
              rw [wedgesOver, Finset.mem_filter] at hw
              exact hsm (hw.2 ▸ wedgeSupport_mem_mixedTriples G hw.1)
            simp [hsm, hz]
    _ = 2 * (mixedTriples G).card := by simp [mul_comm]

lemma cliqueFinset_disjoint_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Disjoint (G.cliqueFinset 3) (Gᶜ.cliqueFinset 3) := by
  rw [Finset.disjoint_left]
  intro s hsG hsC
  have hcard := (SimpleGraph.mem_cliqueFinset_iff.mp hsG).card_eq
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hG := (SimpleGraph.mem_cliqueFinset_iff.mp hsG).isClique
  have hC := (SimpleGraph.mem_cliqueFinset_iff.mp hsC).isClique
  have eG : G.Adj a b := hG (by simp) (by simp) hab
  have eC : Gᶜ.Adj a b := hC (by simp) (by simp) hab
  exact ((SimpleGraph.compl_adj G a b).mp eC).2 eG

lemma card_mixedTriples_add_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (mixedTriples G).card + (G.cliqueFinset 3).card + (Gᶜ.cliqueFinset 3).card =
      (Fintype.card V).choose 3 := by
  classical
  let U := (Finset.univ : Finset V).powersetCard 3
  let C := G.cliqueFinset 3 ∪ Gᶜ.cliqueFinset 3
  have hsub : C ⊆ U := by
    intro s hs
    simp only [C, Finset.mem_union] at hs
    simp only [U, Finset.mem_powersetCard]
    rcases hs with hs | hs
    · simpa using (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq
    · simpa using (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  have hC : C.card = (G.cliqueFinset 3).card + (Gᶜ.cliqueFinset 3).card := by
    simp only [C]
    rw [Finset.card_union_of_disjoint (cliqueFinset_disjoint_compl G)]
  simp only [U, Finset.card_powersetCard] at hsplit
  simpa [mixedTriples, U, C, hC, add_assoc] using hsplit

lemma goodman_identity_nat {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, G.degree v * (Fintype.card V - 1 - G.degree v)) +
        2 * (G.cliqueFinset 3).card + 2 * (Gᶜ.cliqueFinset 3).card =
      2 * (Fintype.card V).choose 3 := by
  have hw := card_mixedWedges_eq_two_mul_mixedTriples G
  rw [card_mixedWedges G] at hw
  have ht := card_mixedTriples_add_triangles G
  omega

lemma six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simpa [Nat.descFactorial, Nat.factorial, mul_comm, mul_left_comm, mul_assoc] using h.symm

lemma degree_square_triangle_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, G.degree v ^ 2 ≤
      Fintype.card V * G.edgeFinset.card + 3 * (G.cliqueFinset 3).card := by
  classical
  calc
    ∑ v : V, G.degree v ^ 2 =
        ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) :=
      (Counting.edge_endpoint_degree_sum_eq_sum_sq G).symm
    _ ≤ ∑ e ∈ G.edgeFinset,
        (Fintype.card V + Counting.triangleDegree G e) := by
      apply Finset.sum_le_sum
      intro e he
      have h := Counting.degree_add_degree_le_card_add_commonNeighbors
        G e.out.1 e.out.2
      have hc : Fintype.card (G.commonNeighbors e.out.1 e.out.2) =
          Counting.triangleDegree G e := by
        rw [← Counting.commonNeighbors_card_eq_triangleDegree_edge G e]
        exact Fintype.card_of_finset'
          (Finset.filter (fun y ↦ y ∈ G.commonNeighbors e.out.1 e.out.2)
            (Finset.univ : Finset V)) (by simp)
      omega
    _ = Fintype.card V * G.edgeFinset.card +
        3 * (G.cliqueFinset 3).card := by
      rw [Finset.sum_add_distrib,
        Counting.sum_triangleDegree_eq_three_mul_cliqueFinset]
      simp [mul_comm]

lemma even_gap_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r t : ℕ}
    (hr : 2 ≤ r) (ht : 1 ≤ t) (htr : t < r)
    (hn : Fintype.card V = 2 * r) (hm : G.edgeFinset.card = r ^ 2 + t)
    (hgap : ∀ v, G.degree v ≤ t + 1 ∨ r + t ≤ G.degree v) :
    r * t ≤ (G.cliqueFinset 3).card := by
  let y : V → ℤ := fun v ↦ (G.degree v : ℤ) - r
  let Q : ℤ := ∑ v : V, (y v) ^ 2
  let k : ℤ := r - t - 1
  have hsumdeg := G.sum_degrees_eq_twice_card_edges
  have hsumdegZ := congrArg (fun x : ℕ ↦ (x : ℤ)) hsumdeg
  push_cast at hsumdegZ
  have hsumy : ∑ v : V, y v = 2 * t := by
    simp only [y, Finset.sum_sub_distrib]
    simp [hn, hm] at hsumdegZ ⊢
    nlinarith
  have hpoint (v : V) : (t - k) * y v + k * t ≤ (y v) ^ 2 := by
    have hg := hgap v
    have hk : 0 ≤ k := by dsimp [k]; omega
    rcases hg with hlo | hhi
    · have hloZ : (G.degree v : ℤ) ≤ t + 1 := by exact_mod_cast hlo
      have h1 : y v + k ≤ 0 := by dsimp [y, k]; omega
      have h2 : y v - t ≤ 0 := by dsimp [y]; omega
      have hp : 0 ≤ (y v + k) * (y v - t) := mul_nonneg_of_nonpos_of_nonpos h1 h2
      nlinarith
    · have hhiZ : (r : ℤ) + t ≤ G.degree v := by exact_mod_cast hhi
      have h1 : 0 ≤ y v + k := by dsimp [y, k]; omega
      have h2 : 0 ≤ y v - t := by dsimp [y]; omega
      have hp : 0 ≤ (y v + k) * (y v - t) := mul_nonneg h1 h2
      nlinarith
  have hQraw := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun v _ ↦ hpoint v)
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum] at hQraw
  rw [← Finset.mul_sum, hsumy] at hQraw
  have hQ : (r : ℤ) * t ≤ Q := by
    simp [hn] at hQraw
    have hk : k = r - t - 1 := rfl
    have hfac1 : 0 ≤ (t : ℤ) := by positivity
    have hfac2 : 0 ≤ (r : ℤ) - 2 := by omega
    have hfac3 : 0 ≤ 2 * (r : ℤ) - 2 * t - 1 := by omega
    have hp : 0 ≤ (t : ℤ) * (r - 2) * (2 * r - 2 * t - 1) :=
      mul_nonneg (mul_nonneg hfac1 hfac2) hfac3
    nlinarith
  have hb := degree_square_triangle_bound G
  have hbZ : (∑ v : V, ((G.degree v : ℤ) ^ 2)) ≤
      (Fintype.card V : ℤ) * G.edgeFinset.card +
        3 * (G.cliqueFinset 3).card := by exact_mod_cast hb
  have hexpand : (∑ v : V, (G.degree v : ℤ) ^ 2) =
      Q + 2 * r * (∑ v : V, y v) + (2 * r : ℤ) * r ^ 2 := by
    calc
      _ = ∑ v : V, (y v ^ 2 + 2 * r * y v + r ^ 2) := by
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [y]
        ring
      _ = _ := by simp [Q, hn, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hexpand] at hbZ
  simp only [ge_iff_le] at hbZ
  have hgoalZ : (r : ℤ) * t ≤ ((G.cliqueFinset 3).card : ℤ) := by
    ring_nf at hbZ hQ ⊢
    linarith
  exact_mod_cast hgoalZ

lemma odd_gap_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r t : ℕ}
    (hr : 2 ≤ r) (ht : 1 ≤ t) (htr : t < r)
    (hn : Fintype.card V = 2 * r + 1)
    (hm : G.edgeFinset.card = r * (r + 1) + t)
    (hgap : ∀ v, G.degree v ≤ t ∨ r + t ≤ G.degree v) :
    r * t ≤ (G.cliqueFinset 3).card := by
  let y : V → ℤ := fun v ↦ (G.degree v : ℤ) - r
  let Q : ℤ := ∑ v : V, (y v) ^ 2
  let k : ℤ := r - t
  have hsumdeg := G.sum_degrees_eq_twice_card_edges
  have hsumdegZ := congrArg (fun x : ℕ ↦ (x : ℤ)) hsumdeg
  push_cast at hsumdegZ
  have hsumy : ∑ v : V, y v = r + 2 * t := by
    simp only [y, Finset.sum_sub_distrib]
    simp [hn, hm] at hsumdegZ ⊢
    nlinarith
  have hpoint (v : V) : (t - k) * y v + k * t ≤ (y v) ^ 2 := by
    have hg := hgap v
    rcases hg with hlo | hhi
    · have hloZ : (G.degree v : ℤ) ≤ t := by exact_mod_cast hlo
      have h1 : y v + k ≤ 0 := by dsimp [y, k]; omega
      have h2 : y v - t ≤ 0 := by dsimp [y]; omega
      have hp : 0 ≤ (y v + k) * (y v - t) := mul_nonneg_of_nonpos_of_nonpos h1 h2
      nlinarith
    · have hhiZ : (r : ℤ) + t ≤ G.degree v := by exact_mod_cast hhi
      have h1 : 0 ≤ y v + k := by dsimp [y, k]; omega
      have h2 : 0 ≤ y v - t := by dsimp [y]; omega
      have hp : 0 ≤ (y v + k) * (y v - t) := mul_nonneg h1 h2
      nlinarith
  have hQraw := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun v _ ↦ hpoint v)
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum] at hQraw
  rw [← Finset.mul_sum, hsumy] at hQraw
  have hQ : (r : ℤ) * t + t + r ≤ Q := by
    simp [hn] at hQraw
    have hk : k = r - t := rfl
    let a : ℤ := r - t - 1
    have ha : 0 ≤ a := by dsimp [a]; omega
    have hf1 : 0 ≤ 2 * (t : ℤ) - 1 := by omega
    have hf2 : 0 ≤ 2 * (t : ℤ) ^ 2 + 2 * t - 3 := by
      nlinarith [sq_nonneg ((t : ℤ) - 1)]
    have hf3 : 0 ≤ 4 * (t : ℤ) ^ 2 - 2 * t - 2 := by
      nlinarith [sq_nonneg ((t : ℤ) - 1)]
    have hp1 : 0 ≤ a ^ 2 * (2 * (t : ℤ) - 1) := mul_nonneg (sq_nonneg a) hf1
    have hp2 : 0 ≤ a * (2 * (t : ℤ) ^ 2 + 2 * t - 3) := mul_nonneg ha hf2
    have hpoly : 0 ≤ a ^ 2 * (2 * (t : ℤ) - 1) +
        a * (2 * (t : ℤ) ^ 2 + 2 * t - 3) +
        (4 * (t : ℤ) ^ 2 - 2 * t - 2) := by linarith
    have haeq : (r : ℤ) = t + 1 + a := by dsimp [a]; ring
    have hlower : (r : ℤ) * t + t + r ≤
        (t - k) * (r + 2 * t) + (2 * r + 1) * (k * t) := by
      rw [hk]
      calc
        (r : ℤ) * t + t + r ≤
            (r : ℤ) * t + t + r +
              (a ^ 2 * (2 * (t : ℤ) - 1) +
                a * (2 * (t : ℤ) ^ 2 + 2 * t - 3) +
                (4 * (t : ℤ) ^ 2 - 2 * t - 2)) := by linarith
        _ = (t - (r - t)) * (r + 2 * t) + (2 * r + 1) * ((r - t) * t) := by
          rw [haeq]
          ring
    exact hlower.trans hQraw
  have hb := degree_square_triangle_bound G
  have hbZ : (∑ v : V, ((G.degree v : ℤ) ^ 2)) ≤
      (Fintype.card V : ℤ) * G.edgeFinset.card +
        3 * (G.cliqueFinset 3).card := by exact_mod_cast hb
  have hexpand : (∑ v : V, (G.degree v : ℤ) ^ 2) =
      Q + 2 * r * (∑ v : V, y v) + (2 * r + 1 : ℤ) * r ^ 2 := by
    calc
      _ = ∑ v : V, (y v ^ 2 + 2 * r * y v + r ^ 2) := by
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [y]
        ring
      _ = _ := by simp [Q, hn, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hexpand] at hbZ
  simp only [ge_iff_le] at hbZ
  have hgoalZ : (r : ℤ) * t ≤ ((G.cliqueFinset 3).card : ℤ) := by
    ring_nf at hbZ hQ ⊢
    linarith
  exact_mod_cast hgoalZ

/-! ## Pure arithmetic used by the four degree-gap cases -/

private lemma base_even_high_pos (b : ℤ) (hb : 0 ≤ b) :
    0 < 2 * b ^ 4 + 4 * b ^ 3 - 2 * b ^ 2 - 4 * b + 6 := by
  by_cases h0 : b = 0
  · subst b
    norm_num
  have hb1 : 1 ≤ b := by omega
  have hs : 0 ≤ b ^ 2 - 1 := by nlinarith [sq_nonneg b]
  have hprod : 0 ≤ (b ^ 2 + 2 * b) * (b ^ 2 - 1) :=
    mul_nonneg (by nlinarith [sq_nonneg b]) hs
  nlinarith

private lemma base_even_low_pos (b : ℤ) (hb : 0 ≤ b) :
    0 < 4 * b ^ 4 + 6 * b ^ 3 - 4 * b ^ 2 + 12 := by
  by_cases h0 : b = 0
  · subst b
    norm_num
  have hb1 : 1 ≤ b := by omega
  have hs : 0 ≤ b ^ 2 - 1 := by nlinarith [sq_nonneg b]
  have hprod : 0 ≤ 2 * b ^ 2 * (b ^ 2 - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) hs
  have hcub : 0 ≤ b ^ 3 := by positivity
  nlinarith

lemma even_high_arithmetic {r t Q : ℤ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (htr : t < r) (hQ : 4 * t ^ 2 ≤ 2 * r * Q) :
    6 * r * t - 6 < 3 * Q + 2 * r ^ 3 - 6 * r ^ 2 + 4 * r + 6 * t := by
  let a := r - 1 - t
  let b := r - 2
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hbase := base_even_high_pos b hb
  have hmul : 0 ≤ r := by omega
  have hscaled : 0 <
      r * (3 * Q + 2 * r ^ 3 - 6 * r ^ 2 + 4 * r + 6 * t -
        (6 * r * t - 6)) := by
    have hvar : 0 ≤ 2 * r * Q - 4 * t ^ 2 := by omega
    have haa : 0 ≤ a ^ 2 := sq_nonneg a
    have hab2 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    dsimp [a, b] at hbase ⊢
    nlinarith
  nlinarith

lemma even_low_arithmetic {r t Q : ℤ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (htr : t < r)
    (hQ : (2 * r - 1) * (r - t - 1) ^ 2 + (r + t - 1) ^ 2 ≤
      (2 * r - 1) * Q) :
    6 * r * t - 6 < 3 * Q + 2 * r ^ 3 - 6 * r ^ 2 + 4 * r + 6 * t := by
  let a := r - 1 - t
  let b := r - 2
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hbase := base_even_low_pos b hb
  have hden : 0 < 2 * r - 1 := by omega
  have hscaled : 0 <
      (2 * r - 1) * (3 * Q + 2 * r ^ 3 - 6 * r ^ 2 + 4 * r + 6 * t -
        (6 * r * t - 6)) := by
    have hvar : 0 ≤ (2 * r - 1) * Q -
        ((2 * r - 1) * (r - t - 1) ^ 2 + (r + t - 1) ^ 2) := by omega
    have haa : 0 ≤ a ^ 2 := sq_nonneg a
    have haab : 0 ≤ a ^ 2 * b := mul_nonneg haa hb
    have hab2 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    dsimp [a, b] at hbase ⊢
    nlinarith
  nlinarith

lemma odd_high_arithmetic {r t Q : ℤ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (htr : t < r) (hQ : (r + 2 * t) ^ 2 ≤ (2 * r + 1) * Q) :
    6 * r * t - 6 < 3 * Q + 2 * r ^ 3 - 3 * r ^ 2 - 2 * r := by
  let a := r - 1 - t
  let b := r - 2
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hden : 0 < 2 * r + 1 := by omega
  have hscaled : 0 <
      (2 * r + 1) * (3 * Q + 2 * r ^ 3 - 3 * r ^ 2 - 2 * r -
        (6 * r * t - 6)) := by
    have hvar : 0 ≤ (2 * r + 1) * Q - (r + 2 * t) ^ 2 := by omega
    have haa : 0 ≤ a ^ 2 := sq_nonneg a
    have hab2 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
    have hb3 : 0 ≤ b ^ 3 := by positivity
    have hb4 : 0 ≤ b ^ 4 := by positivity
    dsimp [a, b] at *
    nlinarith
  nlinarith

lemma odd_low_arithmetic {r t Q : ℤ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (htr : t < r)
    (hQ : 2 * r * (r - t) ^ 2 + (2 * r + t) ^ 2 ≤ 2 * r * Q) :
    6 * r * t - 6 < 3 * Q + 2 * r ^ 3 - 3 * r ^ 2 - 2 * r := by
  let a := r - 1 - t
  let b := r - 2
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hden : 0 < 2 * r := by omega
  have hscaled : 0 <
      2 * r * (3 * Q + 2 * r ^ 3 - 3 * r ^ 2 - 2 * r -
        (6 * r * t - 6)) := by
    have hvar : 0 ≤ 2 * r * Q -
        (2 * r * (r - t) ^ 2 + (2 * r + t) ^ 2) := by omega
    have haa : 0 ≤ a ^ 2 := sq_nonneg a
    have haab : 0 ≤ a ^ 2 * b := mul_nonneg haa hb
    have hab2 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
    have hb3 : 0 ≤ b ^ 3 := by positivity
    have hb4 : 0 ≤ b ^ 4 := by positivity
    dsimp [a, b] at *
    nlinarith
  nlinarith

end

end Erdos1010

/-- **Erdős Problem 1010.** Every finite simple graph with
`⌊n²/4⌋ + t` edges, where `t < ⌊n/2⌋`, contains at least
`t * ⌊n/2⌋` unordered triangles. -/
theorem erdos_1010 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ}
    (ht : t < Fintype.card V / 2)
    (hE : G.edgeFinset.card = Fintype.card V ^ 2 / 4 + t) :
    t * (Fintype.card V / 2) ≤ (G.cliqueFinset 3).card := by
  let r := Fintype.card V / 2
  have htr : t < r := ht
  have hparity : Fintype.card V = 2 * r ∨ Fintype.card V = 2 * r + 1 := by
    dsimp [r]
    omega
  rcases hparity with hn | hn
  · have hsquare : Fintype.card V ^ 2 = 4 * r ^ 2 := by rw [hn]; ring
    have hbase : Fintype.card V ^ 2 / 4 = r ^ 2 := by rw [hsquare]; omega
    have hm : G.edgeFinset.card = r ^ 2 + t := by rwa [hbase] at hE
    have h := Erdos1010.even_triangles G hn htr hm
    simpa [r, Nat.mul_comm] using h
  · have hsquare : Fintype.card V ^ 2 = 4 * (r * (r + 1)) + 1 := by rw [hn]; ring
    have hbase : Fintype.card V ^ 2 / 4 = r * (r + 1) := by rw [hsquare]; omega
    have hm : G.edgeFinset.card = r * (r + 1) + t := by rwa [hbase] at hE
    have h := Erdos1010.odd_triangles G hn htr hm
    simpa [r, Nat.mul_comm] using h
