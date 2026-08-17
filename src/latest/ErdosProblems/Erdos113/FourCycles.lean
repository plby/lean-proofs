import ErdosProblems.Erdos113.Cycles

open scoped Real SimpleGraph BigOperators

namespace Erdos113FourCycles

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

def codegree (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (commonNeighborFinset G u v).card

@[simp] lemma mem_commonNeighborFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v w : V} :
    w ∈ commonNeighborFinset G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNeighborFinset, SimpleGraph.mem_neighborFinset]

/-- Ordered choices of the two other vertices of a four-cycle containing
the oriented edge `u-y`.  The first coordinate is the other neighbor of
`y`; the second is the other common neighbor of `u` and that vertex. -/
noncomputable def extensionsThroughEdge (G : SimpleGraph V)
    [DecidableRel G.Adj] (u y : V) : Finset (Σ _x : V, V) := by
  classical
  exact ((G.neighborFinset y).erase u).sigma fun x ↦
    (commonNeighborFinset G u x).erase y

@[simp] lemma mem_extensionsThroughEdge
    {G : SimpleGraph V} [DecidableRel G.Adj] {u y : V} {p : Σ _x : V, V} :
    p ∈ extensionsThroughEdge G u y ↔
      G.Adj y p.1 ∧ p.1 ≠ u ∧ G.Adj u p.2 ∧
        G.Adj p.1 p.2 ∧ p.2 ≠ y := by
  classical
  simp only [extensionsThroughEdge, Finset.mem_sigma, Finset.mem_erase,
    SimpleGraph.mem_neighborFinset, mem_commonNeighborFinset]
  aesop

def extensionCycleTuple (u y : V) (p : Σ _x : V, V) : Fin 4 → V :=
  ![y, u, p.2, p.1]

lemma extensionCycleTuple_genuine
    {G : SimpleGraph V} [DecidableRel G.Adj] {u y : V} {p : Σ _x : V, V}
    (huy : G.Adj y u) (hp : p ∈ extensionsThroughEdge G u y) :
    IsGenuineCycle G (extensionCycleTuple u y p) := by
  have h := mem_extensionsThroughEdge.mp hp
  have hyu : y ≠ u := huy.ne
  have hyx : y ≠ p.1 := h.1.ne
  have hux : u ≠ p.1 := h.2.1.symm
  have huz : u ≠ p.2 := h.2.2.1.ne
  have hxz : p.1 ≠ p.2 := h.2.2.2.1.ne
  have hyz : y ≠ p.2 := h.2.2.2.2.symm
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extensionCycleTuple]
  · intro i
    fin_cases i
    · exact huy
    · exact h.2.2.1
    · exact h.2.2.2.1.symm
    · exact h.1.symm

noncomputable def extensionToCycleThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    ↑(extensionsThroughEdge G u y) →
      ↑(cyclesThroughEdge G 4 s(u, y)) := fun p ↦ by
  refine ⟨extensionCycleTuple u y p.1, ?_⟩
  rw [mem_cyclesThroughEdge]
  refine ⟨extensionCycleTuple_genuine huy p.2, ⟨0, ?_⟩⟩
  simp [cycleEdge, extensionCycleTuple, Sym2.eq_swap]

lemma extensionToCycleThroughEdge_injective
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    Function.Injective (extensionToCycleThroughEdge G u y huy) := by
  intro p q hpq
  apply Subtype.ext
  apply Sigma.ext
  · have ht := congrArg Subtype.val hpq
    change extensionCycleTuple u y p.1 = extensionCycleTuple u y q.1 at ht
    have h := congrFun ht (3 : Fin 4)
    simpa [extensionCycleTuple] using h
  · apply heq_of_eq
    have ht := congrArg Subtype.val hpq
    change extensionCycleTuple u y p.1 = extensionCycleTuple u y q.1 at ht
    have h := congrFun ht (2 : Fin 4)
    simpa [extensionCycleTuple] using h

lemma card_extensionsThroughEdge_le_cyclesThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (u y : V) (huy : G.Adj y u) :
    (extensionsThroughEdge G u y).card ≤
      (cyclesThroughEdge G 4 s(u, y)).card := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (extensionToCycleThroughEdge G u y huy)
    (extensionToCycleThroughEdge_injective G u y huy)

def highCodegreeNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (u y : V) : Finset V :=
  (G.neighborFinset y).filter fun x ↦ u ≠ x ∧ s < codegree G u x

@[simp] lemma mem_highCodegreeNeighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : ℕ} {u y x : V} :
    x ∈ highCodegreeNeighbors G s u y ↔
      G.Adj y x ∧ u ≠ x ∧ s < codegree G u x := by
  simp [highCodegreeNeighbors, SimpleGraph.mem_neighborFinset]

lemma card_highCodegreeNeighbors_mul_le_extensionsThroughEdge
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) {u y : V}
    (huy : G.Adj y u) :
    (highCodegreeNeighbors G s u y).card * s ≤
      (extensionsThroughEdge G u y).card := by
  classical
  let S := highCodegreeNeighbors G s u y
  let T := (G.neighborFinset y).erase u
  let f (x : V) := (commonNeighborFinset G u x).erase y
  have hST : S ⊆ T := by
    intro x hx
    have hx' := mem_highCodegreeNeighbors.mp hx
    exact Finset.mem_erase.mpr ⟨hx'.2.1.symm, by
      simpa [SimpleGraph.mem_neighborFinset] using hx'.1⟩
  have hf (x : V) (hx : x ∈ S) : s ≤ (f x).card := by
    have hx' := mem_highCodegreeNeighbors.mp hx
    have hy : y ∈ commonNeighborFinset G u x := by
      rw [mem_commonNeighborFinset]
      exact ⟨huy.symm, hx'.1.symm⟩
    have herase := Finset.card_erase_add_one hy
    change ((commonNeighborFinset G u x).erase y).card + 1 =
      (commonNeighborFinset G u x).card at herase
    have hhigh := hx'.2.2
    change s < (commonNeighborFinset G u x).card at hhigh
    change s ≤ ((commonNeighborFinset G u x).erase y).card
    omega
  rw [extensionsThroughEdge, Finset.card_sigma]
  change S.card * s ≤ ∑ x ∈ T, (f x).card
  calc
    S.card * s = ∑ _x ∈ S, s := by simp
    _ ≤ ∑ x ∈ S, (f x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact hf x hx
    _ ≤ ∑ x ∈ T, (f x).card :=
      Finset.sum_le_sum_of_subset hST

lemma card_highCodegreeNeighbors_cast_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) {u y : V}
    (hs : 0 < s) (huy : G.Adj y u) (Q : ℝ)
    (hcap : ((extensionsThroughEdge G u y).card : ℝ) ≤ Q) :
    ((highCodegreeNeighbors G s u y).card : ℝ) ≤ Q / s := by
  have hmulNat :=
    card_highCodegreeNeighbors_mul_le_extensionsThroughEdge G s huy
  have hmul : ((highCodegreeNeighbors G s u y).card : ℝ) * s ≤ Q := by
    calc
      ((highCodegreeNeighbors G s u y).card : ℝ) * s =
          (((highCodegreeNeighbors G s u y).card * s : ℕ) : ℝ) := by
        norm_num
      _ ≤ ((extensionsThroughEdge G u y).card : ℝ) := by
        exact_mod_cast hmulNat
      _ ≤ Q := hcap
  exact (le_div_iff₀ (by exact_mod_cast hs)).2 hmul

end Erdos113FourCycles
