import ErdosProblems.Erdos788.NormalizedGraph
import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Triangle counting and neighborhood incidence for normalized sum graphs

This module formalizes the triangle injection and the exact local and global
incidence identities used in the lower-bound argument.
-/

namespace Erdos788

open Finset

def pairSums {N : ℕ} (t : Finset (Fin N)) : Finset ℕ :=
  t.offDiag.image fun xy ↦ xy.1.1 + xy.2.1

theorem triple_pairSums {N : ℕ} {x y z : Fin N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    pairSums {x, y, z} = {x.1 + y.1, x.1 + z.1, y.1 + z.1} := by
  classical
  ext q
  simp only [pairSums, mem_image, mem_offDiag, mem_insert, mem_singleton,
    Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩
    rcases ha with (rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl) <;>
      simp_all [add_comm]
  · rintro (rfl | rfl | rfl)
    · exact ⟨x, y, ⟨by simp, by simp, hxy⟩, rfl⟩
    · exact ⟨x, z, ⟨by simp, by simp, hxz⟩, rfl⟩
    · exact ⟨y, z, ⟨by simp, by simp, hyz⟩, rfl⟩

theorem card_pairSums_of_three {N : ℕ} {t : Finset (Fin N)} (ht : t.card = 3) :
    (pairSums t).card = 3 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp ht
  rw [triple_pairSums hxy hxz hyz]
  have hxy_xz : x.1 + y.1 ≠ x.1 + z.1 := by
    intro h
    exact hyz (Fin.ext (Nat.add_left_cancel h))
  have hxz_yz : x.1 + z.1 ≠ y.1 + z.1 := by
    intro h
    exact hxy (Fin.ext (Nat.add_right_cancel h))
  have hxy_yz : x.1 + y.1 ≠ y.1 + z.1 := by
    intro h
    have : x.1 = z.1 := by omega
    exact hxz (Fin.ext this)
  exact card_eq_three.mpr
    ⟨x.1 + y.1, x.1 + z.1, y.1 + z.1, hxy_xz, hxy_yz, hxz_yz, rfl⟩

theorem triple_eq_of_pairSum_finsets_eq
    {x y z u v w : ℕ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : ({x + y, x + z, y + z} : Finset ℕ) =
      ({u + v, u + w, v + w} : Finset ℕ)) :
    ({x, y, z} : Finset ℕ) = {u, v, w} := by
  classical
  have hxy_xz : x + y ≠ x + z := fun e ↦ hyz (Nat.add_left_cancel e)
  have hxy_yz : x + y ≠ y + z := by omega
  have hxz_yz : x + z ≠ y + z := fun e ↦ hxy (Nat.add_right_cancel e)
  have huv_uw : u + v ≠ u + w := fun e ↦ hvw (Nat.add_left_cancel e)
  have huv_vw : u + v ≠ v + w := by omega
  have huw_vw : u + w ≠ v + w := fun e ↦ huv (Nat.add_right_cancel e)
  have hxy_not : x + y ∉ ({x + z, y + z} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxy_xz, hxy_yz⟩
  have hxz_not : x + z ∉ ({y + z} : Finset ℕ) := by
    simpa only [mem_singleton, not_false_eq_true] using! hxz_yz
  have huv_not : u + v ∉ ({u + w, v + w} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨huv_uw, huv_vw⟩
  have huw_not : u + w ∉ ({v + w} : Finset ℕ) := by
    simpa only [mem_singleton, not_false_eq_true] using! huw_vw
  have hsum_left :
      (∑ a ∈ ({x + y, x + z, y + z} : Finset ℕ), a) =
        (x + y) + (x + z) + (y + z) := by
    rw [sum_insert hxy_not, sum_insert hxz_not, sum_singleton]
    simp only [Nat.add_assoc]
  have hsum_right :
      (∑ a ∈ ({u + v, u + w, v + w} : Finset ℕ), a) =
        (u + v) + (u + w) + (v + w) := by
    rw [sum_insert huv_not, sum_insert huw_not, sum_singleton]
    simp only [Nat.add_assoc]
  have hpairs := congrArg (fun s : Finset ℕ ↦ ∑ a ∈ s, a) h
  rw [hsum_left, hsum_right] at hpairs
  have htotal : x + y + z = u + v + w := by omega
  apply Finset.Subset.antisymm
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq ⊢
    rcases hq with (rfl | rfl | rfl)
    · have hm : y + z ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : x + z ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : x + y ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq ⊢
    rcases hq with (rfl | rfl | rfl)
    · have hm : v + w ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : u + w ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : u + v ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega

theorem pairSums_mem_powersetCard_of_is3Clique
    {N : ℕ} {A : Finset ℕ} {t : Finset (Fin N)}
    (ht : (sumGraph N A).IsNClique 3 t) :
    pairSums t ∈ A.powersetCard 3 := by
  classical
  rw [mem_powersetCard]
  constructor
  · intro q hq
    rw [pairSums, mem_image] at hq
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hq
    rw [mem_offDiag] at hxy
    exact (sumGraph_adj.mp (ht.isClique hxy.1 hxy.2.1 hxy.2.2)).2
  · exact card_pairSums_of_three ht.card_eq

theorem pairSums_injOn_card_three {N : ℕ} :
    Set.InjOn pairSums {t : Finset (Fin N) | t.card = 3} := by
  classical
  intro t ht u hu htu
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hu
  rw [triple_pairSums hxy hxz hyz, triple_pairSums hab hac hbc] at htu
  have hvals : ({x.1, y.1, z.1} : Finset ℕ) = {a.1, b.1, c.1} :=
    triple_eq_of_pairSum_finsets_eq
      (fun h ↦ hxy (Fin.ext h)) (fun h ↦ hxz (Fin.ext h))
      (fun h ↦ hyz (Fin.ext h)) (fun h ↦ hab (Fin.ext h))
      (fun h ↦ hac (Fin.ext h)) (fun h ↦ hbc (Fin.ext h)) htu
  apply Finset.map_injective Fin.valEmbedding
  simpa using! hvals

/-- Lemma 3.1 of the paper: triangles inject into the three-element subsets
of the selected sum palette. -/
theorem triangle_count_le_choose {N : ℕ} (A : Finset ℕ) :
    ((sumGraph N A).cliqueFinset 3).card ≤ A.card.choose 3 := by
  classical
  rw [← card_powersetCard 3 A]
  refine card_le_card_of_injOn pairSums ?_ ?_
  · intro t ht
    exact pairSums_mem_powersetCard_of_is3Clique
      (SimpleGraph.mem_cliqueFinset_iff.mp (by simpa only [Finset.mem_coe] using! ht))
  · intro t ht u hu htu
    apply pairSums_injOn_card_three
    · exact (SimpleGraph.mem_cliqueFinset_iff.mp
        (by simpa only [Finset.mem_coe] using! ht)).card_eq
    · exact (SimpleGraph.mem_cliqueFinset_iff.mp
        (by simpa only [Finset.mem_coe] using! hu)).card_eq
    · exact htu

section TriangleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges spanned by the neighborhood of `v`, represented as two-cliques. -/
def neighborhoodEdges (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 2).filter fun e ↦ ∀ x ∈ e, G.Adj v x

/-- Triangles containing `v`. -/
def trianglesAt (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t ↦ v ∈ t

@[simp]
theorem mem_neighborhoodEdges {v : V} {e : Finset V} :
    e ∈ neighborhoodEdges G v ↔
      G.IsNClique 2 e ∧ ∀ x ∈ e, G.Adj v x := by
  simp [neighborhoodEdges]

@[simp]
theorem mem_trianglesAt {v : V} {t : Finset V} :
    t ∈ trianglesAt G v ↔ G.IsNClique 3 t ∧ v ∈ t := by
  simp [trianglesAt]

theorem insert_mem_trianglesAt_of_mem_neighborhoodEdges
    {v : V} {e : Finset V} (he : e ∈ neighborhoodEdges G v) :
    insert v e ∈ trianglesAt G v := by
  rw [mem_neighborhoodEdges] at he
  rw [mem_trianglesAt]
  have hvnot : v ∉ e := fun hv ↦ G.irrefl (he.2 v hv)
  constructor
  · constructor
    · simpa only [Finset.coe_insert] using!
        he.1.isClique.insert (fun x hx _hvx ↦ he.2 x hx)
    · rw [card_insert_of_notMem hvnot, he.1.card_eq]
  · exact mem_insert_self v e

theorem erase_mem_neighborhoodEdges_of_mem_trianglesAt
    {v : V} {t : Finset V} (ht : t ∈ trianglesAt G v) :
    t.erase v ∈ neighborhoodEdges G v := by
  rw [mem_trianglesAt] at ht
  rw [mem_neighborhoodEdges]
  constructor
  · constructor
    · exact ht.1.isClique.subset (erase_subset v t)
    · rw [card_erase_of_mem ht.2, ht.1.card_eq]
  · intro x hx
    exact ht.1.isClique ht.2 (mem_of_mem_erase hx) (mem_erase.mp hx).1.symm

/-- Exact local incidence identity: the number of triangles through a vertex
is the number of graph edges spanned by its neighborhood. -/
theorem card_trianglesAt_eq_card_neighborhoodEdges (v : V) :
    (trianglesAt G v).card = (neighborhoodEdges G v).card := by
  apply Nat.le_antisymm
  · refine card_le_card_of_injOn (fun t ↦ t.erase v) ?_ ?_
    · intro t ht
      exact erase_mem_neighborhoodEdges_of_mem_trianglesAt G
        (by simpa only [Finset.mem_coe] using! ht)
    · intro t ht u hu htu
      have htv : v ∈ t := ((mem_trianglesAt G).mp
        (by simpa only [Finset.mem_coe] using! ht)).2
      have huv : v ∈ u := ((mem_trianglesAt G).mp
        (by simpa only [Finset.mem_coe] using! hu)).2
      change t.erase v = u.erase v at htu
      calc
        t = insert v (t.erase v) := (insert_erase htv).symm
        _ = insert v (u.erase v) := congrArg (insert v) htu
        _ = u := insert_erase huv
  · refine card_le_card_of_injOn (fun e ↦ insert v e) ?_ ?_
    · intro e he
      exact insert_mem_trianglesAt_of_mem_neighborhoodEdges G
        (by simpa only [Finset.mem_coe] using! he)
    · intro e he f hf hef
      have hev : v ∉ e := by
        have he' : e ∈ neighborhoodEdges G v := by
          simpa only [Finset.mem_coe] using! he
        rw [mem_neighborhoodEdges] at he'
        exact fun hv ↦ G.irrefl (he'.2 v hv)
      have hfv : v ∉ f := by
        have hf' : f ∈ neighborhoodEdges G v := by
          simpa only [Finset.mem_coe] using! hf
        rw [mem_neighborhoodEdges] at hf'
        exact fun hv ↦ G.irrefl (hf'.2 v hv)
      simpa [hev, hfv] using! congrArg (Finset.erase · v) hef

/-- Exact global incidence identity: counting triangle--vertex incidences by
vertices or by triangles gives `sum_v t_v = 3 T`. -/
theorem sum_card_trianglesAt :
    (∑ v : V, (trianglesAt G v).card) =
      3 * (G.cliqueFinset 3).card := by
  classical
  calc
    (∑ v : V, (trianglesAt G v).card) =
        ∑ v : V, ∑ t ∈ G.cliqueFinset 3, if v ∈ t then 1 else 0 := by
      apply sum_congr rfl
      intro v _hv
      rw [trianglesAt, card_eq_sum_ones, sum_filter]
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ v : V, if v ∈ t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ G.cliqueFinset 3, t.card := by
      apply sum_congr rfl
      intro t _ht
      simp
    _ = ∑ _t ∈ G.cliqueFinset 3, 3 := by
      apply sum_congr rfl
      intro t ht
      exact (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    _ = 3 * (G.cliqueFinset 3).card := by
      simp [Nat.mul_comm]

end TriangleIncidence

/-- For a sum graph, the total number of neighborhood edges is bounded by
three times the number of three-element palette subsets.  This is the exact
finite inequality used before the averaging step in the paper. -/
theorem sum_card_neighborhoodEdges_sumGraph_le {N : ℕ} (A : Finset ℕ) :
    (∑ v : Fin N, (neighborhoodEdges (sumGraph N A) v).card) ≤
      3 * A.card.choose 3 := by
  calc
    (∑ v : Fin N, (neighborhoodEdges (sumGraph N A) v).card) =
        ∑ v : Fin N, (trianglesAt (sumGraph N A) v).card := by
      apply sum_congr rfl
      intro v _hv
      exact (card_trianglesAt_eq_card_neighborhoodEdges (sumGraph N A) v).symm
    _ = 3 * ((sumGraph N A).cliqueFinset 3).card :=
      sum_card_trianglesAt (sumGraph N A)
    _ ≤ 3 * A.card.choose 3 :=
      Nat.mul_le_mul_left 3 (triangle_count_le_choose A)

section FiniteAveraging

variable {W : Type*} [Fintype W]

/-- Vertices whose value is at most twice the average, written without
division so that the definition also behaves correctly on empty types. -/
noncomputable def averageGood (t : W → ℕ) : Finset W := by
  classical
  exact Finset.univ.filter fun w ↦
    Fintype.card W * t w ≤ 2 * ∑ u : W, t u

/-- At least half the points have value at most twice the average.  The
conclusion is in the division-free form `|W| ≤ 2 |good|`. -/
theorem card_le_twice_card_averageGood (t : W → ℕ) :
    Fintype.card W ≤ 2 * (averageGood t).card := by
  classical
  let total : ℕ := ∑ w : W, t w
  let good : Finset W := averageGood t
  let bad : Finset W := Finset.univ.filter fun w ↦
    ¬(Fintype.card W * t w ≤ 2 * total)
  have hpart : good.card + bad.card = Fintype.card W := by
    simpa only [good, bad, averageGood, total, card_univ] using!
      (card_filter_add_card_filter_not
        (s := (Finset.univ : Finset W))
        (fun w ↦ Fintype.card W * t w ≤ 2 * ∑ u : W, t u))
  have hpoint : ∀ w ∈ bad,
      2 * total + 1 ≤ Fintype.card W * t w := by
    intro w hw
    have hnle := (mem_filter.mp hw).2
    exact Nat.succ_le_iff.mpr (lt_of_not_ge hnle)
  have hsum :
      ∑ w ∈ bad, (2 * total + 1) ≤
        ∑ w ∈ bad, Fintype.card W * t w := by
    exact sum_le_sum fun w hw ↦ hpoint w hw
  have hbadSum : ∑ w ∈ bad, t w ≤ total := by
    exact sum_le_sum_of_subset (filter_subset _ _)
  have hbad : bad.card * (2 * total + 1) ≤ Fintype.card W * total := by
    calc
      bad.card * (2 * total + 1) = ∑ _w ∈ bad, (2 * total + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ bad, Fintype.card W * t w := hsum
      _ = Fintype.card W * ∑ w ∈ bad, t w := by
        simp [Finset.mul_sum]
      _ ≤ Fintype.card W * total := Nat.mul_le_mul_left _ hbadSum
  by_contra hgood
  have hgood' : ¬(Fintype.card W ≤ 2 * good.card) := by
    simpa only [good] using! hgood
  have hcardlt : 2 * good.card < Fintype.card W := lt_of_not_ge hgood'
  have hbadpos : 0 < bad.card := by omega
  have hNS : Fintype.card W * total ≤ (2 * bad.card) * total := by
    apply Nat.mul_le_mul_right total
    omega
  have hstrict : (2 * bad.card) * total < bad.card * (2 * total + 1) := by
    calc
      (2 * bad.card) * total = bad.card * (2 * total) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ < bad.card * (2 * total + 1) :=
        (Nat.mul_lt_mul_left hbadpos).mpr (Nat.lt_succ_self (2 * total))
  exact (not_lt_of_ge hbad) (hNS.trans_lt hstrict)

end FiniteAveraging

theorem six_mul_choose_three_le_cube (b : ℕ) :
    6 * b.choose 3 ≤ b ^ 3 := by
  calc
    6 * b.choose 3 = Nat.factorial 3 * b.choose 3 := by rfl
    _ = b.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose b 3).symm
    _ ≤ b ^ 3 := Nat.descFactorial_le_pow b 3

noncomputable section

/-- The division-free predicate saying that a vertex has at most twice the
average number of edges in its neighborhood. -/
def SumGraphGood (N : ℕ) (A : Finset ℕ) (v : Fin N) : Prop :=
  N * (neighborhoodEdges (sumGraph N A) v).card ≤
    2 * ∑ u : Fin N, (neighborhoodEdges (sumGraph N A) u).card

noncomputable instance sumGraphGoodDecidablePred (N : ℕ) (A : Finset ℕ) :
    DecidablePred (SumGraphGood N A) :=
  Classical.decPred _

/-- Good vertices after the triangle-incidence averaging step. -/
def sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (SumGraphGood N A)

@[simp]
theorem mem_sumGraphGoodVertices {N : ℕ} {A : Finset ℕ} {v : Fin N} :
    v ∈ sumGraphGoodVertices N A ↔ SumGraphGood N A v := by
  simp [sumGraphGoodVertices]

theorem card_le_twice_card_sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) :
    N ≤ 2 * (sumGraphGoodVertices N A).card := by
  have hgood : sumGraphGoodVertices N A =
      averageGood
        (fun v : Fin N ↦ (neighborhoodEdges (sumGraph N A) v).card) := by
    ext v
    simp [sumGraphGoodVertices, averageGood, SumGraphGood]
  rw [hgood]
  simpa using! card_le_twice_card_averageGood
    (t := fun v : Fin N ↦ (neighborhoodEdges (sumGraph N A) v).card)

theorem half_le_card_sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) :
    N / 2 ≤ (sumGraphGoodVertices N A).card := by
  have h := card_le_twice_card_sumGraphGoodVertices N A
  omega

theorem good_vertex_mul_local_le_cube_of_good
    {N : ℕ} {A : Finset ℕ} {v : Fin N} (hv : SumGraphGood N A v) :
    N * (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 := by
  calc
    N * (neighborhoodEdges (sumGraph N A) v).card ≤
        2 * ∑ u : Fin N, (neighborhoodEdges (sumGraph N A) u).card :=
      hv
    _ ≤ 2 * (3 * A.card.choose 3) :=
      Nat.mul_le_mul_left 2 (sum_card_neighborhoodEdges_sumGraph_le A)
    _ = 6 * A.card.choose 3 := by omega
    _ ≤ A.card ^ 3 := six_mul_choose_three_le_cube A.card

theorem good_vertex_mul_local_le_cube {N : ℕ} {A : Finset ℕ} {v : Fin N}
    (hv : v ∈ sumGraphGoodVertices N A) :
    N * (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 :=
  good_vertex_mul_local_le_cube_of_good (mem_sumGraphGoodVertices.mp hv)

theorem good_vertex_local_le_cube_div {N : ℕ} {A : Finset ℕ} {v : Fin N}
    (hN : 0 < N) (hv : v ∈ sumGraphGoodVertices N A) :
    (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 / N := by
  apply (Nat.le_div_iff_mul_le hN).2
  simpa [Nat.mul_comm] using! good_vertex_mul_local_le_cube hv

section InducedNeighborhoodEdges

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)]

def mapSubtypeFinsetEmbedding : Finset s ↪ Finset V where
  toFun e := e.map (Function.Embedding.subtype s)
  inj' := Finset.map_injective _

theorem map_neighborhoodEdges_induce_subset (v : s) :
    (neighborhoodEdges (G.induce s) v).map (mapSubtypeFinsetEmbedding s) ⊆
      neighborhoodEdges G v.1 := by
  intro e he
  rw [mem_map] at he
  obtain ⟨e, he, rfl⟩ := he
  rw [mem_neighborhoodEdges] at he ⊢
  constructor
  · exact he.1.map.mono (G.spanningCoe_induce_le s)
  · intro x hx
    change x ∈ e.map (Function.Embedding.subtype s) at hx
    rw [mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact SimpleGraph.induce_adj.mp (he.2 y hy)

theorem card_neighborhoodEdges_induce_le (v : s) :
    (neighborhoodEdges (G.induce s) v).card ≤
      (neighborhoodEdges G v.1).card := by
  calc
    (neighborhoodEdges (G.induce s) v).card =
        ((neighborhoodEdges (G.induce s) v).map
          (mapSubtypeFinsetEmbedding s)).card :=
      (card_map (mapSubtypeFinsetEmbedding s)).symm
    _ ≤ (neighborhoodEdges G v.1).card :=
      card_le_card (map_neighborhoodEdges_induce_subset G s v)

theorem degree_induce_le (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((G.induce s).neighborFinset v).card =
        (((G.induce s).neighborFinset v).map
          (Function.Embedding.subtype s)).card :=
      (card_map (Function.Embedding.subtype s)).symm
    _ = (G.neighborFinset v.1 ∩ s.toFinset).card :=
      congrArg Finset.card (G.map_neighborFinset_induce v)
    _ ≤ (G.neighborFinset v.1).card :=
      card_le_card inter_subset_left

end InducedNeighborhoodEdges

abbrev SumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :=
  {v : Fin N // SumGraphGood N A v}

/-- The induced graph on the vertices retained by averaging. -/
abbrev goodInducedSumGraph (N : ℕ) (A : Finset ℕ) :
    SimpleGraph (SumGraphGoodVertex N A) :=
  (sumGraph N A).induce {v | SumGraphGood N A v}

@[simp]
theorem goodInducedSumGraph_adj {N : ℕ} {A : Finset ℕ}
    {u v : SumGraphGoodVertex N A} :
    (goodInducedSumGraph N A).Adj u v ↔ (sumGraph N A).Adj u.1 v.1 := by
  exact SimpleGraph.induce_adj

@[simp]
theorem card_sumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :
    Fintype.card (SumGraphGoodVertex N A) = (sumGraphGoodVertices N A).card := by
  simpa [SumGraphGoodVertex, sumGraphGoodVertices] using!
    Fintype.card_subtype (SumGraphGood N A)

theorem half_le_card_sumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :
    N / 2 ≤ Fintype.card (SumGraphGoodVertex N A) := by
  rw [card_sumGraphGoodVertex]
  exact half_le_card_sumGraphGoodVertices N A

theorem goodInduced_mul_local_le_cube {N : ℕ} {A : Finset ℕ}
    (v : SumGraphGoodVertex N A) :
    N * (neighborhoodEdges
      ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        A.card ^ 3 := by
  calc
    N * (neighborhoodEdges
        ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        N * (neighborhoodEdges (sumGraph N A) v.1).card :=
      Nat.mul_le_mul_left N
        (card_neighborhoodEdges_induce_le (sumGraph N A)
          {v | SumGraphGood N A v} v)
    _ ≤ A.card ^ 3 := good_vertex_mul_local_le_cube_of_good v.2

theorem goodInduced_local_le_cube_div {N : ℕ} {A : Finset ℕ}
    (hN : 0 < N) (v : SumGraphGoodVertex N A) :
    (neighborhoodEdges
      ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        A.card ^ 3 / N := by
  apply (Nat.le_div_iff_mul_le hN).2
  simpa [Nat.mul_comm] using! goodInduced_mul_local_le_cube v

theorem degree_goodInducedSumGraph_le {N : ℕ} {A : Finset ℕ}
    (v : SumGraphGoodVertex N A) :
    ((sumGraph N A).induce
      {v | SumGraphGood N A v}).degree v ≤ A.card := by
  exact (degree_induce_le (sumGraph N A)
    {v | SumGraphGood N A v} v).trans
      (degree_sumGraph_le_card A v.1)

/-- Forget that vertices lie in the good-vertex subtype. -/
def liftGoodVertexFinset {N : ℕ} {A : Finset ℕ}
    (C : Finset (SumGraphGoodVertex N A)) : Finset (Fin N) :=
  C.map (Function.Embedding.subtype {v | SumGraphGood N A v})

@[simp]
theorem card_liftGoodVertexFinset {N : ℕ} {A : Finset ℕ}
    (C : Finset (SumGraphGoodVertex N A)) :
    (liftGoodVertexFinset C).card = C.card := by
  exact card_map _

theorem isIndepSet_liftGoodVertexFinset
    {N : ℕ} {A : Finset ℕ} {C : Finset (SumGraphGoodVertex N A)}
    (hC : (goodInducedSumGraph N A).IsIndepSet
      (C : Set (SumGraphGoodVertex N A))) :
    (sumGraph N A).IsIndepSet (liftGoodVertexFinset C : Set (Fin N)) := by
  rw [SimpleGraph.isIndepSet_iff] at hC ⊢
  intro x hx y hy hxy
  change x ∈ liftGoodVertexFinset C at hx
  change y ∈ liftGoodVertexFinset C at hy
  rw [liftGoodVertexFinset, mem_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hxy' : x ≠ y := by
    intro h
    exact hxy (congrArg Subtype.val h)
  exact hC (by simpa using! hx) (by simpa using! hy) hxy'

theorem normalizedAdmissible_liftGoodVertexFinset
    {N : ℕ} {A : Finset ℕ} {C : Finset (SumGraphGoodVertex N A)}
    (hC : (goodInducedSumGraph N A).IsIndepSet
      (C : Set (SumGraphGoodVertex N A))) :
    NormalizedAdmissible A (liftGoodVertexFinset C) :=
  normalizedAdmissible_iff_isIndepSet.mpr
    (isIndepSet_liftGoodVertexFinset hC)

theorem indepNum_goodInducedSumGraph_le (N : ℕ) (A : Finset ℕ) :
    (goodInducedSumGraph N A).indepNum ≤ (sumGraph N A).indepNum := by
  obtain ⟨C, hC⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := goodInducedSumGraph N A)
  calc
    (goodInducedSumGraph N A).indepNum = C.card := hC.card_eq.symm
    _ = (liftGoodVertexFinset C).card := (card_liftGoodVertexFinset C).symm
    _ ≤ (sumGraph N A).indepNum :=
      (isIndepSet_liftGoodVertexFinset hC.isIndepSet).card_le_indepNum

end

end Erdos788
