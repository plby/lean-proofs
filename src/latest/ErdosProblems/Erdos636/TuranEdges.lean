import Mathlib

/-!
# A total-edge form of the Caro--Wei bound

This file records the exact finite inequality used in the proof of Erdős
Problem 636.  If a finite simple graph has `v` vertices and `e` edges, it has
an independent set `S` such that

`v ^ 2 ≤ S.card * (v + 2 * e)`.

The proof first establishes the Caro--Wei bound and then applies
Cauchy--Schwarz together with the degree-sum identity.
-/

namespace Erdos636

open Finset Fintype

variable {V : Type*} [Fintype V]

/-- The Caro--Wei bound: the independence number is at least the sum of the
reciprocals of one plus the vertex degrees. -/
theorem caroWei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
  classical
  induction n : Fintype.card V using Nat.strong_induction_on generalizing V G with
  | h n ih =>
    by_cases hV : Nonempty V
    · obtain ⟨v, hvmin_eq⟩ :=
        @SimpleGraph.exists_minimal_degree_vertex V G inferInstance inferInstance hV
      have hvmin : ∀ u : V, G.degree v ≤ G.degree u := by
        intro u
        rw [← hvmin_eq]
        exact G.minDegree_le_degree u
      let S : Finset V := insert v (G.neighborFinset v)
      let W : Type _ := {x : V // x ∉ S}
      let G' : SimpleGraph W := SimpleGraph.comap (fun x : W => x.val) G
      have hS_card : S.card = G.degree v + 1 := by
        simp [S]
      have hW_lt : Fintype.card W < Fintype.card V := by
        dsimp [W]
        rw [Fintype.card_subtype]
        exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨v, by simp [S]⟩)
      have h_ind :
          (∑ u : W, (1 : ℝ) / (G'.degree u + 1)) ≤ (G'.indepNum : ℝ) :=
        ih (Fintype.card W) (by rw [← n]; exact hW_lt) G' rfl
      have hdeg_le : ∀ u : W, G'.degree u ≤ G.degree u.val := by
        intro u
        let emb : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
        change (G'.neighborFinset u).card ≤ (G.neighborFinset u.val).card
        calc
          (G'.neighborFinset u).card = ((G'.neighborFinset u).map emb).card := by
            rw [Finset.card_map]
          _ ≤ (G.neighborFinset u.val).card := by
            refine Finset.card_le_card ?_
            intro y hy
            rw [Finset.mem_map] at hy
            rcases hy with ⟨x, hx, rfl⟩
            rw [SimpleGraph.mem_neighborFinset] at hx ⊢
            simpa [G', emb] using hx
      have hS_sum : ∑ u ∈ S, (1 : ℝ) / (G.degree u + 1) ≤ 1 := by
        calc
          ∑ u ∈ S, (1 : ℝ) / (G.degree u + 1)
              ≤ ∑ u ∈ S, (1 : ℝ) / (G.degree v + 1) := by
            refine Finset.sum_le_sum ?_
            intro u _hu
            have hle : ((G.degree v : ℝ) + 1) ≤ ((G.degree u : ℝ) + 1) := by
              exact_mod_cast Nat.succ_le_succ (hvmin u)
            exact one_div_le_one_div_of_le (by positivity) hle
          _ = 1 := by
            rw [Finset.sum_const, hS_card, nsmul_eq_mul]
            have hpos : (0 : ℝ) < (G.degree v : ℝ) + 1 := by positivity
            field_simp [Nat.cast_add, hpos.ne']
            norm_num [Nat.cast_add]
      have hout_eq :
          (∑ u ∈ Finset.univ \ S, (1 : ℝ) / (G.degree u + 1)) =
            ∑ u : W, (1 : ℝ) / (G.degree u.val + 1) := by
        have hfilter :
            (Finset.univ \ S : Finset V) = Finset.univ.filter (fun x : V => x ∉ S) := by
          ext x
          simp
        rw [hfilter]
        symm
        simpa [W] using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset V))
            (p := fun x : V => x ∉ S)
            (f := fun x : V => (1 : ℝ) / (G.degree x + 1)))
      have hout_sum :
          (∑ u ∈ Finset.univ \ S, (1 : ℝ) / (G.degree u + 1)) ≤
            ∑ u : W, (1 : ℝ) / (G'.degree u + 1) := by
        rw [hout_eq]
        refine Finset.sum_le_sum ?_
        intro u _hu
        have hle : ((G'.degree u : ℝ) + 1) ≤ ((G.degree u.val : ℝ) + 1) := by
          exact_mod_cast Nat.succ_le_succ (hdeg_le u)
        exact one_div_le_one_div_of_le (by positivity) hle
      have hsum_total :
          (∑ u : V, (1 : ℝ) / (G.degree u + 1)) ≤
            1 + ∑ u : W, (1 : ℝ) / (G'.degree u + 1) := by
        have hsplit :
            (∑ u : V, (1 : ℝ) / (G.degree u + 1)) =
              ∑ u ∈ S, (1 : ℝ) / (G.degree u + 1) +
                ∑ u ∈ Finset.univ \ S, (1 : ℝ) / (G.degree u + 1) := by
          calc
            (∑ u : V, (1 : ℝ) / (G.degree u + 1)) =
                ∑ u ∈ (Finset.univ : Finset V),
                  (1 : ℝ) / (G.degree u + 1) := rfl
            _ = ∑ u ∈ Finset.univ \ S, (1 : ℝ) / (G.degree u + 1) +
                  ∑ u ∈ S, (1 : ℝ) / (G.degree u + 1) := by
              exact (Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
                (f := fun u : V => (1 : ℝ) / (G.degree u + 1))
                (Finset.subset_univ S)).symm
            _ = ∑ u ∈ S, (1 : ℝ) / (G.degree u + 1) +
                  ∑ u ∈ Finset.univ \ S, (1 : ℝ) / (G.degree u + 1) := by ring
        rw [hsplit]
        linarith [hS_sum, hout_sum]
      have halpha_nat : 1 + G'.indepNum ≤ G.indepNum := by
        obtain ⟨I', hI'⟩ := G'.exists_isNIndepSet_indepNum
        let emb : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
        let I0 : Finset V := I'.map emb
        let I : Finset V := insert v I0
        have hv_not_I0 : v ∉ I0 := by
          intro hvI0
          rw [Finset.mem_map] at hvI0
          rcases hvI0 with ⟨x, _hxI', hxv⟩
          have hxval : x.val = v := by simpa [emb] using hxv
          have hxS : x.val ∈ S := by
            rw [hxval]
            simp [S]
          exact x.property hxS
        have hI_indep : G.IsIndepSet (I : Set V) := by
          intro x hx y hy hxy
          simp [I] at hx hy
          rcases hx with rfl | hxI0
          · rcases hy with rfl | hyI0
            · exact (hxy rfl).elim
            · intro hxy_adj
              rw [Finset.mem_map] at hyI0
              rcases hyI0 with ⟨y', _hyI', rfl⟩
              exact y'.property (by
                simp [S, SimpleGraph.mem_neighborFinset,
                  Or.inr (by simpa [emb] using hxy_adj)])
          · rcases hy with rfl | hyI0
            · intro hxy_adj
              rw [Finset.mem_map] at hxI0
              rcases hxI0 with ⟨x', _hxI', rfl⟩
              exact x'.property (by
                simp [S, SimpleGraph.mem_neighborFinset,
                  Or.inr (by simpa [emb] using hxy_adj.symm)])
            · intro hxy_adj
              rw [Finset.mem_map] at hxI0 hyI0
              rcases hxI0 with ⟨x', hxI', rfl⟩
              rcases hyI0 with ⟨y', hyI', rfl⟩
              have hxy' : x' ≠ y' := by
                intro hxy_sub
                exact hxy (by simpa [emb] using congrArg Subtype.val hxy_sub)
              exact (hI'.isIndepSet hxI' hyI' hxy')
                (by simpa [G', emb] using hxy_adj)
        have hI_card : I.card = 1 + G'.indepNum := by
          rw [Finset.card_insert_of_notMem hv_not_I0]
          rw [Finset.card_map, hI'.card_eq]
          omega
        have hle := hI_indep.card_le_indepNum (G := G)
        rw [hI_card] at hle
        exact hle
      have halpha : 1 + (G'.indepNum : ℝ) ≤ (G.indepNum : ℝ) := by
        exact_mod_cast halpha_nat
      calc
        (∑ u : V, (1 : ℝ) / (G.degree u + 1)) ≤
            1 + ∑ u : W, (1 : ℝ) / (G'.degree u + 1) := hsum_total
        _ ≤ 1 + (G'.indepNum : ℝ) := by linarith
        _ ≤ (G.indepNum : ℝ) := halpha
    · have huniv : (Finset.univ : Finset V) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v _hv
        exact hV ⟨v⟩
      rw [show (∑ v : V, (1 : ℝ) / (G.degree v + 1)) = 0 by simp [huniv]]
      exact Nat.cast_nonneg G.indepNum

/-- Cauchy--Schwarz and the degree-sum formula put the Caro--Wei bound in
terms of only the total numbers of vertices and edges. -/
theorem card_sq_le_indepNum_mul_card_add_twice_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ^ 2 ≤ G.indepNum * (Fintype.card V + 2 * G.edgeFinset.card) := by
  classical
  by_cases hV : Nonempty V
  · have h_jensen :
        (Fintype.card V : ℝ) ^ 2 /
            (∑ v : V, ((G.degree v + 1 : ℕ) : ℝ)) ≤
          ∑ v : V, (1 : ℝ) / (G.degree v + 1) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun v : V => 1 / Real.sqrt (G.degree v + 1))
        (fun v : V => Real.sqrt (G.degree v + 1))
      simp_all +decide only [Nat.cast_add, Nat.cast_one, one_div, ge_iff_le,
        Real.sq_sqrt (add_nonneg (Nat.cast_nonneg _) zero_le_one)]
      simp_all +decide
        [ne_of_gt (Real.sqrt_pos.mpr
          (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))]
      have hsqrt (v : V) :
          Real.sqrt ((G.degree v : ℝ) + 1) ^ 2 = (G.degree v : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      simp_rw [hsqrt] at hcs
      exact div_le_of_le_mul₀
        (Finset.sum_nonneg fun _ _ => by positivity)
        (Finset.sum_nonneg fun _ _ => by positivity)
        hcs
    have hdenpos : 0 < ∑ v : V, ((G.degree v + 1 : ℕ) : ℝ) := by
      let v : V := Classical.choice hV
      exact Finset.sum_pos'
        (fun _ _ => by positivity)
        ⟨v, Finset.mem_univ v, by positivity⟩
    have hproduct :
        (Fintype.card V : ℝ) ^ 2 ≤
          (∑ v : V, (1 : ℝ) / (G.degree v + 1)) *
            (∑ v : V, ((G.degree v + 1 : ℕ) : ℝ)) :=
      (div_le_iff₀ hdenpos).mp h_jensen
    have hcw := caroWei G
    have hbound :
        (Fintype.card V : ℝ) ^ 2 ≤
          (G.indepNum : ℝ) * (∑ v : V, ((G.degree v + 1 : ℕ) : ℝ)) :=
      hproduct.trans (mul_le_mul_of_nonneg_right hcw hdenpos.le)
    have hsumNat :
        ∑ v : V, (G.degree v + 1) =
          2 * G.edgeFinset.card + Fintype.card V := by
      simp [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges]
    have hsumReal :
        (∑ v : V, ((G.degree v + 1 : ℕ) : ℝ)) =
          2 * G.edgeFinset.card + Fintype.card V := by
      exact_mod_cast hsumNat
    rw [hsumReal] at hbound
    have hbound' :
        (Fintype.card V : ℝ) ^ 2 ≤
          (G.indepNum : ℝ) *
            ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)) := by
      simpa [add_comm] using hbound
    exact_mod_cast hbound'
  · have hcard : Fintype.card V = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun v => hV ⟨v⟩⟩
    simp [hcard]

/-- Exact Turán/Caro--Wei inequality, with an independent set as a witness. -/
theorem exists_indepSet_card_sq_le_card_mul_card_add_twice_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, G.IsIndepSet S ∧
      Fintype.card V ^ 2 ≤ S.card * (Fintype.card V + 2 * G.edgeFinset.card) := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  refine ⟨S, hS.isIndepSet, ?_⟩
  simpa [hS.card_eq] using card_sq_le_indepNum_mul_card_add_twice_edges G

/-- Threshold form: if `r (v + 2e) < v²`, then there is an independent set
with more than `r` vertices. -/
theorem exists_indepSet_card_gt_of_mul_card_add_twice_edges_lt_sq
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (h : r * (Fintype.card V + 2 * G.edgeFinset.card) < Fintype.card V ^ 2) :
    ∃ S : Finset V, G.IsIndepSet S ∧ r < S.card := by
  obtain ⟨S, hS, hbound⟩ :=
    exists_indepSet_card_sq_le_card_mul_card_add_twice_edges G
  refine ⟨S, hS, ?_⟩
  by_contra hnot
  have hcard : S.card ≤ r := Nat.le_of_not_gt hnot
  have hfactor : 0 ≤ Fintype.card V + 2 * G.edgeFinset.card := Nat.zero_le _
  have := Nat.mul_le_mul_right (Fintype.card V + 2 * G.edgeFinset.card) hcard
  omega

/-- Contrapositive threshold form: a uniform upper bound on independent-set
sizes forces the corresponding total-edge inequality. -/
theorem card_sq_le_mul_card_add_twice_edges_of_indepSet_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (h : ∀ S : Finset V, G.IsIndepSet S → S.card ≤ r) :
    Fintype.card V ^ 2 ≤ r * (Fintype.card V + 2 * G.edgeFinset.card) := by
  obtain ⟨S, hS, hbound⟩ :=
    exists_indepSet_card_sq_le_card_mul_card_add_twice_edges G
  exact hbound.trans (Nat.mul_le_mul_right _ (h S hS))

/-- If the total edge count is at most `v*d`, the exact inequality simplifies
to the usual average-degree threshold `v ≤ |S| (1 + 2d)`. -/
theorem exists_indepSet_card_le_average_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hedges : G.edgeFinset.card ≤ Fintype.card V * d) :
    ∃ S : Finset V, G.IsIndepSet S ∧
      Fintype.card V ≤ S.card * (1 + 2 * d) := by
  obtain ⟨S, hS, hbound⟩ :=
    exists_indepSet_card_sq_le_card_mul_card_add_twice_edges G
  refine ⟨S, hS, ?_⟩
  by_cases hv : Fintype.card V = 0
  · simp [hv]
  have hvpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hv
  have hfactor :
      Fintype.card V + 2 * G.edgeFinset.card ≤
        Fintype.card V * (1 + 2 * d) := by
    nlinarith only [hedges]
  have hsquare :
      Fintype.card V ^ 2 ≤ S.card * (Fintype.card V * (1 + 2 * d)) :=
    hbound.trans (Nat.mul_le_mul_left S.card hfactor)
  exact Nat.le_of_mul_le_mul_left (c := Fintype.card V)
    (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsquare) hvpos

end Erdos636
