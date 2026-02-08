/-

This is a Lean formalization of a solution to Erdős Problem 666.
https://www.erdosproblems.com/forum/thread/666

The original proof was found by: Chung and Brouwer & Dejter &
Thomassen

[Ch92] Chung, Fan R. K., Subgraphs of a hypercube containing no small
even cycles. J. Graph Theory (1992), 273-286.

[BDT93] Brouwer, A. E. and Dejter, I. J. and Thomassen, C., Highly
symmetric subgraphs of hypercubes. J. Algebraic Combin. (1993), 25-29.


A proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We define the hypercube graph Q_n and a partition of its edges into four subgraphs G_ab. We prove that each G_ab is C_6-free. As a corollary, we show that for any epsilon > 0, there exists a subgraph of Q_n with at least epsilon |E(Q_n)| edges that is C_6-free, disproving a density conjecture.
-/

import Mathlib

namespace Erdos666

open scoped Classical
open SimpleGraph

set_option maxHeartbeats 0

/-
Definition of the hypercube graph Q_n and the property of containing a cycle of length k.
-/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → ZMod 2) where
  Adj x y := hammingDist x y = 1
  symm x y h := by
    -- Since the Hamming distance is symmetric, if hammingDist x y = 1, then hammingDist y x = 1 as well.
    simp [hammingDist] at h ⊢;
    simpa only [ eq_comm ] using h
  loopless x h := by
    -- The Hamming distance between a vertex and itself is 0, not 1.
    simp [hammingDist] at h

def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = k

/-
Definition of edge direction: the index where two adjacent vertices differ.
-/
noncomputable def edgeDirection {n : ℕ} (x y : Fin n → ZMod 2) (h : hammingDist x y = 1) : Fin n :=
  (Finset.univ.filter (fun i => x i ≠ y i)).min' (by
  contrapose! h; simp_all +decide [ hammingDist ] ;)

/-
Definition of lower endpoint: the endpoint with 0 at the differing coordinate.
-/
noncomputable def lowerEndpoint {n : ℕ} (x y : Fin n → ZMod 2) (h : hammingDist x y = 1) : Fin n → ZMod 2 :=
  if x (edgeDirection x y h) = 0 then x else y

/-
Definition of L: sum of coordinates of the lower endpoint with index less than the edge direction.
-/
noncomputable def L {n : ℕ} (x y : Fin n → ZMod 2) (h : hammingDist x y = 1) : ZMod 2 :=
  let u := lowerEndpoint x y h
  let i := edgeDirection x y h
  ∑ t ∈ Finset.univ.filter (· < i), u t

/-
Definition of R: sum of coordinates of the lower endpoint with index greater than the edge direction.
-/
noncomputable def R {n : ℕ} (x y : Fin n → ZMod 2) (h : hammingDist x y = 1) : ZMod 2 :=
  let u := lowerEndpoint x y h
  let i := edgeDirection x y h
  ∑ t ∈ Finset.univ.filter (i < ·), u t

/-
Definition of walkIndices: the list of indices flipped along a walk.
-/
noncomputable def walkIndices {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) : List (Fin n) :=
  match p with
  | Walk.nil => []
  | Walk.cons h p' => edgeDirection _ _ h :: walkIndices p'

/-
Lemma: The coordinate v_i is equal to u_i plus the number of times direction i appears in the walk, modulo 2.
-/
theorem walk_coordinate_change {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) (i : Fin n) :
  v i = u i + ((walkIndices p).count i : ZMod 2) := by
    induction' p with u v p ih generalizing i;
    · exact left_eq_add.mpr rfl;
    · rename_i h hp ihp;
      -- Since $v$ and $p$ differ in exactly one coordinate, we have $p i = v i + 1$ if $i$ is the differing coordinate, and $p i = v i$ otherwise.
      have h_diff : ∀ i, p i = if i = edgeDirection v p h then v i + 1 else v i := by
        intro i
        by_cases hi : i = edgeDirection v p h;
        · have h_diff : v (edgeDirection v p h) ≠ p (edgeDirection v p h) := by
            have := Finset.min'_mem ( Finset.univ.filter fun i => v i ≠ p i ) ⟨ edgeDirection v p h, by
              exact Finset.min'_mem _ _ ⟩ ; aesop;
          cases Fin.exists_fin_two.mp ⟨ v ( edgeDirection v p h ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ p ( edgeDirection v p h ), rfl ⟩ <;> aesop;
        · have h_diff : ∀ i, i ≠ edgeDirection v p h → v i = p i := by
            intros i hi
            have h_diff : ∀ i, i ≠ edgeDirection v p h → v i = p i := by
              intro i hi
              have h_diff : Finset.filter (fun j => v j ≠ p j) Finset.univ = {edgeDirection v p h} := by
                have h_diff : Finset.card (Finset.filter (fun j => v j ≠ p j) Finset.univ) = 1 := by
                  convert h using 1;
                rw [ Finset.card_eq_one ] at h_diff;
                obtain ⟨ a, ha ⟩ := h_diff; simp_all +decide [ Finset.ext_iff ] ;
                have h_diff : Finset.filter (fun j => v j ≠ p j) Finset.univ = {a} := by
                  grind;
                unfold edgeDirection; aesop;
              rw [ Finset.ext_iff ] at h_diff; specialize h_diff i; aesop;
            exact h_diff i hi;
          grind;
      simp_all +singlePass [ walkIndices ];
      split_ifs <;> simp_all +decide [ List.count_cons ];
      · ring;
      · tauto

/-
Lemma: In any cycle, each coordinate direction appears an even number of times.
-/
theorem cycle_indices_even_count {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (i : Fin n) :
  (walkIndices p).count i % 2 = 0 := by
    -- By definition of $walkIndices$, we know that $walkIndices p$ contains the list of indices flipped along the walk.
    have h_walk_indices : u i = u i + ((walkIndices p).count i : ZMod 2) := by
      convert walk_coordinate_change p i;
    erw [ ← ZMod.val_natCast ] ; aesop

/-
Definition of directionsUsed and lemma: if a direction is used in a cycle, it appears at least twice.
-/
noncomputable def directionsUsed {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) : Finset (Fin n) :=
  (walkIndices p).toFinset

theorem cycle_directions_count_ge_two {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (i : Fin n) :
  i ∈ directionsUsed p → (walkIndices p).count i ≥ 2 := by
    -- If a direction $i$ is used in the cycle $p$, then the number of times it appears in the walk is even.
    have h_even_count : i ∈ directionsUsed p → Even ((walkIndices p).count i) := by
      exact fun hi => Nat.even_iff.mpr ( cycle_indices_even_count p i );
    intro hi
    have h_even : Even ((walkIndices p).count i) := h_even_count hi
    have h_pos : 0 < (walkIndices p).count i := by
      exact List.count_pos_iff.mpr ( by unfold directionsUsed at hi; aesop )
    exact Nat.le_of_dvd h_pos (even_iff_two_dvd.mp h_even)

/-
Lemma: For any walk, all vertices in the walk agree with the starting vertex on coordinates that are not in the set of used directions.
-/
theorem walk_support_in_subcube {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) :
  ∀ w ∈ p.support, ∀ i ∉ directionsUsed p, w i = u i := by
    -- We proceed by induction on the length of the walk.
    induction' p with p ih;
    · simp +zetaDelta at *;
    · unfold directionsUsed at *; simp_all +decide
      -- Since the walkIndices of the cons is the edgeDirection of h plus the walkIndices of the original walk, if i is not in the walkIndices of the cons, it means i is not in the edgeDirection of h and not in the walkIndices of the original walk.
      intros a ha i hi
      by_cases hi_edge : i = edgeDirection _ _ ‹_›;
      · exact False.elim <| hi <| by rw [ hi_edge ] ; exact List.mem_cons_self;
      · rename_i h₁ h₂ h₃ h₄; simp_all +decide [ walkIndices ] ;
        -- Since $i$ is not equal to the edge direction, the value at $i$ in $v✝$ is the same as in $ih$.
        have h_value_eq : ∀ (x y : Fin n → ZMod 2) (h : hammingDist x y = 1), ∀ i, i ≠ edgeDirection x y h → x i = y i := by
          intros x y h i hi; unfold edgeDirection at hi; simp_all +decide [ Finset.min' ] ;
          contrapose! hi; simp_all +decide
          refine' le_antisymm _ _ <;> simp_all +decide
          · intro j hj; have := Finset.card_eq_one.mp h; obtain ⟨ k, hk ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
          · exact ⟨ i, hi, le_rfl ⟩;
        rw [ h_value_eq _ _ h₂ i hi_edge ]

/-
Lemma: The number of distinct directions used in a 6-cycle is at most 3.
-/
theorem cycle_directions_card_le_three {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (hlen : p.length = 6) :
  (directionsUsed p).card ≤ 3 := by
    -- Since the walk is a cycle, the number of times each coordinate appears in the walk is even. Therefore, the number of distinct directions used is at most half the length of the walk.
    have h_even_count : ∀ i ∈ directionsUsed p, (walkIndices p).count i ≥ 2 := by
      exact fun i a => cycle_directions_count_ge_two p i a
    generalize_proofs at *; (
    -- The sum of the counts of all directions in the walk is equal to the length of the walk.
    have h_sum_counts : ∑ i ∈ directionsUsed p, (walkIndices p).count i = p.length := by
      have h_sum_counts : ∀ {l : List (Fin n)}, (∑ i ∈ l.toFinset, List.count i l) = l.length := by
        exact fun {l} => List.sum_toFinset_count_eq_length l
      generalize_proofs at *; (
      convert h_sum_counts using 1
      generalize_proofs at *; (
      -- The length of the walk is equal to the number of edges, and each edge corresponds to a direction in the walkIndices.
      have h_walk_length : ∀ {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v), p.length = (walkIndices p).length := by
        intros u v p; induction p <;> aesop;
      generalize_proofs at *; (
      exact h_walk_length p ▸ rfl)))
    generalize_proofs at *; (
    have := Finset.sum_le_sum h_even_count; simp_all +decide ; linarith;))

/-
Lemma: The number of distinct vertices in a walk is at most 2 raised to the power of the number of distinct directions used.
-/
theorem support_card_le_two_pow_directions_card {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) :
  p.support.toFinset.card ≤ 2 ^ (directionsUsed p).card := by
    -- Any vertex in the support of the walk agrees with the starting vertex on coordinates that are not in the set of used directions.
    have h_support_subset : ∀ w ∈ p.support, w ∈ Finset.image (fun t : Finset (Fin n) => u + ∑ i ∈ t, Pi.single i 1) (Finset.powerset (directionsUsed p)) := by
      -- Let $w$ be a vertex in the support of $p$. By definition of support, $w$ is reachable from $u$ by following the edges of $p$.
      intro w hw
      have hw_eq : ∀ i ∉ directionsUsed p, w i = u i := by
        exact fun i a => walk_support_in_subcube p w hw i a;
      -- Since $w$ agrees with $u$ on all coordinates not in the set of used directions, we can express $w$ as $u$ plus the sum of the coordinates where $w$ and $u$ differ.
      have hw_diff : w = u + ∑ i ∈ Finset.univ.filter (fun i => w i ≠ u i), Pi.single i 1 := by
        ext i; by_cases hi : w i = u i <;> simp_all +decide [ Finset.sum_apply, Pi.single_apply ] ;
        cases Fin.exists_fin_two.mp ⟨ w i, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ u i, rfl ⟩ <;> aesop;
      refine' Finset.mem_image.mpr ⟨ Finset.univ.filter ( fun i => w i ≠ u i ), _, _ ⟩ <;> simp +decide [ Finset.subset_iff ];
      · exact fun i hi => Classical.not_not.1 fun hi' => hi <| hw_eq i hi';
      · exact hw_diff.symm;
    exact le_trans ( Finset.card_le_card <| show p.support.toFinset ⊆ Finset.image ( fun t : Finset ( Fin n ) => u + ∑ i ∈ t, Pi.single i 1 ) ( Finset.powerset ( directionsUsed p ) ) from fun x hx => by simpa using h_support_subset x <| List.mem_toFinset.mp hx ) <| Finset.card_image_le.trans <| by simp +decide

/-
Lemma: For a simple cycle of length at least 3, the number of distinct vertices is equal to the length of the cycle.
-/
theorem cycle_support_card_eq_length {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V} (p : G.Walk u u) (hp : p.IsCycle) (hn : p.length ≥ 3) :
  p.support.toFinset.card = p.length := by
    rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.isCycle_def ];
    rw [ List.toFinset_card_of_nodup ] <;> aesop

/-
Lemma: Any cycle of length 6 in the hypercube graph must use at least 3 distinct directions.
-/
theorem cycle_directions_card_ge_three {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (hp : p.IsCycle) (hlen : p.length = 6) :
  (directionsUsed p).card ≥ 3 := by
    -- The number of distinct vertices in the cycle is equal to the length of the cycle, which is 6.
    have h_support_card : p.support.toFinset.card = 6 := by
      convert cycle_support_card_eq_length p hp ( by linarith );
      exact hlen.symm;
    exact le_of_not_gt fun h : ( directionsUsed p |> Finset.card ) < 3 => by have := support_card_le_two_pow_directions_card p; interval_cases directionsUsed p |> Finset.card <;> simp_all +decide ;

/-
Lemma: Any cycle of length 6 in the hypercube graph uses exactly 3 distinct directions.
-/
theorem cycle_directions_card_eq_three {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (hp : p.IsCycle) (hlen : p.length = 6) :
  (directionsUsed p).card = 3 := by
    have := cycle_directions_card_le_three p hlen; ( have := cycle_directions_card_ge_three p hp hlen; interval_cases _ : Finset.card ( directionsUsed p ) ; );
    rfl

/-
Lemma: Every 6-cycle in Q_n is contained in a 3-dimensional subcube.
-/
theorem C6_in_Q3 {n : ℕ} {u : Fin n → ZMod 2} (C : (hypercubeGraph n).Walk u u) (hC : C.IsCycle) (hlen : C.length = 6) :
  ∃ (S : Finset (Fin n)), S.card = 3 ∧ ∀ v ∈ C.support, ∀ i ∉ S, v i = u i := by
    -- By cycle_directions_card_eq_three, there are exactly 3 distinct directions used in the cycle.
    have h_card : (directionsUsed C).card = 3 := by
      apply cycle_directions_card_eq_three C hC hlen;
    exact ⟨ _, h_card, fun v hv i hi => walk_support_in_subcube C v hv i hi ⟩

/-
Lemma: edgeDirection is commutative.
-/
theorem edgeDirection_comm {n : ℕ} (x y : Fin n → ZMod 2) (h : hammingDist x y = 1) (h' : hammingDist y x = 1) :
  edgeDirection x y h = edgeDirection y x h' := by
    -- Since the Hamming distance is 1, there's exactly one index where x and y differ. Therefore, the set of indices where x and y differ is the same as the set where y and x differ.
    have h_diff_set : Finset.univ.filter (fun i => x i ≠ y i) = Finset.univ.filter (fun i => y i ≠ x i) := by
      grind;
    unfold edgeDirection; aesop;

/-
Definition of the partition subgraphs G_ab.
-/
def partitionGraph (n : ℕ) (ab : Fin 2 × Fin 2) : SimpleGraph (Fin n → ZMod 2) where
  Adj x y := ∃ h : hammingDist x y = 1, L x y h = ab.1 ∧ R x y h = ab.2
  symm x y := by
    simp +zetaDelta at *;
    intro h1 h2 h3;
    -- Since the hamming distance is symmetric, we can use h1 to construct the required h for y and x.
    have h_symm : hammingDist y x = 1 := by
      rw [ hammingDist_comm, h1 ];
    unfold L R at *;
    -- Since the lower endpoint is the same for both x and y, the sums should be equal.
    have h_lower_eq : lowerEndpoint x y h1 = lowerEndpoint y x h_symm := by
      unfold lowerEndpoint;
      have h_lower_eq : edgeDirection x y h1 = edgeDirection y x h_symm := by
        apply edgeDirection_comm;
      have h_lower_eq : x (edgeDirection x y h1) ≠ y (edgeDirection x y h1) := by
        have h_lower_eq : Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1 := by
          convert h1 using 1;
        exact Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun i => x i ≠ y i ) Finset.univ ) ( Finset.card_pos.mp ( by linarith ) ) ) |>.2;
      cases Fin.exists_fin_two.mp ⟨ x ( edgeDirection x y h1 ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ y ( edgeDirection x y h1 ), rfl ⟩ <;> simp_all +decide only;
      · contradiction;
      · simp +decide [ ZMod ];
      · exact rfl;
      · contradiction;
    have h_edge_eq : edgeDirection x y h1 = edgeDirection y x h_symm := by
      exact edgeDirection_comm x y h1 h_symm;
    aesop
  loopless x := by
    simp +zetaDelta at *

/-
Lemma: The subgraphs G_ab form an edge partition of the hypercube graph.
-/
theorem partitionGraph_is_partition (n : ℕ) :
  ∀ u v, (hypercubeGraph n).Adj u v ↔ ∃! ab, (partitionGraph n ab).Adj u v := by
    intro u v;
    by_cases h : hammingDist u v = 1 <;> simp +decide [ ExistsUnique ];
    · -- Since the edge is adjacent in the hypercube graph, it must be adjacent in exactly one of the partition graphs.
      have h_adj : ∃ ab : Fin 2 × Fin 2, (partitionGraph n ab).Adj u v := by
        exact ⟨ ⟨ L u v h, R u v h ⟩, h, rfl, rfl ⟩;
      rcases h_adj with ⟨ ab, hab ⟩ ; fin_cases ab <;> simp_all +decide [ partitionGraph ] ;
      · exact h;
      · exact h;
      · exact h;
      · exact h;
    · unfold partitionGraph; aesop;

/-
Lemma: In a Q3 determined by p < q < r, the sum of L values for two edges in direction q equals the sum of their p-coordinates, and similarly for R and r-coordinates.
-/
theorem L_R_differences_in_Q3 {n : ℕ} {p q r : Fin n} (hpq : p < q) (hqr : q < r)
  (u : Fin n → ZMod 2)
  (x₁ y₁ x₂ y₂ : Fin n → ZMod 2)
  (h₁ : hammingDist x₁ y₁ = 1) (h₂ : hammingDist x₂ y₂ = 1)
  (hdir₁ : edgeDirection x₁ y₁ h₁ = q) (hdir₂ : edgeDirection x₂ y₂ h₂ = q)
  (hsupp₁ : ∀ i, i ≠ p → i ≠ q → i ≠ r → x₁ i = u i)
  (hsupp₂ : ∀ i, i ≠ p → i ≠ q → i ≠ r → x₂ i = u i) :
  L x₁ y₁ h₁ + L x₂ y₂ h₂ = (lowerEndpoint x₁ y₁ h₁) p + (lowerEndpoint x₂ y₂ h₂) p ∧
  R x₁ y₁ h₁ + R x₂ y₂ h₂ = (lowerEndpoint x₁ y₁ h₁) r + (lowerEndpoint x₂ y₂ h₂) r := by
    have hsum_L : L x₁ y₁ h₁ + L x₂ y₂ h₂ = lowerEndpoint x₁ y₁ h₁ p + lowerEndpoint x₂ y₂ h₂ p := by
      have hsum_L : L x₁ y₁ h₁ + L x₂ y₂ h₂ = ∑ t ∈ Finset.univ.filter (· < q), (lowerEndpoint x₁ y₁ h₁ t + lowerEndpoint x₂ y₂ h₂ t) := by
        unfold L; rw [ Finset.sum_add_distrib ] ;
        aesop;
      -- Since $t < q$, we know that $lowerEndpoint x₁ y₁ h₁ t = lowerEndpoint x₂ y₂ h₂ t$ for all $t \neq p$.
      have h_lower_eq : ∀ t, t < q → t ≠ p → lowerEndpoint x₁ y₁ h₁ t = lowerEndpoint x₂ y₂ h₂ t := by
        intros t ht ht_ne_p
        have h_lower_eq : lowerEndpoint x₁ y₁ h₁ t = x₁ t ∧ lowerEndpoint x₂ y₂ h₂ t = x₂ t := by
          have h_lower_eq : t ∉ Finset.univ.filter (fun i => x₁ i ≠ y₁ i) ∧ t ∉ Finset.univ.filter (fun i => x₂ i ≠ y₂ i) := by
            have h_lower_eq : ∀ i, i ∈ Finset.univ.filter (fun i => x₁ i ≠ y₁ i) → i ≥ q := by
              intros j hj; exact (by
              exact hdir₁ ▸ Finset.min'_le _ _ hj);
            have h_lower_eq' : ∀ i, i ∈ Finset.univ.filter (fun i => x₂ i ≠ y₂ i) → i ≥ q := by
              intros i hi
              have h_lower_eq' : i ≥ edgeDirection x₂ y₂ h₂ := by
                exact Finset.min'_le _ _ ( by aesop )
              rw [hdir₂] at h_lower_eq'
              exact h_lower_eq'
            exact ⟨fun h => ht.not_ge (h_lower_eq t h), fun h => ht.not_ge (h_lower_eq' t h)⟩
          unfold lowerEndpoint; aesop;
        rw [ h_lower_eq.1, h_lower_eq.2, hsupp₁ t ht_ne_p ( ne_of_lt ht ) ( ne_of_lt ( lt_trans ht hqr ) ), hsupp₂ t ht_ne_p ( ne_of_lt ht ) ( ne_of_lt ( lt_trans ht hqr ) ) ];
      rw [ hsum_L, Finset.sum_eq_single p ] <;> simp_all +decide
      grind +ring
    have hsum_R : R x₁ y₁ h₁ + R x₂ y₂ h₂ = lowerEndpoint x₁ y₁ h₁ r + lowerEndpoint x₂ y₂ h₂ r := by
      unfold R lowerEndpoint;
      -- Since these are the only elements in the sum, we can simplify the expression.
      have hsum_simplified : ∀ (u : Fin n → ZMod 2), (∑ t ∈ {t | q < t}, u t) = u r + ∑ t ∈ {t | q < t ∧ t ≠ r}, u t := by
        intro u; rw [ ← Finset.sum_erase_add _ _ ( show r ∈ Finset.filter ( fun t => q < t ) Finset.univ from Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hqr ⟩ ) ] ; simp +decide [ add_comm ] ;
        rcongr x ; aesop;
      have hsum_zero : ∑ t ∈ {t | q < t ∧ t ≠ r}, (if x₁ q = 0 then x₁ else y₁) t = ∑ t ∈ {t | q < t ∧ t ≠ r}, u t ∧ ∑ t ∈ {t | q < t ∧ t ≠ r}, (if x₂ q = 0 then x₂ else y₂) t = ∑ t ∈ {t | q < t ∧ t ≠ r}, u t := by
        constructor <;> refine' Finset.sum_congr rfl fun i hi => _ <;> simp_all +decide [ Finset.mem_filter ];
        · cases eq_or_ne i p <;> cases eq_or_ne i q <;> cases eq_or_ne i r <;> simp_all +decide
          · exact False.elim <| hi.1.not_gt hpq;
          · cases eq_or_ne ( x₁ q ) 0 <;> simp_all +decide
            have h_eq : x₁ i = y₁ i := by
              have h_diff : hammingDist x₁ y₁ = 1 := h₁
              have h_diff_i : x₁ i = y₁ i := by
                have h_diff_i : Finset.card (Finset.filter (fun t => x₁ t ≠ y₁ t) Finset.univ) = 1 := by
                  convert h_diff using 1
                rw [ Finset.card_eq_one ] at h_diff_i;
                obtain ⟨ a, ha ⟩ := h_diff_i; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
                have := ha.2 q; have := ha.2 i; simp_all +decide [ edgeDirection ] ;
                have := Finset.min'_mem ( Finset.filter ( fun t => ¬x₁ t = y₁ t ) Finset.univ ) ⟨ a, by aesop ⟩ ; simp_all +decide [ Finset.mem_filter ] ;
                grind +ring
              exact h_diff_i;
            rw [ ← h_eq, hsupp₁ i ‹_› ‹_› ‹_› ];
        · split_ifs <;> simp_all +decide [ edgeDirection ];
          · exact hsupp₂ i ( ne_of_gt ( lt_trans hpq hi.1 ) ) ( ne_of_gt hi.1 ) hi.2;
          · have h_eq : ∀ j, j ≠ q → x₂ j = y₂ j := by
              intro j hj; contrapose! hj; simp_all +decide [ Finset.min' ] ;
              have := Finset.card_eq_one.mp h₂; obtain ⟨ k, hk ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
            rw [ ← h_eq i ( ne_of_gt hi.1 ), hsupp₂ i ( ne_of_gt ( lt_trans hpq hi.1 ) ) ( ne_of_gt hi.1 ) hi.2 ];
      simp_all +decide [ add_assoc ];
      grind
    exact ⟨hsum_L, hsum_R⟩

/-
Lemma: In a Q3 determined by p < q < r, edges in direction q with the same (L, R) labels are identical.
-/
theorem distinct_labels_in_Q3_slice {n : ℕ} {p q r : Fin n} (hpq : p < q) (hqr : q < r)
  (u : Fin n → ZMod 2)
  (x₁ y₁ x₂ y₂ : Fin n → ZMod 2)
  (h₁ : hammingDist x₁ y₁ = 1) (h₂ : hammingDist x₂ y₂ = 1)
  (hdir₁ : edgeDirection x₁ y₁ h₁ = q) (hdir₂ : edgeDirection x₂ y₂ h₂ = q)
  (hsupp₁ : ∀ i, i ≠ p → i ≠ q → i ≠ r → x₁ i = u i)
  (hsupp₂ : ∀ i, i ≠ p → i ≠ q → i ≠ r → x₂ i = u i)
  (hL : L x₁ y₁ h₁ = L x₂ y₂ h₂)
  (hR : R x₁ y₁ h₁ = R x₂ y₂ h₂) :
  lowerEndpoint x₁ y₁ h₁ = lowerEndpoint x₂ y₂ h₂ := by
    -- Since the edges are in direction q, the lower endpoints must be 0 at coordinate q.
    have h_lower_q : (lowerEndpoint x₁ y₁ h₁) q = 0 ∧ (lowerEndpoint x₂ y₂ h₂) q = 0 := by
      have h_lower_q₁ : (lowerEndpoint x₁ y₁ h₁) q = 0 := by
        unfold lowerEndpoint;
        have h_lower_q₁ : x₁ q ≠ y₁ q := by
          have h_lower_q₁ : q ∈ Finset.univ.filter (fun i => x₁ i ≠ y₁ i) := by
            exact hdir₁ ▸ Finset.min'_mem _ _;
          aesop;
        have := Fin.exists_fin_two.mp ⟨ x₁ q, rfl ⟩ ; ( have := Fin.exists_fin_two.mp ⟨ y₁ q, rfl ⟩ ; aesop; )
      have h_lower_q₂ : (lowerEndpoint x₂ y₂ h₂) q = 0 := by
        unfold lowerEndpoint;
        unfold edgeDirection at *; simp_all +decide [ Finset.min' ] ;
        have := Finset.min'_mem ( Finset.filter ( fun i => ¬x₂ i = y₂ i ) Finset.univ ) ; simp_all +decide
        cases Fin.exists_fin_two.mp ⟨ x₂ q, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ y₂ q, rfl ⟩ <;> simp_all +decide [ Finset.min' ];
        grind
      exact ⟨h_lower_q₁, h_lower_q₂⟩;
    -- Since the edges are in direction q, the lower endpoints must be 0 at coordinate q. For all other coordinates, the vertices agree with u, so the lower endpoints agree with u.
    have h_lower_other : ∀ i, i ≠ p → i ≠ q → i ≠ r → (lowerEndpoint x₁ y₁ h₁) i = (lowerEndpoint x₂ y₂ h₂) i := by
      intros i hi₁ hi₂ hi₃
      have h_lower_eq : (lowerEndpoint x₁ y₁ h₁) i = (lowerEndpoint x₂ y₂ h₂) i := by
        have h_lower_eq_x : (lowerEndpoint x₁ y₁ h₁) i = x₁ i ∨ (lowerEndpoint x₁ y₁ h₁) i = y₁ i := by
          unfold lowerEndpoint; aesop;
        have h_lower_eq_x' : (lowerEndpoint x₂ y₂ h₂) i = x₂ i ∨ (lowerEndpoint x₂ y₂ h₂) i = y₂ i := by
          unfold lowerEndpoint; aesop;
        have h_lower_eq_y : (lowerEndpoint x₁ y₁ h₁) i = (lowerEndpoint x₂ y₂ h₂) i := by
          have h_lower_eq_y₁ : y₁ i = x₁ i := by
            have h_lower_eq_y₁ : hammingDist x₁ y₁ = 1 → ∀ i, i ≠ edgeDirection x₁ y₁ h₁ → x₁ i = y₁ i := by
              intros h_dist i hi_ne_edge
              have h_eq : x₁ i = y₁ i := by
                have h_card : Finset.card (Finset.filter (fun i => x₁ i ≠ y₁ i) Finset.univ) = 1 := by
                  exact h₁
                contrapose! hi_ne_edge; simp_all +decide [ Finset.card_eq_one ] ;
                obtain ⟨ a, ha ⟩ := h_card; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
                exact hdir₁.symm.trans ( by rw [ show edgeDirection x₁ y₁ h₁ = a from by exact le_antisymm ( Finset.min'_le _ _ <| by aesop ) ( Finset.le_min' _ _ _ <| by aesop ) ] ) ▸ rfl;
              generalize_proofs at *; exact h_eq
            generalize_proofs at *; (
            rw [ h_lower_eq_y₁ h₁ i ( by aesop ) ])
          have h_lower_eq_y₂ : y₂ i = x₂ i := by
            have h_lower_eq_y₂ : Finset.card (Finset.filter (fun i => x₂ i ≠ y₂ i) Finset.univ) = 1 := by
              exact h₂;
            contrapose! h_lower_eq_y₂;
            refine' ne_of_gt ( Finset.one_lt_card.mpr ⟨ i, _, q, _, _ ⟩ ) <;> simp_all +decide [ Finset.mem_filter, eq_comm ];
            have h_lower_eq_y₂ : x₂ (edgeDirection x₂ y₂ h₂) ≠ y₂ (edgeDirection x₂ y₂ h₂) := by
              have h_diff : ∃ i, x₂ i ≠ y₂ i := by
                exact not_forall.mp fun h => by simp_all +decide
              exact Finset.min'_mem ( Finset.filter ( fun i => x₂ i ≠ y₂ i ) Finset.univ ) ⟨ h_diff.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_diff.choose_spec ⟩ ⟩ |> fun h => by simpa using Finset.mem_filter.mp h |>.2;
            exact h_lower_eq_y₂
          grind +ring;
        exact h_lower_eq_y;
      exact h_lower_eq;
    -- By L_R_differences_in_Q3, the lower endpoints agree on coordinates p and r.
    have h_lower_pr : (lowerEndpoint x₁ y₁ h₁) p = (lowerEndpoint x₂ y₂ h₂) p ∧ (lowerEndpoint x₁ y₁ h₁) r = (lowerEndpoint x₂ y₂ h₂) r := by
      have := L_R_differences_in_Q3 hpq hqr u x₁ y₁ x₂ y₂ h₁ h₂ hdir₁ hdir₂ hsupp₁ hsupp₂; simp_all +decide ;
      grind;
    ext i; by_cases hi : i = p <;> by_cases hi' : i = q <;> by_cases hi'' : i = r <;> aesop;

/-
Lemma: A 6-cycle in a hypercube uses each of its directions exactly twice.
-/
theorem cycle_uses_each_direction_twice {n : ℕ} {u : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u u) (hp : p.IsCycle) (hlen : p.length = 6) :
  ∀ i ∈ directionsUsed p, (walkIndices p).count i = 2 := by
    have h_sum_edges : (directionsUsed p).sum (fun i => (walkIndices p).count i) = 6 := by
      convert hlen using 1;
      have h_sum_edges : ∀ {l : List (Fin n)}, (∑ i ∈ l.toFinset, List.count i l) = l.length := by
        exact fun {l} => List.sum_toFinset_count_eq_length l;
      convert h_sum_edges using 1;
      -- The length of the walk is equal to the length of the list of edge directions by definition.
      have h_walk_length : ∀ {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v), p.length = (walkIndices p).length := by
        intros u v p; induction p <;> aesop;
      apply h_walk_length;
    have h_card_edges : directionsUsed p ⊆ Finset.univ ∧ Finset.card (directionsUsed p) = 3 := by
      exact ⟨ Finset.subset_univ _, cycle_directions_card_eq_three p hp hlen ⟩;
    have h_each_edge_twice : ∀ i ∈ directionsUsed p, (walkIndices p).count i ≥ 2 := by
      exact fun i a => cycle_directions_count_ge_two p i a;
    exact fun i hi => le_antisymm ( by exact le_of_not_gt fun hi' => by have := Finset.sum_lt_sum ( fun x hx => h_each_edge_twice x hx ) ( show ∃ x, x ∈ directionsUsed p ∧ List.count x ( walkIndices p ) > 2 from ⟨ i, hi, hi' ⟩ ) ; norm_num [ h_card_edges ] at this ; linarith ) ( h_each_edge_twice i hi )

/-
The partition graph G_ab is a subgraph of the hypercube graph Q_n.
-/
theorem partitionGraph_le_hypercube (n : ℕ) (ab : Fin 2 × Fin 2) :
  partitionGraph n ab ≤ hypercubeGraph n := by
    -- By definition of partitionGraph, if x and y are adjacent in partitionGraph n ab, then there exists an edgeDirection h such that L x y h = ab.1 and R x y h = ab.2, and hammingDist x y = 1.
    intro x y h_adj
    obtain ⟨h, hL, hR⟩ := h_adj;
    exact h

/-
A set has cardinality 3 iff it can be written as {x, y, z} with x < y < z.
-/
theorem card_eq_three_iff_exists_sorted {α : Type*} [LinearOrder α] [DecidableEq α] {S : Finset α} :
  S.card = 3 ↔ ∃ x y z, x < y ∧ y < z ∧ S = {x, y, z} := by
    constructor <;> intro h;
    · rcases Finset.card_eq_three.mp h with ⟨ x, y, z, hx, hy, hz, h ⟩ ; cases lt_trichotomy x y <;> cases lt_trichotomy y z <;> cases lt_trichotomy x z <;> aesop;
    · rcases h with ⟨ x, y, z, hxy, hyz, rfl ⟩ ; rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> simp +decide [ *, ne_of_lt ] ;
      exact ne_of_lt ( lt_trans hxy hyz )

/-
If two edges in the partition graph lie in the same Q3 slice (direction q), they must have the same lower endpoint.
-/
lemma partition_q_edges_eq_lowerEndpoint {n : ℕ} {ab : Fin 2 × Fin 2}
  {p q r : Fin n} (hpq : p < q) (hqr : q < r)
  (u : Fin n → ZMod 2)
  (v1 w1 v2 w2 : Fin n → ZMod 2)
  (h1 : (partitionGraph n ab).Adj v1 w1)
  (h2 : (partitionGraph n ab).Adj v2 w2)
  (hq1 : edgeDirection v1 w1 (partitionGraph_le_hypercube n ab h1) = q)
  (hq2 : edgeDirection v2 w2 (partitionGraph_le_hypercube n ab h2) = q)
  (hsupp1 : ∀ i, i ≠ p → i ≠ q → i ≠ r → v1 i = u i)
  (hsupp2 : ∀ i, i ≠ p → i ≠ q → i ≠ r → v2 i = u i) :
  lowerEndpoint v1 w1 (partitionGraph_le_hypercube n ab h1) = lowerEndpoint v2 w2 (partitionGraph_le_hypercube n ab h2) := by
    apply distinct_labels_in_Q3_slice hpq hqr u v1 w1 v2 w2 h1.1 h2.1 hq1 hq2 hsupp1 hsupp2
    generalize_proofs at *;
    · cases h1 ; cases h2 ; aesop;
    · unfold partitionGraph at h1 h2; aesop;

/-
If a list has exactly two occurrences of x, there are two distinct indices pointing to x.
-/
theorem list_count_two_implies_exists_indices {α : Type*} [DecidableEq α] (l : List α) (x : α) (h : l.count x = 2) :
  ∃ i j : Fin l.length, i < j ∧ l.get i = x ∧ l.get j = x := by
    induction' l with hd tl hl generalizing x;
    · cases h;
    · by_cases h' : x = hd <;> simp_all +decide [ List.count_cons ];
      · obtain ⟨ i, hi ⟩ := List.get_of_mem ( List.count_pos_iff.mp ( by linarith ) );
        refine' ⟨ ⟨ 0, _ ⟩, ⟨ i + 1, _ ⟩, _, _, _ ⟩ <;> simp_all +decide
        exact Nat.succ_pos _;
      · obtain ⟨ i, j, hij, hi, hj ⟩ := hl x ( by aesop );
        exact ⟨ ⟨ i + 1, by simp ⟩, ⟨ j + 1, by simp ⟩, Nat.succ_lt_succ hij, by simpa using hi, by simpa using hj ⟩

/-
The length of the list of walk indices is equal to the length of the walk.
-/
theorem walkIndices_length {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) :
  (walkIndices p).length = p.length := by
    -- We can prove this by induction on the walk.
    induction' p with p' hp' ih;
    · rfl;
    · (expose_names; exact Nat.succ_inj.mpr p_ih)

/-
The i-th element of walkIndices is the direction of the i-th edge in the walk.
-/
theorem walkIndices_get {n : ℕ} {u v : Fin n → ZMod 2} (p : (hypercubeGraph n).Walk u v) (i : ℕ) (hi : i < p.length) :
  (walkIndices p).get ⟨i, by rw [walkIndices_length]; exact hi⟩ =
  edgeDirection (p.getVert i) (p.getVert (i + 1)) (p.adj_getVert_succ hi) := by
    generalize_proofs at *
    generalize_proofs at *;
    induction' p with u v p ih generalizing i;
    · contradiction;
    · rcases i with ( _ | i ) <;> simp_all +decide [ walkIndices ]
      rename_i h₁ h₂ h₃ h₄ h₅
      generalize_proofs at *
      exact h₅ _ hi (by assumption) (by assumption)

/-
If two edges have the same direction and lower endpoint, they are the same edge (as a set of vertices).
-/
lemma same_edge_of_lowerEndpoint_eq {n : ℕ} {u v x y : Fin n → ZMod 2}
  (huv : hammingDist u v = 1) (hxy : hammingDist x y = 1) :
  edgeDirection u v huv = edgeDirection x y hxy →
  lowerEndpoint u v huv = lowerEndpoint x y hxy →
  ({u, v} : Set (Fin n → ZMod 2)) = {x, y} := by
    -- Since the sets where u and v differ and where x and y differ each have cardinality 1, they must be singletons.
    obtain ⟨i, hi⟩ : ∃ i, {j | u j ≠ v j} = {i} := by
      exact Finset.card_eq_one.mp huv |> Exists.imp fun i hi => by simpa [ Finset.ext_iff, Set.ext_iff ] using hi;
    obtain ⟨j, hj⟩ : ∃ j, {k | x k ≠ y k} = {j} := by
      exact ( Finset.card_eq_one.mp hxy ) |> fun ⟨ j, hj ⟩ => ⟨ j, by simpa [ Finset.ext_iff, Set.ext_iff ] using hj ⟩;
    unfold lowerEndpoint; simp_all +decide [ Set.ext_iff ] ;
    -- Since edgeDirection u v huv = edgeDirection x y hxy, we have i = j.
    intro h_eq h_lower x_1
    have h_eq_ij : i = j := by
      unfold edgeDirection at h_eq;
      simp_all +decide [ Finset.min', Finset.filter_eq' ];
    have h_eq_or_swap : ∀ k, k ≠ i → u k = x k ∧ v k = y k ∨ u k = y k ∧ v k = x k := by
      grind;
    cases Fin.exists_fin_two.mp ⟨ u i, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ v i, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ x i, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ y i, rfl ⟩ <;> simp_all +decide only [funext_iff];
    all_goals have := hi j; have := hj j; simp_all +decide ;
    · grind +ring;
    · grind;
    · grind +ring;
    · grind +ring

/-
A 6-cycle contained in a Q3 cannot have all its edges in the same partition class G_ab.
-/
lemma C6_in_Q3_impossible {n : ℕ} {ab : Fin 2 × Fin 2} {u : Fin n → ZMod 2}
  (C : (hypercubeGraph n).Walk u u) (hC : C.IsCycle) (hlen : C.length = 6)
  (S : Finset (Fin n)) (hS : S.card = 3)
  (h_supp : ∀ v ∈ C.support, ∀ i ∉ S, v i = u i)
  (h_partition : ∀ i : Fin 6, (partitionGraph n ab).Adj (C.getVert i) (C.getVert (i + 1))) :
  False := by
    -- Since $|S|=3$, let $S = \{p, q, r\}$ with $p < q < r$.
    obtain ⟨p, q, r, hpq, hqr, hS_eq⟩ : ∃ p q r : Fin n, p < q ∧ q < r ∧ S = {p, q, r} := by
      have := card_eq_three_iff_exists_sorted.mp hS;
      tauto;
    -- By `cycle_uses_each_direction_twice`, the cycle $C$ uses direction $q$ exactly twice. Let the two edges in direction $q$ be $e_1 = (x_1, y_1)$ and $e_2 = (x_2, y_2)$.
    obtain ⟨i1, i2, hi1, hi2, h_eq⟩ : ∃ i1 i2 : Fin 6, i1 < i2 ∧ edgeDirection (C.getVert i1) (C.getVert (i1 + 1)) (partitionGraph_le_hypercube n ab (h_partition i1)) = q ∧ edgeDirection (C.getVert i2) (C.getVert (i2 + 1)) (partitionGraph_le_hypercube n ab (h_partition i2)) = q := by
      -- Since the cycle uses each direction exactly twice, and q is one of the directions in S, there must be exactly two edges in direction q.
      have h_count_q : (List.count q (List.map (fun i : Fin 6 => edgeDirection (C.getVert i) (C.getVert (i + 1)) (partitionGraph_le_hypercube n ab (h_partition i))) (List.finRange 6))) = 2 := by
        have h_count_q : (List.count q (List.map (fun i : Fin 6 => edgeDirection (C.getVert i) (C.getVert (i + 1)) (partitionGraph_le_hypercube n ab (h_partition i))) (List.finRange 6))) = (List.count q (walkIndices C)) := by
          have h_count_q : List.map (fun i : Fin 6 => edgeDirection (C.getVert i) (C.getVert (i + 1)) (partitionGraph_le_hypercube n ab (h_partition i))) (List.finRange 6) = walkIndices C := by
            have h_count_q : ∀ i : Fin 6, edgeDirection (C.getVert i) (C.getVert (i + 1)) (partitionGraph_le_hypercube n ab (h_partition i)) = (walkIndices C).get ⟨i, by
              simp +decide [ walkIndices_length, hlen ]⟩ := by
              intro i; exact (by
              convert walkIndices_get C i ( by fin_cases i <;> simp +decide [ hlen ] ) |> Eq.symm using 1)
            generalize_proofs at *;
            refine' List.ext_get _ _ <;> simp +decide [ h_count_q ];
            rw [ walkIndices_length, hlen ];
          rw [h_count_q];
        convert cycle_uses_each_direction_twice C hC hlen q _;
        have h_count_q : (directionsUsed C).card = 3 := by
          exact cycle_directions_card_eq_three C hC hlen;
        have h_count_q : directionsUsed C = S := by
          have h_count_q : directionsUsed C ⊆ S := by
            intro i hi;
            contrapose! hi;
            simp_all +decide [ directionsUsed ];
            have h_count_q : ∀ v ∈ C.support, v i = u i := by
              exact fun v hv => h_supp v hv i hi.1 hi.2.1 hi.2.2;
            have h_count_q : ∀ j : Fin 6, edgeDirection (C.getVert j) (C.getVert (j + 1)) (partitionGraph_le_hypercube n ab (h_partition j)) ≠ i := by
              intro j hj; have := h_count_q ( C.getVert j ) ( by
                exact Walk.getVert_mem_support C ↑j ) ; have := h_count_q ( C.getVert ( j + 1 ) ) ( by
                simp +decide ) ; simp_all +decide [ edgeDirection ] ;
              have := Finset.min'_mem ( Finset.filter ( fun i => ¬C.getVert ( j : ℕ ) i = C.getVert ( j + 1 : ℕ ) i ) Finset.univ ) ; simp_all +decide [ Finset.min' ] ;
              grind;
            have h_count_q : walkIndices C = List.map (fun j : Fin 6 => edgeDirection (C.getVert j) (C.getVert (j + 1)) (partitionGraph_le_hypercube n ab (h_partition j))) (List.finRange 6) := by
              refine' List.ext_get _ _ <;> simp +decide
              · rw [ walkIndices_length, hlen ];
              · intro j hj₁ hj₂; exact (by
                convert walkIndices_get C j ( by linarith ) using 1);
            simp_all +decide [ List.mem_map ];
          exact Finset.eq_of_subset_of_card_le h_count_q ( by linarith );
        aesop;
      obtain ⟨ i1, hi1, i2, hi2, h ⟩ := list_count_two_implies_exists_indices ( List.map ( fun i : Fin 6 => edgeDirection ( C.getVert i ) ( C.getVert ( i + 1 ) ) ( partitionGraph_le_hypercube n ab ( h_partition i ) ) ) ( List.finRange 6 ) ) q h_count_q;
      exact ⟨ ⟨ i1, by simpa using i1.2 ⟩, ⟨ hi1, by simpa using hi1.2 ⟩, i2, by simpa using hi2, by simpa using h ⟩;
    -- By `distinct_labels_in_Q3_slice`, since $e_1$ and $e_2$ are in the same $Q_3$ slice and have the same labels, their lower endpoints must be equal.
    have h_lower_eq : lowerEndpoint (C.getVert i1) (C.getVert (i1 + 1)) (partitionGraph_le_hypercube n ab (h_partition i1)) = lowerEndpoint (C.getVert i2) (C.getVert (i2 + 1)) (partitionGraph_le_hypercube n ab (h_partition i2)) := by
      apply partition_q_edges_eq_lowerEndpoint hpq hqr u (C.getVert i1) (C.getVert (i1 + 1)) (C.getVert i2) (C.getVert (i2 + 1)) (h_partition i1) (h_partition i2) hi2 h_eq;
      · intro i hi1 hi2 hi3; specialize h_supp ( C.getVert i1 ) ( by
          exact Walk.getVert_mem_support C ↑i1 ) i; aesop;
      · intro i hi1 hi2 hi3; specialize h_supp ( C.getVert i2 ) ( by
          simp +decide ) i; aesop;
    -- Since $e_1$ and $e_2$ have the same direction and lower endpoint, they are the same edge (as sets of vertices).
    have h_edge_eq : ({C.getVert i1, C.getVert (i1 + 1)} : Set (Fin n → ZMod 2)) = {C.getVert i2, C.getVert (i2 + 1)} := by
      apply same_edge_of_lowerEndpoint_eq;
      grind;
      exact h_lower_eq;
    -- Since $C$ is a simple cycle, it cannot contain the same edge twice.
    have h_simple_cycle : ∀ i j : Fin 6, i ≠ j → ({C.getVert i, C.getVert (i + 1)} : Set (Fin n → ZMod 2)) ≠ {C.getVert j, C.getVert (j + 1)} := by
      intro i j hij h_eq
      have h_edge_eq : C.edges.Nodup := by
        exact hC.edges_nodup;
      have h_edge_eq : ∀ i : Fin 6, C.edges[i]! = Sym2.mk (C.getVert i, C.getVert (i + 1)) := by
        intro i
        have h_edge_eq : C.edges[i]! = Sym2.mk (C.getVert i, C.getVert (i + 1)) := by
          have h_edge_eq : C.edges = List.map (fun i : Fin 6 => Sym2.mk (C.getVert i, C.getVert (i + 1))) (List.finRange 6) := by
            refine' List.ext_get _ _ <;> simp +decide [ hlen ];
            intro n hn; fin_cases i <;> simp +decide [ *, SimpleGraph.Walk.edges ] ;
            all_goals interval_cases n <;> simp +decide
            all_goals rcases C with ( _ | ⟨ _, _, _, _, _, _, _ ⟩ ) <;> simp +decide [ SimpleGraph.Walk.getVert ] at hlen ⊢;
            all_goals rcases p : ‹SimpleGraph.Walk _ _ _› with ( _ | ⟨ _, _, _, _, _, _, _ ⟩ ) <;> simp +decide [ p ] at hlen ⊢;
            all_goals rcases p : ‹SimpleGraph.Walk _ _ _› with ( _ | ⟨ _, _, _, _, _, _, _ ⟩ ) <;> simp +decide [ p ] at hlen ⊢;
          fin_cases i <;> simp +decide [ h_edge_eq ];
        exact h_edge_eq;
      have h_edge_eq : ∀ i j : Fin 6, i ≠ j → C.edges[i]! ≠ C.edges[j]! := by
        intros i j hij h_eq;
        have := List.nodup_iff_injective_get.mp ‹_›; simp_all +decide [ Fin.ext_iff ] ;
        have := @this ⟨ i, by simp +decide [ hlen ] ⟩ ⟨ j, by simp +decide [ hlen ] ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      cases h_eq.1.1 <;> cases h_eq.1.2 <;> specialize h_edge_eq i j hij <;> aesop;
    exact h_simple_cycle i1 i2 hi1.ne h_edge_eq

/-
The partition graph G_ab contains no cycle of length 6.
-/
theorem partitionGraph_C6_free (n : ℕ) (ab : Fin 2 × Fin 2) :
  ¬ HasCycleOfLength (partitionGraph n ab) 6 := by
    -- By contradiction, assume there exists a cycle of length 6 in `partitionGraph n ab` with vertices in a 3-dimensional subcube.
    by_contra h
    obtain ⟨u, C_part, hC_part, hlen⟩ := h;
    -- Lift `C_part` to a cycle `C` in `hypercubeGraph n` using the inclusion `partitionGraph_le_hypercube`.
    obtain ⟨C, hC_cycle, hC_length⟩ : ∃ C : (hypercubeGraph n).Walk u u, C.length = 6 ∧ C.IsCycle ∧ ∀ i : Fin 6, (partitionGraph n ab).Adj (C.getVert i) (C.getVert (i + 1)) := by
      use C_part.map (SimpleGraph.Hom.ofLE (partitionGraph_le_hypercube n ab));
      cases C_part <;> simp_all +decide [ SimpleGraph.Walk.isCycle_def ];
      intro i; fin_cases i <;> simp_all +decide [ SimpleGraph.Walk.getVert ] ;
      · cases ‹ ( partitionGraph n ab ).Walk _ _ › <;> aesop;
      · rcases p : ‹SimpleGraph.Walk ( partitionGraph n ab ) _ _› with ( _ | ⟨ _, _, p ⟩ ) <;> aesop;
      · rename_i p hp;
        rcases hp with ( _ | ⟨ _, _, hp ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        rename_i k hk hk₂ hk₃ hk₄;
        rcases hk₄ with ( _ | ⟨ _, _, hk₄ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
      · rename_i p hp;
        rcases hp with ( _ | ⟨ _, _, hp ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        rename_i k hk hk₂ hk₃ hk₄;
        rcases hk₄ with ( _ | ⟨ _, _, hk₄ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
      · rename_i p hp;
        rcases hp with ( _ | ⟨ _, _, hp ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        rename_i k hk hk₂ hk₃ hk₄;
        rcases hk₄ with ( _ | ⟨ _, _, hk₄ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        rename_i h₁ h₂ h₃ h₄ h₅ h₆;
        rcases h₆ with ( _ | ⟨ _, _, h₆ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
    -- By `C6_in_Q3`, `C` is contained in a 3-dimensional subcube determined by a set `S` of size 3.
    obtain ⟨S, hS_card, hS_supp⟩ : ∃ S : Finset (Fin n), S.card = 3 ∧ ∀ v ∈ C.support, ∀ i ∉ S, v i = u i := by
      exact C6_in_Q3 C hC_length.1 hC_cycle |> fun ⟨ S, hS_card, hS_supp ⟩ => ⟨ S, hS_card, fun v hv i hi => hS_supp v hv i hi ⟩;
    exact C6_in_Q3_impossible C hC_length.1 hC_cycle S hS_card hS_supp hC_length.2

/-
The number of edges in the hypercube graph Q_n is n * 2^(n-1).
-/
theorem hypercube_card_edges (n : ℕ) :
  (hypercubeGraph n).edgeFinset.card = n * 2 ^ (n - 1) := by
    have h_degrees : ∀ v : Fin n → ZMod 2, (hypercubeGraph n).degree v = n := by
      intro v
      have h_neighbors : (hypercubeGraph n).neighborFinset v = Finset.image (fun i => Function.update v i (v i + 1)) Finset.univ := by
        ext w; simp [hypercubeGraph];
        constructor <;> intro h <;> simp_all +decide [ hammingDist ];
        · obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp h;
          use i; ext j; by_cases hj : j = i <;> simp_all +decide [ Finset.ext_iff, Function.update_apply ] ;
          · cases Fin.exists_fin_two.mp ⟨ v i, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ w i, rfl ⟩ <;> specialize hi i <;> aesop;
          · specialize hi j; aesop;
        · obtain ⟨ a, rfl ⟩ := h; rw [ Finset.card_eq_one ] ; use a; ext i; by_cases hi : i = a <;> simp +decide [ hi ] ;
      rw [ SimpleGraph.degree, h_neighbors, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      intro i j h; replace h := congr_fun h i; by_cases hi : i = j <;> simp_all +decide [ Function.update_apply ] ;
    have := SimpleGraph.sum_degrees_eq_twice_card_edges ( hypercubeGraph n ) ; simp_all +decide [ mul_comm ] ;
    cases n <;> simp_all +decide [ pow_succ' ] ; linarith

/-
It is not true that for every epsilon > 0, sufficiently large subgraphs of Q_n contain a C6.
-/
theorem not_erdos_666 :
  ¬ (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ G ≤ hypercubeGraph n, (G.edgeFinset.card : ℝ) ≥ ε * n * 2^(n-1) → HasCycleOfLength G 6) := by
    by_contra h_contra;
    obtain ⟨ N, hN ⟩ := h_contra ( 1 / 4 ) ( by norm_num );
    -- By the theorem, $E(Q_n)$ is partitioned into four sets $E_{00},E_{01},E_{10},E_{11}$, so by the pigeonhole principle at least one class, say $E_{ab}$, satisfies
    obtain ⟨ab, hab⟩ : ∃ ab : Fin 2 × Fin 2, (partitionGraph N ab).edgeFinset.card ≥ (1 / 4 : ℝ) * N * 2 ^ (N - 1) := by
      have h_partition : (hypercubeGraph N).edgeFinset.card = ∑ ab : Fin 2 × Fin 2, (partitionGraph N ab).edgeFinset.card := by
        have h_partition : (hypercubeGraph N).edgeFinset = Finset.biUnion (Finset.univ : Finset (Fin 2 × Fin 2)) (fun ab => (partitionGraph N ab).edgeFinset) := by
          ext ⟨ u, v ⟩ ; simp +decide [ partitionGraph_is_partition ] ;
          constructor;
          · rintro ⟨ ab, hab, hab' ⟩ ; fin_cases ab <;> tauto;
          · intro h;
            have := partitionGraph_is_partition N u v;
            exact this.mp ( by rcases h with ( ( h | h ) | h | h ) <;> [ exact h.1; exact h.1; exact h.1; exact h.1 ] );
        rw [ h_partition, Finset.card_biUnion ];
        intros ab hab;
        intros cd hcd hne; simp_all +decide [ Finset.disjoint_left, SimpleGraph.edgeSet ] ;
        intro e he₁ he₂; simp_all +decide [ edgeSetEmbedding ] ;
        rcases e with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.fromRel ];
        cases he₁ ; cases he₂ ; aesop;
      have h_pigeonhole : ∑ ab : Fin 2 × Fin 2, (partitionGraph N ab).edgeFinset.card ≥ (1 / 4 : ℝ) * N * 2 ^ (N - 1) * 4 := by
        rw [ ← h_partition, hypercube_card_edges ] ; norm_num ; ring_nf ; norm_num;
      contrapose! h_pigeonhole;
      simpa [ mul_comm ] using Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun x _ => h_pigeonhole x;
    exact absurd ( hN N le_rfl _ ( partitionGraph_le_hypercube N ab ) hab ) ( by simpa using partitionGraph_C6_free N ab )

#print axioms not_erdos_666
-- 'not_erdos_666' depends on axioms: [propext, Classical.choice, Quot.sound]
