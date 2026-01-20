/-
We proved that every graph with $m$ edges contains a $C_4$-free subgraph with at least $(3/8) m^{2/3}$ edges. This was done by first bounding the number of $C_4$s by $m^2$ (specifically, by counting disjoint edge pairs), and then applying a probabilistic/combinatorial argument to find a large $C_4$-free subgraph.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Check if SimpleGraph.cycleGraph and SimpleGraph.Free are available.
-/
#check SimpleGraph.cycleGraph
#check SimpleGraph.Free

/-
Print the definition of SimpleGraph.Free.
-/
#print SimpleGraph.Free

/-
Print the definition of SimpleGraph.IsContained.
-/
#print SimpleGraph.IsContained

/-
Print the definition of SimpleGraph.Copy.
-/
#print SimpleGraph.Copy

/-
Check if SimpleGraph.edgeFinset is available.
-/
variable (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
#check G.edgeFinset

/-
Check the full signature of SimpleGraph.edgeFinset.
-/
#check @SimpleGraph.edgeFinset

/-
A set of edges forms a C4 if it has size 4 and the graph formed by these edges contains a C4.
-/
def is_C4 {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) : Prop :=
  s.card = 4 ∧ ¬ (SimpleGraph.cycleGraph 4).Free (SimpleGraph.fromEdgeSet (s : Set (Sym2 V)))

/-
C4s is the set of all subsets of edges of G that form a C4.
-/
def C4s {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  (G.edgeFinset.powerset).filter is_C4

/-
The number of P3s (paths of length 2) is at most 2 times the square of the number of edges.
-/
def num_P3s {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ v, (G.degree v).choose 2

theorem num_P3s_le_sq_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  num_P3s G ≤ 2 * (G.edgeFinset.card) ^ 2 := by
    unfold num_P3s;
    have h_sum : (∑ v : V, (G.degree v) ^ 2) ≤ (∑ v : V, G.degree v) ^ 2 := by
      simpa only [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun v _ => Nat.zero_le ( G.degree v ) ) ( Finset.mem_univ v ) ) ( Nat.zero_le ( G.degree v ) );
    have h_sum : (∑ v : V, (G.degree v) ^ 2) = (∑ v : V, (G.degree v).choose 2) * 2 + (∑ v : V, G.degree v) := by
      rw [ Finset.sum_mul _ _ _ ];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun v _ => by induction' G.degree v with d hd <;> norm_num [ Nat.choose ] at * ; linarith;
    have := SimpleGraph.sum_degrees_eq_twice_card_edges G;
    nlinarith

/-
Given a collection of 4-element subsets of a set of size m, if the number of such subsets is at most m^2, then there exists a subset S such that the number of elements in S minus the number of 4-element subsets contained in S is at least 3/8 * m^(2/3).
-/
theorem combinatorial_lemma (m : ℕ) (C : Finset (Finset (Fin m)))
  (h_card : ∀ s ∈ C, s.card = 4)
  (h_count : C.card ≤ m ^ 2) :
  ∃ (S : Finset (Fin m)), (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (3/8) * (m : ℝ) ^ ((2 : ℝ) / 3) := by
    by_cases hm : m = 0;
    · aesop;
    · have h_prob : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ (m : ℝ) * p - (m ^ 2 : ℝ) * p ^ 4 ≥ (3 / 8 : ℝ) * (m : ℝ) ^ (2 / 3 : ℝ) := by
        refine' ⟨ 1 / 2 * ( m : ℝ ) ^ ( -1 / 3 : ℝ ), _, _, _ ⟩ <;> ring <;> norm_num [ hm ];
        · positivity;
        · exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr hm ) ( show ( - ( 1 / 3 ) : ℝ ) ≤ 0 by norm_num ) ) ( by norm_num ) ) ( by norm_num );
        · norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg m ), ← Real.rpow_add' ( Nat.cast_nonneg m ) ] ; ring_nf ; norm_num;
          rw [ ← Real.rpow_one_add' ] <;> norm_num ; ring_nf ; norm_num [ hm ];
          exact mul_le_mul_of_nonneg_left ( by norm_num ) ( by positivity );
      obtain ⟨ p, hp₀, hp₁, hp₂ ⟩ := h_prob;
      -- Consider a random subset $S$ where each element is included with probability $p$.
      have h_random_subset : ∃ S : Finset (Fin m), (S.card : ℝ) - (Finset.card (Finset.filter (fun s => s ⊆ S) C) : ℝ) ≥ (m : ℝ) * p - (m ^ 2 : ℝ) * p ^ 4 := by
        have h_random_subset : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) - ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (Finset.card (Finset.filter (fun s => s ⊆ S) C) : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) ≥ (m : ℝ) * p - (m ^ 2 : ℝ) * p ^ 4 := by
          have h_random_subset : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) = (m : ℝ) * p := by
            have h_exp_S : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) = ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * k * p ^ k * (1 - p) ^ (m - k) := by
              have h_exp_S : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) = ∑ k ∈ Finset.range (m + 1), ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin m)), (S.card : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) := by
                rw [ Finset.sum_powerset ];
                norm_num [ Finset.card_univ ];
              rw [ h_exp_S ];
              refine' Finset.sum_congr rfl fun k hk => _;
              rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ];
            have h_exp_S : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * k * p ^ k * (1 - p) ^ (m - k) = m * p * ∑ k ∈ Finset.range (m), (Nat.choose (m - 1) k : ℝ) * p ^ k * (1 - p) ^ (m - 1 - k) := by
              rw [ Finset.sum_range_succ' ];
              norm_num [ Finset.mul_sum _ _ _ ];
              refine Finset.sum_congr rfl fun x hx => ?_;
              rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hx ];
              · rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.factorial, Nat.succ_sub ];
                -- Combine and simplify the fractions
                field_simp
                ring;
              · exact Nat.le_pred_of_lt ( Finset.mem_range.mp hx );
            have h_exp_S : ∑ k ∈ Finset.range m, (Nat.choose (m - 1) k : ℝ) * p ^ k * (1 - p) ^ (m - 1 - k) = (p + (1 - p)) ^ (m - 1) := by
              rw [ add_pow ];
              rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hm ) ] ; ac_rfl;
            aesop;
          have h_random_subset : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (Finset.card (Finset.filter (fun s => s ⊆ S) C) : ℝ) * p ^ S.card * (1 - p) ^ (m - S.card) ≤ ∑ s ∈ C, ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0) := by
            rw [ Finset.sum_comm ];
            simp +decide [ Finset.sum_ite, mul_assoc ];
          have h_random_subset : ∀ s ∈ C, ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0) = p ^ s.card := by
            intros s hs
            have h_random_subset : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0) = ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ (s.card + T.card) * (1 - p) ^ (m - (s.card + T.card)) := by
              have h_random_subset : Finset.filter (fun S => s ⊆ S) (Finset.powerset (Finset.univ : Finset (Fin m))) = Finset.image (fun T => s ∪ T) (Finset.powerset (Finset.univ \ s)) := by
                ext; simp [Finset.mem_image];
                constructor <;> intro h;
                · exact ⟨ ‹_› \ s, fun x hx => Finset.mem_sdiff.mpr ⟨ Finset.mem_univ _, by aesop ⟩, by aesop ⟩;
                · aesop;
              rw [ ← Finset.sum_filter, h_random_subset, Finset.sum_image ];
              · refine' Finset.sum_congr rfl fun T hT => _;
                rw [ Finset.card_union_of_disjoint ];
                exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_powerset.mp hT hx₂ ) |>.2 hx₁;
              · intro T₁ hT₁ T₂ hT₂ h_eq; simp_all +decide [ Finset.ext_iff ] ;
                intro a; specialize h_eq a; by_cases ha : a ∈ s <;> simp_all +decide [ Set.subset_def ] ;
                exact ⟨ fun h => False.elim <| hT₁ a h ha, fun h => False.elim <| hT₂ a h ha ⟩;
            have h_random_subset : ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ (s.card + T.card) * (1 - p) ^ (m - (s.card + T.card)) = p ^ s.card * ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ T.card * (1 - p) ^ ((Finset.univ \ s).card - T.card) := by
              rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun T hT => _ ; rw [ show m - ( s.card + T.card ) = ( Finset.univ \ s ).card - T.card from _ ] ; ring;
              simp +decide [ Finset.card_sdiff, * ];
              rw [ Nat.sub_sub ];
            have h_random_subset : ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ T.card * (1 - p) ^ ((Finset.univ \ s).card - T.card) = (p + (1 - p)) ^ (Finset.univ \ s).card := by
              rw [ add_pow ];
              rw [ Finset.sum_powerset ];
              exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_powersetCard ] ;
            aesop;
          simp_all +decide [ Finset.sum_ite ];
          nlinarith [ show ( C.card : ℝ ) ≤ m ^ 2 by norm_cast, show ( p ^ 4 : ℝ ) ≥ 0 by positivity ];
        contrapose! h_random_subset;
        rw [ ← Finset.sum_sub_distrib ];
        field_simp;
        refine' lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun x hx => mul_lt_mul_of_pos_left ( h_random_subset x ) ( mul_pos ( pow_pos hp₀ _ ) ( pow_pos ( sub_pos.mpr hp₁ ) _ ) ) ) _;
        rw [ ← Finset.sum_mul _ _ _ ];
        have h_sum : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), p ^ S.card * (1 - p) ^ (m - S.card) = (p + (1 - p)) ^ m := by
          rw [ add_pow ];
          rw [ Finset.sum_powerset ];
          norm_num [ Finset.sum_powersetCard ];
          exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ] ;
        field_simp;
        aesop;
      exact ⟨ h_random_subset.choose, hp₂.trans h_random_subset.choose_spec ⟩

/-
Given a collection of 4-element subsets of a set of size m, if the number of such subsets is at most 2*m^2, then there exists a subset S such that the number of elements in S minus the number of 4-element subsets contained in S is at least 3/8 * m^(2/3).
-/
theorem combinatorial_lemma_2 (m : ℕ) (C : Finset (Finset (Fin m)))
  (h_card : ∀ s ∈ C, s.card = 4)
  (h_count : C.card ≤ 2 * m ^ 2) :
  ∃ (S : Finset (Fin m)), (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (3/8) * (m : ℝ) ^ ((2 : ℝ) / 3) := by
    by_cases hm : m = 0;
    · aesop;
    · have h_prob : ∃ S : Finset (Fin m), (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (m : ℝ) * (1/2 : ℝ) * (m : ℝ) ^ (-1/3 : ℝ) - 2 * m ^ 2 * (1/2 : ℝ) ^ 4 * (m : ℝ) ^ (-4/3 : ℝ) := by
        have h_prob : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ S : Finset (Fin m), (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (m : ℝ) * p - (C.card : ℝ) * p ^ 4 := by
          intro p hp_nonneg hp_le_one
          have h_prob : ∃ S : Finset (Fin m), (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (m : ℝ) * p - (C.card : ℝ) * p ^ 4 := by
            have h_exp : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), ((S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card) * (p ^ S.card * (1 - p) ^ (m - S.card)) ≥ (m : ℝ) * p - (C.card : ℝ) * p ^ 4 := by
              have h_exp : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * (p ^ S.card * (1 - p) ^ (m - S.card)) = (m : ℝ) * p := by
                have h_exp : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (S.card : ℝ) * (p ^ S.card * (1 - p) ^ (m - S.card)) = ∑ k ∈ Finset.range (m + 1), (k : ℝ) * Nat.choose m k * p ^ k * (1 - p) ^ (m - k) := by
                  rw [ Finset.sum_powerset ];
                  simp +decide [ Finset.sum_powersetCard, mul_assoc, mul_comm, mul_left_comm ];
                  exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ] ;
                have h_exp : ∑ k ∈ Finset.range (m + 1), (k : ℝ) * Nat.choose m k * p ^ k * (1 - p) ^ (m - k) = m * p * ∑ k ∈ Finset.range (m), Nat.choose (m - 1) k * p ^ k * (1 - p) ^ (m - 1 - k) := by
                  rw [ Finset.sum_range_succ' ];
                  have h_exp : ∀ k ∈ Finset.range m, (k + 1 : ℝ) * Nat.choose m (k + 1) = m * Nat.choose (m - 1) k := by
                    norm_cast;
                    cases m <;> simp_all +decide [ Nat.succ_mul_choose_eq ];
                    exact fun _ _ => mul_comm _ _;
                  simp +zetaDelta at *;
                  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ h_exp x ( Finset.mem_range.mp hx ) ] ; rw [ show m - ( x + 1 ) = m - 1 - x from by omega ] ; ring;
                have h_exp : ∑ k ∈ Finset.range m, Nat.choose (m - 1) k * p ^ k * (1 - p) ^ (m - 1 - k) = (p + (1 - p)) ^ (m - 1) := by
                  rw [ add_pow ];
                  rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hm ) ] ; ac_rfl;
                aesop;
              have h_exp : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), ((C.filter (fun s => s ⊆ S)).card : ℝ) * (p ^ S.card * (1 - p) ^ (m - S.card)) ≤ (C.card : ℝ) * p ^ 4 := by
                have h_exp : ∀ s ∈ C, ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0) = p ^ 4 := by
                  intro s hs
                  have h_exp_s : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0) = ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ (s.card + T.card) * (1 - p) ^ (m - (s.card + T.card)) := by
                    have h_exp_s : Finset.filter (fun S => s ⊆ S) (Finset.powerset (Finset.univ : Finset (Fin m))) = Finset.image (fun T => s ∪ T) (Finset.powerset (Finset.univ \ s)) := by
                      ext; simp [Finset.mem_image];
                      exact ⟨ fun h => ⟨ ‹_› \ s, by aesop_cat, by aesop_cat ⟩, by rintro ⟨ t, ht, rfl ⟩ ; exact Finset.subset_union_left ⟩;
                    rw [ ← Finset.sum_filter, h_exp_s, Finset.sum_image ];
                    · refine' Finset.sum_congr rfl fun T hT => _;
                      rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hxS hxT => by have := Finset.mem_sdiff.mp ( Finset.mem_powerset.mp hT hxT ) ; aesop ) ];
                    · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
                      intro a; specialize h_eq a; replace hT := @hT a; replace hT' := @hT' a; aesop;
                  have h_exp_s : ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ (s.card + T.card) * (1 - p) ^ (m - (s.card + T.card)) = p ^ s.card * ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ T.card * (1 - p) ^ ((Finset.univ \ s).card - T.card) := by
                    simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
                    simp +decide [ Finset.card_sdiff, * ];
                    simp +decide only [Nat.sub_sub];
                  have h_exp_s : ∑ T ∈ Finset.powerset (Finset.univ \ s), p ^ T.card * (1 - p) ^ ((Finset.univ \ s).card - T.card) = (p + (1 - p)) ^ ((Finset.univ \ s).card) := by
                    rw [ add_pow ];
                    rw [ Finset.sum_powerset ];
                    exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun t ht => by rw [ Finset.mem_powersetCard.mp ht |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_powersetCard ] ;
                  aesop;
                have h_exp : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin m)), (∑ s ∈ C, (if s ⊆ S then p ^ S.card * (1 - p) ^ (m - S.card) else 0)) = ∑ s ∈ C, p ^ 4 := by
                  rw [ ← Finset.sum_congr rfl h_exp, Finset.sum_comm ];
                simp_all +decide [ Finset.sum_ite ];
              simp_all +decide [ sub_mul ];
              linarith
            contrapose! h_exp;
            refine' lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun x hx => mul_lt_mul_of_pos_right ( h_exp x ) ( mul_pos ( pow_pos ( lt_of_le_of_ne hp_nonneg ( Ne.symm _ ) ) _ ) ( pow_pos ( sub_pos.mpr ( lt_of_le_of_ne hp_le_one ( Ne.symm _ ) ) ) _ ) ) ) _;
            · rintro rfl; specialize h_exp ∅; norm_num at h_exp;
              obtain ⟨ s, hs ⟩ := h_exp; specialize h_card s; aesop;
            · specialize h_exp Finset.univ ; aesop;
            · -- The sum of the probabilities is 1, so we can factor out $p * (m - p^3 * C.card)$.
              have h_sum : ∑ x ∈ Finset.powerset (Finset.univ : Finset (Fin m)), p ^ x.card * (1 - p) ^ (m - x.card) = (p + (1 - p)) ^ m := by
                rw [ add_pow ];
                rw [ Finset.sum_powerset ];
                simp +decide [ Finset.sum_powersetCard, mul_assoc, mul_comm, mul_left_comm ];
                exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_powersetCard.mp hy |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ] ;
              simp_all +decide [ mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
          exact h_prob;
        obtain ⟨ S, hS ⟩ := h_prob ( ( 1 / 2 : ℝ ) * ( m : ℝ ) ^ ( -1 / 3 : ℝ ) ) ( by positivity ) ( by exact mul_le_one₀ ( by norm_num ) ( by positivity ) ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr hm ) ( show ( -1 / 3 : ℝ ) ≤ 0 by norm_num ) ) ( by norm_num ) ) );
        refine' ⟨ S, le_trans _ hS ⟩ ; ring_nf ; norm_num;
        rw [ ← Real.rpow_natCast _ 4, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf ; norm_num;
        nlinarith [ show ( m : ℝ ) ^ ( - ( 4 / 3 : ℝ ) ) ≥ 0 by positivity, show ( m : ℝ ) ^ ( - ( 1 / 3 : ℝ ) ) ≥ 0 by positivity, show ( C.card : ℝ ) ≤ 2 * m ^ 2 by exact_mod_cast h_count ];
      convert h_prob using 3 ; ring;
      norm_num [ sq, mul_assoc, ← Real.rpow_one_add' ( Nat.cast_nonneg m ) ] ; ring

/-
Check if Sym2.toFinset is available.
-/
#check Sym2.toFinset

/-
disjoint_edge_pairs is the set of pairs of edges in G that are vertex-disjoint.
-/
def disjoint_edge_pairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  (G.edgeFinset.powersetCard 2).filter (fun s =>
    match s.toList with
    | [e1, e2] => Disjoint e1.toFinset e2.toFinset
    | _ => False)

/-
The number of disjoint edge pairs is at most the number of pairs of edges.
-/
theorem card_disjoint_pairs_le_choose_two {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (disjoint_edge_pairs G).card ≤ (G.edgeFinset.card).choose 2 := by
    exact Finset.card_filter_le _ _ |> le_trans <| by simp +decide [ Nat.choose_two_right ] ;

/-
The number of disjoint edge pairs in the cycle graph C4 is 2.
-/
theorem cycleGraph4_disjoint_pairs_card :
  (disjoint_edge_pairs (SimpleGraph.cycleGraph 4)).card = 2 := by
    rw [ Finset.card_eq_two ];
    -- Let's choose the two disjoint pairs: {(0,1), (2,3)} and {(1,2), (3,0)}.
    use {Sym2.mk (0, 1), Sym2.mk (2, 3)}, {Sym2.mk (1, 2), Sym2.mk (3, 0)};
    simp +decide [ Finset.ext_iff, disjoint_edge_pairs ];
    rintro a;
    rcases x : a.toList with ( _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ) <;> simp_all +decide;
    · fin_cases e1 <;> simp +decide;
    · have := congr_arg List.toFinset x; norm_num [ Finset.ext_iff ] at this;
      fin_cases e1 <;> fin_cases e2 <;> simp_all +decide only [Set.subset_def];
      all_goals simp_all +decide [ Finset.card_eq_two, Set.ext_iff ];
      · exact ⟨ s(0, 1), s(2, 3), by decide, by ext; aesop ⟩;
      · exact ⟨ s(0, 3), s(1, 2), by decide, by ext; aesop ⟩;
      · exact ⟨ s(1, 2), s(0, 3), by decide, by ext; aesop ⟩;
      · exact ⟨ s(2, 3), s(0, 1), by decide, by ext; aesop ⟩;
    · replace x := congr_arg List.length x; simp_all +decide ;
      have := Finset.card_le_univ a; simp_all +decide ;
      simp_all +arith +decide [ Sym2.card ];
      have : List.length ‹_› ≤ 7 := Nat.le_of_lt_succ ( by { norm_num [ Nat.choose ] at this; linarith } ) ; interval_cases _ : List.length ‹_› <;> simp_all +decide ;
      all_goals revert a; native_decide;

/-
A generalization of the combinatorial lemma to arbitrary types.
-/
theorem combinatorial_lemma_general {α : Type} [DecidableEq α] (U : Finset α) (C : Finset (Finset α))
  (h_card : ∀ s ∈ C, s.card = 4)
  (h_subset : ∀ s ∈ C, s ⊆ U)
  (h_count : C.card ≤ U.card ^ 2) :
  ∃ (S : Finset α), S ⊆ U ∧ (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (3/8) * (U.card : ℝ) ^ ((2 : ℝ) / 3) := by
    have h_bij : ∀ {β : Type} [Fintype β] [DecidableEq β] (C : Finset (Finset β)), (∀ s ∈ C, s.card = 4) → (C.card ≤ (Finset.card (Finset.univ : Finset β)) ^ 2) → ∃ S : Finset β, (S.card : ℝ) - (C.filter (fun s => s ⊆ S)).card ≥ (3 / 8) * (Finset.card (Finset.univ : Finset β)) ^ ((2 : ℝ) / 3) := by
      intros β _ _ C h_card h_count
      obtain ⟨e, he⟩ : ∃ e : β ≃ Fin (Finset.card (Finset.univ : Finset β)), True := by
        exact ⟨ Fintype.equivFin β, trivial ⟩;
      have h_bij : ∃ S : Finset (Fin (Finset.card (Finset.univ : Finset β))), ((S.card : ℝ) - (Finset.card (Finset.filter (fun s => s ⊆ S) (Finset.image (fun s => Finset.image e s) C)))) ≥ (3 / 8 : ℝ) * (Finset.card (Finset.univ : Finset β)) ^ ((2 : ℝ) / 3) := by
        have := combinatorial_lemma_2 ( Finset.card ( Finset.univ : Finset β ) ) ( Finset.image ( fun s => Finset.image e s ) C );
        exact this ( fun s hs => by obtain ⟨ t, ht, rfl ⟩ := Finset.mem_image.mp hs; rw [ Finset.card_image_of_injective _ e.injective ] ; exact h_card t ht ) ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Finset.image_injective e.injective hxy ] ; linarith ) |> fun ⟨ S, hS ⟩ => ⟨ S, by linarith ⟩;
      obtain ⟨ S, hS ⟩ := h_bij; use S.image e.symm; simp_all +decide [ Finset.filter_image ] ;
      convert hS using 2 <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
      rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Finset.image_injective ( e.injective ) hxy ];
      congr! 2;
      ext; simp +decide [ Finset.subset_iff ] ;
      grind;
    contrapose! h_bij;
    refine' ⟨ U, _, _, _, _, _ ⟩ <;> norm_num;
    all_goals try infer_instance;
    exact Finset.image ( fun s : Finset α => Finset.filter ( fun x : { x // x ∈ U } => x.val ∈ s ) Finset.univ ) C;
    · simp +zetaDelta at *;
      intro s hs; rw [ ← h_card s hs ] ; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr; ext; aesop;
    · refine' ⟨ _, _ ⟩;
      · exact le_trans ( Finset.card_image_le ) h_count;
      · intro x;
        convert h_bij ( Finset.image Subtype.val x ) _;
        · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ];
        · fapply Finset.card_bij;
          use fun s hs => Finset.image Subtype.val s;
          · simp +contextual [ Finset.subset_iff ];
            intro s hs hs'; convert hs using 1; ext; aesop;
          · simp +contextual [ Finset.ext_iff ];
            grind;
          · simp +zetaDelta at *;
            grind;
        · exact Finset.image_subset_iff.mpr fun y hy => y.2

/-
The set of common neighbors of two vertices.
-/
def common_neighbors {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

#check SimpleGraph.deleteEdges

#check SimpleGraph.fromEdgeSet

/-
A set of edges is a disjoint pair if and only if it consists of two distinct edges that are vertex-disjoint.
-/
def is_disjoint_pair_prop {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) : Prop :=
  match s.toList with
  | [e1, e2] => Disjoint e1.toFinset e2.toFinset
  | _ => False

lemma is_disjoint_pair_iff {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) :
  is_disjoint_pair_prop s ↔ ∃ e1 e2, s = {e1, e2} ∧ e1 ≠ e2 ∧ Disjoint e1.toFinset e2.toFinset := by
    constructor;
    · unfold is_disjoint_pair_prop;
      intro hs;
      rcases n : s.toList with ( _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ) <;> simp_all +decide;
      refine' ⟨ e1, e2, _, _, hs ⟩;
      · simpa using congr_arg ( fun x : List ( Sym2 V ) => x.toFinset ) n;
      · replace n := congr_arg List.Nodup n; simp_all +decide [ List.nodup_cons ] ;
        exact n.mp ( Finset.nodup_toList _ );
    · unfold is_disjoint_pair_prop;
      norm_num +zetaDelta at *;
      intro x y hxy hne hdisj
      have h_toList : s.toList = [x, y] ∨ s.toList = [y, x] := by
        rcases n : Finset.toList { x, y } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
        · replace n := congr_arg List.length n; aesop;
        · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
          cases this x ; cases this y ; aesop;
        · replace n := congr_arg List.length n ; simp_all +decide;
      cases h_toList <;> simp_all +decide [ Finset.disjoint_left ];
      tauto

#print SimpleGraph.Free

/-
The vertices of a $C_4$ containing two disjoint edges are exactly the endpoints of those edges.
-/
lemma vertices_of_C4_with_disjoint_edges {V : Type} [DecidableEq V] (S : Finset (Sym2 V)) (e1 e2 : Sym2 V)
  (h_C4 : is_C4 S) (h_subset : {e1, e2} ⊆ S) (h_disjoint : Disjoint e1.toFinset e2.toFinset) :
  S.sup Sym2.toFinset = e1.toFinset ∪ e2.toFinset := by
    rcases h_C4 with ⟨ h_card, h_cycle ⟩;
    contrapose! h_cycle;
    refine' ⟨ fun x => _ ⟩;
    simp_all +decide [ Finset.subset_iff, SimpleGraph.fromEdgeSet_adj ];
    rcases x with ⟨ f, hf ⟩;
    have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 0 1 from by decide ) ; have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 1 2 from by decide ) ; have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 2 3 from by decide ) ; have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 3 0 from by decide ) ; simp_all +decide [ SimpleGraph.fromEdgeSet_adj ] ;
    have h_eq : S = {s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 0)} := by
      have h_eq : Finset.image (fun i => s(f i, f (i + 1))) (Finset.univ : Finset (Fin 4)) = S := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _ <;> simp_all +decide [ Finset.card_image_of_injective _ hf ];
        · exact fun x => by fin_cases x <;> tauto;
        · rw [ Finset.card_image_of_injective _ ] <;> simp +decide [ Function.Injective, * ];
          simp_all +decide [ Fin.forall_fin_succ, Function.Injective.eq_iff hf ];
      simp +decide [ ← h_eq, Fin.univ_succ ];
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    obtain ⟨ x, hx ⟩ := h_cycle; simp_all +decide [ Sym2.toFinset ] ;
    rcases h_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide [ Sym2.toMultiset ];
    · grind;
    · grind;
    · grind;
    · grind

/-
The set of edges of a C4 defined by an embedding f.
-/
def cycle_edges_image {V : Type} [DecidableEq V] (f : Fin 4 ↪ V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => Sym2.mk (f i, f (i + 1)))

#check Sym2.IsDiag

/-
The number of edges in the image of a C4 embedding is 4.
-/
lemma cycle_edges_image_card {V : Type} [DecidableEq V] (f : Fin 4 ↪ V) :
  (cycle_edges_image f).card = 4 := by
    convert Finset.card_image_of_injective _ _;
    simp +decide [ Function.Injective ]

/-
The number of edges connecting two disjoint non-loop edges is 4.
-/
def crossing_edges {V : Type} [DecidableEq V] (e1 e2 : Sym2 V) : Finset (Sym2 V) :=
  let s1 := e1.toFinset
  let s2 := e2.toFinset
  (s1.product s2).image (fun (x, y) => Sym2.mk (x, y))

lemma card_crossing_edges {V : Type} [DecidableEq V] (e1 e2 : Sym2 V)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  (crossing_edges e1 e2).card = 4 := by
    revert e1 e2;
    rintro ⟨ a, b ⟩ ⟨ c, d ⟩ ; simp_all +decide [ Sym2.eq, Finset.disjoint_left ];
    intro hac had hbc hbd hab hcd; unfold crossing_edges; simp +decide [ Finset.card_insert_of_notMem, * ] ;
    rw [ Finset.card_image_of_injOn ] <;> simp +decide [ *, Finset.card_image_of_injective, Function.Injective ];
    · simp +decide [ Sym2.toFinset, * ];
      simp +decide [ Sym2.toMultiset, Finset.card_insert_of_notMem, * ];
    · simp +decide [ Set.InjOn ];
      grind

#print SimpleGraph.IsContained

/-
Any edge connecting vertices in the union of two disjoint edges is either one of the two edges or a crossing edge.
-/
lemma edges_between_disjoint_edges {V : Type} [DecidableEq V] (e1 e2 : Sym2 V) (e : Sym2 V)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_subset : e.toFinset ⊆ e1.toFinset ∪ e2.toFinset)
  (h_nd : ¬e.IsDiag) (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  e = e1 ∨ e = e2 ∨ e ∈ crossing_edges e1 e2 := by
    -- Since $e$ is not a loop, we can write it as $\{a, b\}$ with $a \neq b$.
    obtain ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b ∧ e = Sym2.mk (a, b) := by
      rcases e with ⟨ a, b ⟩ ; use a, b ; aesop;
    simp_all +decide [ Finset.subset_iff, Sym2.IsDiag ];
    rcases h_subset with ⟨ ha | ha, hb | hb ⟩ <;> simp_all +decide [ Finset.disjoint_left, Sym2.lift ];
    · rcases e1 with ⟨ ⟨ x, y ⟩ ⟩ ; aesop;
    · exact Or.inr <| Or.inr <| Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_product.mpr ⟨ by aesop, by aesop ⟩, rfl ⟩;
    · exact Or.inr <| Or.inr <| Finset.mem_image.mpr ⟨ ( b, a ), Finset.mem_product.mpr ⟨ by aesop, by aesop ⟩, by aesop ⟩;
    · cases e2 ; aesop

/-
Any $C_4$ containing two disjoint edges is contained in the union of those edges and the crossing edges between them.
-/
lemma C4_subset_union_crossing {V : Type} [DecidableEq V] (S : Finset (Sym2 V)) (e1 e2 : Sym2 V)
  (h_C4 : is_C4 S) (h_subset : {e1, e2} ⊆ S) (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  S ⊆ {e1, e2} ∪ crossing_edges e1 e2 := by
    -- Take any edge e in S. By h_subset, e is either e1 or e2.
    intro e he
    by_cases h_cases : e = e1 ∨ e = e2;
    · aesop;
    · -- Since $e \in S$ and $S$ is a $C_4$, $e$ must connect vertices in $e_1 \cup e_2$.
      have h_edge_subset : e.toFinset ⊆ e1.toFinset ∪ e2.toFinset := by
        have := vertices_of_C4_with_disjoint_edges S e1 e2 h_C4 h_subset h_disjoint;
        exact this ▸ Finset.le_sup ( f := Sym2.toFinset ) he;
      have h_edge_not_diag : ¬e.IsDiag := by
        contrapose! h_C4;
        cases e ; simp_all +decide [ Finset.subset_iff ];
        rintro ⟨ h1, h2 ⟩;
        obtain ⟨ f, hf ⟩ := not_forall.mp h2;
        obtain ⟨ g, hg ⟩ := f;
        cases g ; simp_all +decide [ Function.Injective ];
        rename_i f hf;
        simp_all +decide [ Fin.forall_fin_succ, SimpleGraph.cycleGraph ];
        have h_card : S ⊇ {s(‹_›, ‹_›), s(f 0, f 1), s(f 0, f 3), s(f 1, f 2), s(f 2, f 3), s(f 3, f 0), s(f 3, f 2)} := by
          simp_all +decide [ Finset.insert_subset_iff ];
        have := Finset.card_le_card h_card; simp_all +decide ;
      have := edges_between_disjoint_edges e1 e2 e h_disjoint h_edge_subset h_edge_not_diag h_nd1 h_nd2; aesop;

/-
The set of potential completions of two disjoint edges to a C4.
-/
def potential_completions {V : Type} [DecidableEq V] (e1 e2 : Sym2 V) : Finset (Finset (Sym2 V)) :=
  match e1.toFinset.toList, e2.toFinset.toList with
  | [u, v], [x, y] =>
    { {Sym2.mk (u, x), Sym2.mk (v, y)}, {Sym2.mk (u, y), Sym2.mk (v, x)} }
  | _, _ => ∅

/-
Edges in a $C_4$ are not loops.
-/
lemma C4_no_loops {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) (e : Sym2 V)
  (h_C4 : is_C4 s) (h_mem : e ∈ s) : ¬e.IsDiag := by
    -- Since $s$ is a $C_4$, it has 4 edges. If $e$ were a loop, then $s$ would have to include $e$ and another edge connecting the same vertices, which would make $s$ have more than 4 edges, contradicting the definition of a $C_4$.
    have h_no_loops : ∀ e ∈ s, ¬e.IsDiag := by
      intro e he
      have h_card : s.card = 4 := by
        exact h_C4.1
      contrapose! h_C4;
      unfold is_C4;
      simp_all +decide [ SimpleGraph.fromEdgeSet ];
      constructor;
      rintro ⟨ f, hf ⟩;
      have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 0 1 from by decide ) ; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 1 2 from by decide ) ; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 2 3 from by decide ) ; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      have := f.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) 3 0 from by decide ) ; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      have := Finset.eq_of_subset_of_card_le ( show { s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 0) } ⊆ s from by aesop_cat ) ; simp_all +decide ;
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> simp_all +decide [ Sym2.eq_swap ];
      · rw [ Finset.ext_iff ] at this ; specialize this e ; aesop;
      · exact hf.ne ( by decide );
      · exact ⟨ by rintro h; have := @hf 1 3; aesop, by rintro h; have := @hf 1 3; aesop ⟩;
      · exact ⟨ by intro h; have := @hf 0 2; aesop, by intro h; have := @hf 0 2; aesop, by intro h; have := @hf 1 3; aesop, by intro h; have := @hf 0 3; aesop ⟩;
    exact h_no_loops e h_mem

/-
Any $C_4$ containing two disjoint edges is contained in the union of those edges and the crossing edges between them.
-/
lemma C4_subset_union_crossing' {V : Type} [DecidableEq V] (S : Finset (Sym2 V)) (e1 e2 : Sym2 V)
  (h_C4 : is_C4 S) (h_subset : {e1, e2} ⊆ S) (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  S ⊆ {e1, e2} ∪ crossing_edges e1 e2 := by
    exact?

/-
The set of disjoint pairs of edges connecting e1 and e2.
-/
def crossing_pairs {V : Type} [DecidableEq V] (e1 e2 : Sym2 V) : Finset (Finset (Sym2 V)) :=
  ((crossing_edges e1 e2).powersetCard 2).filter is_disjoint_pair_prop

/-
The number of potential completions is 2.
-/
lemma potential_completions_card {V : Type} [DecidableEq V] (e1 e2 : Sym2 V)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset) :
  (potential_completions e1 e2).card = 2 := by
    unfold potential_completions;
    rcases e1 with ⟨ u, v ⟩ ; rcases e2 with ⟨ x, y ⟩ ; simp +decide [ h_disjoint, Finset.disjoint_left ] at *;
    rcases n : ( Sym2.toFinset ( Quot.mk ( Sym2.Rel V ) ( u, v ) ) ).toList with _ | ⟨ u, _ | ⟨ v, _ | h ⟩ ⟩ ; rcases n' : ( Sym2.toFinset ( Quot.mk ( Sym2.Rel V ) ( x, y ) ) ).toList with _ | ⟨ x, _ | ⟨ y, _ | h' ⟩ ⟩ ; simp_all +decide;
    all_goals simp_all +decide [ Sym2.toFinset ];
    all_goals simp_all +decide [ Sym2.toMultiset ];
    · rw [ Finset.eq_singleton_iff_unique_mem ] at n ; aesop;
    · rcases n' : ( { x, y } : Finset V ).toList with _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ; aesop;
      · replace n' := congr_arg List.length n'; aesop;
      · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ * ];
        rw [ Finset.ext_iff ] ; simp +decide [ Sym2.eq_iff ];
        use s(u, x); simp +decide [ *, Sym2.eq_iff ] ;
        replace n := congr_arg List.toFinset n; replace n' := congr_arg List.toFinset n'; simp_all +decide [ Finset.ext_iff ] ;
        cases n _ |>.1 ( Or.inl rfl ) <;> cases n _ |>.1 ( Or.inr rfl ) <;> cases n' _ |>.1 ( Or.inl rfl ) <;> cases n' _ |>.1 ( Or.inr rfl ) <;> aesop;
      · replace n' := congr_arg List.length n'; simp_all +decide ;
    · replace n := congr_arg List.length n ; simp_all +decide

/-
The set of crossing edges between two edges is the set of edges connecting their endpoints.
-/
lemma crossing_edges_eq {V : Type} [DecidableEq V] (u v x y : V)
  (hu : u ≠ v) (hx : x ≠ y) :
  crossing_edges (Sym2.mk (u, v)) (Sym2.mk (x, y)) =
  {Sym2.mk (u, x), Sym2.mk (u, y), Sym2.mk (v, x), Sym2.mk (v, y)} := by
    unfold crossing_edges; aesop;

/-
The potential completions of two edges are well-defined and equal to the expected two sets of edges.
-/
lemma potential_completions_spec {V : Type} [DecidableEq V] (u v x y : V)
  (hu : u ≠ v) (hx : x ≠ y) :
  potential_completions (Sym2.mk (u, v)) (Sym2.mk (x, y)) =
  { {Sym2.mk (u, x), Sym2.mk (v, y)}, {Sym2.mk (u, y), Sym2.mk (v, x)} } := by
    -- Since Sym2.mk (u, v) and Sym2.mk (x, y) are non-diagonal, their endpoints are distinct. Therefore, the list of elements in each set is exactly [u, v] and [x, y], respectively.
    have h_list : Sym2.toFinset (Sym2.mk (u, v)) = {u, v} ∧ Sym2.toFinset (Sym2.mk (x, y)) = {x, y} := by
      aesop;
    -- Since the lists are [u, v] and [x, y], the potential completions are exactly the two pairs given.
    have h_lists : (Sym2.toFinset (Sym2.mk (u, v))).toList = [u, v] ∧ (Sym2.toFinset (Sym2.mk (x, y))).toList = [x, y] ∨ (Sym2.toFinset (Sym2.mk (u, v))).toList = [v, u] ∧ (Sym2.toFinset (Sym2.mk (x, y))).toList = [x, y] ∨ (Sym2.toFinset (Sym2.mk (u, v))).toList = [u, v] ∧ (Sym2.toFinset (Sym2.mk (x, y))).toList = [y, x] ∨ (Sym2.toFinset (Sym2.mk (u, v))).toList = [v, u] ∧ (Sym2.toFinset (Sym2.mk (x, y))).toList = [y, x] := by
      have h_lists : (Sym2.toFinset (Sym2.mk (u, v))).toList = [u, v] ∨ (Sym2.toFinset (Sym2.mk (u, v))).toList = [v, u] := by
        have h_list : ∀ {l : List V}, List.length l = 2 → l.toFinset = {u, v} → l = [u, v] ∨ l = [v, u] := by
          intros l hl hl'; rw [ List.length_eq_two ] at hl; obtain ⟨ a, b, rfl ⟩ := hl; simp_all +decide [ Finset.ext_iff ] ;
          cases hl' a ; cases hl' b ; aesop;
        aesop;
      have h_lists' : (Sym2.toFinset (Sym2.mk (x, y))).toList = [x, y] ∨ (Sym2.toFinset (Sym2.mk (x, y))).toList = [y, x] := by
        have h_lists' : ∀ {l : List V}, l.length = 2 → l.toFinset = {x, y} → l = [x, y] ∨ l = [y, x] := by
          intros l hl hl'; rw [ List.length_eq_two ] at hl; obtain ⟨ a, b, rfl ⟩ := hl; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
          grind;
        simp +decide [ *, Finset.card_insert_of_notMem ];
      grind;
    unfold potential_completions; aesop;

/-
Every potential completion is a disjoint pair of crossing edges.
-/
lemma potential_completions_subset_crossing_pairs {V : Type} [DecidableEq V] (e1 e2 : Sym2 V)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset) :
  potential_completions e1 e2 ⊆ crossing_pairs e1 e2 := by
    intro s hs;
    -- By definition of potential_completions, s must be one of the two sets { {u, x}, {v, y} } or { {u, y}, {v, x} }.
    obtain ⟨u, v, x, y, hu, hv, hx, hy, hs_eq⟩ : ∃ u v x y : V, e1 = Sym2.mk (u, v) ∧ e2 = Sym2.mk (x, y) ∧ s = {Sym2.mk (u, x), Sym2.mk (v, y)} ∨ e1 = Sym2.mk (u, v) ∧ e2 = Sym2.mk (x, y) ∧ s = {Sym2.mk (u, y), Sym2.mk (v, x)} := by
      unfold potential_completions at hs;
      rcases e : e1.toFinset.toList with ( _ | ⟨ u, _ | ⟨ v, _ | h ⟩ ⟩ ) <;> rcases e' : e2.toFinset.toList with ( _ | ⟨ x, _ | ⟨ y, _ | h' ⟩ ⟩ ) <;> simp_all +decide;
      -- Since the lists are [u, v] and [x, y], we can directly use these elements to construct the required equality.
      have h_eq : e1 = Sym2.mk (u, v) ∧ e2 = Sym2.mk (x, y) := by
        have h_eq : e1.toFinset = {u, v} ∧ e2.toFinset = {x, y} := by
          exact ⟨ by simpa using congr_arg List.toFinset e, by simpa using congr_arg List.toFinset e' ⟩;
        simp_all +decide [ Finset.ext_iff, Sym2.ext_iff ];
      exact ⟨ u, v, x, y, by aesop ⟩;
    · simp_all +decide [ Finset.subset_iff, crossing_pairs ];
      unfold is_disjoint_pair_prop; simp_all +decide [ Finset.disjoint_left, Sym2.IsDiag ] ;
      unfold crossing_edges; simp +decide [ *, Finset.mem_product ] ;
      constructor;
      · exact ⟨ ⟨ u, x, by tauto ⟩, ⟨ v, y, by tauto ⟩ ⟩;
      · rcases n : Finset.toList { s(u, x), s(v, y) } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
        · replace n := congr_arg List.length n ; simp_all +decide;
        · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n ( s(u, x) ) ; have := n ( s(v, y) ) ; aesop;
        · replace n := congr_arg List.length n ; simp_all +decide;
    · -- Since $u \neq v$ and $x \neq y$, the edges $\{u, y\}$ and $\{v, x\}$ are distinct and have no common vertices, hence they are disjoint.
      have h_disjoint_edges : Disjoint (Sym2.mk (u, y)).toFinset (Sym2.mk (v, x)).toFinset := by
        simp_all +decide [ Finset.disjoint_left, Sym2.toFinset ];
        grind;
      -- Since $s$ is a subset of the crossing edges, it is in the crossing_pairs.
      have h_subset_crossing : s ⊆ crossing_edges e1 e2 := by
        simp_all +decide [ Finset.subset_iff ];
        unfold crossing_edges; aesop;
      refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
      · simp_all +decide [ Finset.subset_iff ];
        rw [ Finset.card_pair ];
        intro h; simp_all +decide [ Finset.disjoint_left ] ;
      · rw [ is_disjoint_pair_iff ];
        use Sym2.mk (u, y), Sym2.mk (v, x);
        simp_all +decide [ Sym2.eq_swap ];
        rintro rfl; simp_all +decide [ Finset.disjoint_left ] ;

/-
Check the definition of SimpleGraph.Free.
-/
#print SimpleGraph.Free

/-
Check the definitions of SimpleGraph.IsContained and SimpleGraph.cycleGraph.
-/
#print SimpleGraph.IsContained
#print SimpleGraph.cycleGraph

/-
Check if SimpleGraph.Iso is available.
-/
#check SimpleGraph.Iso

/-
Check if SimpleGraph.Hom is available.
-/
#check SimpleGraph.Hom

/-
Check the definition of SimpleGraph.Copy.
-/
#print SimpleGraph.Copy

/-
If s is a C4, then s is the image of the edges of a C4 under some embedding.
-/
lemma is_C4_implies_exists_embedding {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) (h : is_C4 s) :
  ∃ f : Fin 4 ↪ V, s = cycle_edges_image f := by
    cases h;
    simp_all +decide [ SimpleGraph.Free ];
    rename_i h1 h2;
    obtain ⟨ f, hf ⟩ := h2;
    have h_card : (Finset.image (fun i => Sym2.mk (f i, f (i + 1))) Finset.univ).card = 4 := by
      rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      simp +decide [ hf.eq_iff ];
    have h_eq : Finset.image (fun i => Sym2.mk (f i, f (i + 1))) Finset.univ = s := by
      exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => by have := f.map_rel' ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) i ( i + 1 ) from by fin_cases i <;> trivial ) ; aesop ) ( by aesop );
    exact ⟨ ⟨ f, hf ⟩, h_eq.symm ⟩

/-
The number of disjoint pairs of edges in the image of a C4 embedding is 2.
-/
lemma cycle_edges_image_disjoint_pairs_card {V : Type} [DecidableEq V] (f : Fin 4 ↪ V) :
  (((cycle_edges_image f).powersetCard 2).filter is_disjoint_pair_prop).card = 2 := by
    unfold cycle_edges_image;
    unfold is_disjoint_pair_prop; simp +decide [ Finset.card_eq_two ] ;
    use { s(f 0, f 1), s(f 2, f 3) }, { s(f 1, f 2), s(f 3, f 0) };
    constructor;
    · simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    · ext s;
      constructor;
      · have h_pairs : ∀ s ∈ Finset.powersetCard 2 (Finset.image (fun i => s(f i, f (i + 1))) Finset.univ), s = {s(f 0, f 1), s(f 1, f 2)} ∨ s = {s(f 0, f 1), s(f 2, f 3)} ∨ s = {s(f 0, f 1), s(f 3, f 0)} ∨ s = {s(f 1, f 2), s(f 2, f 3)} ∨ s = {s(f 1, f 2), s(f 3, f 0)} ∨ s = {s(f 2, f 3), s(f 3, f 0)} := by
          simp +decide [ Finset.mem_powersetCard, Finset.mem_image ];
          intro s hs hs'; rw [ Finset.card_eq_two ] at hs'; obtain ⟨ x, y, hxy ⟩ := hs'; simp_all +decide [ Finset.subset_iff ] ;
          rcases hs with ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩ ; fin_cases a <;> fin_cases b <;> simp +decide at hxy ⊢;
          all_goals simp +decide [ Finset.pair_comm ] ;
          exact Or.inl <| Finset.pair_comm _ _;
        simp +zetaDelta at *;
        intro hs hs' hs''; specialize h_pairs s hs hs'; rcases h_pairs with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +decide [ *, Finset.disjoint_left ] at hs'' ⊢;
        · rcases n : Finset.toList { s(f 0, f 1), s(f 1, f 2) } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_self _ _ ) ; have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ; aesop;
          · grind;
        · rcases n : Finset.toList { s(f 0, f 1), s(f 3, f 0) } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
          · grind;
          · have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_self _ _ ) ; have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ; aesop;
          · grind;
        · rcases n : Finset.toList { s(f 1, f 2), s(f 2, f 3) } with _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_self _ _ ) ; have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ; aesop;
          · replace n := congr_arg List.length n ; simp_all +decide;
        · rcases n : Finset.toList { s(f 2, f 3), s(f 3, f 0) } with _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
            cases this ( s(f 2, f 3) ) ; cases this ( s(f 3, f 0) ) ; aesop;
          · grind;
      · simp +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
        rintro ( rfl | rfl ) <;> simp +decide [ Finset.card_insert_of_notMem, Finset.disjoint_left ];
        · rcases n : Finset.toList { s(f 0, f 1), s(f 2, f 3) } with _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n ; simp +decide at n;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n ( s(f 0, f 1) ) ; have := n ( s(f 2, f 3) ) ; aesop;
          · replace n := congr_arg List.length n ; simp +decide at n;
        · rcases h : Finset.toList { s(f 1, f 2), s(f 3, f 0) } with _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ; aesop;
          · replace h := congr_arg List.length h ; simp +decide at h;
          · replace h := congr_arg List.toFinset h; rw [ Finset.ext_iff ] at h; have := h ( s(f 1, f 2) ) ; have := h ( s(f 3, f 0) ) ; aesop;
          · replace h := congr_arg List.length h ; simp +decide at h

/-
Every C4 has exactly 2 disjoint pairs of edges.
-/
lemma C4_has_two_disjoint_pairs {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) (h : is_C4 s) :
  ((s.powersetCard 2).filter is_disjoint_pair_prop).card = 2 := by
    -- Let's unfold the definition of `is_C4` to use the existence of an embedding `f`.
    obtain ⟨f, hf⟩ := is_C4_implies_exists_embedding s h;
    rw [ hf ] ; exact?;

/-
The set of potential completions of two disjoint edges is exactly the set of disjoint pairs of crossing edges between them.
-/
lemma potential_completions_eq_crossing_disjoint_pairs {V : Type} [DecidableEq V] (e1 e2 : Sym2 V)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset) :
  potential_completions e1 e2 = crossing_pairs e1 e2 := by
    refine' Finset.Subset.antisymm _ _;
    · exact?;
    · -- Let's take any disjoint pair in crossing_pairs e1 e2 and show that it must be one of the potential completions.
      intro s hs
      obtain ⟨e1', e2', he1', he2', h_disjoint'⟩ : ∃ e1' e2', s = {e1', e2'} ∧ e1' ≠ e2' ∧ Disjoint e1'.toFinset e2'.toFinset ∧ e1' ∈ crossing_edges e1 e2 ∧ e2' ∈ crossing_edges e1 e2 := by
        unfold crossing_pairs at hs;
        rw [ Finset.mem_filter, Finset.mem_powersetCard ] at hs;
        obtain ⟨ e1', e2', he1', he2', h ⟩ := Finset.card_eq_two.mp hs.1.2;
        unfold is_disjoint_pair_prop at hs;
        rcases n : Finset.toList { e1', e2' } with ( _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ) <;> simp_all +decide;
        replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n e1'; have := n e2'; aesop;
      -- Since e1' and e2' are in crossing_edges e1 e2, they must be of the form {u, x}, {u, y}, {v, x}, or {v, y}.
      obtain ⟨u, v, x, y, hu, hv, hx, hy⟩ : ∃ u v x y : V, e1 = Sym2.mk (u, v) ∧ e2 = Sym2.mk (x, y) ∧ u ≠ v ∧ x ≠ y := by
        rcases e1 with ⟨ u, v ⟩ ; rcases e2 with ⟨ x, y ⟩ ; use u, v, x, y; aesop;
      -- Since e1' and e2' are in crossing_edges e1 e2, they must be of the form {u, x}, {u, y}, {v, x}, or {v, y}. Therefore, s must be one of the potential completions.
      have h_cases : e1' = Sym2.mk (u, x) ∧ e2' = Sym2.mk (v, y) ∨ e1' = Sym2.mk (u, y) ∧ e2' = Sym2.mk (v, x) ∨ e1' = Sym2.mk (v, y) ∧ e2' = Sym2.mk (u, x) ∨ e1' = Sym2.mk (v, x) ∧ e2' = Sym2.mk (u, y) := by
        unfold crossing_edges at h_disjoint'; simp_all +decide [ Finset.disjoint_left ] ;
        rcases h_disjoint'.2.1 with ⟨ a, b, ⟨ rfl | rfl, rfl | rfl ⟩, rfl ⟩ <;> rcases h_disjoint'.2.2 with ⟨ c, d, ⟨ rfl | rfl, rfl | rfl ⟩, rfl ⟩ <;> simp_all +decide;
      rcases h_cases with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ potential_completions_spec ];
      · exact Or.inl <| Finset.pair_comm _ _;
      · exact Or.inr ( Finset.pair_comm _ _ )

/-
Check if C4_subset_union_crossing is available and what its status is.
-/
#check C4_subset_union_crossing
#print C4_subset_union_crossing

/-
The set of crossing edges between two disjoint edges is the image of a C4 embedding.
-/
lemma crossing_edges_is_cycle_image {V : Type} [DecidableEq V] (e1 e2 : Sym2 V)
  (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  ∃ f : Fin 4 ↪ V, crossing_edges e1 e2 = cycle_edges_image f := by
    rcases e1 with ⟨ u, v ⟩ ; rcases e2 with ⟨ x, y ⟩ ; cases' em ( u = v ) with hu hu <;> cases' em ( x = y ) with hx hx <;> simp_all +decide [ Sym2.mk ];
    -- Define the embedding $f$ such that $f(0) = u$, $f(1) = x$, $f(2) = v$, and $f(3) = y$.
    use ⟨![u, x, v, y], by
      simp_all +decide [ Fin.forall_fin_succ, Function.Injective, Sym2.toFinset ];
      rw [ Multiset.disjoint_iff_ne ] at h_disjoint ; aesop⟩
    generalize_proofs at *;
    simp +decide [ Finset.ext_iff, crossing_edges, cycle_edges_image ];
    intro a; constructor <;> intro h <;> rcases h with ⟨ a, b, h ⟩ <;> simp_all +decide [ Fin.exists_fin_succ ] ;
    · aesop;
    · fin_cases a <;> simp +decide [ * ];
      · exact ⟨ u, x, by aesop ⟩;
      · exact ⟨ v, x, by aesop ⟩;
      · exact ⟨ v, y, by tauto ⟩;
      · exact ⟨ u, y, by aesop ⟩

/-
If p is a disjoint pair of edges in a C4 s, then s \ p is also a disjoint pair of edges.
-/
lemma C4_complement_of_disjoint_pair_is_disjoint_pair {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) (p : Finset (Sym2 V))
  (h_C4 : is_C4 s) (h_p : p ∈ (s.powersetCard 2).filter is_disjoint_pair_prop) :
  is_disjoint_pair_prop (s \ p) := by
    -- Use `is_C4_implies_exists_embedding` to get an embedding `f` such that `s = cycle_edges_image f`.
    obtain ⟨f, hf⟩ := is_C4_implies_exists_embedding s h_C4;
    have := C4_has_two_disjoint_pairs s h_C4; simp_all +decide [ Finset.powersetCard_one ] ;
    -- Since p is a disjoint pair in s, we know that p is one of the two disjoint pairs in s.
    have h_p_cases : p = {Sym2.mk (f 0, f 1), Sym2.mk (f 2, f 3)} ∨ p = {Sym2.mk (f 1, f 2), Sym2.mk (f 3, f 0)} := by
      have h_p_cases : p ∈ Finset.filter is_disjoint_pair_prop (Finset.powersetCard 2 (cycle_edges_image f)) := by
        aesop;
      rw [ show Finset.filter is_disjoint_pair_prop ( Finset.powersetCard 2 ( cycle_edges_image f ) ) = { { Sym2.mk ( f 0, f 1 ), Sym2.mk ( f 2, f 3 ) }, { Sym2.mk ( f 1, f 2 ), Sym2.mk ( f 3, f 0 ) } } from ?_ ] at h_p_cases ; aesop;
      rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ ?_, ?_ ⟩ ) ] <;> simp_all +decide [ Finset.subset_iff ];
      · simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      · unfold cycle_edges_image; simp +decide [ Finset.mem_image ] ;
        unfold is_disjoint_pair_prop; simp +decide [ Finset.toList ] ;
        rcases x : Multiset.toList { s(f 0, f 1), s(f 2, f 3) } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
        · replace x := congr_arg List.length x; simp_all +decide ;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; have := x ( s(f 0, f 1) ) ; have := x ( s(f 2, f 3) ) ; simp_all +decide ;
          cases this <;> cases ‹s(f 0, f 1) = a ∨ s(f 0, f 1) = b› <;> simp_all +decide [ Sym2.eq_swap ];
          · aesop;
          · simp +decide [ ← ‹s(f 2, f 3) = a›, ← ‹s(f 0, f 1) = b›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · simp +decide [ ← ‹s(f 0, f 1) = a›, ← ‹s(f 2, f 3) = b›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · aesop;
        · replace x := congr_arg List.length x ; simp_all +decide;
      · unfold cycle_edges_image; simp +decide [ Finset.mem_image ] ;
        unfold is_disjoint_pair_prop; simp +decide [ Finset.toList ] ;
        rcases h : Multiset.toList { s(f 1, f 2), s(f 3, f 0) } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
        · replace h := congr_arg List.length h; simp +decide at h;
        · replace h := congr_arg List.toFinset h; rw [ Finset.ext_iff ] at h; have := h ( s(f 1, f 2) ) ; have := h ( s(f 3, f 0) ) ; simp_all +decide ;
          cases ‹s(f 1, f 2) = a ∨ s(f 1, f 2) = b› <;> cases ‹s(f 3, f 0) = a ∨ s(f 3, f 0) = b› <;> simp_all +decide [ Sym2.eq_swap ];
          · aesop;
          · simp +decide [ ← ‹s(f 1, f 2) = a›, ← ‹s(f 0, f 3) = b›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · simp +decide [ ← ‹s(f 1, f 2) = b›, ← ‹s(f 0, f 3) = a›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · aesop;
        · replace h := congr_arg List.length h ; simp +decide at h;
    rcases h_p_cases with ( rfl | rfl ) <;> simp_all +decide [ cycle_edges_image ];
    · rw [ show ( Finset.image ( fun i => s(f i, f ( i + 1 ) ) ) Finset.univ : Finset ( Sym2 V ) ) \ { s(f 0, f 1), s(f 2, f 3) } = { s(f 1, f 2), s(f 3, f 0) } from ?_ ] ; simp +decide [ is_disjoint_pair_prop ] ;
      · rcases n : Finset.toList { s(f 1, f 2), s(f 3, f 0) } with _ | ⟨ e1, _ | ⟨ e2, _ | h ⟩ ⟩ ; aesop;
        · replace n := congr_arg List.length n ; simp +decide at n;
        · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n ( s(f 1, f 2) ) ; have := n ( s(f 3, f 0) ) ; simp +decide at *;
          cases ‹s(f 1, f 2) = e1 ∨ s(f 1, f 2) = e2› <;> cases ‹s(f 3, f 0) = e1 ∨ s(f 3, f 0) = e2› <;> simp_all +singlePass [ Sym2.mk ];
          · subst_vars; simp_all +decide [ Sym2.eq_swap ] ;
          · simp +decide [ ← ‹Quot.mk ( Sym2.Rel V ) ( f 1, f 2 ) = e1›, ← ‹Quot.mk ( Sym2.Rel V ) ( f 3, f 0 ) = e2›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · simp +decide [ ← ‹Quot.mk ( Sym2.Rel V ) ( f 1, f 2 ) = e2›, ← ‹Quot.mk ( Sym2.Rel V ) ( f 3, f 0 ) = e1›, Sym2.toFinset ];
            simp +decide [ Sym2.toMultiset ];
          · aesop;
        · replace n := congr_arg List.length n ; simp +decide at n;
      · simp +decide [ Finset.ext_iff, Fin.forall_fin_succ ];
        intro a; constructor;
        · rintro ⟨ ⟨ i, rfl ⟩, hi ⟩ ; fin_cases i <;> tauto;
        · rintro ( rfl | rfl ) <;> simp +decide [ Fin.exists_fin_succ ];
    · rw [ Finset.image ];
      unfold is_disjoint_pair_prop; simp +decide [ Finset.toList ] ;
      rcases x : Multiset.toList ( s(f 0, f 1) ::ₘ { s(f 2, f 3) } ) with ( _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ) <;> simp_all +decide;
      · rw [ eq_comm ] at x ; aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; have := x ( s(f 0, f 1) ) ; have := x ( s(f 2, f 3) ) ; simp +decide at *;
        cases this <;> cases ‹s(f 0, f 1) = a ∨ s(f 0, f 1) = b› <;> simp_all +singlePass [ Sym2.eq_iff ];
        · subst_vars; simp +decide [ Sym2.eq_iff ] at *;
        · subst_vars;
          simp +decide [ Finset.disjoint_left, Sym2.toFinset ];
        · simp +decide [ ← ‹s(f 2, f 3) = b›, ← ‹s(f 0, f 1) = a›, Sym2.toFinset ];
          simp +decide [ Sym2.toMultiset ];
        · simp +decide [ ← ‹s(f 2, f 3) = b›, ← ‹s(f 0, f 1) = b› ] at *;
      · replace x := congr_arg List.length x ; simp +decide at x

/-
If a C4 contains a disjoint pair of edges {e1, e2}, then the remaining edges form a pair in the potential completions of e1 and e2.
-/
lemma C4_containing_disjoint_pair_implies_remainder_in_potential_completions {V : Type} [DecidableEq V] (S : Finset (Sym2 V)) (e1 e2 : Sym2 V)
  (h_C4 : is_C4 S) (h_subset : {e1, e2} ⊆ S) (h_disjoint : Disjoint e1.toFinset e2.toFinset)
  (h_nd1 : ¬e1.IsDiag) (h_nd2 : ¬e2.IsDiag) :
  S \ {e1, e2} ∈ potential_completions e1 e2 := by
    have h_complement_subset : S \ {e1, e2} ⊆ crossing_edges e1 e2 := by
      exact fun x hx => Classical.not_not.1 fun hx' => by have := C4_subset_union_crossing' S e1 e2 h_C4 h_subset h_disjoint h_nd1 h_nd2; exact absurd ( this ( Finset.mem_sdiff.1 hx |>.1 ) ) ( by aesop ) ;
    have h_complement_card : (S \ {e1, e2}).card = 2 := by
      have h_complement_card : (S \ {e1, e2}).card = S.card - ({e1, e2} : Finset (Sym2 V)).card := by
        exact?;
      rw [ h_complement_card, h_C4.1, Finset.card_insert_of_notMem, Finset.card_singleton ];
      simp_all +decide [ Finset.disjoint_left ];
      cases e1 ; cases e2 ; aesop;
    -- Since S \ {e1, e2} is a subset of crossing_edges e1 e2 and has cardinality 2, it must be in the filter.
    have h_complement_in_filter : S \ {e1, e2} ∈ ((crossing_edges e1 e2).powersetCard 2).filter is_disjoint_pair_prop := by
      simp_all +decide [ Finset.mem_filter, Finset.mem_powersetCard ];
      apply_rules [ C4_complement_of_disjoint_pair_is_disjoint_pair ];
      rw [ Finset.mem_filter, Finset.mem_powersetCard ];
      rw [ is_disjoint_pair_iff ];
      by_cases h : e1 = e2 <;> simp_all +decide [ Finset.subset_iff ];
      · cases e2 ; simp_all +decide [ Finset.ext_iff ];
        grind;
      · exact ⟨ e1, e2, rfl, h, h_disjoint ⟩;
    rwa [ potential_completions_eq_crossing_disjoint_pairs e1 e2 h_nd1 h_nd2 h_disjoint ]

/-
A disjoint pair of edges is contained in at most 2 C4s.
-/
lemma disjoint_pair_in_at_most_two_C4s {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (d : Finset (Sym2 V)) (h : d ∈ disjoint_edge_pairs G) :
  ((C4s G).filter (fun s => d ⊆ s)).card ≤ 2 := by
    unfold disjoint_edge_pairs at h;
    -- Let $d = \{e1, e2\}$.
    obtain ⟨e1, e2, he1, he2, hd⟩ : ∃ e1 e2 : Sym2 V, d = {e1, e2} ∧ e1 ≠ e2 ∧ Disjoint e1.toFinset e2.toFinset := by
      rw [ Finset.mem_filter, Finset.mem_powersetCard ] at h;
      rcases h with ⟨ ⟨ hd₁, hd₂ ⟩, hd₃ ⟩;
      exact?;
    -- Let $S$ be a C4 containing $d$. Then $S \setminus d$ is a pair in the potential completions of $e1$ and $e2$.
    have h_subset : ∀ S ∈ C4s G, d ⊆ S → S \ d ∈ potential_completions e1 e2 := by
      intro S hS hdS
      have h_subset : is_C4 S := by
        exact Finset.mem_filter.mp hS |>.2;
      convert C4_containing_disjoint_pair_implies_remainder_in_potential_completions S e1 e2 h_subset ( by aesop ) hd ( by
        have := h_subset.2;
        contrapose! this;
        exact ⟨ fun x => by have := C4_no_loops S e1 h_subset ( by aesop ) ; aesop ⟩ ) ( by
        have h_subset : e2 ∈ S := by
          exact hdS ( he1.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) );
        exact? ) using 1;
      rw [ he1 ];
    -- Since $S \setminus d$ is a pair in the potential completions of $e1$ and $e2$, and there are at most 2 such pairs, the number of C4s containing $d$ is at most 2.
    have h_card : (Finset.filter (fun S => d ⊆ S) (C4s G)).card ≤ (potential_completions e1 e2).card := by
      have h_card : (Finset.filter (fun S => d ⊆ S) (C4s G)).card ≤ (Finset.image (fun S => S \ d) (Finset.filter (fun S => d ⊆ S) (C4s G))).card := by
        rw [ Finset.card_image_of_injOn ];
        intros S hS T hT h_eq;
        rw [ Finset.ext_iff ] at h_eq;
        ext x; specialize h_eq x; by_cases hx : x ∈ d <;> aesop;
      exact h_card.trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun S hS => h_subset S ( Finset.mem_filter.mp hS |>.1 ) ( Finset.mem_filter.mp hS |>.2 ) );
    -- Since $e1$ and $e2$ are edges, they are not loops, so we can apply the lemma potential_completions_card.
    have h_not_loops : ¬e1.IsDiag ∧ ¬e2.IsDiag := by
      have h_not_loops : ∀ e ∈ G.edgeFinset, ¬e.IsDiag := by
        exact?;
      aesop;
    exact h_card.trans ( by rw [ potential_completions_card e1 e2 h_not_loops.1 h_not_loops.2 hd ] )

/-
The number of C4s is at most the square of the number of edges.
-/
theorem C4s_card_le_sq_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (C4s G).card ≤ (G.edgeFinset.card) ^ 2 := by
    -- By the above two lemmas, each C4 contains exactly 2 disjoint pairs of edges, and each disjoint pair is contained in at most 2 C4s.
    have h_count : 2 * (C4s G).card ≤ 2 * (disjoint_edge_pairs G).card := by
      -- By the lemma, each C4 contains exactly 2 disjoint pairs of edges.
      have h_each_C4 : ∀ S ∈ C4s G, ((S.powersetCard 2).filter is_disjoint_pair_prop).card = 2 := by
        intro S hS
        have h_C4 : is_C4 S := by
          unfold C4s at hS; aesop;
        exact C4_has_two_disjoint_pairs S h_C4;
      have h_total_pairs : ∑ S ∈ C4s G, ((S.powersetCard 2).filter is_disjoint_pair_prop).card ≤ ∑ d ∈ disjoint_edge_pairs G, ((C4s G).filter (fun s => d ⊆ s)).card := by
        -- Each term in the sum on the left corresponds to a term in the sum on the right, and the right sum includes all possible pairs, not just those in C4s.
        have h_sum_le : ∀ S ∈ C4s G, ((S.powersetCard 2).filter is_disjoint_pair_prop).card ≤ ∑ d ∈ disjoint_edge_pairs G, (if d ⊆ S then 1 else 0) := by
          intros S hS
          have h_subset : ∀ d ∈ (S.powersetCard 2).filter is_disjoint_pair_prop, d ∈ disjoint_edge_pairs G := by
            simp +zetaDelta at *;
            intro d hd hcard hdisjoint
            have h_subset : d ⊆ G.edgeFinset := by
              exact Finset.Subset.trans hd ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) );
            exact Finset.mem_filter.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ h_subset, hcard ⟩, hdisjoint ⟩;
          have h_sum_le : Finset.filter is_disjoint_pair_prop (Finset.powersetCard 2 S) ⊆ Finset.filter (fun d => d ⊆ S) (disjoint_edge_pairs G) := by
            intro d hd; specialize h_subset d hd; aesop;
          simpa [ Finset.sum_filter ] using Finset.card_le_card h_sum_le;
        refine' le_trans ( Finset.sum_le_sum h_sum_le ) _;
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
      have h_each_pair : ∀ d ∈ disjoint_edge_pairs G, ((C4s G).filter (fun s => d ⊆ s)).card ≤ 2 := by
        exact?;
      exact le_trans ( by rw [ Finset.sum_congr rfl h_each_C4 ] ; simp +arith +decide [ mul_comm ] ) ( h_total_pairs.trans ( Finset.sum_le_sum h_each_pair ) ) |> le_trans <| by simp +decide [ mul_comm ] ;
    exact le_trans ( by linarith ) ( card_disjoint_pairs_le_choose_two G ) |> le_trans <| Nat.choose_le_pow _ _

/-
Every graph with m edges contains a C4-free subgraph with at least (3/8) * m^(2/3) edges.
-/
theorem exists_C4_free_subgraph_with_many_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ (S' : Finset (Sym2 V)), S' ⊆ G.edgeFinset ∧
  (∀ s, s ⊆ S' → ¬is_C4 s) ∧
  (S'.card : ℝ) ≥ (3/8) * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) := by
    by_contra! h;
    obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ (S.card : ℝ) - ((C4s G).filter (fun s => s ⊆ S)).card ≥ (3/8) * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) := by
      apply_rules [ combinatorial_lemma_general ];
      · exact fun s hs => Finset.mem_filter.mp hs |>.2.1;
      · exact fun s hs => Finset.mem_powerset.mp ( Finset.mem_filter.mp hs |>.1 );
      · exact?;
    -- For each $c \in C_S$, pick an edge $e_c \in c$.
    obtain ⟨f, hf⟩ : ∃ f : Finset (Sym2 V) → Sym2 V, ∀ c ∈ (C4s G).filter (fun s => s ⊆ S), f c ∈ c ∧ f c ∈ S := by
      have h_choose : ∀ c ∈ (C4s G).filter (fun s => s ⊆ S), ∃ e ∈ c, e ∈ S := by
        simp_all +decide [ Finset.subset_iff ];
        exact fun c hc hc' => Exists.elim ( Finset.card_pos.mp ( by linarith [ show c.card = 4 from ( Finset.mem_filter.mp hc ) |>.2.1 ] ) ) fun x hx => ⟨ x, hx, hc' hx ⟩;
      choose! f hf₁ hf₂ using h_choose;
      exact ⟨ fun c => if hc : c ∈ Finset.filter ( fun s => s ⊆ S ) ( C4s G ) then f c hc else Classical.choose ( Finset.card_pos.mp ( by
        norm_num +zetaDelta at *;
        exact Finset.card_pos.mp ( Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at hS; linarith [ show ( 0 : ℝ ) < 3 / 8 * ( Finset.card ( Finset.filter ( Membership.mem G.edgeSet ) Finset.univ ) : ℝ ) ^ ( 2 / 3 : ℝ ) by exact mul_pos ( by norm_num ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| by
                                                                                                        by_cases h : Finset.card ( Finset.filter ( Membership.mem G.edgeSet ) Finset.univ ) = 0 <;> simp_all +decide;
                                                                                                        · rename_i h₁ h₂;
                                                                                                          exact absurd ( h₁ ∅ ( by simp +decide ) ( by simp +decide [ is_C4 ] ) ) ( by norm_num );
                                                                                                        · exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.choose_spec ⟩ ⟩ ) _ ) ] ) ) : Finset.card S > 0 ) ), fun c hc => by aesop ⟩;
    -- Let $S' = S \setminus \{f(c) \mid c \in C_S\}$.
    set S' := S \ Finset.image f ((C4s G).filter (fun s => s ⊆ S));
    -- We need to show that $S'$ is $C4$-free.
    have hS'_free : ∀ s ⊆ S', ¬is_C4 s := by
      intro s hs h_C4
      have h_subset : s ∈ (C4s G).filter (fun s => s ⊆ S) := by
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by intro x hx; specialize hs hx; aesop ), h_C4 ⟩, fun x hx => Finset.mem_sdiff.mp ( hs hx ) |>.1 ⟩;
      have := hs ( hf s h_subset |>.1 ) ; aesop;
    -- We need to show that $|S'| \geq \frac{3}{8} m^{2/3}$.
    have hS'_card : (S'.card : ℝ) ≥ (3/8) * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · rw [ show ( Finset.image f ( { s ∈ C4s G | s ⊆ S } ) ∩ S ) = Finset.image f ( { s ∈ C4s G | s ⊆ S } ) from Finset.inter_eq_left.mpr <| Finset.image_subset_iff.mpr fun x hx => hf x hx |>.2 ] ; linarith [ show ( Finset.card ( Finset.image f ( { s ∈ C4s G | s ⊆ S } ) ) : ℝ ) ≤ Finset.card ( { s ∈ C4s G | s ⊆ S } ) from mod_cast Finset.card_image_le ];
      · exact Finset.card_le_card fun x hx => by aesop;
    exact not_lt_of_ge hS'_card <| h S' ( Finset.sdiff_subset.trans hS.1 ) hS'_free
