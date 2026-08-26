import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Count-and-load allocation (Lemma 4.2 of the paper)

A self-contained combinatorial allocation lemma used in the profile lemma.
Given component sizes `s₁,…,s_d` (each `≤ n/2`, summing to `n-1`) and capacities
`c₁,…,c_q` with `c_i ≤ (1+δ₀)n` and `∑ c_i ≥ (1+ω)n`, there is an assignment of
the components to the `q` bins respecting the capacities and keeping every bin's
total load below `(1-κ)n`.
-/

open Finset

set_option maxHeartbeats 1600000

namespace Erdos550

/-
If the total capacity is at least the number of items, a capacity-respecting
assignment exists.
-/
theorem exists_feasible_assignment {q : ℕ} :
    ∀ (d : ℕ) (c : Fin q → ℕ), d ≤ ∑ i, c i →
      ∃ I : Fin d → Fin q, ∀ i, #{j | I j = i} ≤ c i := by
  intro d c hcd; induction' d with d hd generalizing c; aesop;
  obtain ⟨I, hI⟩ := hd c (by linarith);
  obtain ⟨i0, hi0⟩ : ∃ i0, (Finset.univ.filter (fun j => I j = i0)).card < c i0 := by
    contrapose! hcd;
    refine' lt_of_le_of_lt ( Finset.sum_le_sum fun i _ => hcd i ) _;
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; aesop;
  refine' ⟨ Fin.cons i0 I, fun i => _ ⟩ ; simp_all +decide [  ];
  rcases eq_or_ne i i0 with rfl | hi <;> simp_all +decide [ Fin.univ_succ ]; all_goals rw [ Finset.filter_insert, Finset.filter_map ] ; aesop

/-
Moving item `j0` to bin `i0` changes the weighted fiber sums in the expected
way (stated additively to avoid truncated subtraction).
-/
theorem sum_fiber_update {q d : ℕ} (I : Fin d → Fin q) (j0 : Fin d) (i0 i : Fin q)
    (w : Fin d → ℕ) :
    (∑ j ∈ {j | Function.update I j0 i0 j = i}, w j) + (if i = I j0 then w j0 else 0)
      = (∑ j ∈ {j | I j = i}, w j) + (if i = i0 then w j0 else 0) := by
  by_cases hi : i = I j0 <;> simp +decide [ hi, Function.update_apply ];
  · by_cases hi0 : I j0 = i0 <;> simp +decide [ hi0 ];
    · congr 1 with x ; by_cases hx : x = j0 <;> aesop;
    · rw [ show ( Finset.filter ( fun x => ( if x = j0 then i0 else I x ) = I j0 ) Finset.univ ) = Finset.filter ( fun x => I x = I j0 ) Finset.univ \ { j0 } from ?_, Finset.sum_eq_sum_sdiff_singleton_add <| Finset.mem_filter.mpr ⟨ Finset.mem_univ j0, by aesop ⟩ ];
      grind;
  · by_cases hi0 : i = i0 <;> simp_all +decide [  ];
    · rw [ show ( Finset.filter ( fun x => ¬x = j0 → I x = i0 ) Finset.univ ) = Finset.filter ( fun x => I x = i0 ) Finset.univ ∪ { j0 } from ?_, Finset.sum_union ] <;> norm_num [ Finset.filter_union_right, hi ];
      · tauto;
      · grind;
    · congr 1 with x ; aesop

/-
**Count-and-load allocation.**
-/
theorem count_and_load (q : ℕ) (_hq : 2 ≤ q) (ω : ℝ) (hω : 0 < ω) :
    ∃ κ δ0 : ℝ, 0 < κ ∧ 0 < δ0 ∧ ∀ (n d : ℕ) (s : Fin d → ℕ) (c : Fin q → ℕ),
      (∀ j, 0 < s j) → (∀ j, 2 * s j ≤ n) → (∑ j, s j = n - 1) →
      (∀ i, (c i : ℝ) ≤ (1 + δ0) * n) → ((1 + ω) * (n : ℝ) ≤ ∑ i, (c i : ℝ)) →
      ∃ I : Fin d → Fin q,
        (∀ i, #{j | I j = i} ≤ c i) ∧
        (∀ i, (∑ j ∈ {j | I j = i}, (s j : ℝ)) ≤ (1 - κ) * n) := by
  refine' ⟨ Min.min ω 1 / 16, ω / 4, _, _, _ ⟩;
  · positivity;
  · positivity;
  · intro n d s c hs hs' hs'' hc hsum
    by_cases hn : n = 0;
    · cases d <;> aesop;
    · -- Choose a feasible assignment $I^*$ minimizing $\Phi$ over the (finite, nonempty) set of feasible assignments via `Finset.exists_min_image` (use `Set.Finite.toFinset` / `Set.toFinite`).
      obtain ⟨I, hI⟩ : ∃ I : Fin d → Fin q, (∀ i, (Finset.card (Finset.filter (fun j => I j = i) Finset.univ)) ≤ c i) ∧ ∀ I' : Fin d → Fin q, (∀ i, (Finset.card (Finset.filter (fun j => I' j = i) Finset.univ)) ≤ c i) → (∑ i, (∑ j ∈ Finset.filter (fun j => I j = i) Finset.univ, s j : ℝ) ^ 2) ≤ (∑ i, (∑ j ∈ Finset.filter (fun j => I' j = i) Finset.univ, s j : ℝ) ^ 2) := by
        apply_rules [ Set.exists_min_image ];
        · exact Set.toFinite _;
        · convert! exists_feasible_assignment d c _;
          have h_sum_c : d ≤ n - 1 := by
            exact hs''.symm ▸ le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => Nat.succ_le_of_lt ( hs _ ) );
          exact le_trans h_sum_c ( Nat.sub_le_of_le_add <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ) ] );
      refine' ⟨ I, hI.1, _ ⟩;
      intro i
      by_contra h_contra
      have h_heavy : ∃ h, (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) > (1 - min ω 1 / 16) * n := by
        exact ⟨ i, not_le.mp h_contra ⟩;
      obtain ⟨ h, hh ⟩ := h_heavy
      have h_free_slot : ∃ i0, i0 ≠ h ∧ (Finset.card (Finset.filter (fun j => I j = i0) Finset.univ)) < c i0 := by
        have h_free_slot : ∑ i ∈ Finset.univ.erase h, (Finset.card (Finset.filter (fun j => I j = i) Finset.univ)) < ∑ i ∈ Finset.univ.erase h, (c i : ℝ) := by
          have h_free_slot : ∑ i ∈ Finset.univ.erase h, (Finset.card (Finset.filter (fun j => I j = i) Finset.univ)) ≤ (n - 1) - (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) := by
            have h_free_slot : ∑ i ∈ Finset.univ.erase h, (Finset.card (Finset.filter (fun j => I j = i) Finset.univ)) ≤ ∑ j ∈ Finset.univ.filter (fun j => I j ≠ h), (s j : ℝ) := by
              have h_free_slot : ∀ i ∈ Finset.univ.erase h, (Finset.card (Finset.filter (fun j => I j = i) Finset.univ)) ≤ ∑ j ∈ Finset.filter (fun j => I j = i) Finset.univ, (s j : ℝ) := by
                exact fun i hi => mod_cast le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => Nat.succ_le_of_lt ( hs _ ) );
              convert! Finset.sum_le_sum h_free_slot using 1;
              · norm_cast;
              · rw [ ← Finset.sum_biUnion ];
                · rcongr j ; aesop;
                · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
            convert! h_free_slot using 1;
            rw [ eq_comm, Finset.sum_filter ];
            rw [ Finset.sum_ite ] ; norm_num [ Finset.filter_not, Finset.sum_add_distrib ] ; ring_nf;
            norm_cast ; cases n <;> aesop;
          simp_all +decide;
          nlinarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ), min_le_left ω 1, min_le_right ω 1, hc h ];
        norm_cast at *;
        exact not_forall_not.mp fun h => h_free_slot.not_ge <| Finset.sum_le_sum fun i hi => le_of_not_gt fun hi' => h i <| by aesop;
      obtain ⟨ i0, hi0₁, hi0₂ ⟩ := h_free_slot
      obtain ⟨ j0, hj0 ⟩ : ∃ j0, I j0 = h := by
        exact not_forall_not.mp fun contra => by rw [ Finset.sum_eq_zero fun x hx => False.elim <| contra x <| by aesop ] at hh; nlinarith [ show ( 0 : ℝ ) < n by positivity, show ( 0 : ℝ ) < min ω 1 by positivity, min_le_left ω 1, min_le_right ω 1 ] ;
      set I' : Fin d → Fin q := Function.update I j0 i0
      have hI'_feasible : ∀ i, (Finset.card (Finset.filter (fun j => I' j = i) Finset.univ)) ≤ c i := by
        intro i
        have hc := sum_fiber_update I j0 i0 i (fun _ => 1)
        simp only [Finset.sum_const, smul_eq_mul, mul_one, hj0] at hc
        by_cases hi : i = i0
        · subst i
          simp only [hi0₁, ↓reduceIte] at hc
          change #{j | Function.update I j0 i0 j = i0} ≤ c i0
          omega
        · by_cases hh : i = h
          · subst i
            simp only [Ne.symm hi0₁, ↓reduceIte] at hc
            change #{j | Function.update I j0 i0 j = h} ≤ c h
            have := hI.1 h
            omega
          · simp only [hi, hh, ↓reduceIte, add_zero] at hc
            change #{j | Function.update I j0 i0 j = i} ≤ c i
            exact hc.trans_le (hI.1 i)
      have hI'_potential : (∑ i, (∑ j ∈ Finset.filter (fun j => I' j = i) Finset.univ, (s j : ℝ)) ^ 2) < (∑ i, (∑ j ∈ Finset.filter (fun j => I j = i) Finset.univ, (s j : ℝ)) ^ 2) := by
        have hI'_potential : (∑ j ∈ Finset.filter (fun j => I' j = i0) Finset.univ, (s j : ℝ)) = (∑ j ∈ Finset.filter (fun j => I j = i0) Finset.univ, (s j : ℝ)) + (s j0 : ℝ) ∧ (∑ j ∈ Finset.filter (fun j => I' j = h) Finset.univ, (s j : ℝ)) = (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) - (s j0 : ℝ) := by
          constructor;
          · rw [ show ( Finset.filter ( fun j => I' j = i0 ) Finset.univ ) = Finset.filter ( fun j => I j = i0 ) Finset.univ ∪ { j0 } from ?_, Finset.sum_union ] <;> norm_num [ hj0, hi0₁ ]; all_goals grind;
          · rw [ show ( Finset.filter ( fun j => I' j = h ) Finset.univ ) = Finset.filter ( fun j => I j = h ) Finset.univ \ { j0 } from ?_, Finset.sum_eq_sum_sdiff_singleton_add ( show j0 ∈ Finset.filter ( fun j => I j = h ) Finset.univ from Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj0 ⟩ ) ] ; aesop;
            grind;
        have hI'_potential : (∑ j ∈ Finset.filter (fun j => I j = i0) Finset.univ, (s j : ℝ)) < (min ω 1 / 16) * n := by
          have hI'_potential : (∑ j ∈ Finset.filter (fun j => I j = i0) Finset.univ, (s j : ℝ)) + (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) ≤ (n - 1 : ℝ) := by
            have hI'_potential : (∑ j ∈ Finset.filter (fun j => I j = i0) Finset.univ, (s j : ℝ)) + (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) ≤ (∑ j, (s j : ℝ)) := by
              rw [ ← Finset.sum_union ];
              · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => Nat.cast_nonneg _;
              · exact Finset.disjoint_filter.mpr fun _ _ _ _ => hi0₁ <| by aesop;
            exact hI'_potential.trans ( by rw [ ← Nat.cast_sum, hs'' ] ; cases n <;> norm_num at * );
          linarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ) ];
        have hI'_potential : (∑ j ∈ Finset.filter (fun j => I' j = i0) Finset.univ, (s j : ℝ)) ^ 2 + (∑ j ∈ Finset.filter (fun j => I' j = h) Finset.univ, (s j : ℝ)) ^ 2 < (∑ j ∈ Finset.filter (fun j => I j = i0) Finset.univ, (s j : ℝ)) ^ 2 + (∑ j ∈ Finset.filter (fun j => I j = h) Finset.univ, (s j : ℝ)) ^ 2 := by
          have hI'_potential : (s j0 : ℝ) ≤ n / 2 := by
            rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ hs' j0 ];
          have hI'_potential : (min ω 1 / 16) * n - (1 - min ω 1 / 16) * n + n / 2 < 0 := by
            cases min_cases ω 1 <;> nlinarith [ show ( n : ℝ ) > 0 by positivity ];
          nlinarith [ show ( s j0 : ℝ ) > 0 from Nat.cast_pos.mpr ( hs j0 ) ];
        have hI'_potential : ∀ i, i ≠ i0 ∧ i ≠ h → (∑ j ∈ Finset.filter (fun j => I' j = i) Finset.univ, (s j : ℝ)) = (∑ j ∈ Finset.filter (fun j => I j = i) Finset.univ, (s j : ℝ)) := by
          intros i hi
          have hI'_potential : ∀ j, I' j = i ↔ I j = i := by
            grind;
          simp +decide only [hI'_potential];
        have hI'_potential : ∑ i ∈ Finset.univ \ {i0, h}, (∑ j ∈ Finset.filter (fun j => I' j = i) Finset.univ, (s j : ℝ)) ^ 2 = ∑ i ∈ Finset.univ \ {i0, h}, (∑ j ∈ Finset.filter (fun j => I j = i) Finset.univ, (s j : ℝ)) ^ 2 := by
          exact Finset.sum_congr rfl fun x hx => by rw [ hI'_potential x ⟨ by aesop_cat, by aesop_cat ⟩ ] ;
        simp_all +decide [ Finset.sum_pair hi0₁ ];
        linarith
      exact absurd (hI.2 I' hI'_feasible) (by linarith)

end Erdos550
