/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaSieveFundamental
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Combinatorics of beta-sieve first-failure chains

This file contains the purely finite facts needed to pass from the explicit
`upperFailureTerms` and `lowerFailureTerms` lists to elementary-symmetric
majorants.  No density or product-ratio assumption occurs here.
-/

namespace Erdos851.BetaSieveFundamental

open List

/-- Membership in `buchstabChildren` records an element together with the
literal suffix following that occurrence. -/
theorem mem_buchstabChildren_iff_split {α : Type*}
    {q : α × List α} {l : List α} :
    q ∈ buchstabChildren l ↔ ∃ before, l = before ++ q.1 :: q.2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [buchstabChildren_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨before, rfl⟩)
        · exact ⟨[], rfl⟩
        · exact ⟨a :: before, by simp⟩
      · rintro ⟨before, h⟩
        cases before with
        | nil =>
            simp only [List.nil_append] at h
            exact Or.inl (Prod.ext (List.cons.inj h).1.symm
              (List.cons.inj h).2.symm)
        | cons b before =>
            simp only [List.cons_append, List.cons.injEq] at h
            exact Or.inr ⟨before, h.2⟩

theorem buchstabChild_cons_suffix_sublist {α : Type*}
    {q : α × List α} {l : List α} (hq : q ∈ buchstabChildren l) :
    q.1 :: q.2 <+ l := by
  obtain ⟨before, rfl⟩ := mem_buchstabChildren_iff_split.mp hq
  exact List.sublist_append_right before (q.1 :: q.2)

theorem buchstabChild_suffix_isSuffix {α : Type*}
    {q : α × List α} {l : List α} (hq : q ∈ buchstabChildren l) :
    q.2 <:+ l := by
  obtain ⟨before, rfl⟩ := mem_buchstabChildren_iff_split.mp hq
  exact ⟨before ++ [q.1], by simp [List.append_assoc]⟩

/-- Complete structural information carried by one failure term.  Besides
being an ordered sublist, its second component is *exactly* the suffix after
the final selected element, not merely some suffix of the input. -/
def FailureTermStructure {α : Type*}
    (remaining : List α) (t : List α × List α) : Prop :=
  t.1 ++ t.2 <+ remaining ∧
    ∃ init last before,
      t.1 = init ++ [last] ∧ remaining = before ++ last :: t.2

theorem failureTerms_structure {α : Type*} (stop : List α → Bool) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      (∀ t ∈ upperFailureTerms stop fuel selected remaining,
          FailureTermStructure remaining t) ∧
        (∀ t ∈ lowerFailureTerms stop fuel selected remaining,
          FailureTermStructure remaining t) := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [upperFailureTerms, lowerFailureTerms]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · intro t ht
        simp only [upperFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, hq, ht⟩ := ht
        obtain ⟨beforeq, hsplitq⟩ := mem_buchstabChildren_iff_split.mp hq
        cases hstop : stop (selected ++ [q.1])
        · simp only [hstop, Bool.false_eq_true, ↓reduceIte,
            List.mem_singleton] at ht
          subst t
          constructor
          · exact buchstabChild_cons_suffix_sublist hq
          · exact ⟨[], q.1, beforeq, by simp, hsplitq⟩
        · simp only [hstop, ↓reduceIte, List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          obtain ⟨husub, init, last, before, hchain, hsuffix⟩ :=
            (ih (selected ++ [q.1]) q.2).2 u hu
          constructor
          · exact (husub.cons_cons q.1).trans
              (buchstabChild_cons_suffix_sublist hq)
          · refine ⟨q.1 :: init, last, beforeq ++ q.1 :: before, ?_, ?_⟩
            · simp [hchain]
            · simp [hsplitq, hsuffix, List.append_assoc]
      · intro t ht
        simp only [lowerFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, hq, ht⟩ := ht
        obtain ⟨beforeq, hsplitq⟩ := mem_buchstabChildren_iff_split.mp hq
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        obtain ⟨husub, init, last, before, hchain, hsuffix⟩ :=
          (ih (selected ++ [q.1]) q.2).1 u hu
        constructor
        · exact (husub.cons_cons q.1).trans
            (buchstabChild_cons_suffix_sublist hq)
        · refine ⟨q.1 :: init, last, beforeq ++ q.1 :: before, ?_, ?_⟩
          · simp [hchain]
          · simp [hsplitq, hsuffix, List.append_assoc]

/-- The full first-failure recursion invariant. Upper failure chains have odd
length and lower failure chains have even length. The full selected chain
fails `stop`, while every earlier nonempty tested prefix (that is, a prefix of
the same parity) passes it. -/
theorem failureTerms_parity_prefixes_final {α : Type*}
    (stop : List α → Bool) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      (∀ t ∈ upperFailureTerms stop fuel selected remaining,
          Odd t.1.length ∧
            stop (selected ++ t.1) = false ∧
            ∀ n, 0 < n → n < t.1.length → Odd n →
              stop (selected ++ t.1.take n) = true) ∧
        (∀ t ∈ lowerFailureTerms stop fuel selected remaining,
          Even t.1.length ∧
            stop (selected ++ t.1) = false ∧
            ∀ n, 0 < n → n < t.1.length → Even n →
              stop (selected ++ t.1.take n) = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [upperFailureTerms, lowerFailureTerms]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · intro t ht
        simp only [upperFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        cases hstop : stop (selected ++ [q.1])
        · simp only [hstop, Bool.false_eq_true, ↓reduceIte,
            List.mem_singleton] at ht
          subst t
          refine ⟨by simp, by simpa using hstop, ?_⟩
          intro n _hnpos hnlt hnodd
          obtain ⟨k, hk⟩ := hnodd
          simp only [List.length_singleton] at hnlt
          omega
        · simp only [hstop, ↓reduceIte, List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          obtain ⟨huEven, huFinal, huPrefixes⟩ :=
            (ih (selected ++ [q.1]) q.2).2 u hu
          refine ⟨?_, ?_, ?_⟩
          · simpa using huEven.add_one
          · simpa [List.append_assoc] using huFinal
          · intro n hnpos hnlt hnodd
            cases n with
            | zero => simp at hnpos
            | succ k =>
                have hklt : k < u.1.length := by
                  simp only [List.length_cons] at hnlt
                  omega
                by_cases hkzero : k = 0
                · subst k
                  simpa using hstop
                · have hkeven : Even k := by
                    obtain ⟨j, hj⟩ := hnodd
                    exact ⟨j, by omega⟩
                  have hkpos : 0 < k := Nat.zero_lt_of_ne_zero hkzero
                  have hpass := huPrefixes k hkpos hklt hkeven
                  simpa [List.append_assoc] using hpass
      · intro t ht
        simp only [lowerFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        obtain ⟨huOdd, huFinal, huPrefixes⟩ :=
          (ih (selected ++ [q.1]) q.2).1 u hu
        refine ⟨?_, ?_, ?_⟩
        · simpa using huOdd.add_one
        · simpa [List.append_assoc] using huFinal
        · intro n hnpos hnlt hneven
          cases n with
          | zero => simp at hnpos
          | succ k =>
              have hklt : k < u.1.length := by
                simp only [List.length_cons] at hnlt
                omega
              have hkodd : Odd k := by
                obtain ⟨j, hj⟩ := hneven
                cases j with
                | zero => omega
                | succ j => exact ⟨j, by omega⟩
              obtain ⟨j, hj⟩ := hkodd
              have hkpos : 0 < k := by omega
              have hpass := huPrefixes k hkpos hklt ⟨j, hj⟩
              simpa [List.append_assoc] using hpass

theorem upperFailureTerms_chain_length_odd {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining) :
    Odd t.1.length :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).1 t ht).1

theorem lowerFailureTerms_chain_length_even {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining) :
    Even t.1.length :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).2 t ht).1

theorem upperFailureTerms_terminal_failure {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining) :
    stop (selected ++ t.1) = false :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).1 t ht).2.1

theorem lowerFailureTerms_terminal_failure {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining) :
    stop (selected ++ t.1) = false :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).2 t ht).2.1

/-- Every nonempty proper prefix of an upper failure chain having the same
parity as that (necessarily odd) chain passed `stop`. -/
theorem upperFailureTerms_sameParity_prefix_passes {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining)
    {n : ℕ} (hnpos : 0 < n) (hnlt : n < t.1.length) (hnodd : Odd n) :
    stop (selected ++ t.1.take n) = true :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).1 t ht).2.2
    n hnpos hnlt hnodd

/-- Every nonempty proper prefix of a lower failure chain having the same
parity as that (necessarily even) chain passed `stop`. -/
theorem lowerFailureTerms_sameParity_prefix_passes {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining)
    {n : ℕ} (hnpos : 0 < n) (hnlt : n < t.1.length) (hneven : Even n) :
    stop (selected ++ t.1.take n) = true :=
  ((failureTerms_parity_prefixes_final stop fuel selected remaining).2 t ht).2.2
    n hnpos hnlt hneven

theorem upperFailureTerms_chain_sublist {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining) :
    t.1 <+ remaining :=
  (List.sublist_append_left t.1 t.2).trans
    ((failureTerms_structure stop fuel selected remaining).1 t ht).1

theorem lowerFailureTerms_chain_sublist {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining) :
    t.1 <+ remaining :=
  (List.sublist_append_left t.1 t.2).trans
    ((failureTerms_structure stop fuel selected remaining).2 t ht).1

theorem upperFailureTerms_suffix_isSuffix {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining) :
    t.2 <:+ remaining := by
  obtain ⟨_init, last, before, _hchain, hremaining⟩ :=
    ((failureTerms_structure stop fuel selected remaining).1 t ht).2
  exact ⟨before ++ [last], by simpa [List.append_assoc] using hremaining.symm⟩

theorem lowerFailureTerms_suffix_isSuffix {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining) :
    t.2 <:+ remaining := by
  obtain ⟨_init, last, before, _hchain, hremaining⟩ :=
    ((failureTerms_structure stop fuel selected remaining).2 t ht).2
  exact ⟨before ++ [last], by simpa [List.append_assoc] using hremaining.symm⟩

theorem upperFailureTerms_chain_mem_sublistsLen {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ upperFailureTerms stop fuel selected remaining) :
    t.1 ∈ remaining.sublistsLen t.1.length :=
  List.mem_sublistsLen.mpr
    ⟨upperFailureTerms_chain_sublist stop fuel selected remaining ht, rfl⟩

theorem lowerFailureTerms_chain_mem_sublistsLen {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    {t : List α × List α}
    (ht : t ∈ lowerFailureTerms stop fuel selected remaining) :
    t.1 ∈ remaining.sublistsLen t.1.length :=
  List.mem_sublistsLen.mpr
    ⟨lowerFailureTerms_chain_sublist stop fuel selected remaining ht, rfl⟩

@[simp]
theorem buchstabChildren_map_fst {α : Type*} (l : List α) :
    (buchstabChildren l).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Failure chains do not occur with multiplicity when the ambient ordered
list has no repeated entries.  This is the injectivity input needed when a
chain sum is enlarged to all members of `sublistsLen`. -/
theorem failureTerms_chains_nodup {α : Type*} (stop : List α → Bool) :
    ∀ (fuel : ℕ) (selected remaining : List α), remaining.Nodup →
      ((upperFailureTerms stop fuel selected remaining).map Prod.fst).Nodup ∧
        ((lowerFailureTerms stop fuel selected remaining).map Prod.fst).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining _hrem
      simp [upperFailureTerms, lowerFailureTerms]
  | succ fuel ih =>
      intro selected remaining hrem
      let U : (α × List α) → List (List α) := fun q =>
        if stop (selected ++ [q.1]) then
          (lowerFailureTerms stop fuel (selected ++ [q.1]) q.2).map
            (fun t => q.1 :: t.1)
        else [[q.1]]
      let L : (α × List α) → List (List α) := fun q =>
        (upperFailureTerms stop fuel (selected ++ [q.1]) q.2).map
          (fun t => q.1 :: t.1)
      have hupperEq :
          (upperFailureTerms stop (fuel + 1) selected remaining).map Prod.fst =
            (buchstabChildren remaining).flatMap U := by
        simp only [upperFailureTerms, List.map_flatMap]
        apply List.flatMap_congr
        intro q _hq
        simp only [U]
        split <;> simp [List.map_map, Function.comp_def]
      have hlowerEq :
          (lowerFailureTerms stop (fuel + 1) selected remaining).map Prod.fst =
            (buchstabChildren remaining).flatMap L := by
        simp only [lowerFailureTerms, List.map_flatMap]
        apply List.flatMap_congr
        intro q _hq
        simp [L, List.map_map, Function.comp_def]
      have hchildren :
          (buchstabChildren remaining).Pairwise
            (fun q q' => q.1 ≠ q'.1) := by
        have hmapped :
            ((buchstabChildren remaining).map Prod.fst).Nodup := by
          simpa using hrem
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmapped
        exact hmapped
      have hUnodup : ∀ q ∈ buchstabChildren remaining, (U q).Nodup := by
        intro q hq
        have hqnodup : q.2.Nodup :=
          hrem.sublist (buchstabChild_suffix_isSuffix hq).sublist
        have hi := ih (selected ++ [q.1]) q.2 hqnodup
        simp only [U]
        split
        · simpa only [List.map_map, Function.comp_def] using
            (List.nodup_map_iff
              (fun _ _ h => List.cons.inj h |>.2)).mpr hi.2
        · simp
      have hLnodup : ∀ q ∈ buchstabChildren remaining, (L q).Nodup := by
        intro q hq
        have hqnodup : q.2.Nodup :=
          hrem.sublist (buchstabChild_suffix_isSuffix hq).sublist
        have hi := ih (selected ++ [q.1]) q.2 hqnodup
        simp only [L]
        simpa only [List.map_map, Function.comp_def] using
          (List.nodup_map_iff
            (fun _ _ h => List.cons.inj h |>.2)).mpr hi.1
      have hUhead : ∀ q, ∀ c ∈ U q, ∃ tail, c = q.1 :: tail := by
        intro q c hc
        simp only [U] at hc
        split at hc
        · obtain ⟨t, _ht, rfl⟩ := List.mem_map.mp hc
          exact ⟨t.1, rfl⟩
        · simp only [List.mem_singleton] at hc
          subst c
          exact ⟨[], rfl⟩
      have hLhead : ∀ q, ∀ c ∈ L q, ∃ tail, c = q.1 :: tail := by
        intro q c hc
        obtain ⟨t, _ht, rfl⟩ := List.mem_map.mp hc
        exact ⟨t.1, rfl⟩
      rw [hupperEq, hlowerEq]
      constructor
      · apply List.nodup_flatMap.mpr
        refine ⟨hUnodup, hchildren.imp ?_⟩
        intro q q' hqq'
        change List.Disjoint (U q) (U q')
        rw [List.disjoint_left]
        intro c hc hc'
        obtain ⟨ct, hcEq⟩ := hUhead q c hc
        obtain ⟨dt, hcEq'⟩ := hUhead q' c hc'
        exact hqq' (List.cons.inj (hcEq.symm.trans hcEq')).1
      · apply List.nodup_flatMap.mpr
        refine ⟨hLnodup, hchildren.imp ?_⟩
        intro q q' hqq'
        change List.Disjoint (L q) (L q')
        rw [List.disjoint_left]
        intro c hc hc'
        obtain ⟨ct, hcEq⟩ := hLhead q c hc
        obtain ⟨dt, hcEq'⟩ := hLhead q' c hc'
        exact hqq' (List.cons.inj (hcEq.symm.trans hcEq')).1

/-- Selected chains at one exact depth, forgetting their terminal suffixes. -/
def failureChainsAtDepth {α : Type*}
    (terms : List (List α × List α)) (r : ℕ) : List (List α) :=
  (terms.map Prod.fst).filter fun c => c.length = r

theorem upper_failureChainsAtDepth_nodup {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    (hrem : remaining.Nodup) (r : ℕ) :
    (failureChainsAtDepth
      (upperFailureTerms stop fuel selected remaining) r).Nodup :=
  (failureTerms_chains_nodup stop fuel selected remaining hrem).1.filter _

theorem lower_failureChainsAtDepth_nodup {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    (hrem : remaining.Nodup) (r : ℕ) :
    (failureChainsAtDepth
      (lowerFailureTerms stop fuel selected remaining) r).Nodup :=
  (failureTerms_chains_nodup stop fuel selected remaining hrem).2.filter _

theorem upper_failureChainsAtDepth_subset_sublistsLen {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    (r : ℕ) :
    ∀ c ∈ failureChainsAtDepth
        (upperFailureTerms stop fuel selected remaining) r,
      c ∈ remaining.sublistsLen r := by
  intro c hc
  simp only [failureChainsAtDepth, List.mem_filter, List.mem_map] at hc
  obtain ⟨⟨t, ht, rfl⟩, hlen⟩ := hc
  simp only [decide_eq_true_eq] at hlen
  exact List.mem_sublistsLen.mpr
    ⟨upperFailureTerms_chain_sublist stop fuel selected remaining ht, hlen⟩

theorem lower_failureChainsAtDepth_subset_sublistsLen {α : Type*}
    (stop : List α → Bool) (fuel : ℕ) (selected remaining : List α)
    (r : ℕ) :
    ∀ c ∈ failureChainsAtDepth
        (lowerFailureTerms stop fuel selected remaining) r,
      c ∈ remaining.sublistsLen r := by
  intro c hc
  simp only [failureChainsAtDepth, List.mem_filter, List.mem_map] at hc
  obtain ⟨⟨t, ht, rfl⟩, hlen⟩ := hc
  simp only [decide_eq_true_eq] at hlen
  exact List.mem_sublistsLen.mpr
    ⟨lowerFailureTerms_chain_sublist stop fuel selected remaining ht, hlen⟩

/-- The elementary-symmetric mass of the length-`r` ordered sublists of `l`. -/
def sublistsLenMass {α : Type*} (x : α → ℝ) (l : List α) (r : ℕ) : ℝ :=
  ((l.sublistsLen r).map fun s => (s.map x).prod).sum

@[simp]
theorem sublistsLenMass_zero {α : Type*} (x : α → ℝ) (l : List α) :
    sublistsLenMass x l 0 = 1 := by
  simp [sublistsLenMass]

theorem sublistsLenMass_succ_cons {α : Type*} (x : α → ℝ)
    (a : α) (l : List α) (r : ℕ) :
    sublistsLenMass x (a :: l) (r + 1) =
      sublistsLenMass x l (r + 1) + x a * sublistsLenMass x l r := by
  simp only [sublistsLenMass, List.sublistsLen_succ_cons, List.map_append,
    List.sum_append, List.map_map]
  congr 1
  change
    (List.map (fun s => x a * (s.map x).prod) (l.sublistsLen r)).sum = _
  exact List.sum_map_mul_left (l.sublistsLen r)
    (fun s => (s.map x).prod) (x a)

/-- The standard factorial elementary-symmetric estimate, in the list form
used by the failure-chain recursion. -/
theorem factorial_mul_sublistsLenMass_le_sum_pow {α : Type*}
    (x : α → ℝ) (hx : ∀ a, 0 ≤ x a) :
    ∀ (l : List α) (r : ℕ),
      (r.factorial : ℝ) * sublistsLenMass x l r ≤
        (l.map x).sum ^ r := by
  intro l
  induction l with
  | nil =>
      intro r
      cases r <;> simp [sublistsLenMass]
  | cons a l ih =>
      intro r
      cases r with
      | zero => simp
      | succ r =>
          have hsum0 : 0 ≤ (l.map x).sum :=
            List.sum_nonneg fun y hy => by
              obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hy
              exact hx b
          have hmain := ih (r + 1)
          have hprev := ih r
          have hfac : (((r + 1).factorial : ℕ) : ℝ) =
              ((r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) := by
            rw [Nat.factorial_succ]
            norm_num
          rw [sublistsLenMass_succ_cons]
          calc
            ((r + 1).factorial : ℝ) *
                (sublistsLenMass x l (r + 1) +
                  x a * sublistsLenMass x l r) =
                ((r + 1).factorial : ℝ) * sublistsLenMass x l (r + 1) +
                  ((r + 1 : ℕ) : ℝ) * x a *
                    ((r.factorial : ℝ) * sublistsLenMass x l r) := by
              rw [hfac]
              ring
            _ ≤ (l.map x).sum ^ (r + 1) +
                ((r + 1 : ℕ) : ℝ) * x a * (l.map x).sum ^ r := by
              exact add_le_add hmain (mul_le_mul_of_nonneg_left hprev
                (mul_nonneg (Nat.cast_nonneg _) (hx a)))
            _ ≤ ((l.map x).sum + x a) ^ (r + 1) := by
              simpa [Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm,
                mul_left_comm] using
                (pow_add_mul_le_add_pow (R := ℝ) hsum0
                  (add_nonneg (mul_nonneg (by norm_num) hsum0) (hx a))
                  (r + 1))
            _ = ((a :: l).map x).sum ^ (r + 1) := by
              simp [add_comm]

/-- Chain-product mass at one exact depth, before inserting the terminal
Euler-product factor. -/
def failureChainMassAtDepth {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α)) (r : ℕ) : ℝ :=
  ((failureChainsAtDepth terms r).map fun c => (c.map x).prod).sum

/-- The list-filter presentation of the already-exported `depthFailureMass`.
Unlike its `zipIdx` definition, this form is convenient for termwise bounds. -/
def failureTermMassAtDepth {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α)) (r : ℕ) : ℝ :=
  ((terms.filter fun t => t.1.length = r).map fun t =>
    (t.1.map x).prod * buchstabProduct x t.2).sum

theorem depthFailureMass_eq_failureTermMassAtDepth {α : Type*}
    (x : α → ℝ) (terms : List (List α × List α)) (r : ℕ) :
    depthFailureMass x terms r = failureTermMassAtDepth x terms r := by
  classical
  unfold depthFailureMass failureTermMassAtDepth
  let F : (List α × List α) → ℝ := fun t =>
    (t.1.map x).prod * buchstabProduct x t.2
  have hnodup : terms.zipIdx.Nodup :=
    List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd terms)
  have hfilter :
      (terms.zipIdx.toFinset.filter fun z => z.1.1.length = r) =
        (terms.zipIdx.filter fun z => z.1.1.length = r).toFinset := by
    ext z
    simp
  rw [hfilter, List.sum_toFinset (fun z => F z.1) (hnodup.filter _)]
  have hzipAux : ∀ (l : List (List α × List α)) (n : ℕ),
      ((l.zipIdx n).filter fun z => z.1.1.length = r).map
          (fun z => F z.1) =
        (l.filter fun t => t.1.length = r).map F := by
    intro l
    induction l with
    | nil => intro n; simp
    | cons a l ih =>
        intro n
        simp only [List.zipIdx, List.filter_cons]
        split <;> simp [ih]
  exact congrArg List.sum (hzipAux terms 0)

theorem depthFailureMass_le_mul_failureChainMassAtDepth {α : Type*}
    (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (terms : List (List α × List α)) (r : ℕ) (B : ℝ)
    (hsuffix : ∀ t ∈ terms, t.1.length = r →
      buchstabProduct x t.2 ≤ B) :
    depthFailureMass x terms r ≤ B * failureChainMassAtDepth x terms r := by
  rw [depthFailureMass_eq_failureTermMassAtDepth]
  unfold failureTermMassAtDepth failureChainMassAtDepth failureChainsAtDepth
  rw [List.filter_map]
  calc
    ((terms.filter fun t => t.1.length = r).map fun t =>
        (t.1.map x).prod * buchstabProduct x t.2).sum ≤
        ((terms.filter fun t => t.1.length = r).map fun t =>
          B * (t.1.map x).prod).sum := by
      apply List.sum_le_sum
      intro t ht
      simp only [List.mem_filter] at ht
      have hlen : t.1.length = r := by
        simpa only [decide_eq_true_eq] using ht.2
      rw [mul_comm (t.1.map x).prod]
      exact mul_le_mul_of_nonneg_right (hsuffix t ht.1 hlen)
        (List.prod_nonneg fun y hy => by
          obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
          exact hx a)
    _ = B *
        (((terms.filter fun t => t.1.length = r).map fun t =>
          (t.1.map x).prod).sum) := by
      exact List.sum_map_mul_left _ _ B
    _ = B *
        (((terms.filter ((fun c => c.length = r) ∘ Prod.fst)).map Prod.fst).map
          (fun c => (c.map x).prod)).sum := by
      simp [List.map_map, Function.comp_def]

private theorem sum_map_le_sum_map_of_nodup_subset {α : Type*}
    (f : α → ℝ) (l₁ l₂ : List α)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hsub : ∀ a ∈ l₁, a ∈ l₂) (hf : ∀ a ∈ l₂, 0 ≤ f a) :
    (l₁.map f).sum ≤ (l₂.map f).sum := by
  classical
  rw [← List.sum_toFinset f h₁, ← List.sum_toFinset f h₂]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact List.mem_toFinset.mpr (hsub a (List.mem_toFinset.mp ha))
  · intro a ha _ha'
    exact hf a (List.mem_toFinset.mp ha)

theorem upper_failureChainMassAtDepth_le_sublistsLenMass {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) :
    failureChainMassAtDepth x
        (upperFailureTerms stop fuel selected remaining) r ≤
      sublistsLenMass x remaining r := by
  apply sum_map_le_sum_map_of_nodup_subset
  · exact upper_failureChainsAtDepth_nodup stop fuel selected remaining hrem r
  · exact List.nodup_sublistsLen r hrem
  · exact upper_failureChainsAtDepth_subset_sublistsLen
      stop fuel selected remaining r
  · intro c _hc
    exact List.prod_nonneg fun y hy => by
      obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
      exact hx a

theorem lower_failureChainMassAtDepth_le_sublistsLenMass {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) :
    failureChainMassAtDepth x
        (lowerFailureTerms stop fuel selected remaining) r ≤
      sublistsLenMass x remaining r := by
  apply sum_map_le_sum_map_of_nodup_subset
  · exact lower_failureChainsAtDepth_nodup stop fuel selected remaining hrem r
  · exact List.nodup_sublistsLen r hrem
  · exact lower_failureChainsAtDepth_subset_sublistsLen
      stop fuel selected remaining r
  · intro c _hc
    exact List.prod_nonneg fun y hy => by
      obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
      exact hx a

theorem upper_failureChainMassAtDepth_le_sum_pow_div_factorial {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) :
    failureChainMassAtDepth x
        (upperFailureTerms stop fuel selected remaining) r ≤
      (remaining.map x).sum ^ r / (r.factorial : ℝ) := by
  refine (upper_failureChainMassAtDepth_le_sublistsLenMass
    stop x hx fuel selected remaining hrem r).trans ?_
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
  simpa [mul_comm] using
    factorial_mul_sublistsLenMass_le_sum_pow x hx remaining r

theorem lower_failureChainMassAtDepth_le_sum_pow_div_factorial {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) :
    failureChainMassAtDepth x
        (lowerFailureTerms stop fuel selected remaining) r ≤
      (remaining.map x).sum ^ r / (r.factorial : ℝ) := by
  refine (lower_failureChainMassAtDepth_le_sublistsLenMass
    stop x hx fuel selected remaining hrem r).trans ?_
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
  simpa [mul_comm] using
    factorial_mul_sublistsLenMass_le_sum_pow x hx remaining r

/-- A ready-to-use weighted depth bound: it separates the uniform bound for
the terminal Euler-product suffix from the factorial chain estimate. -/
theorem upper_depthFailureMass_le_mul_sum_pow_div_factorial {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsuffix : ∀ t ∈ upperFailureTerms stop fuel selected remaining,
      t.1.length = r → buchstabProduct x t.2 ≤ B) :
    depthFailureMass x (upperFailureTerms stop fuel selected remaining) r ≤
      B * ((remaining.map x).sum ^ r / (r.factorial : ℝ)) := by
  calc
    depthFailureMass x (upperFailureTerms stop fuel selected remaining) r ≤
        B * failureChainMassAtDepth x
          (upperFailureTerms stop fuel selected remaining) r :=
      depthFailureMass_le_mul_failureChainMassAtDepth x hx _ r B hsuffix
    _ ≤ B * ((remaining.map x).sum ^ r / (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (upper_failureChainMassAtDepth_le_sum_pow_div_factorial
          stop x hx fuel selected remaining hrem r) hB

theorem lower_depthFailureMass_le_mul_sum_pow_div_factorial {α : Type*}
    (stop : List α → Bool) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a)
    (fuel : ℕ) (selected remaining : List α) (hrem : remaining.Nodup)
    (r : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsuffix : ∀ t ∈ lowerFailureTerms stop fuel selected remaining,
      t.1.length = r → buchstabProduct x t.2 ≤ B) :
    depthFailureMass x (lowerFailureTerms stop fuel selected remaining) r ≤
      B * ((remaining.map x).sum ^ r / (r.factorial : ℝ)) := by
  calc
    depthFailureMass x (lowerFailureTerms stop fuel selected remaining) r ≤
        B * failureChainMassAtDepth x
          (lowerFailureTerms stop fuel selected remaining) r :=
      depthFailureMass_le_mul_failureChainMassAtDepth x hx _ r B hsuffix
    _ ≤ B * ((remaining.map x).sum ^ r / (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (lower_failureChainMassAtDepth_le_sum_pow_div_factorial
          stop x hx fuel selected remaining hrem r) hB

end Erdos851.BetaSieveFundamental
