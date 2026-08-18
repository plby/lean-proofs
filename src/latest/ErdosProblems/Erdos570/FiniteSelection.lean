/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.Hall.Basic

/-!
# A uniform finite choice lemma

If an `n`-indexed family of finite sets has at least `n` elements in every
member, then it has distinct representatives.  This deliberately strong
hypothesis makes Hall's condition immediate and is exactly what is needed in
the alternating-path construction for the sparse case of Erdős 570.
-/

namespace Erdos570

/-- Choose distinct representatives from `n` finite sets, each of cardinality
at least `n`. -/
theorem exists_injective_mem_of_card_ge
    {α : Type*} [DecidableEq α] {n : ℕ} (A : Fin n → Finset α)
    (hcard : ∀ i, n ≤ (A i).card) :
    ∃ f : Fin n → α, Function.Injective f ∧ ∀ i, f i ∈ A i := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp
  intro s
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    calc
      s.card ≤ n := by simpa using s.card_le_univ
      _ ≤ (A i).card := hcard i
      _ ≤ (s.biUnion A).card := Finset.card_le_card (by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- From a finite set with at least `r+2` elements, enumerate `r+2`
distinct elements with two prescribed distinct members at the two ends. -/
theorem exists_injective_sequence_with_endpoints
    {α : Type*} [DecidableEq α] {U : Finset α} {r : ℕ} {a b : α}
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (hcard : r + 2 ≤ U.card) :
    ∃ w : Fin (r + 2) → α, Function.Injective w ∧
      (∀ i, w i ∈ U) ∧ w 0 = a ∧ w (Fin.last (r + 1)) = b := by
  classical
  let R := (U.erase a).erase b
  have hbR : b ∈ U.erase a := by simp [hb, hab.symm]
  have hRcard : R.card = U.card - 2 := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hbR, Finset.card_erase_of_mem ha]
    omega
  have hrR : r ≤ R.card := by omega
  obtain ⟨M, hMR, hMcard⟩ := Finset.exists_subset_card_eq hrR
  let e : Fin r ≃ M := Fintype.equivOfCardEq (by simp [hMcard])
  let mid : Fin r → α := fun i ↦ (e i).1
  have hmidinj : Function.Injective mid := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  have hmidU (i : Fin r) : mid i ∈ U := by
    exact Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase (hMR (e i).2))
  have hmidneA (i : Fin r) : mid i ≠ a := by
    have hiR := hMR (e i).2
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hiR)
  have hmidneB (i : Fin r) : mid i ≠ b := by
    exact Finset.ne_of_mem_erase (hMR (e i).2)
  let tail : Fin (r + 1) → α := Fin.snoc mid b
  have htailinj : Function.Injective tail := by
    apply Fin.snoc_injective_of_injective hmidinj
    rintro ⟨i, hi⟩
    exact hmidneB i hi
  have haTail : a ∉ Set.range tail := by
    change a ∉ Set.range (Fin.snoc mid b)
    rw [Fin.range_snoc]
    simp only [Set.mem_insert_iff, Set.mem_range, not_or]
    constructor
    · exact hab
    · rintro ⟨i, hi⟩
      exact hmidneA i hi
  let w : Fin (r + 2) → α := Fin.cons a tail
  refine ⟨w, Fin.cons_injective_of_injective haTail htailinj, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa [w] using ha
    | succ j =>
        induction j using Fin.lastCases with
        | last => simpa [w, tail] using hb
        | cast j => simpa [w, tail, mid] using hmidU j
  · simp [w]
  · simp [w, tail]

/-- Choose an injective sequence with prescribed distinct endpoints whose
`r` internal entries all lie in `K`.  The endpoints need not belong to `K`;
the two extra elements in the cardinal hypothesis absorb their possible
presence there. -/
theorem exists_injective_sequence_with_middle
    {α : Type*} [DecidableEq α] {K : Finset α} {r : ℕ} {a b : α}
    (hab : a ≠ b) (hcard : r + 2 ≤ K.card) :
    ∃ w : Fin (r + 2) → α, Function.Injective w ∧
      w 0 = a ∧ w (Fin.last (r + 1)) = b ∧
      ∀ i : Fin r, w i.succ.castSucc ∈ K := by
  classical
  let R := (K.erase a).erase b
  have hRcard : r ≤ R.card := by
    have hfirst := Finset.pred_card_le_card_erase (s := K) (a := a)
    have hsecond := Finset.pred_card_le_card_erase
      (s := K.erase a) (a := b)
    dsimp only [R]
    omega
  obtain ⟨M, hMR, hMcard⟩ := Finset.exists_subset_card_eq hRcard
  let e : Fin r ≃ M := Fintype.equivOfCardEq (by simp [hMcard])
  let mid : Fin r → α := fun i ↦ (e i).1
  have hmidinj : Function.Injective mid := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hmidK (i : Fin r) : mid i ∈ K := by
    exact Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase (hMR (e i).2))
  have hmidneA (i : Fin r) : mid i ≠ a := by
    have hiR := hMR (e i).2
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hiR)
  have hmidneB (i : Fin r) : mid i ≠ b := by
    exact Finset.ne_of_mem_erase (hMR (e i).2)
  let tail : Fin (r + 1) → α := Fin.snoc mid b
  have htailinj : Function.Injective tail := by
    apply Fin.snoc_injective_of_injective hmidinj
    rintro ⟨i, hi⟩
    exact hmidneB i hi
  have haTail : a ∉ Set.range tail := by
    change a ∉ Set.range (Fin.snoc mid b)
    rw [Fin.range_snoc]
    simp only [Set.mem_insert_iff, Set.mem_range, not_or]
    constructor
    · exact hab
    · rintro ⟨i, hi⟩
      exact hmidneA i hi
  let w : Fin (r + 2) → α := Fin.cons a tail
  refine ⟨w, Fin.cons_injective_of_injective haTail htailinj, ?_, ?_, ?_⟩
  · simp [w]
  · simp [w, tail]
  · intro i
    simpa [w, tail, mid] using hmidK i

end Erdos570
