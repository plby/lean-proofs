import Mathlib
import ErdosProblems.Erdos336.FiniteRemovalNormalization
import ErdosProblems.Erdos336.TwoGeneratorLShape

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sharp weak-to-strong bound for two-element finite bases
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A list over two elements has well-defined multiplicities summing to its
length and its sum is the corresponding linear combination. -/
lemma exists_twoPoint_counts (a b : G) (xs : List G)
    (hxs : ∀ x ∈ xs, x = a ∨ x = b) :
    ∃ i j : ℕ, i + j = xs.length ∧ xs.sum = i • a + j • b := by
  induction xs with
  | nil => exact ⟨0, 0, by simp, by simp⟩
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have htail : ∀ z ∈ xs, z = a ∨ z = b := by
        intro z hz
        exact hxs z (by simp [hz])
      obtain ⟨i, j, hij, hsum⟩ := ih htail
      rcases hx with rfl | hxb
      · refine ⟨i + 1, j, by simp [← hij, add_assoc, add_comm, add_left_comm], ?_⟩
        simp only [List.sum_cons, hsum, add_nsmul, one_nsmul]
        ac_rfl
      · subst x
        refine ⟨i, j + 1, by simp [← hij, add_assoc], ?_⟩
        simp only [List.sum_cons, hsum, add_nsmul, one_nsmul]
        ac_rfl

/-- A weak cover by `{a,b}` is exactly a directed two-generator diameter
bound. -/
theorem twoGen_cover_of_twoPoint_weak
    [Fintype G] (a b : G) {h : ℕ}
    (hweak : ∀ y : G, GroupRepAtMost ({a, b} : Set G) h y) :
    ∀ y : G, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ h ∧ twoGenLabel a b p = y := by
  intro y
  obtain ⟨j, hj, xs, hlen, hxmem, hxsum⟩ := hweak y
  have hpair : ∀ x ∈ xs, x = a ∨ x = b := by
    intro x hx
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem x hx
  obtain ⟨i, k, hik, hsum⟩ := exists_twoPoint_counts a b xs hpair
  refine ⟨(i, k), ?_, ?_⟩
  · omega
  · simpa [twoGenLabel] using hsum.symm.trans hxsum

/-- Exact full coverage by `{a,b}` implies that `a-b` generates every element
by a nonnegative multiple. -/
theorem exists_nsmul_sub_of_twoPoint_exact
    (a b : G) {q : ℕ}
    (hq : ∀ y : G, GroupRepExactly ({a, b} : Set G) q y) :
    ∀ y : G, ∃ i : ℕ, i • (a - b) = y := by
  have hset : ShiftToZero ({a, b} : Set G) b = ({a - b, 0} : Set G) := by
    ext z
    simp only [ShiftToZero, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Or.inl ((eq_sub_iff_add_eq).2 hz)
      · right
        apply add_right_cancel (b := b)
        simpa using hz
    · intro hz
      rcases hz with hz | rfl
      · exact Or.inl ((eq_sub_iff_add_eq).1 hz)
      · exact Or.inr (by simp)
  have hshift : ∀ y : G, GroupRepExactly ({a - b, 0} : Set G) q y := by
    rw [← hset]
    exact (all_exact_shift_iff q).mp hq
  intro y
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hshift y
  have hpair : ∀ x ∈ xs, x = a - b ∨ x = 0 := by
    intro x hx
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem x hx
  obtain ⟨i, k, -, hsum⟩ := exists_twoPoint_counts (a - b) 0 xs hpair
  refine ⟨i, ?_⟩
  simpa using hsum.symm.trans hxsum

/-- The explicit universal two-point weak-to-strong cost. -/
def twoPointWeakStrongCost (h : ℕ) : ℕ := (h + 2) ^ 2 / 3

/-- For a two-element subset of any finite abelian group, weak order `h` plus
primitivity implies full exact coverage at
`floor((h+2)^2/3)`. -/
theorem twoPoint_weakStrong
    [Fintype G] (a b : G) {h : ℕ}
    (hweak : ∀ y : G, GroupRepAtMost ({a, b} : Set G) h y)
    (hexact : ∃ q : ℕ, ∀ y : G, GroupRepExactly ({a, b} : Set G) q y) :
    ∀ y : G, GroupRepExactly ({a, b} : Set G)
      (twoPointWeakStrongCost h) y := by
  let M := twoPointWeakStrongCost h
  have hcover := twoGen_cover_of_twoPoint_weak a b hweak
  have hcardThird := twoGenerator_card_le_third a b hcover
  have hcard : Fintype.card G ≤ M := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
    simpa [M, twoPointWeakStrongCost, mul_comm] using hcardThird
  obtain ⟨q, hq⟩ := hexact
  have hgen := exists_nsmul_sub_of_twoPoint_exact a b hq
  have hshift : ∀ y : G,
      GroupRepExactly ({a - b, 0} : Set G) M y := by
    intro y
    obtain ⟨i, hi⟩ := hgen y
    let r := i % addOrderOf (a - b)
    have hordpos : 0 < addOrderOf (a - b) := addOrderOf_pos _
    have hrord : r < addOrderOf (a - b) := Nat.mod_lt _ hordpos
    have hordcard : addOrderOf (a - b) ≤ Fintype.card G := by
      simpa [Nat.card_eq_fintype_card] using (addOrderOf_le_card :
        addOrderOf (a - b) ≤ Nat.card G)
    have hrM : r ≤ M := le_trans (Nat.le_of_lt hrord) (le_trans hordcard hcard)
    have hr : r • (a - b) = y := by
      rw [← hi]
      exact (nsmul_eq_nsmul_iff_modEq).2 (Nat.mod_modEq i _)
    let xs : List G := List.replicate r (a - b) ++ List.replicate (M - r) 0
    refine ⟨xs, ?_, ?_, ?_⟩
    · simp [xs, Nat.add_sub_of_le hrM]
    · intro z hz
      simp only [xs, List.mem_append, List.mem_replicate] at hz
      rcases hz with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp [xs, hr]
  have hset : ShiftToZero ({a, b} : Set G) b = ({a - b, 0} : Set G) := by
    ext z
    simp only [ShiftToZero, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (hz | hz)
      · exact Or.inl ((eq_sub_iff_add_eq).2 hz)
      · right
        apply add_right_cancel (b := b)
        simpa using hz
    · rintro (hz | rfl)
      · exact Or.inl ((eq_sub_iff_add_eq).1 hz)
      · exact Or.inr (by simp)
  apply (all_exact_shift_iff (A := ({a, b} : Set G)) (x := b) M).mpr
  simpa only [hset] using hshift

end Erdos336
