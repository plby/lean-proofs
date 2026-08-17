import ErdosProblems.Erdos896.Ford.LowerPrimeBlocks

/-!
# Reciprocal mass of Ford occupancy profiles

This file proves the squarefree collision estimate behind Ford's profile
lower bound.  A profile chooses `b i` distinct primes from each consecutive
greedy block.  Ordered tuples give the factorial model; an explicit
insert/erase double count removes repeated primes, while the summable greedy
block deficits preserve the base `log 2` uniformly in the profile length.
-/

namespace Erdos896.Ford

open Filter
open scoped BigOperators Topology


noncomputable def eMass {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard n, ∏ x ∈ t, w x

theorem eMass_succ_identity {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (n : ℕ) :
    (n + 1 : ℝ) * eMass s w (n + 1) =
      ∑ t ∈ s.powersetCard n,
        (∏ x ∈ t, w x) * (∑ x ∈ s \ t, w x) := by
  classical
  let source := ((s.powersetCard n).product s).filter fun z => z.2 ∉ z.1
  let target := ((s.powersetCard (n + 1)).product s).filter fun z => z.2 ∈ z.1
  have hbij :
      (∑ z ∈ source, (∏ x ∈ z.1, w x) * w z.2) =
        ∑ z ∈ target, ∏ x ∈ z.1, w x := by
    refine Finset.sum_bij'
      (fun z _ => (insert z.2 z.1, z.2))
      (fun z _ => (z.1.erase z.2, z.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      have hprod := Finset.mem_product.mp htx.1
      obtain ⟨ht, hx⟩ := hprod
      have hxt := htx.2
      have ht' := Finset.mem_powersetCard.mp ht
      simp only [target, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset hx ht'.1, ?_⟩, hx⟩, Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hxt, ht'.2]
    · rintro ⟨u, x⟩ hux
      simp only [target, Finset.mem_filter] at hux
      have hprod := Finset.mem_product.mp hux.1
      obtain ⟨hu, hx⟩ := hprod
      have hxu := hux.2
      have hu' := Finset.mem_powersetCard.mp hu
      simp only [source, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, hx⟩,
        Finset.notMem_erase _ _⟩
      · exact fun y hy => hu'.1 (Finset.mem_of_mem_erase hy)
      · rw [Finset.card_erase_of_mem hxu, hu'.2]
        omega
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      have hxt := htx.2
      apply Prod.ext
      · simp [Finset.erase_insert hxt]
      · rfl
    · rintro ⟨u, x⟩ hux
      simp only [target, Finset.mem_filter] at hux
      have hxu := hux.2
      apply Prod.ext
      · simp [Finset.insert_erase hxu]
      · rfl
    · rintro ⟨t, x⟩ htx
      simp only [source, Finset.mem_filter] at htx
      have hxt := htx.2
      change (∏ y ∈ t, w y) * w x = ∏ y ∈ insert x t, w y
      calc
        (∏ y ∈ t, w y) * w x = w x * ∏ y ∈ t, w y := mul_comm _ _
        _ = ∏ y ∈ insert x t, w y := (Finset.prod_insert hxt).symm
  calc
    (n + 1 : ℝ) * eMass s w (n + 1) =
        ∑ u ∈ s.powersetCard (n + 1), ∑ _x ∈ u, ∏ x ∈ u, w x := by
          simp only [eMass, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          have hcard := (Finset.mem_powersetCard.mp hu).2
          rw [hcard]
          push_cast
          ring
    _ = ∑ z ∈ target, ∏ x ∈ z.1, w x := by
      rw [Finset.sum_finset_product target (s.powersetCard (n + 1))
        (fun u => u) (by
          intro z
          simp only [target, Finset.mem_filter]
          constructor
          · rintro ⟨hprod, hmem⟩
            exact ⟨(Finset.mem_product.mp hprod).1, hmem⟩
          · rintro ⟨hu, hmem⟩
            have husub := (Finset.mem_powersetCard.mp hu).1
            exact ⟨Finset.mem_product.mpr ⟨hu, husub hmem⟩, hmem⟩)]
    _ = ∑ z ∈ source, (∏ x ∈ z.1, w x) * w z.2 := hbij.symm
    _ = ∑ t ∈ s.powersetCard n,
        (∏ x ∈ t, w x) * (∑ x ∈ s \ t, w x) := by
      rw [Finset.sum_finset_product source (s.powersetCard n)
        (fun t => s \ t) (by
          intro z
          simp only [source, Finset.mem_filter]
          constructor
          · rintro ⟨hprod, hnot⟩
            exact ⟨(Finset.mem_product.mp hprod).1,
              Finset.mem_sdiff.mpr ⟨(Finset.mem_product.mp hprod).2, hnot⟩⟩
          · rintro ⟨ht, hx⟩
            exact ⟨Finset.mem_product.mpr ⟨ht, (Finset.mem_sdiff.mp hx).1⟩,
              (Finset.mem_sdiff.mp hx).2⟩)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]

theorem eMass_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) (n : ℕ) :
    0 ≤ eMass s w n := by
  unfold eMass
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro x hx
  exact hw x ((Finset.mem_powersetCard.mp ht).1 hx)

theorem eMass_succ_lower {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (η : ℝ) (n : ℕ)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hwη : ∀ x ∈ s, w x ≤ η) :
    eMass s w n * ((∑ x ∈ s, w x) - n * η) ≤
      (n + 1 : ℝ) * eMass s w (n + 1) := by
  rw [eMass_succ_identity]
  calc
    eMass s w n * ((∑ x ∈ s, w x) - n * η) =
        ∑ t ∈ s.powersetCard n,
          (∏ x ∈ t, w x) * ((∑ x ∈ s, w x) - n * η) := by
      rw [eMass, Finset.sum_mul]
    _ ≤ ∑ t ∈ s.powersetCard n,
        (∏ x ∈ t, w x) * (∑ x ∈ s \ t, w x) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_powersetCard.mp ht
      have hsumt := Finset.sum_le_card_nsmul t w η fun x hx => hwη x (ht'.1 hx)
      have hcard : t.card = n := ht'.2
      have hsumt' : (∑ x ∈ t, w x) ≤ n * η := by
        simpa [hcard, nsmul_eq_mul] using hsumt
      have hsplit := Finset.sum_sdiff ht'.1 (f := w)
      have hcomp : (∑ x ∈ s, w x) - n * η ≤ ∑ x ∈ s \ t, w x := by
        linarith
      exact mul_le_mul_of_nonneg_left hcomp (by
        apply Finset.prod_nonneg
        intro x hx
        exact hw0 x (ht'.1 hx))

theorem eMass_succ_upper {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (n : ℕ)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) :
    (n + 1 : ℝ) * eMass s w (n + 1) ≤
      eMass s w n * ∑ x ∈ s, w x := by
  rw [eMass_succ_identity, eMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  have ht' := Finset.mem_powersetCard.mp ht
  have hcomp : (∑ x ∈ s \ t, w x) ≤ ∑ x ∈ s, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.sdiff_subset
    · intro x hx hnot
      exact hw0 x hx
  exact mul_le_mul_of_nonneg_left hcomp (by
    apply Finset.prod_nonneg
    intro x hx
    exact hw0 x (ht'.1 hx))

theorem factorial_mul_eMass_le_pow {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (n : ℕ)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) :
    (n.factorial : ℝ) * eMass s w n ≤ (∑ x ∈ s, w x) ^ n := by
  induction n with
  | zero => simp [eMass]
  | succ n ih =>
      have hrec := eMass_succ_upper s w n hw0
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      calc
        ((↑n + 1) * ↑n.factorial) * eMass s w (n + 1) =
            (n.factorial : ℝ) * ((↑n + 1) * eMass s w (n + 1)) := by ring
        _ ≤ (n.factorial : ℝ) *
            (eMass s w n * ∑ x ∈ s, w x) :=
          mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
        _ = ((n.factorial : ℝ) * eMass s w n) * ∑ x ∈ s, w x := by ring
        _ ≤ (∑ x ∈ s, w x) ^ n * ∑ x ∈ s, w x :=
          mul_le_mul_of_nonneg_right ih (Finset.sum_nonneg fun x hx => hw0 x hx)

theorem factorial_mul_eMass_ge_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (η : ℝ) (n : ℕ)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hwη : ∀ x ∈ s, w x ≤ η)
    (hfac : ∀ r < n, (r : ℝ) * η ≤ ∑ x ∈ s, w x) :
    (∏ r ∈ Finset.range n, ((∑ x ∈ s, w x) - r * η)) ≤
      (n.factorial : ℝ) * eMass s w n := by
  induction n with
  | zero => simp [eMass]
  | succ n ih =>
      rw [Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      have hrec := eMass_succ_lower s w η n hw0 hwη
      have hih := ih (fun r hr => hfac r (by omega))
      have hlast : 0 ≤ (∑ x ∈ s, w x) - n * η := sub_nonneg.mpr (hfac n (by omega))
      calc
        (∏ r ∈ Finset.range n, ((∑ x ∈ s, w x) - r * η)) *
            ((∑ x ∈ s, w x) - ↑n * η) ≤
            ((n.factorial : ℝ) * eMass s w n) *
              ((∑ x ∈ s, w x) - ↑n * η) :=
          mul_le_mul_of_nonneg_right hih hlast
        _ ≤ (n.factorial : ℝ) * ((↑n + 1) * eMass s w (n + 1)) := by
          calc
            (n.factorial : ℝ) * eMass s w n *
                ((∑ x ∈ s, w x) - ↑n * η) =
                (n.factorial : ℝ) *
                  (eMass s w n * ((∑ x ∈ s, w x) - ↑n * η)) := by ring
            _ ≤ (n.factorial : ℝ) * ((↑n + 1) * eMass s w (n + 1)) :=
              mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
        _ = ((↑n + 1) * ↑n.factorial) * eMass s w (n + 1) := by
          ring

private theorem one_sub_sum_le_prod_one_sub
    (d : ℕ → ℝ) (n : ℕ) (hd0 : ∀ i < n, 0 ≤ d i)
    (hd1 : ∀ i < n, d i ≤ 1) :
    1 - ∑ i ∈ Finset.range n, d i ≤
      ∏ i ∈ Finset.range n, (1 - d i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      have hsum : 0 ≤ ∑ i ∈ Finset.range n, d i :=
        Finset.sum_nonneg fun i hi => hd0 i (by
          have := Finset.mem_range.mp hi
          omega)
      have hih := ih (fun i hi => hd0 i (by omega)) (fun i hi => hd1 i (by omega))
      calc
        1 - ((∑ i ∈ Finset.range n, d i) + d n) ≤
            (1 - ∑ i ∈ Finset.range n, d i) * (1 - d n) := by
          nlinarith [mul_nonneg hsum (hd0 n (by omega))]
        _ ≤ (∏ i ∈ Finset.range n, (1 - d i)) * (1 - d n) :=
          mul_le_mul_of_nonneg_right hih (sub_nonneg.mpr (hd1 n (by omega)))

theorem eMass_collision_lower {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (η : ℝ) (n : ℕ)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hwη : ∀ x ∈ s, w x ≤ η)
    (hmass : 0 < ∑ x ∈ s, w x)
    (hloss : (n : ℝ) ^ 2 * η / (∑ x ∈ s, w x) ≤ 1) :
    (1 - (n : ℝ) ^ 2 * η / (∑ x ∈ s, w x)) *
        ((∑ x ∈ s, w x) ^ n / n.factorial) ≤ eMass s w n := by
  let m := ∑ x ∈ s, w x
  let d : ℕ → ℝ := fun r => (r : ℝ) * η / m
  have hη : 0 ≤ η := by
    by_cases hs : s.Nonempty
    · obtain ⟨x, hx⟩ := hs
      exact (hw0 x hx).trans (hwη x hx)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs] at hmass
  have hd0 : ∀ r, 0 ≤ d r := fun r =>
    div_nonneg (mul_nonneg (by positivity) hη) hmass.le
  have hdn : ∀ r < n, d r ≤ 1 := by
    intro r hr
    have hrn : (r : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hr)
    have hle : (r : ℝ) * η ≤ (n : ℝ) ^ 2 * η := by
      have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases n with _ | n
        · simp
        · norm_num
          nlinarith [show (0 : ℝ) ≤ n by positivity]
      exact mul_le_mul_of_nonneg_right (hrn.trans hn) hη
    have hbig : (n : ℝ) ^ 2 * η ≤ m :=
      (div_le_one hmass).mp (by simpa [m] using hloss)
    exact (div_le_one hmass).mpr (hle.trans hbig)
  have hfac : ∀ r < n, (r : ℝ) * η ≤ m := by
    intro r hr
    exact (div_le_one hmass).mp (hdn r hr)
  have hprod := factorial_mul_eMass_ge_prod s w η n hw0 hwη (by simpa [m] using hfac)
  have hsum : (∑ r ∈ Finset.range n, d r) ≤
      (n : ℝ) ^ 2 * η / m := by
    calc
      (∑ r ∈ Finset.range n, d r) ≤
          ∑ _r ∈ Finset.range n, (n : ℝ) * η / m := by
        apply Finset.sum_le_sum
        intro r hr
        have hrn : (r : ℝ) ≤ n := by
          exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hr)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hrn hη) hmass.le
      _ = (n : ℝ) ^ 2 * η / m := by
        simp [pow_two]
        ring
  have hone := one_sub_sum_le_prod_one_sub d n
    (fun r hr => hd0 r) hdn
  have hnorm :
      (∏ r ∈ Finset.range n, (m - r * η)) =
        m ^ n * ∏ r ∈ Finset.range n, (1 - d r) := by
    have hmprod : (∏ _r ∈ Finset.range n, m) = m ^ n := by simp
    rw [← hmprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    dsimp [d]
    rw [mul_sub, mul_one]
    congr 1
    exact (mul_div_cancel₀ ((r : ℝ) * η) (ne_of_gt hmass)).symm
  have hmain :
      m ^ n * (1 - (n : ℝ) ^ 2 * η / m) ≤
        (n.factorial : ℝ) * eMass s w n := by
    calc
      m ^ n * (1 - (n : ℝ) ^ 2 * η / m) ≤
          m ^ n * (1 - ∑ r ∈ Finset.range n, d r) := by
        gcongr
      _ ≤ m ^ n * ∏ r ∈ Finset.range n, (1 - d r) :=
        mul_le_mul_of_nonneg_left hone (pow_nonneg hmass.le _)
      _ = ∏ r ∈ Finset.range n, (m - r * η) := hnorm.symm
      _ ≤ (n.factorial : ℝ) * eMass s w n := by simpa [m] using hprod
  have hfact : (0 : ℝ) < n.factorial := by positivity
  change (1 - (n : ℝ) ^ 2 * η / m) * (m ^ n / n.factorial) ≤ eMass s w n
  calc
    (1 - (n : ℝ) ^ 2 * η / m) * (m ^ n / n.factorial) =
        (m ^ n * (1 - (n : ℝ) ^ 2 * η / m)) / n.factorial := by ring
    _ ≤ eMass s w n := (div_le_iff₀ hfact).mpr (by
      simpa [mul_comm, mul_left_comm] using hmain)

/-! Block profiles. -/

/-- Reciprocal mass of squarefree choices of exactly `n` primes from block `j`. -/
noncomputable def blockChoiceMass (j n : ℕ) : ℝ :=
  eMass (primeBlock j) (fun p => (1 : ℝ) / p) n

/-- The reciprocal mass of a block profile, as a product of independent
squarefree block-choice masses. -/
noncomputable def profileMass (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∏ i ∈ Finset.range blocks, blockChoiceMass (start + i) (b i)

/-- The ordered-tuple model before repeated primes are removed. -/
noncomputable def profileTupleMass (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∏ i ∈ Finset.range blocks,
    primeBlockMass (start + i) ^ b i / (b i).factorial

/-- Total number of primes prescribed by a profile. -/
def profilePrimeCount (blocks : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range blocks, b i

/-- The factorial denominator attached to a profile. -/
def profileFactorial (blocks : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∏ i ∈ Finset.range blocks, (b i).factorial

/-- A concrete profile selection assigns to every block index a finite set of
primes.  Membership in `profileSelections` below imposes the block and
cardinality conditions. -/
abbrev ProfileSelection (blocks : ℕ) :=
  ∀ i : ℕ, i ∈ Finset.range blocks → Finset ℕ

/-- The finite set of all blockwise selections prescribed by `b`. -/
noncomputable def profileSelections
    (start blocks : ℕ) (b : ℕ → ℕ) : Finset (ProfileSelection blocks) :=
  (Finset.range blocks).pi fun i =>
    (primeBlock (start + i)).powersetCard (b i)

/-- The squarefree natural-number product represented by a profile
selection. -/
noncomputable def profileSelectionProduct
    {blocks : ℕ} (c : ProfileSelection blocks) : ℕ :=
  ∏ i ∈ (Finset.range blocks).attach, ∏ p ∈ c i.1 i.2, p

/-- Reciprocal weight of a concrete profile selection. -/
noncomputable def profileSelectionWeight
    {blocks : ℕ} (c : ProfileSelection blocks) : ℝ :=
  ∏ i ∈ (Finset.range blocks).attach,
    ∏ p ∈ c i.1 i.2, (1 : ℝ) / p

/-- The union of all primes occurring in a concrete profile selection. -/
noncomputable def profileSelectionPrimes
    {blocks : ℕ} (c : ProfileSelection blocks) : Finset ℕ :=
  (Finset.range blocks).attach.biUnion fun i => c i.1 i.2

/-- The analytic product `profileMass` is exactly the reciprocal mass of all
concrete blockwise prime selections. -/
theorem profileMass_eq_sum_profileSelections
    (start blocks : ℕ) (b : ℕ → ℕ) :
    profileMass start blocks b =
      ∑ c ∈ profileSelections start blocks b, profileSelectionWeight c := by
  classical
  unfold profileMass blockChoiceMass eMass profileSelections profileSelectionWeight
  exact Finset.prod_sum (Finset.range blocks)
    (fun i => (primeBlock (start + i)).powersetCard (b i))
    (fun _i t => ∏ p ∈ t, (1 : ℝ) / p)

/-- The displayed selection weight really is the reciprocal of its natural
number product. -/
theorem profileSelectionWeight_eq_reciprocal
    {blocks : ℕ} (c : ProfileSelection blocks) :
    profileSelectionWeight c = (1 : ℝ) / profileSelectionProduct c := by
  classical
  unfold profileSelectionWeight profileSelectionProduct
  push_cast
  simp only [one_div, Finset.prod_inv_distrib]

theorem profileSelection_subset_block
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b)
    (i : ℕ) (hi : i ∈ Finset.range blocks) :
    c i hi ⊆ primeBlock (start + i) := by
  have hci := (Finset.mem_pi.mp hc) i hi
  exact (Finset.mem_powersetCard.mp hci).1

theorem profileSelection_card
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b)
    (i : ℕ) (hi : i ∈ Finset.range blocks) :
    (c i hi).card = b i := by
  have hci := (Finset.mem_pi.mp hc) i hi
  exact (Finset.mem_powersetCard.mp hci).2

theorem profileSelection_pairwiseDisjoint
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    Set.PairwiseDisjoint
      (↑(Finset.range blocks).attach :
        Set {i // i ∈ Finset.range blocks})
      (fun i : {i // i ∈ Finset.range blocks} => c i.1 i.2) := by
  intro i hi j hj hij
  have hijVal : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  exact (primeBlock_disjoint_of_ne
    (by omega : start + i.1 ≠ start + j.1)).mono
    (profileSelection_subset_block hc i.1 i.2)
    (profileSelection_subset_block hc j.1 j.2)

theorem profileSelectionProduct_eq_prod_primes
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    profileSelectionProduct c = ∏ p ∈ profileSelectionPrimes c, p := by
  unfold profileSelectionProduct profileSelectionPrimes
  exact (Finset.prod_biUnion (f := id)
    (profileSelection_pairwiseDisjoint hc)).symm

theorem prime_of_mem_profileSelectionPrimes
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) {p : ℕ}
    (hp : p ∈ profileSelectionPrimes c) : p.Prime := by
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact prime_of_mem_primeBlock
    (profileSelection_subset_block hc i.1 i.2 hp)

/-- Every represented natural number is genuinely squarefree: selections
have no repetitions inside a block, and distinct prime blocks are disjoint. -/
theorem squarefree_profileSelectionProduct
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    Squarefree (profileSelectionProduct c) := by
  rw [profileSelectionProduct_eq_prod_primes hc]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (prime_of_mem_profileSelectionPrimes hc hp)
      (prime_of_mem_profileSelectionPrimes hc hq)).mpr hpq
  · intro p hp
    exact (prime_of_mem_profileSelectionPrimes hc hp).squarefree

theorem profileSelectionPrimes_card
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    (profileSelectionPrimes c).card = profilePrimeCount blocks b := by
  rw [profileSelectionPrimes,
    Finset.card_biUnion (profileSelection_pairwiseDisjoint hc)]
  unfold profilePrimeCount
  calc
    (∑ i ∈ (Finset.range blocks).attach, (c i.1 i.2).card) =
        ∑ i ∈ (Finset.range blocks).attach, b i.1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact profileSelection_card hc i.1 i.2
    _ = ∑ i ∈ Finset.range blocks, b i :=
      Finset.sum_attach (Finset.range blocks) b

theorem profileSelectionProduct_primeFactors_card
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    (profileSelectionProduct c).primeFactors.card =
      profilePrimeCount blocks b := by
  rw [profileSelectionProduct_eq_prod_primes hc,
    Nat.primeFactors_prod (fun p hp =>
      prime_of_mem_profileSelectionPrimes hc hp),
    profileSelectionPrimes_card hc]

theorem divisorCount_eq_two_pow_primeFactors_card_of_squarefree
    {a : ℕ} (ha : Squarefree a) :
    divisorCount a = 2 ^ a.primeFactors.card := by
  unfold divisorCount
  rw [Nat.card_divisors ha.ne_zero]
  calc
    (∏ p ∈ a.primeFactors, (a.factorization p + 1)) =
        ∏ _p ∈ a.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree ha
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ a.primeFactors.card := by simp

theorem divisorCount_profileSelectionProduct
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    divisorCount (profileSelectionProduct c) =
      2 ^ profilePrimeCount blocks b := by
  rw [divisorCount_eq_two_pow_primeFactors_card_of_squarefree
    (squarefree_profileSelectionProduct hc),
    profileSelectionProduct_primeFactors_card hc]

/-- A block component can be recovered from the union of selected primes by
intersecting with that block. -/
theorem profileSelection_eq_inter_primes
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b)
    (i : ℕ) (hi : i ∈ Finset.range blocks) :
    c i hi = profileSelectionPrimes c ∩ primeBlock (start + i) := by
  ext p
  simp only [Finset.mem_inter]
  constructor
  · intro hp
    exact ⟨Finset.mem_biUnion.mpr
      ⟨⟨i, hi⟩, Finset.mem_attach _ _, hp⟩,
      profileSelection_subset_block hc i hi hp⟩
  · rintro ⟨hpUnion, hpBlock⟩
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpUnion
    have hpjBlock := profileSelection_subset_block hc j.1 j.2 hpj
    have hji : j.1 = i := by
      by_contra hne
      have hd := primeBlock_disjoint_of_ne
        (by omega : start + j.1 ≠ start + i)
      exact (Finset.disjoint_left.mp hd) hpjBlock hpBlock
    have hjEq : j = ⟨i, hi⟩ := Subtype.ext hji
    subst j
    simpa using hpj

/-- Unique factorization makes the natural-number product map injective on
valid profile selections. -/
theorem profileSelectionProduct_injOn (start blocks : ℕ) (b : ℕ → ℕ) :
    Set.InjOn profileSelectionProduct
      (↑(profileSelections start blocks b) : Set (ProfileSelection blocks)) := by
  intro c hc d hd hprod
  have hcPrimes : ∀ p ∈ profileSelectionPrimes c, p.Prime :=
    fun p hp => prime_of_mem_profileSelectionPrimes hc hp
  have hdPrimes : ∀ p ∈ profileSelectionPrimes d, p.Prime :=
    fun p hp => prime_of_mem_profileSelectionPrimes hd hp
  have hunion : profileSelectionPrimes c = profileSelectionPrimes d := by
    calc
      profileSelectionPrimes c = (profileSelectionProduct c).primeFactors := by
        rw [profileSelectionProduct_eq_prod_primes hc,
          Nat.primeFactors_prod hcPrimes]
      _ = (profileSelectionProduct d).primeFactors := congrArg Nat.primeFactors hprod
      _ = profileSelectionPrimes d := by
        rw [profileSelectionProduct_eq_prod_primes hd,
          Nat.primeFactors_prod hdPrimes]
  funext i hi
  rw [profileSelection_eq_inter_primes hc i hi,
    profileSelection_eq_inter_primes hd i hi, hunion]

/-- The actual finite family of squarefree natural-number products with
occupancy profile `b`. -/
noncomputable def profileNumberFamily
    (start blocks : ℕ) (b : ℕ → ℕ) : Finset ℕ :=
  (profileSelections start blocks b).image profileSelectionProduct

/-- Reciprocal mass of an ordinary finite family. -/
noncomputable def reciprocalFamilyMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

theorem mem_profileNumberFamily_squarefree
    {start blocks : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ profileNumberFamily start blocks b) : Squarefree a := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact squarefree_profileSelectionProduct hc

theorem divisorCount_of_mem_profileNumberFamily
    {start blocks : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ profileNumberFamily start blocks b) :
    divisorCount a = 2 ^ profilePrimeCount blocks b := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact divisorCount_profileSelectionProduct hc

/-- The analytic profile mass is exactly the reciprocal mass of the actual
finite squarefree number family. -/
theorem reciprocalFamilyMass_profileNumberFamily
    (start blocks : ℕ) (b : ℕ → ℕ) :
    reciprocalFamilyMass (profileNumberFamily start blocks b) =
      profileMass start blocks b := by
  classical
  rw [profileMass_eq_sum_profileSelections]
  unfold reciprocalFamilyMass profileNumberFamily
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro c hc
    exact (profileSelectionWeight_eq_reciprocal c).symm
  · intro c hc d hd hcd
    exact profileSelectionProduct_injOn start blocks b hc hd hcd

/-! ## Exact divisor-pair bridge -/

private theorem primeFinsetProd_injOn {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (↑s.powerset) := by
  intro t ht u hu hprod
  have ht' := Finset.mem_powerset.mp ht
  have hu' := Finset.mem_powerset.mp hu
  have hpt : ∀ p ∈ t, p.Prime := fun p hp => hs p (ht' hp)
  have hpu : ∀ p ∈ u, p.Prime := fun p hp => hs p (hu' hp)
  calc
    t = (∏ p ∈ t, p).primeFactors := (Nat.primeFactors_prod hpt).symm
    _ = (∏ p ∈ u, p).primeFactors := congrArg Nat.primeFactors hprod
    _ = u := Nat.primeFactors_prod hpu

theorem divisors_profileSelectionProduct_eq_image
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    (profileSelectionProduct c).divisors =
      (profileSelectionPrimes c).powerset.image (fun t => ∏ p ∈ t, p) := by
  let a := profileSelectionProduct c
  let s := profileSelectionPrimes c
  have ha : Squarefree a := squarefree_profileSelectionProduct hc
  have has : a = ∏ p ∈ s, p := profileSelectionProduct_eq_prod_primes hc
  ext d
  constructor
  · intro hd
    have hda := (Nat.mem_divisors.mp hd).1
    have hdSq : Squarefree d := ha.squarefree_of_dvd hda
    refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (by
        rw [← Nat.primeFactors_prod (fun p hp =>
          prime_of_mem_profileSelectionPrimes hc hp), ← has]
        exact Nat.primeFactors_mono hda ha.ne_zero)
    · exact Nat.prod_primeFactors_of_squarefree hdSq
  · intro hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    exact Nat.mem_divisors.mpr ⟨by
      change (∏ p ∈ t, p) ∣ a
      rw [has]
      exact Finset.prod_dvd_prod_of_subset t s id hts, ha.ne_zero⟩

/-- Ordered pairs of prime subsets whose products are dyadically close. -/
noncomputable def profileSelectionClosePairs
    {blocks : ℕ} (c : ProfileSelection blocks) :
    Finset (Finset ℕ × Finset ℕ) :=
  ((profileSelectionPrimes c).powerset.product
    (profileSelectionPrimes c).powerset).filter fun tu =>
      |Real.log (∏ p ∈ tu.1, p) - Real.log (∏ p ∈ tu.2, p)| ≤ dyadicSigma

/-- Number of close ordered subset pairs away from the diagonal. -/
noncomputable def profileSelectionOffDiagonalCount
    {blocks : ℕ} (c : ProfileSelection blocks) : ℕ :=
  (profileSelectionClosePairs c).filter (fun tu => tu.1 ≠ tu.2) |>.card

private theorem prodMap_profileSubset_injOn
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Set.InjOn
      (Prod.map (fun t : Finset ℕ => ∏ p ∈ t, p)
        (fun t : Finset ℕ => ∏ p ∈ t, p))
      (↑(s.powerset.product s.powerset)) := by
  intro x hx y hy hxy
  apply Prod.ext
  · apply primeFinsetProd_injOn hs (Finset.mem_product.mp hx).1
      (Finset.mem_product.mp hy).1
    exact congrArg Prod.fst hxy
  · apply primeFinsetProd_injOn hs (Finset.mem_product.mp hx).2
      (Finset.mem_product.mp hy).2
    exact congrArg Prod.snd hxy

theorem W_profileSelectionProduct_eq_closePairs_card
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    W (profileSelectionProduct c) dyadicSigma =
      (profileSelectionClosePairs c).card := by
  classical
  let s := profileSelectionPrimes c
  let f : Finset ℕ → ℕ := fun t => ∏ p ∈ t, p
  let F : Finset ℕ × Finset ℕ → ℕ × ℕ := Prod.map f f
  have hs : ∀ p ∈ s, p.Prime := fun p hp =>
    prime_of_mem_profileSelectionPrimes hc hp
  have hF : Set.InjOn F (↑(s.powerset.product s.powerset)) :=
    prodMap_profileSubset_injOn hs
  unfold W nearDivisorPairs
  rw [divisors_profileSelectionProduct_eq_image hc]
  rw [show
    ((profileSelectionPrimes c).powerset.image
        (fun t => ∏ p ∈ t, p)).product
      ((profileSelectionPrimes c).powerset.image
        (fun t => ∏ p ∈ t, p)) =
      ((profileSelectionPrimes c).powerset.product
        (profileSelectionPrimes c).powerset).image
          (Prod.map (fun t => ∏ p ∈ t, p) (fun t => ∏ p ∈ t, p)) from
    (Finset.prodMap_image_product
      (fun t : Finset ℕ => ∏ p ∈ t, p)
      (fun t : Finset ℕ => ∏ p ∈ t, p)
      (profileSelectionPrimes c).powerset
      (profileSelectionPrimes c).powerset).symm]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · unfold profileSelectionClosePairs
    congr 2
    ext tu
    simp only [Prod.map_fst, Prod.map_snd]
    push_cast
    rfl
  · exact hF.mono (Finset.filter_subset _ _)

private theorem profileSelectionClosePairs_diagonal_card
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    ((profileSelectionClosePairs c).filter fun tu => tu.1 = tu.2).card =
      2 ^ profilePrimeCount blocks b := by
  classical
  have hdiag :
      (profileSelectionClosePairs c).filter (fun tu => tu.1 = tu.2) =
        (profileSelectionPrimes c).powerset.image (fun t => (t, t)) := by
    ext tu
    constructor
    · intro htu
      have hm := Finset.mem_filter.mp htu
      have hp := Finset.mem_filter.mp hm.1
      have heq := hm.2
      refine Finset.mem_image.mpr ⟨tu.1,
        (Finset.mem_product.mp hp.1).1, ?_⟩
      exact Prod.ext rfl heq
    · intro htu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp htu
      simp [profileSelectionClosePairs, ht, dyadicSigma_pos.le]
  rw [hdiag, Finset.card_image_of_injective]
  · rw [Finset.card_powerset, profileSelectionPrimes_card hc]
  · intro t u htu
    exact congrArg Prod.fst htu

theorem profileSelectionClosePairs_card_eq_diagonal_add_offDiagonal
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    (profileSelectionClosePairs c).card =
      2 ^ profilePrimeCount blocks b + profileSelectionOffDiagonalCount c := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := profileSelectionClosePairs c) (fun tu => tu.1 = tu.2)
  calc
    (profileSelectionClosePairs c).card =
        ((profileSelectionClosePairs c).filter fun tu => tu.1 = tu.2).card +
          profileSelectionOffDiagonalCount c := by
      unfold profileSelectionOffDiagonalCount
      simpa only [ne_eq] using hsplit.symm
    _ = 2 ^ profilePrimeCount blocks b +
        profileSelectionOffDiagonalCount c := by
      rw [profileSelectionClosePairs_diagonal_card hc]

theorem W_profileSelectionProduct_eq_diagonal_add_offDiagonal
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    W (profileSelectionProduct c) dyadicSigma =
      2 ^ profilePrimeCount blocks b + profileSelectionOffDiagonalCount c := by
  rw [W_profileSelectionProduct_eq_closePairs_card hc,
    profileSelectionClosePairs_card_eq_diagonal_add_offDiagonal hc]

/-- Reciprocal-weighted off-diagonal close-pair mass of a profile. -/
noncomputable def profileOffDiagonalMass
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑ c ∈ profileSelections start blocks b,
    (profileSelectionOffDiagonalCount c : ℝ) * profileSelectionWeight c

/-- Exact diagonal/off-diagonal bridge for the reciprocal-weighted `W`
mass of a concrete occupancy profile. -/
theorem weightedDyadicPairMass_profileNumberFamily_eq_diagonal_add_offDiagonal
    (start blocks : ℕ) (b : ℕ → ℕ) :
    weightedDyadicPairMass (profileNumberFamily start blocks b) =
      (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        profileOffDiagonalMass start blocks b := by
  classical
  unfold weightedDyadicPairMass profileNumberFamily
  rw [Finset.sum_image (profileSelectionProduct_injOn start blocks b)]
  rw [profileMass_eq_sum_profileSelections, Finset.mul_sum]
  unfold profileOffDiagonalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [W_profileSelectionProduct_eq_diagonal_add_offDiagonal hc,
    profileSelectionWeight_eq_reciprocal]
  push_cast
  ring

/-- Repeated-prime loss in one block.  The factor `n^2` is the union-bound
cost for a collision among `n` ordered slots. -/
noncomputable def blockCollisionLoss (j n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (1 / (primeBlockLower j + 1 : ℕ) : ℝ) / primeBlockMass j

/-- Sum of the blockwise repeated-prime losses. -/
noncomputable def profileCollisionPotential
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range blocks, blockCollisionLoss (start + i) (b i)

theorem primeBlockMass_pos (j : ℕ) : 0 < primeBlockMass j := by
  have hdef := primeBlockMass_deficit_le_geometric j
  have hp : (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) ≤ 1 / 3 := by
    have hpow : (2 / 3 : ℝ) ^ (j + 1) ≤ 2 / 3 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    linarith
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

theorem blockChoiceMass_nonneg (j n : ℕ) : 0 ≤ blockChoiceMass j n := by
  apply eMass_nonneg
  intro p hp
  positivity

theorem profileMass_nonneg (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profileMass start blocks b := by
  unfold profileMass
  apply Finset.prod_nonneg
  intro i hi
  exact blockChoiceMass_nonneg _ _

theorem profileTupleMass_nonneg (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profileTupleMass start blocks b := by
  unfold profileTupleMass
  apply Finset.prod_nonneg
  intro i hi
  exact div_nonneg (pow_nonneg (primeBlockMass_nonneg _) _) (by positivity)

theorem blockChoiceMass_le_tupleMass (j n : ℕ) :
    blockChoiceMass j n ≤ primeBlockMass j ^ n / n.factorial := by
  have h := factorial_mul_eMass_le_pow (primeBlock j)
    (fun p => (1 : ℝ) / p) n (fun p hp => by positivity)
  have hfact : (0 : ℝ) < n.factorial := by positivity
  apply (le_div_iff₀ hfact).mpr
  simpa [blockChoiceMass, primeBlockMass, mul_comm] using h

theorem profileMass_le_profileTupleMass (start blocks : ℕ) (b : ℕ → ℕ) :
    profileMass start blocks b ≤ profileTupleMass start blocks b := by
  unfold profileMass profileTupleMass
  apply Finset.prod_le_prod
  · intro i hi
    exact blockChoiceMass_nonneg _ _
  · intro i hi
    exact blockChoiceMass_le_tupleMass _ _

theorem blockCollisionLoss_nonneg (j n : ℕ) :
    0 ≤ blockCollisionLoss j n := by
  unfold blockCollisionLoss
  exact div_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (primeBlockMass_pos j).le

theorem profileCollisionPotential_nonneg (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profileCollisionPotential start blocks b := by
  unfold profileCollisionPotential
  exact Finset.sum_nonneg fun i hi => blockCollisionLoss_nonneg _ _

theorem reciprocal_le_block_endpoint {j p : ℕ} (hp : p ∈ primeBlock j) :
    (1 : ℝ) / p ≤ (1 : ℝ) / (primeBlockLower j + 1 : ℕ) := by
  have hpos : (0 : ℝ) < primeBlockLower j + 1 := by positivity
  push_cast
  apply one_div_le_one_div_of_le hpos
  exact_mod_cast primeBlockLower_lt_of_mem hp

/-- The actual square-prime mass is bounded by the collision scale used in
`blockCollisionLoss`. -/
theorem squareMass_ratio_le_blockCollisionLoss (j n : ℕ) :
    (n : ℝ) ^ 2 * primeBlockSquareMass j / primeBlockMass j ^ 2 ≤
      blockCollisionLoss j n := by
  have hm := primeBlockMass_pos j
  have hs := primeBlockSquareMass_le j
  unfold blockCollisionLoss
  calc
    (n : ℝ) ^ 2 * primeBlockSquareMass j / primeBlockMass j ^ 2 ≤
        (n : ℝ) ^ 2 *
          ((1 / (primeBlockLower j + 1 : ℕ) : ℝ) * primeBlockMass j) /
            primeBlockMass j ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (n : ℝ) ^ 2 * (1 / (primeBlockLower j + 1 : ℕ) : ℝ) /
          primeBlockMass j := by
      field_simp [ne_of_gt hm]

theorem blockChoiceMass_collision_lower (j n : ℕ)
    (hloss : blockCollisionLoss j n ≤ 1) :
    (1 - blockCollisionLoss j n) *
        (primeBlockMass j ^ n / n.factorial) ≤ blockChoiceMass j n := by
  unfold blockCollisionLoss at hloss
  unfold blockChoiceMass blockCollisionLoss
  push_cast at hloss
  have h := eMass_collision_lower (primeBlock j) (fun p => (1 : ℝ) / p)
    (1 / ((primeBlockLower j : ℝ) + 1)) n
    (fun p hp => by positivity)
    (fun p hp => by simpa using reciprocal_le_block_endpoint hp)
    (by simpa [primeBlockMass] using primeBlockMass_pos j)
    (by simpa only [primeBlockMass] using hloss)
  push_cast
  simpa [primeBlockMass] using h

theorem profileMass_ge_one_sub_collision_mul_tuple
    (start blocks : ℕ) (b : ℕ → ℕ)
    (hloss : ∀ i < blocks, blockCollisionLoss (start + i) (b i) ≤ 1) :
    (1 - profileCollisionPotential start blocks b) *
        profileTupleMass start blocks b ≤ profileMass start blocks b := by
  have hblock :
      (∏ i ∈ Finset.range blocks,
        ((1 - blockCollisionLoss (start + i) (b i)) *
          (primeBlockMass (start + i) ^ b i / (b i).factorial))) ≤
        profileMass start blocks b := by
    unfold profileMass
    apply Finset.prod_le_prod
    · intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hloss i (Finset.mem_range.mp hi)))
        (div_nonneg (pow_nonneg (primeBlockMass_nonneg _) _) (by positivity))
    · intro i hi
      exact blockChoiceMass_collision_lower _ _ (hloss i (Finset.mem_range.mp hi))
  have hprodLoss :
      1 - profileCollisionPotential start blocks b ≤
        ∏ i ∈ Finset.range blocks,
          (1 - blockCollisionLoss (start + i) (b i)) := by
    apply one_sub_sum_le_prod_one_sub
    · intro i hi
      exact blockCollisionLoss_nonneg _ _
    · intro i hi
      exact hloss i hi
  calc
    (1 - profileCollisionPotential start blocks b) *
        profileTupleMass start blocks b ≤
      (∏ i ∈ Finset.range blocks,
        (1 - blockCollisionLoss (start + i) (b i))) *
          profileTupleMass start blocks b :=
      mul_le_mul_of_nonneg_right hprodLoss (profileTupleMass_nonneg _ _ _)
    _ = ∏ i ∈ Finset.range blocks,
        ((1 - blockCollisionLoss (start + i) (b i)) *
          (primeBlockMass (start + i) ^ b i / (b i).factorial)) := by
      rw [profileTupleMass, Finset.prod_mul_distrib]
    _ ≤ profileMass start blocks b := hblock

/-- Ford's collision-removal estimate: losing at most half of the ordered
tuple mass leaves a uniform half of the squarefree profile mass. -/
theorem half_profileTupleMass_le_profileMass
    (start blocks : ℕ) (b : ℕ → ℕ)
    (hloss : profileCollisionPotential start blocks b ≤ 1 / 2) :
    (1 / 2 : ℝ) * profileTupleMass start blocks b ≤
      profileMass start blocks b := by
  have hpoint : ∀ i < blocks, blockCollisionLoss (start + i) (b i) ≤ 1 := by
    intro i hi
    have hone := Finset.single_le_sum
      (fun x _ => blockCollisionLoss_nonneg (start + x) (b x))
      (Finset.mem_range.mpr hi)
    have := hone.trans hloss
    linarith
  have hmain := profileMass_ge_one_sub_collision_mul_tuple start blocks b hpoint
  have ht := profileTupleMass_nonneg start blocks b
  calc
    (1 / 2 : ℝ) * profileTupleMass start blocks b ≤
        (1 - profileCollisionPotential start blocks b) *
          profileTupleMass start blocks b := by gcongr; linarith
    _ ≤ profileMass start blocks b := hmain

/-- Loss caused by replacing the actual block mass by its target `log 2`,
after using the block `n` times. -/
noncomputable def blockPrimeMassLoss (j n : ℕ) : ℝ :=
  1 - (primeBlockMass j / Real.log 2) ^ n

/-- Total loss from all greedy prime-block masses in one profile. -/
noncomputable def profilePrimeMassPotential
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range blocks, blockPrimeMassLoss (start + i) (b i)

theorem primeBlockMass_div_log_two_mem_Icc (j : ℕ) :
    primeBlockMass j / Real.log 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (primeBlockMass_nonneg _) (Real.log_pos (by norm_num)).le
  · exact (div_le_one (Real.log_pos (by norm_num))).mpr (primeBlockMass_le_log_two _)

theorem blockPrimeMassLoss_nonneg (j n : ℕ) :
    0 ≤ blockPrimeMassLoss j n := by
  unfold blockPrimeMassLoss
  exact sub_nonneg.mpr (pow_le_one₀
    (primeBlockMass_div_log_two_mem_Icc j).1
    (primeBlockMass_div_log_two_mem_Icc j).2)

theorem blockPrimeMassLoss_le_one (j n : ℕ) :
    blockPrimeMassLoss j n ≤ 1 := by
  unfold blockPrimeMassLoss
  exact sub_le_self _ (pow_nonneg (primeBlockMass_div_log_two_mem_Icc j).1 _)

theorem profilePrimeMassPotential_nonneg
    (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profilePrimeMassPotential start blocks b := by
  unfold profilePrimeMassPotential
  exact Finset.sum_nonneg fun i hi => blockPrimeMassLoss_nonneg _ _

private theorem profileTargetMass_eq_prod
    (blocks : ℕ) (b : ℕ → ℕ) :
    (Real.log 2) ^ profilePrimeCount blocks b /
        (profileFactorial blocks b : ℕ) =
      ∏ i ∈ Finset.range blocks,
        (Real.log 2) ^ b i / (b i).factorial := by
  rw [profilePrimeCount, profileFactorial, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum]
  congr 1
  exact_mod_cast Finset.prod_natCast (Finset.range blocks)
    (fun i => (b i).factorial)

private theorem blockTupleMass_eq_target_mul_one_sub_loss (j n : ℕ) :
    primeBlockMass j ^ n / n.factorial =
      ((Real.log 2) ^ n / n.factorial) * (1 - blockPrimeMassLoss j n) := by
  unfold blockPrimeMassLoss
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  rw [div_pow]
  field_simp
  ring

theorem profileTupleMass_ge_one_sub_primeLoss_mul_target
    (start blocks : ℕ) (b : ℕ → ℕ) :
    (1 - profilePrimeMassPotential start blocks b) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) ≤
      profileTupleMass start blocks b := by
  have hprodLoss :
      1 - profilePrimeMassPotential start blocks b ≤
        ∏ i ∈ Finset.range blocks,
          (1 - blockPrimeMassLoss (start + i) (b i)) := by
    apply one_sub_sum_le_prod_one_sub
    · intro i hi
      exact blockPrimeMassLoss_nonneg _ _
    · intro i hi
      exact blockPrimeMassLoss_le_one _ _
  have htarget :
      0 ≤ (Real.log 2) ^ profilePrimeCount blocks b /
        (profileFactorial blocks b : ℕ) := by positivity
  calc
    (1 - profilePrimeMassPotential start blocks b) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) ≤
      (∏ i ∈ Finset.range blocks,
        (1 - blockPrimeMassLoss (start + i) (b i))) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) :=
      mul_le_mul_of_nonneg_right hprodLoss htarget
    _ = ∏ i ∈ Finset.range blocks,
        ((1 - blockPrimeMassLoss (start + i) (b i)) *
          ((Real.log 2) ^ b i / (b i).factorial)) := by
      rw [profileTargetMass_eq_prod, Finset.prod_mul_distrib]
    _ = profileTupleMass start blocks b := by
      unfold profileTupleMass
      apply Finset.prod_congr rfl
      intro i hi
      rw [mul_comm]
      exact (blockTupleMass_eq_target_mul_one_sub_loss _ _).symm

/-- Ford's `(10.75)` profile-mass bound in explicit finite form.  The two
potentials separately record greedy-block deficit and repeated-prime
collisions. -/
theorem quarter_targetProfileMass_le_profileMass
    (start blocks : ℕ) (b : ℕ → ℕ)
    (hprime : profilePrimeMassPotential start blocks b ≤ 1 / 2)
    (hcollision : profileCollisionPotential start blocks b ≤ 1 / 2) :
    (1 / 4 : ℝ) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) ≤
      profileMass start blocks b := by
  have ht := profileTupleMass_ge_one_sub_primeLoss_mul_target start blocks b
  have htarget :
      0 ≤ (Real.log 2) ^ profilePrimeCount blocks b /
        (profileFactorial blocks b : ℕ) := by positivity
  have hhalfTarget :
      (1 / 2 : ℝ) *
          ((Real.log 2) ^ profilePrimeCount blocks b /
            (profileFactorial blocks b : ℕ)) ≤
        profileTupleMass start blocks b := by
    calc
      (1 / 2 : ℝ) *
          ((Real.log 2) ^ profilePrimeCount blocks b /
            (profileFactorial blocks b : ℕ)) ≤
        (1 - profilePrimeMassPotential start blocks b) *
          ((Real.log 2) ^ profilePrimeCount blocks b /
            (profileFactorial blocks b : ℕ)) := by gcongr; linarith
      _ ≤ profileTupleMass start blocks b := ht
  have hc := half_profileTupleMass_le_profileMass start blocks b hcollision
  nlinarith [profileTupleMass_nonneg start blocks b]

/-- Ford's polynomial occupancy cap.  The bound is uniform in the length of
the finite profile. -/
def AdmissibleProfile (M blocks : ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ i < blocks, b i ≤ M + i ^ 2

theorem blockPrimeMassLoss_le_relative (j n : ℕ) :
    blockPrimeMassLoss j n ≤ (n : ℝ) * primeBlockRelativeDeficit j := by
  have hd0 := primeBlockRelativeDeficit_nonneg j
  have hd1 : primeBlockRelativeDeficit j ≤ 1 := by
    exact (primeBlockRelativeDeficit_le_geometric j).trans
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hratio :
      primeBlockMass j / Real.log 2 = 1 - primeBlockRelativeDeficit j := by
    have hlog : Real.log 2 ≠ 0 := ne_of_gt
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    unfold primeBlockRelativeDeficit
    field_simp [hlog]
    ring
  have hbern := one_add_mul_le_pow
    (a := -primeBlockRelativeDeficit j) (by linarith) n
  unfold blockPrimeMassLoss
  rw [hratio]
  have hform :
      1 + (n : ℝ) * (-primeBlockRelativeDeficit j) =
        1 - (n : ℝ) * primeBlockRelativeDeficit j := by ring
  rw [hform] at hbern
  have hbern' :
      1 - (n : ℝ) * primeBlockRelativeDeficit j ≤
        (1 - primeBlockRelativeDeficit j) ^ n := by
    simpa only [sub_eq_add_neg] using hbern
  linarith

theorem one_third_lt_primeBlockMass (j : ℕ) :
    (1 / 3 : ℝ) < primeBlockMass j := by
  have hdef := primeBlockMass_deficit_le_geometric j
  have hp : (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) ≤ 1 / 3 := by
    have hpow : (2 / 3 : ℝ) ^ (j + 1) ≤ 2 / 3 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num)
        (pow_le_one₀ (by norm_num) (by norm_num))
    linarith
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

theorem blockCollisionLoss_le_geometric (j n : ℕ) :
    blockCollisionLoss j n ≤
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ j := by
  have hm : (1 / 3 : ℝ) < primeBlockMass j := one_third_lt_primeBlockMass j
  have he0 : (0 : ℝ) < primeBlockLower j := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (two_le_primeBlockEndpoint j))
  have hend :
      (1 : ℝ) / (primeBlockLower j + 1 : ℕ) ≤
        (1 : ℝ) / primeBlockLower j := by
    apply one_div_le_one_div_of_le he0
    exact_mod_cast Nat.le_succ (primeBlockLower j)
  have hgeom :
      (1 : ℝ) / primeBlockLower j ≤
        (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j := by
    simpa [primeBlockLower] using one_div_primeBlockEndpoint_le_geometric j
  unfold blockCollisionLoss
  calc
    (n : ℝ) ^ 2 * (1 / (primeBlockLower j + 1 : ℕ) : ℝ) /
        primeBlockMass j ≤
      (n : ℝ) ^ 2 * ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j) /
        primeBlockMass j := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hend.trans hgeom) (sq_nonneg _))
        (primeBlockMass_nonneg _)
    _ ≤ (n : ℝ) ^ 2 * ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j) /
        (1 / 3 : ℝ) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (sq_nonneg _) (by positivity)) (by norm_num) hm.le
    _ = (3 / 2 : ℝ) * (n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ j := by ring

private theorem summable_profileDefectMajorant (M : ℕ) :
    Summable (fun i : ℕ => ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ i) := by
  have h0 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (r := 2 / 3) (by norm_num)).mul_left (M : ℝ)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 2 / 3) (by norm_num)
  apply (h0.add h2).congr
  intro i
  push_cast
  simp
  ring

private theorem summable_profileCollisionMajorant (M : ℕ) :
    Summable (fun i : ℕ =>
      (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 * (2 / 3 : ℝ) ^ i) := by
  have h0 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (r := 2 / 3) (by norm_num)).mul_left ((3 / 2 : ℝ) * (M : ℝ) ^ 2)
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 2 / 3) (by norm_num)).mul_left (3 * (M : ℝ))
  have h4 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4
    (r := 2 / 3) (by norm_num)).mul_left (3 / 2 : ℝ)
  apply ((h0.add h2).add h4).congr
  intro i
  push_cast
  simp
  ring

/-- A start index is controlled when both infinite polynomial-geometric
majorants are at most one half. -/
noncomputable def ProfileStartControlled (M start : ℕ) : Prop :=
  (2 / 3 : ℝ) ^ start *
      (∑' i : ℕ, ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ i) ≤ 1 / 2 ∧
  (2 / 3 : ℝ) ^ start *
      (∑' i : ℕ,
        (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 * (2 / 3 : ℝ) ^ i) ≤ 1 / 2

theorem exists_profileStartControlled (M : ℕ) :
    ∃ start : ℕ, ProfileStartControlled M start := by
  let A := ∑' i : ℕ, ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ i
  let B := ∑' i : ℕ,
    (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 * (2 / 3 : ℝ) ^ i
  have hp : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hA : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * A) atTop (nhds 0) := by
    simpa using hp.mul_const A
  have hB : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * B) atTop (nhds 0) := by
    simpa using hp.mul_const B
  have heA := hA.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heB := hB.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  rw [eventually_atTop] at heA heB
  obtain ⟨a, ha⟩ := heA
  obtain ⟨c, hc⟩ := heB
  refine ⟨max a c, ?_⟩
  unfold ProfileStartControlled
  change (2 / 3 : ℝ) ^ max a c * A ≤ 1 / 2 ∧
    (2 / 3 : ℝ) ^ max a c * B ≤ 1 / 2
  exact ⟨(ha _ (le_max_left _ _)).le, (hc _ (le_max_right _ _)).le⟩

theorem admissible_profilePrimeMassPotential_le_half
    {M start blocks : ℕ} {b : ℕ → ℕ}
    (hcontrol : ProfileStartControlled M start)
    (hb : AdmissibleProfile M blocks b) :
    profilePrimeMassPotential start blocks b ≤ 1 / 2 := by
  let f : ℕ → ℝ := fun i => ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ i
  have hsum : (∑ i ∈ Finset.range blocks, f i) ≤ ∑' i, f i :=
    (summable_profileDefectMajorant M).sum_le_tsum _ (fun i hi => by positivity)
  calc
    profilePrimeMassPotential start blocks b ≤
        ∑ i ∈ Finset.range blocks,
          ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ (start + i + 1) := by
      unfold profilePrimeMassPotential
      apply Finset.sum_le_sum
      intro i hi
      calc
        blockPrimeMassLoss (start + i) (b i) ≤
            (b i : ℝ) * primeBlockRelativeDeficit (start + i) :=
          blockPrimeMassLoss_le_relative _ _
        _ ≤ ((M + i ^ 2 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ (start + i + 1) := by
          exact mul_le_mul
            (by exact_mod_cast hb i (Finset.mem_range.mp hi))
            (primeBlockRelativeDeficit_le_geometric _)
            (primeBlockRelativeDeficit_nonneg _)
            (Nat.cast_nonneg _)
    _ = (2 / 3 : ℝ) ^ (start + 1) * ∑ i ∈ Finset.range blocks, f i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [f]
      rw [show start + i + 1 = (start + 1) + i by omega, pow_add]
      ring
    _ ≤ (2 / 3 : ℝ) ^ start * ∑' i, f i := by
      have hp : (2 / 3 : ℝ) ^ (start + 1) ≤ (2 / 3 : ℝ) ^ start := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc
        (2 / 3 : ℝ) ^ (start + 1) * ∑ i ∈ Finset.range blocks, f i ≤
            (2 / 3 : ℝ) ^ (start + 1) * ∑' i, f i :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ (2 / 3 : ℝ) ^ start * ∑' i, f i :=
          mul_le_mul_of_nonneg_right hp (tsum_nonneg fun i => by positivity)
    _ ≤ 1 / 2 := hcontrol.1

theorem admissible_profileCollisionPotential_le_half
    {M start blocks : ℕ} {b : ℕ → ℕ}
    (hcontrol : ProfileStartControlled M start)
    (hb : AdmissibleProfile M blocks b) :
    profileCollisionPotential start blocks b ≤ 1 / 2 := by
  let f : ℕ → ℝ := fun i =>
    (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 * (2 / 3 : ℝ) ^ i
  have hsum : (∑ i ∈ Finset.range blocks, f i) ≤ ∑' i, f i :=
    (summable_profileCollisionMajorant M).sum_le_tsum _ (fun i hi => by positivity)
  calc
    profileCollisionPotential start blocks b ≤
        ∑ i ∈ Finset.range blocks,
          (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 *
            (2 / 3 : ℝ) ^ (start + i) := by
      unfold profileCollisionPotential
      apply Finset.sum_le_sum
      intro i hi
      calc
        blockCollisionLoss (start + i) (b i) ≤
            (3 / 2 : ℝ) * (b i : ℝ) ^ 2 * (2 / 3 : ℝ) ^ (start + i) :=
          blockCollisionLoss_le_geometric _ _
        _ ≤ (3 / 2 : ℝ) * ((M + i ^ 2 : ℕ) : ℝ) ^ 2 *
            (2 / 3 : ℝ) ^ (start + i) := by
          gcongr
          exact_mod_cast hb i (Finset.mem_range.mp hi)
    _ = (2 / 3 : ℝ) ^ start * ∑ i ∈ Finset.range blocks, f i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [f]
      rw [pow_add]
      ring
    _ ≤ (2 / 3 : ℝ) ^ start * ∑' i, f i :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / 2 := hcontrol.2

/-- Uniform Ford profile-mass theorem for every finite admissible occupancy
profile after one start index depending only on `M`. -/
theorem admissible_quarter_targetProfileMass_le_profileMass
    {M start blocks : ℕ} {b : ℕ → ℕ}
    (hcontrol : ProfileStartControlled M start)
    (hb : AdmissibleProfile M blocks b) :
    (1 / 4 : ℝ) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) ≤
      profileMass start blocks b :=
  quarter_targetProfileMass_le_profileMass start blocks b
    (admissible_profilePrimeMassPotential_le_half hcontrol hb)
    (admissible_profileCollisionPotential_le_half hcontrol hb)

/-- Ford's profile bound stated directly for the reciprocal mass of the
finite family of squarefree natural-number products. -/
theorem admissible_quarter_target_le_reciprocal_profileNumberFamily
    {M start blocks : ℕ} {b : ℕ → ℕ}
    (hcontrol : ProfileStartControlled M start)
    (hb : AdmissibleProfile M blocks b) :
    (1 / 4 : ℝ) *
        ((Real.log 2) ^ profilePrimeCount blocks b /
          (profileFactorial blocks b : ℕ)) ≤
      reciprocalFamilyMass (profileNumberFamily start blocks b) := by
  rw [reciprocalFamilyMass_profileNumberFamily]
  exact admissible_quarter_targetProfileMass_le_profileMass hcontrol hb

/-- One threshold depending only on `M` works for every profile length and
every occupancy vector satisfying the polynomial cap. -/
theorem exists_uniform_admissible_profile_mass (M : ℕ) :
    ∃ start : ℕ, ∀ (blocks : ℕ) (b : ℕ → ℕ),
      AdmissibleProfile M blocks b →
        (1 / 4 : ℝ) *
            ((Real.log 2) ^ profilePrimeCount blocks b /
              (profileFactorial blocks b : ℕ)) ≤
          profileMass start blocks b := by
  obtain ⟨start, hstart⟩ := exists_profileStartControlled M
  exact ⟨start, fun blocks b hb =>
    admissible_quarter_targetProfileMass_le_profileMass hstart hb⟩

/-- A single starting block depending only on `M` gives the `(10.75)` lower
bound for every finite admissible squarefree-product profile. -/
theorem exists_uniform_admissible_reciprocal_profileNumberFamily (M : ℕ) :
    ∃ start : ℕ, ∀ (blocks : ℕ) (b : ℕ → ℕ),
      AdmissibleProfile M blocks b →
        (1 / 4 : ℝ) *
            ((Real.log 2) ^ profilePrimeCount blocks b /
              (profileFactorial blocks b : ℕ)) ≤
          reciprocalFamilyMass (profileNumberFamily start blocks b) := by
  obtain ⟨start, hstart⟩ := exists_profileStartControlled M
  exact ⟨start, fun blocks b hb =>
    admissible_quarter_target_le_reciprocal_profileNumberFamily hstart hb⟩

/-! ## Per-profile close-pair estimate -/

/-- The prefix count `b₀+...+bᵢ`. -/
def profilePrefixCount (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ h ∈ Finset.range (i + 1), b h

/-- Ford's exponential occupancy potential.  Shifting the blocks by
`start` pulls the factor `2^{-start}` outside this sum. -/
noncomputable def profilePrefixPotential (blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range blocks,
    (2 : ℝ) ^ profilePrefixCount b i / (2 : ℝ) ^ i

theorem profilePrefixPotential_nonneg (blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profilePrefixPotential blocks b := by
  unfold profilePrefixPotential
  positivity

/-- The completely uniform remainder needed before the sharper
factor-four prime-interval estimate is inserted.  It is kept separate from
`profilePrefixPotential`, so downstream modules can replace this coarse
term without changing the diagonal decomposition. -/
noncomputable def profileCoarsePairPotential
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  (2 : ℝ) ^ start * ((2 : ℝ) ^ profilePrimeCount blocks b - 1)

/-- Combined per-profile potential.  The first summand is Ford's genuine
prefix potential; the second is the unconditional finite-family remainder. -/
noncomputable def profilePairPotential
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  profilePrefixPotential blocks b + profileCoarsePairPotential start blocks b

theorem profileCoarsePairPotential_nonneg
    (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profileCoarsePairPotential start blocks b := by
  unfold profileCoarsePairPotential
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))

theorem profilePairPotential_nonneg
    (start blocks : ℕ) (b : ℕ → ℕ) :
    0 ≤ profilePairPotential start blocks b := by
  unfold profilePairPotential
  exact add_nonneg (profilePrefixPotential_nonneg _ _)
    (profileCoarsePairPotential_nonneg _ _ _)

theorem W_le_divisorCount_sq (a : ℕ) (sigma : ℝ) :
    W a sigma ≤ divisorCount a ^ 2 := by
  classical
  unfold W nearDivisorPairs divisorCount
  calc
    ((a.divisors.product a.divisors).filter fun de =>
        |Real.log de.1 - Real.log de.2| ≤ sigma).card ≤
        (a.divisors.product a.divisors).card := Finset.card_filter_le _ _
    _ = a.divisors.card ^ 2 := by simp [pow_two]

theorem weightedDyadicPairMass_le_sq_mul_reciprocalFamilyMass
    (A : Finset ℕ) (tau : ℕ)
    (htau : ∀ a ∈ A, divisorCount a = tau) :
    weightedDyadicPairMass A ≤ (tau : ℝ) ^ 2 * reciprocalFamilyMass A := by
  unfold weightedDyadicPairMass reciprocalFamilyMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hW : W a dyadicSigma ≤ tau ^ 2 := by
    simpa [htau a ha] using W_le_divisorCount_sq a dyadicSigma
  have hWR : (W a dyadicSigma : ℝ) ≤ (tau : ℝ) ^ 2 := by
    exact_mod_cast hW
  simpa [div_eq_mul_inv] using
    (div_le_div_of_nonneg_right hWR (Nat.cast_nonneg a))

private theorem dyadicScale_mul_coarsePotential
    (start blocks : ℕ) (b : ℕ → ℕ) :
    (1 / (2 : ℝ) ^ start) * profileCoarsePairPotential start blocks b =
      (2 : ℝ) ^ profilePrimeCount blocks b - 1 := by
  unfold profileCoarsePairPotential
  have hp : (2 : ℝ) ^ start ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Unconditional coarse per-profile weighted `W` estimate.  It isolates the
diagonal-size term, but its potential contains `profileCoarsePairPotential`;
consequently this is not the sharp factor-four estimate used in Ford's
Lemma 4.7.  It is retained as a finite-family fallback. -/
theorem ford_profile_weightedDyadicPairMass_coarse_le
    (A : Finset ℕ) (start blocks : ℕ) (b : ℕ → ℕ)
    (hmass : reciprocalFamilyMass A = profileMass start blocks b)
    (htau : ∀ a ∈ A,
      divisorCount a = 2 ^ profilePrimeCount blocks b) :
    weightedDyadicPairMass A ≤
      (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
      (2 : ℝ) ^ profilePrimeCount blocks b * profileTupleMass start blocks b *
        (1 / (2 : ℝ) ^ start) * profilePairPotential start blocks b := by
  let tau : ℝ := (2 : ℝ) ^ profilePrimeCount blocks b
  have hW := weightedDyadicPairMass_le_sq_mul_reciprocalFamilyMass A
    (2 ^ profilePrimeCount blocks b) htau
  have htauCast : ((2 ^ profilePrimeCount blocks b : ℕ) : ℝ) = tau := by
    simp [tau]
  rw [htauCast, hmass] at hW
  have hmassTuple := profileMass_le_profileTupleMass start blocks b
  have htau1 : 1 ≤ tau := by
    dsimp [tau]
    exact one_le_pow₀ (by norm_num)
  have hprefix := profilePrefixPotential_nonneg blocks b
  have hscale : 0 ≤ (1 / (2 : ℝ) ^ start) := by positivity
  have herror :
      tau * (tau - 1) * profileMass start blocks b ≤
        tau * profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePairPotential start blocks b := by
    calc
      tau * (tau - 1) * profileMass start blocks b ≤
          tau * (tau - 1) * profileTupleMass start blocks b :=
        mul_le_mul_of_nonneg_left hmassTuple
          (mul_nonneg (by positivity) (sub_nonneg.mpr htau1))
      _ = tau * profileTupleMass start blocks b *
          (1 / (2 : ℝ) ^ start) *
            profileCoarsePairPotential start blocks b := by
        rw [show tau * profileTupleMass start blocks b *
            (1 / (2 : ℝ) ^ start) * profileCoarsePairPotential start blocks b =
            tau * profileTupleMass start blocks b *
              ((1 / (2 : ℝ) ^ start) *
                profileCoarsePairPotential start blocks b) by ring,
          dyadicScale_mul_coarsePotential]
        ring
      _ ≤ tau * profileTupleMass start blocks b *
          (1 / (2 : ℝ) ^ start) * profilePairPotential start blocks b := by
        unfold profilePairPotential
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left hprefix
        · exact mul_nonneg
            (mul_nonneg (by positivity) (profileTupleMass_nonneg _ _ _)) hscale
  change weightedDyadicPairMass A ≤
    tau * profileMass start blocks b +
      tau * profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
        profilePairPotential start blocks b
  calc
    weightedDyadicPairMass A ≤ tau ^ 2 * profileMass start blocks b := hW
    _ = tau * profileMass start blocks b +
        tau * (tau - 1) * profileMass start blocks b := by ring
    _ ≤ tau * profileMass start blocks b +
        tau * profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePairPotential start blocks b := by
      simpa [add_comm] using add_le_add_left herror
        (tau * profileMass start blocks b)

end Erdos896.Ford
