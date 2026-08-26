import Mathlib

/-! # The exact generating function of records in a uniform permutation

Right-to-left records are convenient for the proof by deleting the first
entry. Reversing an ordering turns these into the usual left-to-right records.
-/

open scoped BigOperators

namespace Erdos1164

/-- The number of entries exceeding every entry to their right. -/
noncomputable def rightRecordCount {n : ℕ} (a : Fin n → ℝ) : ℕ :=
  ∑ i : Fin n, if ∀ j, i < j → a j < a i then 1 else 0

theorem rightRecordCount_zero (a : Fin 0 → ℝ) : rightRecordCount a = 0 := by
  simp [rightRecordCount]

theorem rightRecordCount_succ {n : ℕ} (a : Fin (n + 1) → ℝ) :
    rightRecordCount a = (if ∀ j : Fin n, a j.succ < a 0 then 1 else 0) +
      rightRecordCount (fun j : Fin n ↦ a j.succ) := by
  classical
  unfold rightRecordCount
  rw [Fin.sum_univ_succ]
  congr 1
  · congr 1
    apply propext
    constructor
    · intro h j
      exact h j.succ (Fin.succ_pos j)
    · intro h j hj
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hj)
      exact h k
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply propext
    constructor
    · intro h j hj
      exact h j.succ (Fin.succ_lt_succ_iff.mpr hj)
    · intro h j hj
      have hjzero : j ≠ 0 := by exact ne_of_gt ((Fin.succ_pos i).trans hj)
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hjzero
      exact h k (Fin.succ_lt_succ_iff.mp hj)

private theorem headRecord_iff {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : Function.Injective a) (p : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1)) (hm : ∀ j, a j ≤ a m) :
    (∀ j : Fin n, a (p j.succ) < a (p 0)) ↔ p 0 = m := by
  constructor
  · intro h
    have hmax : ∀ j : Fin (n + 1), a (p j) ≤ a (p 0) := by
      intro j
      refine Fin.cases le_rfl (fun k ↦ (h k).le) j
    have hback := hmax (p.symm m)
    simp only [Equiv.apply_symm_apply] at hback
    exact ha (le_antisymm (hm (p 0)) hback)
  · intro h j
    have hle : a (p j.succ) ≤ a (p 0) := by rw [h]; exact hm _
    apply lt_of_le_of_ne hle
    intro heq
    have hi := p.injective (ha heq)
    exact Fin.succ_ne_zero j hi

private theorem maximum_index {n : ℕ} (a : Fin (n + 1) → ℝ) :
    ∃ m, ∀ j, a j ≤ a m := by
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  exact ⟨m, fun j ↦ hm j (Finset.mem_univ j)⟩

/-- Exact unnormalized generating function, valid for any injectively ranked
finite set. The argument is finite combinatorics, with no independence axiom. -/
theorem sum_pow_rightRecordCount (q : ℝ) :
    ∀ (n : ℕ) (a : Fin n → ℝ), Function.Injective a →
      (∑ p : Equiv.Perm (Fin n), q ^ rightRecordCount (a ∘ p)) =
        ∏ j ∈ Finset.range n, (q + (j : ℝ)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro a _
    simp [rightRecordCount]
  | succ n ih =>
    intro a ha
    obtain ⟨m, hm⟩ := maximum_index a
    let tail (p : Fin (n + 1)) : Fin n → ℝ :=
      fun j ↦ a (Equiv.swap 0 p j.succ)
    have htail (p : Fin (n + 1)) : Function.Injective (tail p) :=
      ha.comp ((Equiv.swap 0 p).injective.comp (Fin.succ_injective n))
    have hrec (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
        rightRecordCount (a ∘ Equiv.Perm.decomposeFin.symm (p, e)) =
          (if p = m then 1 else 0) + rightRecordCount (tail p ∘ e) := by
      rw [rightRecordCount_succ]
      have hh := headRecord_iff a ha (Equiv.Perm.decomposeFin.symm (p, e)) m hm
      rw [Equiv.Perm.decomposeFin_symm_apply_zero] at hh
      simp only [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero]
      rw [if_congr hh rfl rfl]
      congr 2
      funext j
      exact congrArg a (Equiv.Perm.decomposeFin_symm_apply_succ e p j)
    have hhead : (∑ p : Fin (n + 1), q ^ (if p = m then 1 else 0 : ℕ)) = q + n := by
      have heq (p : Fin (n + 1)) : q ^ (if p = m then 1 else 0 : ℕ) =
          (if p = m then q - 1 else 0) + 1 := by
        by_cases h : p = m <;> simp [h]
      simp only [heq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, Nat.cast_add, Nat.cast_one]
      ring
    calc
      (∑ e : Equiv.Perm (Fin (n + 1)), q ^ rightRecordCount (a ∘ e)) =
          ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n),
            q ^ rightRecordCount (a ∘ Equiv.Perm.decomposeFin.symm pe) :=
        (Equiv.Perm.decomposeFin.symm.sum_comp _).symm
      _ = ∑ p : Fin (n + 1), ∑ e : Equiv.Perm (Fin n),
          q ^ ((if p = m then 1 else 0) + rightRecordCount (tail p ∘ e)) := by
        rw [Fintype.sum_prod_type]
        simp only [hrec]
      _ = ∑ p : Fin (n + 1), q ^ (if p = m then 1 else 0 : ℕ) *
          (∏ j ∈ Finset.range n, (q + (j : ℝ))) := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [pow_add, ← Finset.mul_sum, ih (tail p) (htail p)]
      _ = (q + n) * (∏ j ∈ Finset.range n, (q + (j : ℝ))) := by
        rw [← Finset.sum_mul, hhead]
      _ = _ := by rw [Finset.prod_range_succ, mul_comm]

/-- The usual left-to-right record count. -/
noncomputable def leftRecordCount {n : ℕ} (a : Fin n → ℝ) : ℕ :=
  ∑ i : Fin n, if ∀ j, j < i → a j < a i then 1 else 0

theorem leftRecordCount_eq_right_reverse {n : ℕ} (a : Fin n → ℝ) :
    leftRecordCount a = rightRecordCount (a ∘ Fin.rev) := by
  classical
  unfold leftRecordCount rightRecordCount
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n ↦
    if ∀ j, j < i → a j < a i then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply propext
  constructor
  · intro h j hj
    exact h j.rev (Fin.rev_lt_rev.mpr hj)
  · intro h j hj
    have hji : i < j.rev := Fin.lt_rev_iff.mp hj
    simpa only [Function.comp_apply, Fin.rev_rev, Fin.revPerm_apply] using h j.rev hji

theorem sum_pow_leftRecordCount (q : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    (∑ p : Equiv.Perm (Fin n), q ^ leftRecordCount (a ∘ p)) =
      ∏ j ∈ Finset.range n, (q + (j : ℝ)) := by
  classical
  simp_rw [leftRecordCount_eq_right_reverse]
  have heq : (∑ p : Equiv.Perm (Fin n),
      q ^ rightRecordCount ((a ∘ p) ∘ Fin.rev)) =
      ∑ p : Equiv.Perm (Fin n), q ^ rightRecordCount (a ∘ p) := by
    exact Equiv.sum_comp (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n)))
      (fun p : Equiv.Perm (Fin n) ↦ q ^ rightRecordCount (a ∘ p))
  rw [heq]
  exact sum_pow_rightRecordCount q n a ha

/-- The product appearing in the normalized record generating function. -/
noncomputable def recordGeneratingProduct (q : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 + (q - 1) / ((j + 1 : ℕ) : ℝ))

theorem average_pow_leftRecordCount (q : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    (∑ p : Equiv.Perm (Fin n), q ^ leftRecordCount (a ∘ p)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = recordGeneratingProduct q n := by
  classical
  rw [sum_pow_leftRecordCount q n a ha, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hden : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- A simple harmonic lower bound, sufficient for the covering argument. -/
theorem recordGeneratingProduct_lower (q : ℝ) (hq : 1 ≤ q) (n : ℕ) :
    Real.exp ((1 - 1 / q) * (harmonic n : ℝ)) ≤ recordGeneratingProduct q n := by
  have hqpos : 0 < q := by linarith
  have hfactor (j : ℕ) :
      Real.exp ((1 - 1 / q) / ((j + 1 : ℕ) : ℝ)) ≤
        1 + (q - 1) / ((j + 1 : ℕ) : ℝ) := by
    let x : ℝ := ((j + 1 : ℕ) : ℝ)
    have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hxpos : 0 < x := by linarith
    have ht : 1 ≤ 1 + (q - 1) / x := by
      have := div_nonneg (sub_nonneg.mpr hq) hxpos.le
      linarith
    have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + (q - 1) / x)
    have hfrac : (1 - 1 / q) / x ≤ 1 - (1 + (q - 1) / x)⁻¹ := by
      have hden : 0 < x + (q - 1) := by linarith
      field_simp
      nlinarith [mul_nonneg (sq_nonneg (q - 1)) (sub_nonneg.mpr hx)]
    exact (Real.exp_le_exp.mpr (hfrac.trans hlog)).trans_eq
      (Real.exp_log (by linarith))
  calc
    Real.exp ((1 - 1 / q) * (harmonic n : ℝ)) =
        ∏ j ∈ Finset.range n, Real.exp ((1 - 1 / q) / ((j + 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum, div_eq_mul_inv]
    _ ≤ recordGeneratingProduct q n := by
      apply Finset.prod_le_prod
      · intro j _; exact (Real.exp_pos _).le
      · intro j _; exact hfactor j

end Erdos1164
