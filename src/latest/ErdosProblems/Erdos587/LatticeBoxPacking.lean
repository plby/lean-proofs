import ErdosProblems.Erdos587.CosetPacking

/-! A dense subgroup intersection with a wide box forces short coordinate periods. -/

open scoped BigOperators

namespace Erdos587.CFP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBox (lo : ι → ℤ) (w : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun i => Finset.Ico (lo i) (lo i + (w i : ℤ))

@[simp] theorem mem_integerBox {lo : ι → ℤ} {w : ι → ℕ} {x : ι → ℤ} :
    x ∈ integerBox lo w ↔ ∀ i, lo i ≤ x i ∧ x i < lo i + (w i : ℤ) := by
  simp only [integerBox, Fintype.mem_piFinset, Finset.mem_Ico]

@[simp] theorem card_integerBox (lo : ι → ℤ) (w : ι → ℕ) :
    (integerBox lo w).card = ∏ i, w i := by
  simp [integerBox, Fintype.card_piFinset, Int.card_Ico]

def coordinateUnit (j : ι) : ι → ℤ := Pi.single j 1

theorem translate_coordinate_mem_expandedBox {lo : ι → ℤ} {w : ι → ℕ}
    {x : ι → ℤ} (hx : x ∈ integerBox lo w) (j : ι) {M n : ℕ} (hn : n < M) :
    x + n • coordinateUnit j ∈ integerBox lo (Function.update w j (w j + M)) := by
  rw [mem_integerBox] at hx ⊢
  intro i
  have hxi := hx i
  by_cases hij : i = j
  · subst i
    have hnR : (n : ℤ) < M := by exact_mod_cast hn
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have htarget : lo j ≤ x j + (n : ℤ) ∧
        x j + (n : ℤ) < lo j + ((w j : ℤ) + M) := by omega
    simpa [coordinateUnit, nsmul_eq_mul] using htarget
  · simpa [Pi.add_apply, Pi.smul_apply, coordinateUnit, hij, Ne.symm hij] using hxi

theorem card_expandedBox_le_twice {lo : ι → ℤ} {w : ι → ℕ} (j : ι) {M : ℕ}
    (hM : M ≤ w j) :
    (integerBox lo (Function.update w j (w j + M))).card ≤ 2 * (integerBox lo w).card := by
  rw [card_integerBox, card_integerBox]
  have hprod : ∏ i, Function.update w j (w j + M) i =
      (w j + M) * ∏ i ∈ Finset.univ.erase j, w i := by
    rw [← Finset.mul_prod_erase Finset.univ (Function.update w j (w j + M))
      (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
  have horig := Finset.mul_prod_erase Finset.univ w (Finset.mem_univ j)
  rw [hprod, ← horig]
  have hh := Nat.mul_le_mul_right (∏ i ∈ Finset.univ.erase j, w i)
    (show w j + M ≤ 2 * w j by omega)
  nlinarith

/-- The period bound follows from disjoint cosets, not from coordinate projections. -/
theorem exists_short_coordinate_period {Γ : AddSubgroup (ι → ℤ)}
    {S : Finset (ι → ℤ)} {lo : ι → ℤ} {w : ι → ℕ} {M : ℕ}
    (hS : ∀ x ∈ S, x ∈ Γ) (hbox : S ⊆ integerBox lo w)
    (hdense : 2 * (integerBox lo w).card < S.card * M)
    (j : ι) (hwidth : M ≤ w j) :
    ∃ k : ℕ, 0 < k ∧ k < M ∧ k • coordinateUnit j ∈ Γ := by
  apply exists_short_period_of_dense_translates hS
    (V := integerBox lo (Function.update w j (w j + M)))
  · intro x hx n hn
    exact translate_coordinate_mem_expandedBox (hbox hx) j hn
  · exact (card_expandedBox_le_twice j hwidth).trans_lt hdense

end Erdos587.CFP
