import ErdosProblems.Erdos587.LatticeBoxPacking

/-! Finite quotient representatives and the corrected lattice index estimate. -/

open scoped BigOperators

namespace Erdos587.CFP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateRemainder (k : ι → ℕ) (x : ι → ℤ) : ι → ℤ :=
  fun i => x i % (k i : ℤ)

theorem coordinateRemainder_mem_box (k : ι → ℕ) (hk : ∀ i, 0 < k i) (x : ι → ℤ) :
    coordinateRemainder k x ∈ integerBox 0 k := by
  rw [mem_integerBox]
  intro i
  have hki : (0 : ℤ) < k i := by exact_mod_cast hk i
  exact ⟨Int.emod_nonneg _ hki.ne',
    by simpa [coordinateRemainder] using Int.emod_lt_of_pos (x i) hki⟩

theorem sub_coordinateRemainder_mem {Γ : AddSubgroup (ι → ℤ)} {k : ι → ℕ}
    (hperiod : ∀ i, k i • coordinateUnit i ∈ Γ) (x : ι → ℤ) :
    x - coordinateRemainder k x ∈ Γ := by
  have heq : ∑ i, (x i / (k i : ℤ)) • (k i • coordinateUnit i) =
      x - coordinateRemainder k x := by
    ext j
    simp only [Finset.sum_apply, Pi.sub_apply, coordinateRemainder]
    simp [coordinateUnit, nsmul_eq_mul, zsmul_eq_mul, Pi.single_apply]
    have hh := Int.emod_add_mul_ediv (x j) (k j : ℤ)
    nlinarith
  rw [← heq]
  exact Γ.sum_mem (fun i _hi => Γ.zsmul_mem (hperiod i) (x i / (k i : ℤ)))

theorem coordinate_box_surjects_quotient {Γ : AddSubgroup (ι → ℤ)} {k : ι → ℕ}
    (hk : ∀ i, 0 < k i) (hperiod : ∀ i, k i • coordinateUnit i ∈ Γ) :
    Function.Surjective (fun r : integerBox (0 : ι → ℤ) k =>
      QuotientAddGroup.mk' Γ r.val) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Γ q
  refine ⟨⟨coordinateRemainder k x, coordinateRemainder_mem_box k hk x⟩, ?_⟩
  apply QuotientAddGroup.eq.mpr
  simpa only [sub_eq_add_neg, add_comm] using sub_coordinateRemainder_mem hperiod x

theorem finiteIndex_of_coordinate_periods {Γ : AddSubgroup (ι → ℤ)} {k : ι → ℕ}
    (hk : ∀ i, 0 < k i) (hperiod : ∀ i, k i • coordinateUnit i ∈ Γ) :
    Γ.FiniteIndex := by
  have hsurj := coordinate_box_surjects_quotient hk hperiod
  haveI : Finite ((ι → ℤ) ⧸ Γ) := Finite.of_surjective _ hsurj
  exact AddSubgroup.finiteIndex_of_finite_quotient

theorem index_le_product_of_coordinate_periods {Γ : AddSubgroup (ι → ℤ)} {k : ι → ℕ}
    (hk : ∀ i, 0 < k i) (hperiod : ∀ i, k i • coordinateUnit i ∈ Γ) :
    Γ.index ≤ ∏ i, k i := by
  have hh := Nat.card_le_card_of_surjective _ (coordinate_box_surjects_quotient hk hperiod)
  simpa only [AddSubgroup.index, Nat.card_eq_finsetCard, card_integerBox] using hh

/-- Constant density in a sufficiently wide box gives a scale-independent index bound. -/
theorem finiteIndex_and_index_le_of_dense_box {Γ : AddSubgroup (ι → ℤ)}
    {S : Finset (ι → ℤ)} {lo : ι → ℤ} {w : ι → ℕ} {M : ℕ}
    (hS : ∀ x ∈ S, x ∈ Γ) (hbox : S ⊆ integerBox lo w)
    (hdense : 2 * (integerBox lo w).card < S.card * M)
    (hwidth : ∀ i, M ≤ w i) :
    Γ.FiniteIndex ∧ Γ.index ≤ M ^ Fintype.card ι := by
  classical
  choose k hkpos hkM hkperiod using fun i =>
    exists_short_coordinate_period hS hbox hdense i (hwidth i)
  refine ⟨finiteIndex_of_coordinate_periods hkpos hkperiod, ?_⟩
  calc
    Γ.index ≤ ∏ i, k i := index_le_product_of_coordinate_periods hkpos hkperiod
    _ ≤ ∏ _i : ι, M := Finset.prod_le_prod (fun _i _hi => Nat.zero_le _)
      (fun i _hi => (hkM i).le)
    _ = M ^ Fintype.card ι := by simp

end Erdos587.CFP
