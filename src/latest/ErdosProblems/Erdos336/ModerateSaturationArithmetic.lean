import ErdosProblems.Erdos336.DoubleSaturationDefect

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- The exact rectifiable `3n-3` threshold survives any saturation for which
the double-set deficiency is no larger than the original-set deficiency. -/
theorem three_minus_three_survives_balanced_saturation
    {n a aSat d dSat : ℕ} (hn : 2 ≤ n)
    (ha : a ≤ aSat) (hd : d ≤ dSat)
    (hbalance : dSat - d ≤ aSat - a)
    (hsmall : n * d < 3 * (n - 1) * a) :
    n * dSat < 3 * (n - 1) * aSat ∧
      dSat - aSat ≤ d - a := by
  let k := aSat - a
  have haeq : aSat = a + k := by omega
  have hdle : dSat ≤ d + k := by omega
  have hncoef : n ≤ 3 * (n - 1) := by omega
  have hnk : n * k ≤ (3 * (n - 1)) * k :=
    Nat.mul_le_mul_right k hncoef
  have hthreshold : n * dSat < 3 * (n - 1) * aSat := by
    calc
      n * dSat ≤ n * (d + k) := Nat.mul_le_mul_left n hdle
      _ = n * d + n * k := by ring
      _ < 3 * (n - 1) * a + n * k := Nat.add_lt_add_right hsmall _
      _ ≤ 3 * (n - 1) * a + (3 * (n - 1)) * k :=
        Nat.add_le_add_left hnk _
      _ = 3 * (n - 1) * aSat := by rw [haeq]; ring
  exact ⟨hthreshold, by omega⟩

/-- Finset specialization: saturation by a subgroup preserves the
`3(1-1/n)` threshold whenever the double-saturation holes are bounded by the
original saturation holes. -/
theorem three_minus_three_card_survives_balanced_saturation
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n : ℕ) (hn : 2 ≤ n) (A D H : Finset G)
    (hA : A ⊆ A + H) (hD : D ⊆ D + H)
    (hbalance : (D + H).card - D.card ≤ (A + H).card - A.card)
    (hsmall : n * D.card < 3 * (n - 1) * A.card) :
    n * (D + H).card < 3 * (n - 1) * (A + H).card ∧
      (D + H).card - (A + H).card ≤ D.card - A.card := by
  exact three_minus_three_survives_balanced_saturation hn
    (Finset.card_le_card hA) (Finset.card_le_card hD) hbalance hsmall

/-- In particular, a subgroup saturation with fewer than one fibre of holes
preserves the moderate-torsion threshold and does not increase doubling
defect. -/
theorem three_minus_three_survives_small_defect_subgroup_saturation
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (n : ℕ) (hn : 2 ≤ n) (K : AddSubgroup G)
    (A : Finset G) (hAne : A.Nonempty)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    (hsmall : n * (A + A).card < 3 * (n - 1) * A.card) :
    n * ((A + A) + addSubgroupFinset K).card <
        3 * (n - 1) * (A + addSubgroupFinset K).card ∧
      ((A + A) + addSubgroupFinset K).card -
          (A + addSubgroupFinset K).card ≤
        (A + A).card - A.card := by
  let H := addSubgroupFinset K
  have hzero : 0 ∈ H := by simp [H]
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hDsub : A + A ⊆ (A + A) + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hbalance := double_saturation_defect_le K A hAne hdefect
  exact three_minus_three_card_survives_balanced_saturation n hn
    A (A + A) H hAsub hDsub (by simpa [H] using hbalance) hsmall

end Erdos336
