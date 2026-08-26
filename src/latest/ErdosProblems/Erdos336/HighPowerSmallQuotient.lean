import Mathlib
import ErdosProblems.Erdos336.DyadicSmallDoubling

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# High exact powers cannot occupy only a few points of a larger quotient
-/

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- Once two consecutive exact powers agree, all later powers agree. -/
theorem exactPower_stable_of_succ_eq {D : Set G} {k : ℕ}
    (hstable : ExactPower D (k + 1) = ExactPower D k) :
    ∀ r : ℕ, ExactPower D (k + r) = ExactPower D k := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        ExactPower D (k + (r + 1)) =
            ExactPower D (k + r) + ExactPower D 1 := by
          simpa [Nat.add_assoc] using (exactPower_add D (k + r) 1).symm
        _ = ExactPower D k + ExactPower D 1 := by rw [ih]
        _ = ExactPower D (k + 1) := exactPower_add D k 1
        _ = ExactPower D k := hstable

/-- For a primitive set containing zero, exact powers grow strictly until they
are the whole group. -/
theorem exactPower_ssubset_succ_of_not_full
    {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {k : ℕ} (hk : ExactPower D k ≠ Set.univ) :
    ExactPower D k ⊂ ExactPower D (k + 1) := by
  refine ⟨exactPower_mono_of_zero hzero (by omega), ?_⟩
  intro heq
  have hstable : ExactPower D (k + 1) = ExactPower D k :=
    Set.Subset.antisymm heq (exactPower_mono_of_zero hzero (by omega))
  obtain ⟨q, hq⟩ := hexact
  by_cases hkq : k ≤ q
  · have hqk := exactPower_stable_of_succ_eq hstable (q - k)
    have hsum : k + (q - k) = q := Nat.add_sub_of_le hkq
    rw [hsum, hq] at hqk
    exact hk hqk.symm
  · have hsub : ExactPower D q ⊆ ExactPower D k :=
      exactPower_mono_of_zero hzero (by omega)
    have hfull : ExactPower D k = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      simpa [hq] using hsub
    exact hk hfull

/-- Before saturation, the `k`-th exact power has at least `k+1` elements. -/
theorem add_one_le_ncard_exactPower_of_not_full
    [Fintype G] {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    (k : ℕ) (hk : ExactPower D k ≠ Set.univ) :
    k + 1 ≤ (ExactPower D k).ncard := by
  induction k with
  | zero =>
      have hmem : 0 ∈ ExactPower D 0 := by
        exact ⟨[], rfl, by simp, by simp⟩
      have hpos : 0 < (ExactPower D 0).ncard := by
        rw [Set.ncard_pos]
        exact ⟨0, hmem⟩
      omega
  | succ k ih =>
      have hkprev : ExactPower D k ≠ Set.univ := by
        intro hfull
        apply hk
        apply Set.eq_univ_of_univ_subset
        have hsub := exactPower_mono_of_zero hzero (show k ≤ k + 1 by omega)
        simpa [hfull] using hsub
      have hgrow := exactPower_ssubset_succ_of_not_full hzero hexact hkprev
      have hcardlt : (ExactPower D k).ncard <
          (ExactPower D (k + 1)).ncard := by
        exact Set.ncard_lt_ncard hgrow
      have hlow := ih hkprev
      omega

/-- In particular, if a primitive `t`-th power with `t≥3` has at most three
points, then the entire ambient finite group has at most three points. -/
theorem card_le_three_of_highPower_ncard_le_three
    [Fintype G] {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {t : ℕ} (ht : 3 ≤ t)
    (hsmall : (ExactPower D t).ncard ≤ 3) :
    Fintype.card G ≤ 3 := by
  by_cases hfull : ExactPower D t = Set.univ
  · simpa [hfull] using hsmall
  · have hlow := add_one_le_ncard_exactPower_of_not_full hzero hexact t hfull
    omega

end Erdos336
