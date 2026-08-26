import ErdosProblems.Erdos117.ClassTwoCoverBound
import ErdosProblems.Erdos117.DerivedCentralizer
import ErdosProblems.Erdos117.CosetExtension

/-!
# The finite-group cover bound before the BFC size estimate

This is an unconditional cover construction for arbitrary finite groups.
Its explicit error depends on `clog 2 |G'|`. The final proof in `SharpUpper`
uses a different class-two reduction and avoids that parameter entirely.
-/

namespace Erdos117

/-- The polynomial cover-extension multiplier already proved for every
subgroup of a group with clique bound `n`. -/
def coverExtensionPolynomial (n : ℕ) : ℕ := 2 * (2 * n) ^ 2 * ((2 * n) ^ 2 * n + 1)

/-- The sharp leading term survives the passage from `C_G(G')` to `G`.
The remaining derived-order parameter is explicit, not assumed small. -/
theorem exists_finite_cover_bound {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : NoncommutingBound G n) :
    let q := Nat.clog 2 (Nat.card (commutator G))
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    ∃ K : ℕ, HasAbelianCover G K ∧
      Real.log K ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n +
        (q : ℝ) ^ 2 * Real.log 2 + Real.log (coverExtensionPolynomial n) := by
  let q := Nat.clog 2 (Nat.card (commutator G))
  let ell := Nat.clog 2 ((2 * n) ^ 2)
  let F : Subgroup G := Subgroup.centralizer (commutator G : Set G)
  let C := coverExtensionPolynomial n
  have hsize : Nat.card (commutator F) ≤ 2 ^ q :=
    (commutator_subgroup_card_le F).trans (Nat.le_pow_clog (by decide) _)
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_bound_of_card_le
    commutator_centralizer_derived_le_center (hn.subgroup F) hsize
  have hindex : F.index ≤ 2 ^ (q ^ 2) := centralizerIndex_le_two_pow_clog_sq (commutator G)
  have hcover : HasAbelianCover G (2 ^ (q ^ 2) * (C * k)) :=
    hasAbelianCover_mono (hasAbelianCover_extension_polynomial F hn hk)
      (Nat.mul_le_mul_right _ hindex)
  have hn1 := one_le_of_noncommutingBound hn
  have hC : 0 < C := by dsimp [C, coverExtensionPolynomial]; positivity
  have hk1 := one_le_of_noncommutingBound (noncommutingBound_of_abelianCover hk)
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  refine ⟨2 ^ (q ^ 2) * (C * k), hcover, ?_⟩
  change Real.log (2 ^ (q ^ 2) * (C * k) : ℕ) ≤ Real.log 2 / 2 * n +
    96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
    (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n +
    (q : ℝ) ^ 2 * Real.log 2 + Real.log C
  have hcost : Real.log (2 ^ (q ^ 2) * (C * k) : ℕ) =
      (q : ℝ) ^ 2 * Real.log 2 + Real.log C + Real.log k := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (pow_ne_zero _ (show (2 : ℝ) ≠ 0 by norm_num)) (mul_ne_zero hC' hk'),
      Real.log_mul hC' hk', Real.log_pow, Nat.cast_pow]
    ring
  rw [hcost]
  change Real.log k ≤ Real.log 2 / 2 * n +
    96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
    (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n at hlog
  linarith only [hlog]

end Erdos117
