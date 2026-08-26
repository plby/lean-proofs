import ErdosProblems.Erdos117.CommutatorBilinear
import ErdosProblems.Erdos117.ErrorEnvelope

/-!
# The sharp upper estimate for finite groups of class at most two

The derived orders of the Sylow factors are bounded by the proved bilinear
argument. Consequently the error here depends only on the clique bound.
No general BFC derived-order theorem is used in this file.
-/

namespace Erdos117

open Filter

universe u

/-- The explicit class-two cover estimate with all structural parameters
bounded in terms of the original clique bound. -/
theorem exists_class_two_cover_clique_bound {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    let q := ell ^ 2
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := by
  classical
  apply exists_class_two_cover_bound_of_sylow_card_le hG hn
  intro p
  have : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  exact class_two_prime_derived_card_le_clique (default : Sylow p.val G).isPGroup'
    (class_two_subgroup hG (default : Sylow p.val G))
    (hn.subgroup ((default : Sylow p.val G) : Subgroup G))

theorem exists_class_two_cover_error_bound {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        finiteCoverError n ((Nat.clog 2 ((2 * n) ^ 2)) ^ 2) := by
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_clique_bound hG hn
  have hn1 := one_le_of_noncommutingBound hn
  have hn0 : 0 < n := by omega
  have hpoly : 0 < coverExtensionPolynomial n := by
    unfold coverExtensionPolynomial
    positivity
  have hlogpoly : 0 ≤ Real.log (coverExtensionPolynomial n) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_le_of_lt hpoly)
  have hextra : (0 : ℝ) ≤
      (((Nat.clog 2 ((2 * n) ^ 2)) ^ 2 : ℕ) : ℝ) ^ 2 * Real.log 2 := by positivity
  refine ⟨k, hk, ?_⟩
  unfold finiteCoverError
  linarith only [hlog, hlogpoly, hextra]

theorem exists_class_two_cover_logScale {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    let q : ℕ := 16 * logScale n ^ 2
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := by
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_clique_bound hG hn
  have hq : (Nat.clog 2 ((2 * n) ^ 2)) ^ 2 ≤ 16 * logScale n ^ 2 := by
    have h := Nat.pow_le_pow_left (conjugacy_clog_le_logScale n) 2
    nlinarith
  have hq' : (((Nat.clog 2 ((2 * n) ^ 2)) ^ 2 : ℕ) : ℝ) ≤
      (16 * logScale n ^ 2 : ℕ) := by exact_mod_cast hq
  refine ⟨k, hk, hlog.trans ?_⟩
  gcongr

/-- A uniform sharp upper estimate for every finite class-two group.
The original problem allows arbitrary groups; that further extension is
not asserted here. -/
theorem class_two_sharp_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : Type u) [Group G] [Finite G],
        commutator G ≤ Subgroup.center G → NoncommutingBound G n →
        ∃ k : ℕ, HasAbelianCover G k ∧
          Real.log k ≤ Real.log 2 / 2 * n +
            C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := by
  refine ⟨errorCoefficient 16 * (2 / Real.log 2) ^ 3, ?_, ?_⟩
  · exact mul_nonneg (errorCoefficient_nonneg _) (by positivity)
  filter_upwards [eventually_finiteCoverError_le_log 16] with n hn
  intro G _ _ hG hbound
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_error_bound hG hbound
  have hq : (Nat.clog 2 ((2 * n) ^ 2)) ^ 2 ≤ 16 * logScale n ^ 2 := by
    have h := Nat.pow_le_pow_left (conjugacy_clog_le_logScale n) 2
    nlinarith
  have herr := hn _ hq
  refine ⟨k, hk, hlog.trans ?_⟩
  simpa only [mul_assoc] using add_le_add (le_refl (Real.log 2 / 2 * n)) herr

end Erdos117
