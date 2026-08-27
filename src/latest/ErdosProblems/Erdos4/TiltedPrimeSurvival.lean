import ErdosProblems.Erdos4.TiltedBlockProbability
import ErdosProblems.Erdos4.JointSurvivalEstimate

/-!
# Uniform joint survival for prime targets

The tilted nonzero atom is at most `1 / s`. Consequently the existing
collision estimate applies with the same quantitative error, even though
the prime survival baseline differs from that of the uniform residue law.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve CollisionModuli LocalSurvivalRatios JointSurvivalEstimate

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem tilted_local_relative_error (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ) (l : P)
    (hsize : 2 * T.card ≤ ell l) :
    |(1 - ((residues ell T l).card : ℝ) * atom (ell l) ((ell l : ℝ) ^ (-τ))) /
      baseline (ell l) ((ell l : ℝ) ^ (-τ)) ^ T.card - 1| ≤ localError ell T l := by
  classical
  let a := atom (ell l) ((ell l : ℝ) ^ (-τ))
  have hs := (Fact.out : (ell l).Prime).two_le
  have hsR : (2 : ℝ) ≤ ell l := by exact_mod_cast hs
  have hpos : (0 : ℝ) < ell l := by linarith
  have ha0 : 0 ≤ a := atom_nonneg hs (rpow_tilt_pos hs τ).le
  have ha : a ≤ 1 / (ell l : ℝ) := atom_le_inv hs (rpow_tilt_pos hs τ).le (rpow_tilt_le_one hs hτ)
  have ha1 : a ≤ 1 := ha.trans ((div_le_one hpos).mpr (by linarith))
  have hcard : (residues ell T l).card ≤ T.card := Finset.card_image_le
  have hsmall : (T.card : ℝ) * a ≤ 1 / 2 := by
    calc
      _ ≤ (T.card : ℝ) * (1 / (ell l : ℝ)) :=
        mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
      _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hpos]
        have hh : (2 : ℝ) * T.card ≤ ell l := by exact_mod_cast hsize
        linarith
  rw [baseline_eq_one_sub_atom hs (rpow_tilt_pos hs τ).le]
  have hh := local_ratio_error ha0 ha1 T.card (Nat.cast_nonneg (residues ell T l).card)
    (by exact_mod_cast hcard) hsmall
  apply hh.trans
  have hquad : 2 * (T.card : ℝ) ^ 2 * a ^ 2 ≤ 2 * (T.card : ℝ) ^ 2 / (ell l : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (T.card : ℝ) ^ 2 * (1 / (ell l : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  unfold localError
  by_cases hc : l ∈ collisionPrimes ell T
  · rw [if_pos hc]
    apply add_le_add hquad
    calc
      _ ≤ 2 * (T.card : ℝ) * a := by
        gcongr
        exact sub_le_self _ (Nat.cast_nonneg _)
      _ ≤ 2 * (T.card : ℝ) * (1 / (ell l : ℝ)) := by gcongr
      _ = _ := by ring
  · rw [if_neg hc]
    have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) T := by
      by_contra h
      exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
    have heq : (residues ell T l).card = T.card := Finset.card_image_of_injOn hinj
    simpa only [heq, sub_self, mul_zero, zero_mul, add_zero] using hquad

theorem tilted_relative_error_le (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ)
    (hnonzero : ∀ n ∈ T, ∀ l, ¬ell l ∣ n) (hsize : ∀ l, 2 * T.card ≤ ell l) :
    |(sieveLaw ell τ hτ).prob (fun a => Survives ell a T) / primeSurvival ell τ ^ T.card - 1| ≤
      Real.exp (2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) * ∑ l ∈ collisionPrimes ell T, 1 / (ell l : ℝ)) - 1 := by
  have hh := product_ratio_error_le
    (fun l => 1 - ((residues ell T l).card : ℝ) * atom (ell l) ((ell l : ℝ) ^ (-τ)))
    (fun l => baseline (ell l) ((ell l : ℝ) ^ (-τ)) ^ T.card) (localError ell T)
    (fun l => tilted_local_relative_error ell τ hτ T l (hsize l)) (sum_localError ell T).le
  rw [Finset.prod_pow] at hh
  rw [sieveLaw_nonzero_set ell τ hτ T hnonzero]
  exact hh

/-- A finite quantitative version of (6.15), uniform in the coordinate primes and target set. -/
theorem tilted_uniform_relative_error_le (hinj : Function.Injective ell)
    (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ)
    (hnonzero : ∀ n ∈ T, ∀ l, ¬ell l ∣ n) (hsize : ∀ l, 2 * T.card ≤ ell l)
    {Y : ℕ} (hY : 1 ≤ Y) (hT : ∀ n ∈ T, n ≤ Y) {w : ℝ}
    (hw : 0 < w) (hlarge : ∀ l, w ≤ ell l) :
    |(sieveLaw ell τ hτ).prob (fun a => Survives ell a T) / primeSurvival ell τ ^ T.card - 1| ≤
      Real.exp (2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) ^ 3 * Real.log Y / (w * Real.log 2)) - 1 := by
  have hc := collision_reciprocal_le ell hinj T hY hT hw hlarge
  apply (tilted_relative_error_le ell τ hτ T hnonzero hsize).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * (T.card : ℝ))
  calc
    _ ≤ 2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) * ((T.card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2)) :=
      add_le_add le_rfl hh
    _ = _ := by ring

end Erdos4.Tilted
