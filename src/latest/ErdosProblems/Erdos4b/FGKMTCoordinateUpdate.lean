/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileVariation
import ErdosProblems.Erdos4b.FGKMTMajorantEnergy

/-!
# Arbitrary-coordinate changes and majorant monotonicity

The coordinate bound is transported by separating any selected index
with `Fin.succAbove`. Each genuine one-long-factor tensor, and hence
their sum, is nonincreasing on the nonnegative orthant.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem oneLongTensor_antitone_on_orthant {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin j) {t u : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) (htu : ∀ q, t q ≤ u q) :
    oneLongTensor k j i u ≤ oneLongTensor k j i t := by
  have hb := profile_scales_bounds hk hlog
  unfold oneLongTensor
  apply Finset.prod_le_prod
  · intro q _hq
    exact oneLongFactor_nonneg k i q (u q)
  · intro q _hq
    unfold oneLongFactor
    split_ifs
    · exact sieveFactor_antitoneOn (zero_le_one.trans hb.1) (by norm_num)
        (ht q) ((ht q).trans (htu q)) (htu q)
    · exact sieveFactor_antitoneOn (zero_le_one.trans hb.1) hb.2.1
        (ht q) ((ht q).trans (htu q)) (htu q)

theorem sieveProfileMajorant_antitone_on_orthant {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {t u : Fin j → ℝ}
    (ht : ∀ q, 0 ≤ t q) (htu : ∀ q, t q ≤ u q) :
    sieveProfileMajorant k j u ≤ sieveProfileMajorant k j t :=
  Finset.sum_le_sum fun i _hi => oneLongTensor_antitone_on_orthant hk hlog i ht htu

theorem sieveProfile_update_eq_cons (k j : ℕ) (i : Fin (j + 1))
    (t : Fin (j + 1) → ℝ) (y : ℝ) :
    sieveProfile k (j + 1) (Function.update t i y) =
      sieveProfile k (j + 1) (Fin.cons y (fun q => t (i.succAbove q))) := by
  classical
  unfold sieveProfile
  rw [Fin.sum_univ_succAbove _ i, Fin.prod_univ_succAbove _ i]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _),
    Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem oneLongTensor_eq_succAbove (k j : ℕ) (i : Fin (j + 1))
    (t : Fin (j + 1) → ℝ) :
    oneLongTensor k (j + 1) i t =
      dimensionLongFactor k (t i) *
        ∏ q : Fin j, dimensionProfileFactor k (t (i.succAbove q)) := by
  classical
  rw [oneLongTensor, Fin.prod_univ_succAbove _ i]
  simp [oneLongFactor, Fin.succAbove_ne]

theorem exists_sieveProfile_update_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (i : Fin j) (t : Fin j → ℝ) (y : ℝ), 0 ≤ t i → t i ≤ y →
        |sieveProfile k j (Function.update t i y) - sieveProfile k j t| ≤
          (C * sieveProfileScale k * oneLongTensor k j i t) * (y - t i) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_coordinate_variation_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog j
  cases j with
  | zero => intro i; exact Fin.elim0 i
  | succ j =>
    intro i t y hti hity
    have hself : sieveProfile k (j + 1) t =
        sieveProfile k (j + 1) (Fin.cons (t i) (fun q => t (i.succAbove q))) := by
      simpa only [Function.update_eq_self] using sieveProfile_update_eq_cons k j i t (t i)
    rw [sieveProfile_update_eq_cons, hself, oneLongTensor_eq_succAbove]
    convert hbound hk hlog j (fun q => t (i.succAbove q)) (t i) y hti hity using 1
    ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveProfileMajorant_antitone_on_orthant
#print axioms Erdos4b.FGKMT.exists_sieveProfile_update_variation_bound
