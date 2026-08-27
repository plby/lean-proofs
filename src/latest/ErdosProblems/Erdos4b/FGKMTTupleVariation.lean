/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoordinateUpdate

/-!
# Finite-coordinate telescoping and common-lower-tuple variation

The majorant is always evaluated at a common lower tuple. This is the
tuple remaining after the moved primes are removed from both endpoint
assignments; no comparison with endpoint majorants is assumed.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem abs_image_sub_le_sum_of_between_updates {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : (ι → ℝ) → ℝ) (t u : ι → ℝ) (B : ι → ℝ)
    (htu : ∀ i, t i ≤ u i)
    (hstep : ∀ v : ι → ℝ, (∀ i, t i ≤ v i) → (∀ i, v i ≤ u i) →
      ∀ i, v i = t i → |f (Function.update v i (u i)) - f v| ≤ B i) :
    |f u - f t| ≤ ∑ i, B i := by
  classical
  let v (s : Finset ι) (q : ι) := if q ∈ s then u q else t q
  have hs (s : Finset ι) : |f (v s) - f t| ≤ ∑ q ∈ s, B q := by
    induction s using Finset.induction_on with
    | empty => simp [v]
    | @insert i s hi ih =>
      have hlo (q : ι) : t q ≤ v s q := by
        dsimp only [v]
        split_ifs
        · exact htu q
        · exact le_rfl
      have hhi (q : ι) : v s q ≤ u q := by
        dsimp only [v]
        split_ifs
        · exact le_rfl
        · exact htu q
      have hinsert : v (insert i s) = Function.update (v s) i (u i) := by
        funext q
        by_cases hq : q = i
        · subst q
          simp [v]
        · simp [v, hq]
      calc
        _ ≤ |f (v (insert i s)) - f (v s)| + |f (v s) - f t| := abs_sub_le _ _ _
        _ ≤ B i + ∑ q ∈ s, B q := by
          apply add_le_add _ ih
          rw [hinsert]
          exact hstep (v s) hlo hhi i (by simp [v, hi])
        _ = _ := by rw [Finset.sum_insert hi]
  simpa only [v, Finset.mem_univ, if_true] using hs Finset.univ

theorem exists_sieveProfile_orthant_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (t u : Fin j → ℝ), (∀ i, 0 ≤ t i) → (∀ i, t i ≤ u i) →
        |sieveProfile k j u - sieveProfile k j t| ≤
          (C * sieveProfileScale k * sieveProfileMajorant k j t) * ∑ i, (u i - t i) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_update_variation_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog j t u ht htu
  have hT : 0 ≤ sieveProfileScale k := zero_le_one.trans (profile_scales_bounds hk hlog).1
  have hCT : 0 ≤ C * sieveProfileScale k := mul_nonneg hC.le hT
  have h := abs_image_sub_le_sum_of_between_updates (sieveProfile k j) t u
    (fun i => (C * sieveProfileScale k * sieveProfileMajorant k j t) * (u i - t i)) htu (by
      intro v hvlo hvhi i hi
      have hTensor : oneLongTensor k j i v ≤ sieveProfileMajorant k j t :=
        (oneLongTensor_antitone_on_orthant hk hlog i ht hvlo).trans
          (Finset.single_le_sum (fun q _hq => oneLongTensor_nonneg k j q t) (Finset.mem_univ i))
      calc
        _ ≤ (C * sieveProfileScale k * oneLongTensor k j i v) * (u i - v i) :=
          hbound hk hlog j i v (u i) ((ht i).trans (hvlo i)) (hvhi i)
        _ = (C * sieveProfileScale k * oneLongTensor k j i v) * (u i - t i) := by rw [hi]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTensor hCT)
          (sub_nonneg.mpr (htu i)))
  simpa only [Finset.mul_sum] using h

theorem exists_sieveProfile_commonBase_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (u t s : Fin j → ℝ), (∀ i, 0 ≤ u i) →
        (∀ i, u i ≤ t i) → (∀ i, u i ≤ s i) →
        |sieveProfile k j t - sieveProfile k j s| ≤
          (C * sieveProfileScale k * sieveProfileMajorant k j u) *
            ((∑ i, (t i - u i)) + ∑ i, (s i - u i)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_orthant_variation_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog j u t s hu hut hus
  calc
    _ ≤ |sieveProfile k j t - sieveProfile k j u| +
        |sieveProfile k j u - sieveProfile k j s| := abs_sub_le _ _ _
    _ = |sieveProfile k j t - sieveProfile k j u| +
        |sieveProfile k j s - sieveProfile k j u| := by
      rw [abs_sub_comm (sieveProfile k j u)]
    _ ≤ (C * sieveProfileScale k * sieveProfileMajorant k j u) * (∑ i, (t i - u i)) +
        (C * sieveProfileScale k * sieveProfileMajorant k j u) * (∑ i, (s i - u i)) :=
      add_le_add (hbound hk hlog j u t hu hut) (hbound hk hlog j u s hu hus)
    _ = _ := by ring

theorem exists_sieveProfile_reassignment_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (u t s : Fin j → ℝ) (a : ℝ), (∀ i, 0 ≤ u i) →
        (∀ i, u i ≤ t i) → (∀ i, u i ≤ s i) →
        (∑ i, (t i - u i)) ≤ a → (∑ i, (s i - u i)) ≤ a →
        |sieveProfile k j t - sieveProfile k j s| ≤
          (C * sieveProfileScale k * sieveProfileMajorant k j u) * a := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_commonBase_variation_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro k hk hlog j u t s a hu hut hus ht hs
  have hT : 0 ≤ sieveProfileScale k := zero_le_one.trans (profile_scales_bounds hk hlog).1
  have hcoef : 0 ≤ C * sieveProfileScale k * sieveProfileMajorant k j u :=
    mul_nonneg (mul_nonneg hC.le hT) (sieveProfileMajorant_nonneg k j u)
  calc
    _ ≤ (C * sieveProfileScale k * sieveProfileMajorant k j u) *
        ((∑ i, (t i - u i)) + ∑ i, (s i - u i)) := hbound hk hlog j u t s hu hut hus
    _ ≤ (C * sieveProfileScale k * sieveProfileMajorant k j u) * (a + a) :=
      mul_le_mul_of_nonneg_left (add_le_add ht hs) hcoef
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.abs_image_sub_le_sum_of_between_updates
#print axioms Erdos4b.FGKMT.exists_sieveProfile_orthant_variation_bound
#print axioms Erdos4b.FGKMT.exists_sieveProfile_commonBase_variation_bound
#print axioms Erdos4b.FGKMT.exists_sieveProfile_reassignment_variation_bound
