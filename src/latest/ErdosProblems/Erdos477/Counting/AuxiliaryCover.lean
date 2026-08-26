/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite covers by congruence-class auxiliary polynomials, with quantitative degrees.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CongruenceAuxiliary
import ErdosProblems.Erdos477.Counting.ResidueImage

namespace Erdos477.Counting

lemma prime_power_depth (p : ℕ) (hp : p.Prime) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ r : ℕ, (p : ℝ) ^ r ≤ Q ∧ Q < (p : ℝ) ^ (r + 1) ∧
      (r : ℝ) ≤ Real.log Q / Real.log p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near hQ hp1
  refine ⟨r, hr, hr', ?_⟩
  apply (le_div_iff₀ (Real.log_pos hp1)).mpr
  have h := Real.log_le_log (pow_pos hp0 r) hr
  simpa only [Real.log_pow] using h

/-- Each occupied prime-power class is contained in one auxiliary hypersurface,
and the degree decreases by the modulus. -/
theorem exists_sextic_class_cover (c : ℤ) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6) (hpc : ¬ (p : ℤ) ∣ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : ℝ) (r : ℕ), 1 ≤ B →
      (p : ℝ) ^ r ≤ B ^ ((41 : ℝ) / 100) →
      ∀ a ∈ sexticResidueImage p r (sexticBox c B),
      ∃ P : MvPolynomial (Fin 3) ℤ, P ≠ 0 ∧ P.degreeOf 2 ≤ 5 ∧
        (P.totalDegree : ℝ) ≤ K * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ r ∧
        ¬ sexticSurface c ∣ P ∧
        ∀ z ∈ sexticBox c B, (fun k => (z k : ZMod (p ^ r))) = a →
          MvPolynomial.eval z P = 0 := by
  classical
  obtain ⟨K, hK, haux⟩ := exists_sextic_congruence_auxiliary c hc p h6 hpc
  refine ⟨K, hK, ?_⟩
  intro B r hB hr a ha
  obtain ⟨center, hcenter, hca⟩ := Finset.mem_image.mp ha
  have hcenter' := (mem_sexticBox c B center).mp hcenter
  obtain ⟨P, hP, hlast, hdeg, hdiv, heval⟩ := haux B r hB hr center hcenter'.1
  refine ⟨P, hP, hlast, hdeg, hdiv, ?_⟩
  intro z hz hza
  have hz' := (mem_sexticBox c B z).mp hz
  apply heval z hz'.1 hz'.2
  intro k
  have hcast : (center k : ZMod (p ^ r)) = (z k : ZMod (p ^ r)) :=
    congrFun (hca.trans hza.symm) k
  simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast

/-- There is an unconditional finite sequence of covers down to bounded
auxiliary degree. This result does not yet count the points on intersections. -/
theorem exists_sextic_refinement_covers (c : ℤ) (hc : c ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B → ∃ r : ℕ,
      (p : ℝ) ^ r ≤ B ^ ((41 : ℝ) / 100) ∧
      B ^ ((41 : ℝ) / 100) < (p : ℝ) ^ (r + 1) ∧
      (r : ℝ) ≤ (41 : ℝ) / 100 * Real.log B / Real.log p ∧
      (∀ t : ℕ, t ≤ r →
        (sexticResidueImage p t (sexticBox c B)).card ≤ 3 * p ^ 3 * (p ^ t) ^ 2 ∧
        ∀ a ∈ sexticResidueImage p t (sexticBox c B),
        ∃ P : MvPolynomial (Fin 3) ℤ, P ≠ 0 ∧ P.degreeOf 2 ≤ 5 ∧
          (P.totalDegree : ℝ) ≤ K * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ t ∧
          ¬ sexticSurface c ∣ P ∧
          ∀ z ∈ sexticBox c B, (fun k => (z k : ZMod (p ^ t))) = a →
            MvPolynomial.eval z P = 0) ∧
      K * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ r < K * p := by
  obtain ⟨p, hp, h6, hpc⟩ := exists_good_sextic_prime c hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hcover⟩ := exists_sextic_class_cover c hc p h6 hpc
  refine ⟨p, hp, K, hK, ?_⟩
  intro B hB
  have hB0 : 0 < B := by linarith
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  obtain ⟨r, hr, hr', hlog⟩ := prime_power_depth p hp (B ^ ((41 : ℝ) / 100))
    (Real.one_le_rpow hB (by norm_num))
  refine ⟨r, hr, hr', ?_, ?_, ?_⟩
  · rwa [Real.log_rpow hB0] at hlog
  · intro t ht
    refine ⟨card_sexticResidueImage_le p h6 t c hpc (sexticBox c B)
      (fun z hz => ((mem_sexticBox c B z).mp hz).1), ?_⟩
    exact hcover B t hB ((pow_le_pow_right₀ hp1 ht).trans hr)
  · apply (div_lt_iff₀ (pow_pos hp0 r)).mpr
    have h := mul_lt_mul_of_pos_left hr' hK
    rw [pow_succ] at h
    nlinarith only [h]

#print axioms exists_sextic_refinement_covers
-- 'Erdos477.Counting.exists_sextic_refinement_covers' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
