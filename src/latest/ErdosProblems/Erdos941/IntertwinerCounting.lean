import ErdosProblems.Erdos941.IntegralIntertwiners
import ErdosProblems.Erdos941.BinaryLatticeCount

/-! # Counting integral intertwiners with a uniform leading coefficient -/

namespace Erdos941

open scoped Quaternion

noncomputable def intertwinerCoefficients {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w))
    (q : integralIntertwiners v w) : ℤ × ℤ := (b.repr q 0, b.repr q 1)

theorem intertwinerCoefficients_injective {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    Function.Injective (intertwinerCoefficients b) := by
  intro q r h
  apply b.repr.injective
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem intertwiner_norm_coefficients {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) (q : integralIntertwiners v w) :
    (hurwitzNorm q : ℚ) = (b.repr q 0 : ℚ) ^ 2 * (hurwitzNorm (b 0) : ℚ) +
      2 * (b.repr q 0 : ℚ) * (b.repr q 1 : ℚ) *
        (star ((b 0 : hurwitzOrder) : ℍ[ℚ]) * ((b 1 : hurwitzOrder) : ℍ[ℚ])).re +
      (b.repr q 1 : ℚ) ^ 2 * (hurwitzNorm (b 1) : ℚ) := by
  have hq : (b.repr q 0) • b 0 + (b.repr q 1) • b 1 = q := by
    simpa only [Fin.sum_univ_two] using b.sum_repr q
  have hq' : (b.repr q 0) • (b 0 : hurwitzOrder) +
      (b.repr q 1) • (b 1 : hurwitzOrder) = (q : hurwitzOrder) := congrArg Subtype.val hq
  rw [← hq']
  exact hurwitzNorm_linear_combination _ _ _ _

theorem integralIntertwiner_basis_count {v w : Triple}
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (integralIntertwiners v w),
      (∀ q ∈ s, (hurwitzNorm q : ℝ) ≤ X) →
      (s.card : ℝ) ≤ 4 * X / Real.sqrt (hurwitzGram (b 0) (b 1) : ℝ) + K * Real.sqrt X + 1 := by
  classical
  let A : ℝ := hurwitzNorm (b 0)
  let B : ℝ := ((star ((b 0 : hurwitzOrder) : ℍ[ℚ]) * ((b 1 : hurwitzOrder) : ℍ[ℚ])).re : ℝ)
  let C : ℝ := hurwitzNorm (b 1)
  have hA : 0 < A := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    intro h
    have hh := (hurwitzNorm_eq_zero (b 0)).mp h
    exact b.ne_zero 0 (Subtype.ext hh)
  have hD : A * C - B ^ 2 = (hurwitzGram (b 0) (b 1) : ℝ) := by
    dsimp [A, B, C, hurwitzGram]
    push_cast
    rw [← hurwitzNorm_cast, ← hurwitzNorm_cast]
    norm_cast
  have hDpos : 0 < A * C - B ^ 2 := by
    rw [hD]
    exact_mod_cast integralIntertwinerBasis_gram_pos b
  obtain ⟨K, hK, hcount⟩ := binary_lattice_count hA hDpos
  refine ⟨K, hK, ?_⟩
  intro X hX s hs
  have hbound := hcount X hX (s.image (intertwinerCoefficients b)) (by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    have hnorm := congrArg (fun z : ℚ => (z : ℝ)) (intertwiner_norm_coefficients b q)
    push_cast at hnorm
    have heq : A * ((intertwinerCoefficients b q).1 : ℝ) ^ 2 +
        2 * B * ((intertwinerCoefficients b q).1 : ℝ) * ((intertwinerCoefficients b q).2 : ℝ) +
        C * ((intertwinerCoefficients b q).2 : ℝ) ^ 2 = (hurwitzNorm q : ℝ) := by
      dsimp [A, B, C, intertwinerCoefficients]
      linear_combination -hnorm
    rw [heq]
    exact hs q hq)
  rw [Finset.card_image_of_injective s (intertwinerCoefficients_injective b), hD] at hbound
  exact hbound

theorem integralIntertwiner_count {v w : Triple} {n : ℕ} (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v)
    (b : Module.Basis (Fin 2) ℤ (integralIntertwiners v w)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (integralIntertwiners v w),
      (∀ q ∈ s, (hurwitzNorm q : ℝ) ≤ X) →
      (s.card : ℝ) ≤ 8 * X / Real.sqrt (n : ℝ) + K * Real.sqrt X + 1 := by
  obtain ⟨K, hK, hcount⟩ := integralIntertwiner_basis_count b
  refine ⟨K, hK, ?_⟩
  intro X hX s hs
  have hD : (n : ℝ) / 4 ≤ (hurwitzGram (b 0) (b 1) : ℝ) := by
    have hh : (((n : ℚ) / 4 : ℚ) : ℝ) ≤ (hurwitzGram (b 0) (b 1) : ℝ) :=
      Rat.cast_le.mpr (integralIntertwinerBasis_gram_lower hv hp b)
    simpa using hh
  have hsD := Real.sqrt_le_sqrt hD
  rw [Real.sqrt_div (Nat.cast_nonneg n) 4, show Real.sqrt (4 : ℝ) = 2 by norm_num] at hsD
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hsG : 0 < Real.sqrt (hurwitzGram (b 0) (b 1) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast integralIntertwinerBasis_gram_pos b
  have hlead : 4 * X / Real.sqrt (hurwitzGram (b 0) (b 1) : ℝ) ≤
      8 * X / Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ hsG hsN).mpr
    nlinarith
  exact (hcount X hX s hs).trans (by linarith)

theorem exists_integralIntertwiner_count {v : Triple} {n : ℕ} (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) (w : Triple) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (integralIntertwiners v w),
      (∀ q ∈ s, (hurwitzNorm q : ℝ) ≤ X) →
      (s.card : ℝ) ≤ 8 * X / Real.sqrt (n : ℝ) + K * Real.sqrt X + 1 := by
  classical
  by_cases hex : ∃ q : integralIntertwiners v w, q ≠ 0
  · obtain ⟨q, hq0⟩ := hex
    letI : Fact (0 < n) := ⟨hn⟩
    have hq0' : (q : hurwitzOrder) ≠ 0 := fun h => hq0 (Subtype.ext h)
    exact integralIntertwiner_count hn hv hp
      (integralIntertwinerBasis hv hp.ne_zero hq0' q.property)
  · refine ⟨0, le_rfl, ?_⟩
    intro X hX s hs
    have hsub : s ⊆ {0} := by
      intro q _
      apply Finset.mem_singleton.mpr
      by_contra h
      exact hex ⟨q, h⟩
    have hcard : s.card ≤ 1 := by simpa using Finset.card_le_card hsub
    have hcardR : (s.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have hnonneg : 0 ≤ 8 * X / Real.sqrt (n : ℝ) := by positivity
    simpa only [zero_mul, add_zero] using hcardR.trans (by linarith)

end Erdos941
