import ErdosProblems.Erdos140.Chang
import ErdosProblems.Erdos140.RegularBohr

/-!
# Large-spectrum characters on a regular Bohr set

A character in the large spectrum of a regular Bohr carrier is almost
constant on a sufficiently small dilate.  The proof keeps the constants
explicit: the exact Fourier translation identity converts the phase error
into the counting-measure `L¹` translation error for the normalized
indicator, to which rank regularity applies.
-/

open AddChar Finset
open scoped BigOperators NNReal

namespace Erdos140

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [normalizedIndicator, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

private lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
      ∑ x : G,
        ((normalizedIndicator A x - normalizedIndicator A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (normalizedIndicator A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (normalizedIndicator A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (normalizedIndicator A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (normalizedIndicator A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

/-- A character in the `eta`-large spectrum of a rank-regular Bohr carrier
has phase variation at most `200 * max(rank,1) * sigma / eta` on the
`sigma`-dilate. -/
theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : BohrData G} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar G ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : G} (ht : t ∈ (C.dilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : G, (normalizedIndicator C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : G,
          ((normalizedIndicator C.carrier x -
              normalizedIndicator C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : G,
            ‖((normalizedIndicator C.carrier x -
                normalizedIndicator C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := hphase
      _ ≤ 200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

/-- Threshold-`1/2` specialization of
`norm_one_sub_le_of_mem_largeSpectrum`. -/
theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : BohrData G} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar G ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : G} (ht : t ∈ (C.dilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end Erdos140

#print axioms Erdos140.norm_one_sub_le_of_mem_largeSpectrum
#print axioms Erdos140.norm_one_sub_le_of_mem_largeSpectrum_half
