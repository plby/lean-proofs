import ErdosProblems.Erdos788.ChosenParameterBounds
import ErdosProblems.Erdos788.SlackCondition
import ErdosProblems.Erdos788.TrevisanRaw
import ErdosProblems.Erdos788.RankPruning

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The canonical Trevisan extractor at the chosen parameters

This file discharges the pointwise numerical hypotheses of reconstruction
and rank pruning.  The eventual analytic estimates are isolated in
`ParameterRegular`; everything below is a finite construction at one `N`.
-/

namespace Erdos788

/-- The chosen dimension is nonzero at every regular parameter. -/
theorem parameterDimension_pos_of_regular {N : ℕ} (h : ParameterRegular N) :
    0 < parameterDimension N := by
  apply parameterDimension_pos
  have hN : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  exact_mod_cast hN

/-- At the chosen parameters, the dimension logarithm is no larger than the
field-size logarithm. -/
theorem log_parameterDimension_le_log_parameterPrime
    {N : ℕ} (h : ParameterRegular N) :
    Real.log (parameterDimension N : ℝ) ≤
      Real.log (parameterPrime N : ℝ) := by
  have hr := parameterDimension_pos_of_regular h
  have hrR : (0 : ℝ) < parameterDimension N := by exact_mod_cast hr
  have hlogr : Real.log (parameterDimension N : ℝ) ≤
      Real.log (Real.log (N : ℝ)) := by
    apply Real.log_le_log hrR
    exact parameterDimension_le_log h
  exact hlogr.trans (loglog_le_log_parameterPrime N)

/-- The explicit design bound and the regularity inequalities leave at least
half of `log N` for reconstruction descriptions. -/
theorem chosenDesign_entropy_log_bound
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    Real.log 128040 +
          (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) *
            Real.log 2 +
          2 * Real.log (parameterPrime N : ℝ) +
          3 * Real.log (parameterDimension N : ℝ) ≤
      (parameterDimension N : ℝ) * Real.log (parameterPrime N : ℝ) := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let r := parameterDimension N
  let p := parameterPrime N
  let D := (SuffixDesign.build C.ell r).coordCard
  let A := L * δ
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := by
    simpa [δ] using! parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := by
    simpa [δ] using! parameterRegular_correction_le_one h
  have hA : 2 ≤ A := by
    simpa [A, L, δ] using! parameterRegular_log_mul_correction h
  have hA0 : 0 ≤ A := (by linarith : (0 : ℝ) ≤ A)
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using!
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  have hpow : δ ^ 3 ≤ δ ^ 2 := by
    nlinarith [sq_nonneg δ]
  have hone_le_delta_mul_A : 1 ≤ δ * A := by
    have hmul := mul_le_mul_of_nonneg_left hpow hL.le
    have hq_le : q ≤ L * δ ^ 2 := by
      calc
        q = L * δ ^ 3 := hrel.symm
        _ ≤ L * δ ^ 2 := hmul
    dsimp [A]
    nlinarith
  have hinv_le_A : δ⁻¹ ≤ A := by
    rw [inv_le_iff_one_le_mul₀' hδ]
    simpa [mul_comm] using! hone_le_delta_mul_A
  have hpLog : Real.log (p : ℝ) ≤ 2 * δ⁻¹ := by
    have hpLog' := log_parameterPrime_le_two_div_correction h.1
      (by linarith [h.2.1]) h.2.2.1
    simpa [p, δ, div_eq_mul_inv] using! hpLog'
  have hrLog : Real.log (r : ℝ) ≤ Real.log (p : ℝ) := by
    simpa [r, p] using! log_parameterDimension_le_log_parameterPrime h
  have hlogs :
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤ 10 * A := by
    calc
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
          5 * Real.log (p : ℝ) := by linarith
      _ ≤ 10 * δ⁻¹ := by linarith
      _ ≤ 10 * A := by gcongr
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert! Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hD : (D : ℝ) ≤ 100000000 * A := by
    simpa [D, A, L, δ, r, mul_assoc] using!
      chosenDesign_coordCard_le h C
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hDterm : (D : ℝ) * Real.log 2 ≤ 100000000 * A := by
    calc
      (D : ℝ) * Real.log 2 ≤ (100000000 * A) * 1 :=
        mul_le_mul hD hlog2 hlog2nonneg (by positivity)
      _ = 100000000 * A := by ring
  have hconstRaw : Real.log (128040 : ℝ) ≤ 128039 := by
    convert! Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 128040) using 1
    norm_num
  have hconst : Real.log (128040 : ℝ) ≤ 64020 * A := by
    calc
      Real.log (128040 : ℝ) ≤ 128039 := hconstRaw
      _ ≤ 64020 * A := by nlinarith
  have hleft : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
      200000000 * A := by
    calc
      Real.log 128040 + (D : ℝ) * Real.log 2 +
            2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
          64020 * A + 100000000 * A + 10 * A := by linarith
      _ ≤ 200000000 * A := by nlinarith
  have hsmall : 200000000 * δ ≤ 1 / 2 := by
    have := h.2.2.2
    dsimp [δ]
    linarith
  have hhalf : 200000000 * A ≤ L / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hL.le
    dsimp [A]
    nlinarith
  have hrpos : 0 < r := by
    simpa [r] using! parameterDimension_pos_of_regular h
  have hlogp : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    have hp2 : 2 < p := by simpa [p] using! two_lt_parameterPrime N
    exact_mod_cast (show 1 < p by omega)
  have hdiv : L / (2 * Real.log (p : ℝ)) ≤ (r : ℝ) := by
    simpa [L, p, r] using!
      log_div_le_cast_parameterDimension (N := N) (by
        have hN : (1 : ℝ) < N :=
          (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
        exact_mod_cast (show (0 : ℝ) < N from zero_lt_one.trans hN))
  have hrhs : L / 2 ≤ (r : ℝ) * Real.log (p : ℝ) := by
    have hden : 0 < 2 * Real.log (p : ℝ) := by positivity
    have hcross := (div_le_iff₀ hden).mp hdiv
    nlinarith
  change Real.log 128040 + (D : ℝ) * Real.log 2 +
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
    (r : ℝ) * Real.log (p : ℝ)
  exact hleft.trans (hhalf.trans hrhs)

/-- The canonical entropy-slack exponent is at most the chosen dimension. -/
theorem chosenSlackExponent_le_dimension
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    trevisanSlackExponent (parameterPrime N) (parameterDimension N)
        (SuffixDesign.build C.ell (parameterDimension N)).coordCard ≤
      parameterDimension N := by
  apply slackExponent_le_of_log_bound
  · exact Nat.lt_trans (by norm_num) (two_lt_parameterPrime N)
  · exact parameterDimension_pos_of_regular h
  · exact chosenDesign_entropy_log_bound h C

/-- The canonical slack is small enough for the uniform-source rank-pruning
argument. -/
theorem chosen_dimension_add_slack_le_two_mul
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    parameterDimension N +
        trevisanSlackExponent (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard ≤
      2 * parameterDimension N := by
  have hs := chosenSlackExponent_le_dimension h C
  omega

/-- At each regular `N`, the canonical raw Trevisan family can be rank
pruned to a surjective linear extractor family with the same integer seed
and entropy exponents. -/
theorem exists_chosenLinearExtractorFamily
    {N : ℕ} (h : ParameterRegular N) :
    ∃ C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
        (trevisanEta (parameterPrime N) (parameterDimension N)),
      Nonempty (LinearExtractorFamily (parameterPrime N) (parameterDimension N)
        (trevisanSeedExponent (parameterPrime N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard)
        (trevisanSlackExponent (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard)) := by
  let p := parameterPrime N
  let r := parameterDimension N
  have hp : 2 < p := by simpa [p] using! two_lt_parameterPrime N
  have hr : 0 < r := by simpa [r] using! parameterDimension_pos_of_regular h
  have hm : 1 ≤ 2 * r := by omega
  obtain ⟨C⟩ := exists_shortLinearCode p (2 * r) hm (trevisanEta p r)
    (trevisanEta_pos (by omega) hr) (trevisanEta_lt_half hp hr)
  let D := SuffixDesign.build C.ell r
  let E := Reconstruction.canonicalRawTrevisanFamily hp hr C D
  have hs : trevisanSlackExponent p r D.coordCard ≤ r := by
    simpa [p, r, D] using! chosenSlackExponent_le_dimension h C
  have hrs : r + trevisanSlackExponent p r D.coordCard ≤ 2 * r := by omega
  refine ⟨C, ?_⟩
  simpa [p, r, D, E] using!
    (prune_rank_deficient_seeds hp hr hrs E)

end Erdos788
