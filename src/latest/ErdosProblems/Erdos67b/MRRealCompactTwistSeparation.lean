import ErdosProblems.Erdos67b.TwistSeparationLFunction

/-!
# Compact opposite-twist separation

On a fixed annulus away from the pole, the Riemann zeta function is bounded.
The existing finite/full Euler-log comparison then shows that the reciprocal-
prime distance between opposite Archimedean twists grows like `log log X`,
uniformly on that annulus.
-/

open scoped BigOperators ComplexConjugate LSeries.notation
open Filter Set

namespace Erdos67b

noncomputable section

/-- At modulus one, the Dirichlet--Archimedean twist has no finite
character component. -/
theorem dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact
    (t : ℝ) :
    dirichletArchimedeanTwist (1 : DirichletCharacter ℂ 1) t =
      archimedeanTwist t := by
  funext n
  have hnunit : IsUnit (n : ZMod 1) := by
    rw [show (n : ZMod 1) = 1 by subsingleton]
    exact isUnit_one
  rw [dirichletArchimedeanTwist, MulChar.one_apply hnunit, one_mul]

theorem quotientCharacter_one_one :
    quotientCharacter (1 : DirichletCharacter ℂ 1)
      (1 : DirichletCharacter ℂ 1) = 1 := by
  exact DirichletCharacter.level_one _

theorem LSeries_dirichletCharacter_one_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    L ↗(1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  rw [show L ↗(1 : DirichletCharacter ℂ 1) s = L 1 s by
    exact congrFun DirichletCharacter.LSeries_modOne_eq s]
  exact LSeries_one_eq_riemannZeta hs

/-- The Riemann zeta function is uniformly bounded on the compact rectangle
`1 ≤ re s ≤ 2`, `4 ≤ |im s| ≤ V`. -/
theorem exists_uniform_norm_riemannZeta_compact_annulus
    (V : ℝ) (hV : 4 ≤ V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, 1 ≤ sigma → sigma ≤ 2 →
        4 ≤ |t| → |t| ≤ V →
        ‖riemannZeta ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤ C := by
  let T : Set ℝ := Set.Icc (-V) (-4) ∪ Set.Icc 4 V
  let K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) 2 ×ˢ T
  let z : ℝ × ℝ → ℂ := fun x ↦
    (x.1 : ℂ) + Complex.I * (x.2 : ℂ)
  let F : ℝ × ℝ → ℝ := fun x ↦ ‖riemannZeta (z x)‖
  have hT : IsCompact T := isCompact_Icc.union isCompact_Icc
  have hK : IsCompact K := isCompact_Icc.prod hT
  have hKne : K.Nonempty := by
    refine ⟨(1, 4), ?_⟩
    exact ⟨⟨le_rfl, by norm_num⟩, Or.inr ⟨le_rfl, hV⟩⟩
  have hz_ne : ∀ x ∈ K, z x ≠ 1 := by
    intro x hx heq
    have him := congrArg Complex.im heq
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_add, Complex.one_im] at him
    rcases hx.2 with hxneg | hxpos
    · linarith [hxneg.2]
    · linarith [hxpos.1]
  have hF : ContinuousOn F K := by
    intro x hx
    have hzcont : ContinuousAt z x := by
      dsimp only [z]
      fun_prop
    have hzetacont : ContinuousAt riemannZeta (z x) :=
      (differentiableAt_riemannZeta (hz_ne x hx)).continuousAt
    exact (hzetacont.norm.comp hzcont).continuousWithinAt
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne hF
  refine ⟨F x + 1, by dsimp only [F]; positivity, ?_⟩
  intro sigma t hsigma1 hsigma2 ht4 htV
  have htT : t ∈ T := by
    by_cases ht : 0 ≤ t
    · right
      rw [abs_of_nonneg ht] at ht4 htV
      exact ⟨ht4, htV⟩
    · left
      have ht' : t ≤ 0 := le_of_not_ge ht
      rw [abs_of_nonpos ht'] at ht4 htV
      constructor <;> linarith
  have hst : (sigma, t) ∈ K := ⟨⟨hsigma1, hsigma2⟩, htT⟩
  exact (hmax hst).trans (le_add_of_nonneg_right zero_le_one)

/-- Uniform finite separation of opposite Archimedean twists on a fixed
compact annulus.  The cutoff is uniform in the frequency `t`; only the
requested separation level `A` and the outer radius `V` enter its choice. -/
theorem exists_pretentiousDistSq_archimedeanTwist_opposite_compact_lower
    (A : ℕ) (V : ℝ) (hV : 4 ≤ V) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧
      ∀ (X : ℕ) (t : ℝ), X₀ ≤ X →
        4 ≤ |2 * t| → |2 * t| ≤ V →
        (4 * A : ℕ) ≤
          pretentiousDistSq (archimedeanTwist t)
            (archimedeanTwist (-t)) X := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_norm_riemannZeta_compact_annulus V hV
  let E : ℝ :=
    8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2
  let B : ℝ := (4 : ℝ) * A + PrimeEstimates.mertensBound + Real.log C + E +
    polynomialHeightPrimePowerRemainderBound + polynomialHeightWeightRemovalBound
  have hloglog : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ X : ℕ in atTop,
      B ≤ Real.log (Real.log (X : ℝ)) :=
    hloglog.eventually (eventually_ge_atTop B)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let X₀ : ℕ := max 4 N
  refine ⟨X₀, le_max_left _ _, ?_⟩
  intro X t hX htLower htUpper
  have h4X : 4 ≤ X := (le_max_left 4 N).trans hX
  have hNX : N ≤ X := (le_max_right 4 N).trans hX
  have hBX : B ≤ Real.log (Real.log (X : ℝ)) := hN X hNX
  have hXR : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXR
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hexpX : Real.exp 1 ≤ (X : ℝ) := by
      exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ X by omega))
    have hlog := Real.log_le_log (Real.exp_pos 1) hexpX
    simpa only [Real.log_exp] using hlog
  let sigma : ℝ := 1 + (Real.log (X : ℝ))⁻¹
  let v : ℝ := -2 * t
  let chi : DirichletCharacter ℂ 1 := 1
  let psi : DirichletCharacter ℂ 1 := quotientCharacter chi chi
  have hsigmaLower : 1 < sigma := by
    dsimp only [sigma]
    linarith [inv_pos.mpr hlogX]
  have hsigmaUpper : sigma ≤ 2 := by
    dsimp only [sigma]
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogX).2 hlogXone
    linarith
  have hvabs : |v| = |2 * t| := by
    dsimp only [v]
    rw [show -2 * t = -(2 * t) by ring, abs_neg]
  have hvLower : 4 ≤ |v| := by simpa only [hvabs] using htLower
  have hvUpper : |v| ≤ V := by simpa only [hvabs] using htUpper
  have hpsi : psi = 1 := by
    dsimp only [psi, chi]
    exact quotientCharacter_one_one
  have hpoint :
      ((sigma : ℝ) : ℂ) + Complex.I * (v : ℂ) =
        polynomialHeightEulerPoint X v := rfl
  have hLnorm : ‖L ↗psi (polynomialHeightEulerPoint X v)‖ ≤ C := by
    rw [← hpoint, hpsi,
      LSeries_dirichletCharacter_one_eq_riemannZeta (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
          sub_zero, add_zero]
        exact hsigmaLower)]
    exact hC sigma v hsigmaLower.le hsigmaUpper hvLower hvUpper
  have hpointRe : (polynomialHeightEulerPoint X v).re = sigma := by
    rw [← hpoint]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
      sub_zero, add_zero]
  have hLne : L ↗psi (polynomialHeightEulerPoint X v) ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re psi
      (by rw [hpointRe]; exact hsigmaLower)
  have hnormPos : 0 < ‖L ↗psi (polynomialHeightEulerPoint X v)‖ :=
    norm_pos_iff.mpr hLne
  have hlogNorm :
      Real.log ‖L ↗psi (polynomialHeightEulerPoint X v)‖ ≤ Real.log C :=
    Real.log_le_log hnormPos hLnorm
  have heuler := truncatedEulerLog_le_log_norm_LSeries_add_uniform psi v h4X
  have hlinear := truncatedEulerLinear_le_log_add_remainder
    (Y := X) psi v (by omega)
  have hcorr := quotientCorrelation_le_eulerLinear_add_weightBound
    (Y := X) (by norm_num : 0 < 1) (by norm_num : 0 < 1) chi chi v (by omega)
  have hcorrFinal :
      characterTwistPrimeCorrelation chi chi v X ≤
        Real.log C + E + polynomialHeightPrimePowerRemainderBound +
          polynomialHeightWeightRemovalBound := by
    calc
      characterTwistPrimeCorrelation chi chi v X ≤
          truncatedPolynomialHeightEulerLinear psi X v +
            polynomialHeightWeightRemovalBound := by
        simpa only [psi, chi] using hcorr
      _ ≤ truncatedPolynomialHeightEulerLog psi X v +
            polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound := by
        gcongr
      _ ≤ Real.log ‖L ↗psi (polynomialHeightEulerPoint X v)‖ + E +
            polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound := by
        dsimp only [E]
        gcongr
      _ ≤ Real.log C + E + polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound := by
        linarith
  have hchar : (4 * A : ℕ) ≤ characterTwistDistSq chi chi v X := by
    rw [characterTwistDistSq_eq_mass_sub_correlation]
    have hmass := characterTwistPrimeMass_mertens_lower (Y := X) (by omega)
    push_cast
    dsimp only [B] at hBX
    linarith
  calc
    (4 * A : ℕ) ≤ characterTwistDistSq chi chi v X := hchar
    _ = characterTwistDistSq chi chi ((-t) - t) X := by
      congr 2
      dsimp only [v]
      ring
    _ = pretentiousDistSq
          (dirichletArchimedeanTwist chi t)
          (dirichletArchimedeanTwist chi (-t)) X :=
      characterTwistDistSq_eq_pretentiousDistSq chi chi t (-t) X
    _ = pretentiousDistSq (archimedeanTwist t)
          (archimedeanTwist (-t)) X := by
      rw [dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact,
        dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact]

/-- Opposite Archimedean twists become arbitrarily far apart, uniformly on
every fixed compact annulus away from zero.  This is the compact-frequency
separation needed in the unconditional real Halasz argument. -/
theorem eventually_four_mul_le_pretentiousDistSq_opposite_archimedeanTwist
    (A V : ℝ) (hV : 4 ≤ V) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ t : ℝ,
      4 ≤ |t| → |t| ≤ V →
        4 * A ≤ pretentiousDistSq
          (archimedeanTwist t) (archimedeanTwist (-t)) X := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_uniform_norm_riemannZeta_compact_annulus (2 * V) (by linarith)
  let E : ℝ :=
    8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2
  let K : ℝ := PrimeEstimates.mertensBound + Real.log C + E +
    polynomialHeightPrimePowerRemainderBound +
      polynomialHeightWeightRemovalBound
  have hloglog : Filter.Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ X : ℕ in Filter.atTop,
      4 * A + K ≤ Real.log (Real.log (X : ℝ)) :=
    (Filter.tendsto_atTop.1 hloglog (4 * A + K))
  filter_upwards [hevent, Filter.eventually_ge_atTop 4] with X hlarge hX
  intro t ht4 htV
  let chi : DirichletCharacter ℂ 1 := 1
  let v : ℝ := -t - t
  let sigma : ℝ := 1 + (Real.log (X : ℝ))⁻¹
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogXone : 1 ≤ Real.log (X : ℝ) := by
    have hexpX : Real.exp 1 ≤ (X : ℝ) := by
      exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ X by omega))
    have hlog := Real.log_le_log (Real.exp_pos 1) hexpX
    simpa only [Real.log_exp] using hlog
  have hsigma1 : 1 < sigma := by
    dsimp only [sigma]
    linarith [inv_pos.mpr hlogX]
  have hsigma2 : sigma ≤ 2 := by
    dsimp only [sigma]
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogX).2 hlogXone
    linarith
  have hvabs : |v| = 2 * |t| := by
    dsimp only [v]
    calc
      |-t - t| = |(-2 : ℝ) * t| := by ring_nf
      _ = |(-2 : ℝ)| * |t| := abs_mul _ _
      _ = 2 * |t| := by norm_num
  have hv4 : 4 ≤ |v| := by rw [hvabs]; linarith
  have hvV : |v| ≤ 2 * V := by rw [hvabs]; linarith
  have hpointRe : (polynomialHeightEulerPoint X v).re = sigma := by
    simp only [polynomialHeightEulerPoint, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      sigma]
  have hLnorm :
      ‖L ↗chi (polynomialHeightEulerPoint X v)‖ ≤ C := by
    rw [show L ↗chi (polynomialHeightEulerPoint X v) =
        riemannZeta (polynomialHeightEulerPoint X v) by
      dsimp only [chi]
      exact LSeries_dirichletCharacter_one_eq_riemannZeta
        (by rw [hpointRe]; exact hsigma1)]
    exact hC sigma v hsigma1.le hsigma2 hv4 hvV
  have hLne : L ↗chi (polynomialHeightEulerPoint X v) ≠ 0 := by
    apply DirichletCharacter.LSeries_ne_zero_of_one_lt_re
    rw [hpointRe]
    exact hsigma1
  have hlogNorm :
      Real.log ‖L ↗chi (polynomialHeightEulerPoint X v)‖ ≤ Real.log C :=
    Real.log_le_log (norm_pos_iff.mpr hLne) hLnorm
  have hquot : quotientCharacter chi chi = chi := by
    dsimp only [chi]
    exact quotientCharacter_one_one
  have heuler := truncatedEulerLog_le_log_norm_LSeries_add_uniform
    chi v hX
  have hlinear := truncatedEulerLinear_le_log_add_remainder
    (Y := X) chi v (by omega)
  have hcorr := quotientCorrelation_le_eulerLinear_add_weightBound
    (Y := X) (q := 1) (q' := 1) (by norm_num) (by norm_num)
      chi chi v (by omega)
  have hcorrFinal :
      characterTwistPrimeCorrelation chi chi v X ≤
        Real.log C + E + polynomialHeightPrimePowerRemainderBound +
          polynomialHeightWeightRemovalBound := by
    rw [hquot] at hcorr
    dsimp only [E]
    linarith
  have hmass := characterTwistPrimeMass_mertens_lower
    (Y := X) (by omega)
  have hdist :
      4 * A ≤ characterTwistDistSq chi chi v X := by
    rw [characterTwistDistSq_eq_mass_sub_correlation]
    dsimp only [K] at hlarge
    linarith
  calc
    4 * A ≤ characterTwistDistSq chi chi v X := hdist
    _ = pretentiousDistSq
        (dirichletArchimedeanTwist chi t)
        (dirichletArchimedeanTwist chi (-t)) X := by
      have hcompat := characterTwistDistSq_eq_pretentiousDistSq
        chi chi t (-t) X
      simpa only [v] using hcompat
    _ = pretentiousDistSq
        (archimedeanTwist t) (archimedeanTwist (-t)) X := by
      dsimp only [chi]
      rw [dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact,
        dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact]

end

end Erdos67b
