import Wikipedia.HopfProblem.PeriodMatrixComparison
import Wikipedia.HopfProblem.CuspFibreBiholomorph

/-!
# The cusp correction matrix and the actual period tori

For supplied holomorphic cusp expansions `μ`, `b`, and `h`, the matrix
`C = !![6μ,h;b-h,μ]` is holomorphic and the period block is exactly
`s B₀ + C(exp(2πis))`.  Exponentiating its periods gives the twisted toric
action.  Reordering the four period generators then identifies the
period-domain torus biholomorphically with the actual nonzero cusp fibre.

This proves the local bridge in Proposition 3.21 and its fibrewise
geometric consequence; it does not assume or assert that the required
global special period functions have already been constructed.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods

open ToricSpace CuspUniformization

/-- The holomorphic correction matrix in Proposition 3.21. -/
def cuspCorrection (μ b h : ℂ → ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * μ t, h t; b t - h t, μ t]

theorem cuspCorrection_analyticAt {μ b h : ℂ → ℂ} {a : ℂ}
    (hμ : AnalyticAt ℂ μ a) (hb : AnalyticAt ℂ b a) (hh : AnalyticAt ℂ h a)
    (i j : Fin 2) : AnalyticAt ℂ (fun t => cuspCorrection μ b h t i j) a := by
  fin_cases i <;> fin_cases j
  · exact analyticAt_const.mul hμ
  · exact hh
  · exact hb.sub hh
  · exact hμ

theorem cuspCorrection_holomorphicOn {μ b h : ℂ → ℂ} {U : Set ℂ}
    (hμ : ContDiffOn ℂ ω μ U) (hb : ContDiffOn ℂ ω b U) (hh : ContDiffOn ℂ ω h U)
    (i j : Fin 2) : ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) U := by
  fin_cases i <;> fin_cases j
  · exact contDiffOn_const.mul hμ
  · exact hh
  · exact hb.sub hh
  · exact hμ

/-- Holomorphic cusp expansions on any disc give a smaller positive
radius satisfying all the cusp quotient's analytic and drift bounds. -/
theorem exists_cuspCorrection_admissible_radius {μ b h : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hμ : ContDiffOn ℂ ω μ (Metric.ball 0 r))
    (hb : ContDiffOn ℂ ω b (Metric.ball 0 r))
    (hh : ContDiffOn ℂ ω h (Metric.ball 0 r)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ε < 1 ∧ SmallDrift (cuspCorrection μ b h) ε ∧
      ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) :=
  CuspQuotient.exists_admissible_radius (cuspCorrection μ b h) hr
    (cuspCorrection_holomorphicOn hμ hb hh)

/-- Analytic germs at zero already suffice for a genuine cusp radius. -/
theorem exists_cuspCorrection_admissible_radius_of_analyticAt {μ b h : ℂ → ℂ}
    (hμ : AnalyticAt ℂ μ 0) (hb : AnalyticAt ℂ b 0) (hh : AnalyticAt ℂ h 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ SmallDrift (cuspCorrection μ b h) ε ∧
      ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hμ.eventually_analyticAt.and (hb.eventually_analyticAt.and hh.eventually_analyticAt))
  have hμr : ContDiffOn ℂ ω μ (Metric.ball 0 r) :=
    fun t ht => (hball ht).1.contDiffAt.contDiffWithinAt
  have hbr : ContDiffOn ℂ ω b (Metric.ball 0 r) :=
    fun t ht => (hball ht).2.1.contDiffAt.contDiffWithinAt
  have hhr : ContDiffOn ℂ ω h (Metric.ball 0 r) :=
    fun t ht => (hball ht).2.2.contDiffAt.contDiffWithinAt
  obtain ⟨ε, hε, _, hε1, hR, hC⟩ :=
    exists_cuspCorrection_admissible_radius hr hμr hbr hhr
  exact ⟨ε, hε, hε1, hR, hC⟩

/-- The original three period entries recovered from the cusp expansions. -/
def cuspPeriodPoint (μ b h : ℂ → ℂ) (s : ℂ) : PeriodPoint :=
  ⟨s + h (exponential s), μ (exponential s),
    b (exponential s) - s - h (exponential s)⟩

/-- The actual period block is the logarithmic period matrix used in
the toric cusp construction, with no change of signs or transposition. -/
theorem cuspPeriodPoint_leftBlock (μ b h : ℂ → ℂ) (s : ℂ) :
    (cuspPeriodPoint μ b h s).leftBlock = logarithmicPeriod (cuspCorrection μ b h) s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspPeriodPoint, PeriodPoint.leftBlock, logarithmicPeriod, cuspCorrection, B₀,
      smul_eq_mul]
  ring

/-- The small-drift bound controls each imaginary correction by one
quarter of the logarithmic height. -/
theorem correction_im_bound_of_smallDrift
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (hR : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (i j : Fin 2) : |(C (exponential s) i j).im| ≤ s.im / 4 := by
  have hentry : ‖driftMatrix C (exponential s) i j‖ ≤
      -Real.log ‖exponential s‖ / 4 :=
    ((norm_le_pi_norm (driftMatrix C (exponential s) i) j).trans
      (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 =>
        driftMatrix C (exponential s) k l) i)).trans hR
  have hscaled : (2 * Real.pi) * |(C (exponential s) i j).im| ≤
      (2 * Real.pi) * (s.im / 4) := by
    simpa [driftMatrix, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
      log_norm_exponential, neg_mul, mul_div_assoc] using hentry
  exact le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 * Real.pi)

/-- The reconstructed periods are in the actual admissible period
domain whenever the cusp's quantitative small-drift bound holds. -/
theorem cuspPeriodPoint_admissible (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix (cuspCorrection μ b h) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4) : (cuspPeriodPoint μ b h s).Admissible := by
  have hs : 0 < s.im := by
    rw [log_norm_exponential] at hlog
    have hp := Real.pi_pos
    nlinarith
  have hh := (abs_le.mp (correction_im_bound_of_smallDrift
    (cuspCorrection μ b h) s hR 0 1)).1
  have hbh := (abs_le.mp (correction_im_bound_of_smallDrift
    (cuspCorrection μ b h) s hR 1 0)).2
  change -(s.im / 4) ≤ (h (exponential s)).im at hh
  change (b (exponential s) - h (exponential s)).im ≤ s.im / 4 at hbh
  have hτ : 0 < (s + h (exponential s)).im := by
    rw [Complex.add_im]
    linarith
  have hβ : (b (exponential s) - s - h (exponential s)).im < 0 := by
    rw [Complex.sub_im] at hbh
    rw [Complex.sub_im, Complex.sub_im]
    linarith
  refine ⟨hτ, ?_⟩
  change (b (exponential s) - s - h (exponential s)).im -
    6 * (μ (exponential s)).im ^ 2 / (s + h (exponential s)).im < 0
  have hn : 0 ≤ 6 * (μ (exponential s)).im ^ 2 / (s + h (exponential s)).im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le
  linarith

/-- The period-domain point supplied by the cusp expansions themselves;
its admissibility is proved from the cusp estimates. -/
def cuspPeriodDomain (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix (cuspCorrection μ b h) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4) : PeriodDomain :=
  ⟨cuspPeriodPoint μ b h s, cuspPeriodPoint_admissible μ b h s hlog hR⟩

/-- The same identity for an already supplied period point whose entries
have the three stated cusp expansions. -/
theorem leftBlock_eq_logarithmicPeriod_of_cusp_expansion
    (μ b h : ℂ → ℂ) (p : PeriodPoint) (s : ℂ)
    (hτ : p.τ = s + h (exponential s)) (hμ : p.μ = μ (exponential s))
    (hβ : p.β = b (exponential s) - s - h (exponential s)) :
    p.leftBlock = logarithmicPeriod (cuspCorrection μ b h) s := by
  have hp : p = cuspPeriodPoint μ b h s := PeriodPoint.ext hτ hμ hβ
  rw [hp, cuspPeriodPoint_leftBlock]

/-- The componentwise exponential identity of Proposition 3.21. -/
theorem cuspPeriodPoint_exponential_period (μ b h : ℂ → ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    exponential (((cuspPeriodPoint μ b h s).leftBlock *ᵥ (fun j => (v j : ℂ))) i) =
      exponential s ^ (B₀ *ᵥ v) i *
        exponential ((cuspCorrection μ b h (exponential s) *ᵥ (fun j => (v j : ℂ))) i) := by
  have hv : cuspVector v = B₀ *ᵥ v := by
    ext j
    fin_cases j <;> simp [cuspVector, B₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [cuspPeriodPoint_leftBlock, exponential_logarithmicPeriod, hv]
  exact mul_comm _ _

theorem cuspCorrection_multiplier_holomorphicOn {μ b h : ℂ → ℂ} {U : Set ℂ}
    (hμ : ContDiffOn ℂ ω μ U) (hb : ContDiffOn ℂ ω b U) (hh : ContDiffOn ℂ ω h U)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    ContDiffOn ℂ ω (fun t => (exponentialMultiplier (cuspCorrection μ b h) v t i : ℂ)) U :=
  exponentialMultiplier_holomorphic _ v (cuspCorrection_holomorphicOn hμ hb hh) i

section TorusComparison

variable (μ b h : ℂ → ℂ) (p : PeriodDomain) (s : ℂ)
    (hτ : p.val.τ = s + h (exponential s)) (hμ : p.val.μ = μ (exponential s))
    (hβ : p.val.β = b (exponential s) - s - h (exponential s))
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix (cuspCorrection μ b h) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4)

include hτ hμ hβ in
/-- The two actual integral lattices coincide under the cusp expansions. -/
theorem cusp_period_lattice_eq :
    (periodData (cuspCorrection μ b h) s hlog hRp).lattice = p.lattice := by
  apply p.fullPeriodLattice_eq
  exact (leftBlock_eq_logarithmicPeriod_of_cusp_expansion μ b h p.val s hτ hμ hβ).symm

/-- The identity on `ℂ²` identifies the period-domain torus with the
logarithmic cusp-period torus, including their quotient complex structures. -/
def cuspPeriodTorusBiholomorph :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus
      (periodData (cuspCorrection μ b h) s hlog hRp).Torus ω :=
  p.fullPeriodBiholomorph (periodData (cuspCorrection μ b h) s hlog hRp)
    (leftBlock_eq_logarithmicPeriod_of_cusp_expansion μ b h p.val s hτ hμ hβ).symm

@[simp] theorem cuspPeriodTorusBiholomorph_mkQ (z : ComplexPlane₂) :
    cuspPeriodTorusBiholomorph μ b h p s hτ hμ hβ hlog hRp (p.lattice.mkQ z) =
      (periodData (cuspCorrection μ b h) s hlog hRp).lattice.mkQ z := rfl

end TorusComparison

/-- The two period tori constructed directly from the same cusp data
are biholomorphic by the identity of their covering vector space. -/
def cuspPeriodDomainTorusBiholomorph (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix (cuspCorrection μ b h) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) (cuspPeriodDomain μ b h s hlog hR).Torus
      (periodData (cuspCorrection μ b h) s hlog hR).Torus ω :=
  cuspPeriodTorusBiholomorph μ b h (cuspPeriodDomain μ b h s hlog hR) s
    rfl rfl rfl hlog hR

section FibreComparison

variable (μ b h : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : ContDiffOn ℂ ω μ (Metric.ball 0 ε))
    (hb : ContDiffOn ℂ ω b (Metric.ball 0 ε))
    (hh : ContDiffOn ℂ ω h (Metric.ball 0 ε))
    (hR : SmallDrift (cuspCorrection μ b h) ε)
    (p : PeriodDomain) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hτ : p.val.τ = s + h (exponential s)) (hμp : p.val.μ = μ (exponential s))
    (hβ : p.val.β = b (exponential s) - s - h (exponential s))

/-- A period-domain torus with the specified cusp expansions is
biholomorphic to the literal nonzero fibre of the constructed cusp space. -/
def cuspFibreBiholomorph :
    letI := fibreChartedSpace (cuspCorrection μ b h) ε hε hε1
      (cuspCorrection_holomorphicOn hμ hb hh) hR (exponential s) (exponential_ne_zero s)
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus
      (CuspQuotient.projection (cuspCorrection μ b h) ε ⁻¹' {exponential s}) ω := by
  let := fibreChartedSpace (cuspCorrection μ b h) ε hε hε1
    (cuspCorrection_holomorphicOn hμ hb hh) hR (exponential s) (exponential_ne_zero s)
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans hε1)
  have hRp := hR _ hpos hs
  exact (cuspPeriodTorusBiholomorph μ b h p s hτ hμp hβ hlog hRp).trans
    (fibreBiholomorph (cuspCorrection μ b h) ε s hs hlog hRp hε hε1
      (cuspCorrection_holomorphicOn hμ hb hh) hR)

/-- On representatives this biholomorphism is the actual exponential
map followed by the twisted cusp quotient. -/
@[simp] theorem cuspFibreBiholomorph_mkQ (z : ComplexPlane₂) :
    (cuspFibreBiholomorph μ b h ε hε hε1 hμ hb hh hR p s hs hτ hμp hβ
        (p.lattice.mkQ z) : CuspQuotient.QuotientSpace (cuspCorrection μ b h) ε) =
      fibreCover (cuspCorrection μ b h) ε s hs z := rfl

end FibreComparison

end Wikipedia.HopfProblem.SpecialPeriods
