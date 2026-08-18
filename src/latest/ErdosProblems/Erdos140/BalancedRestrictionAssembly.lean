import ErdosProblems.Erdos140.BalancedRestriction
import ErdosProblems.Erdos140.LocalizedUnbalancing
import ErdosProblems.Erdos140.ConvolutionComparison
import ErdosProblems.Erdos140.DensityStep

/-! # Concrete localized-unbalancing assembly for balanced restriction -/

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise mu

namespace Erdos140.BalancedRestrictionAssembly

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

lemma normalizedConvolution_eq_ddconv (f g : G → ℝ) :
    normalizedConvolution f g = f ∗ᵈ g := by
  funext x
  rw [normalizedConvolution, ddconv_eq_sum_sub']

lemma normalizedDifferenceConvolution_eq_dddconv (f g : G → ℝ) :
    normalizedDifferenceConvolution f g = f ○ᵈ g := by
  funext x
  rw [normalizedDifferenceConvolution, dddconv_eq_sum_sub']
  simp

/-- The NNReal autocorrelation weight used by localized unbalancing is
exactly the real counting-convolution weight used by the Fourier comparison. -/
theorem coe_smoothingWeight_eq_comparisonWeight (D E : Finset G) :
    ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E : G → ℝ) =
      ConvolutionComparison.comparisonWeight D E := by
  rw [ConvolutionComparison.comparisonWeight,
    normalizedConvolution_eq_ddconv,
    normalizedDifferenceConvolution_eq_dddconv,
    normalizedDifferenceConvolution_eq_dddconv]
  simp only [LocalizedUnbalancing.smoothingWeight,
    LocalizedUnbalancing.smoothingBase, NNReal.coe_comp_dddconv,
    NNReal.coe_comp_ddconv, NNReal.coe_comp_mu,
    LocalizedUnbalancing.mu_eq_normalizedIndicator]
  exact (dddconv_ddconv_dddconv_comm
    (normalizedIndicator D) (normalizedIndicator D)
    (normalizedIndicator E) (normalizedIndicator E)).symm

private lemma abs_normalizedConvolution_pow
    (a : G → ℝ) (p : ℕ) (x : G) :
    |normalizedConvolution a a x| ^ p =
      (Fintype.card G : ℝ) ^ p *
        ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  have h := congrArg norm
    (LpOrthogonality.ofReal_countingConvolution a a x)
  simp only [Complex.norm_real, norm_mul, Complex.norm_natCast] at h
  have h' : |normalizedConvolution a a x| =
      (Fintype.card G : ℝ) *
        ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ := by
    simpa only [Real.norm_eq_abs] using h
  rw [h', mul_pow]

private lemma abs_normalizedDifferenceConvolution_pow
    (a : G → ℝ) (p : ℕ) (x : G) :
    |normalizedDifferenceConvolution a a x| ^ p =
      (Fintype.card G : ℝ) ^ p *
        ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  have h := congrArg norm
    (LpOrthogonality.ofReal_countingAutocorrelation a x)
  simp only [Complex.norm_real, norm_mul, Complex.norm_natCast] at h
  have h' : |normalizedDifferenceConvolution a a x| =
      (Fintype.card G : ℝ) *
        ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ := by
    simpa only [Real.norm_eq_abs] using h
  rw [h', mul_pow]

private lemma weightedAbsMoment_normalizedConvolution_eq
    (w a : G → ℝ) (p : ℕ) :
    weightedAbsMoment w (normalizedConvolution a a) p =
      (Fintype.card G : ℝ) ^ p *
        ∑ x : G, w x *
          ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  unfold weightedAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_normalizedConvolution_pow]
  ring

private lemma weightedAbsMoment_normalizedDifferenceConvolution_eq
    (w a : G → ℝ) (p : ℕ) :
    weightedAbsMoment w (normalizedDifferenceConvolution a a) p =
      (Fintype.card G : ℝ) ^ p *
        ∑ x : G, w x *
          ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  unfold weightedAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_normalizedDifferenceConvolution_pow]
  ring

/-- Concrete factor-two moment comparison in the physical normalization
used by localized unbalancing.  The ambient-cardinality factors on the
convolution and autocorrelation sides cancel exactly. -/
theorem concrete_comparison_moment
    {B : BohrData G} {eta : ℝ≥0} {D E : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (hEsmall : E ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (a : G → ℝ) :
    weightedAbsMoment (normalizedIndicator B.carrier)
        (normalizedConvolution a a) p ≤
      2 * weightedAbsMoment
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (normalizedDifferenceConvolution a a) p := by
  have h := ConvolutionComparison.convolutionComparison_moment_rankRegular
    hreg heta hnarrow hD hE hDsmall hEsmall hp heven ((↑) ∘ a)
  rw [← coe_smoothingWeight_eq_comparisonWeight D E] at h
  have hscale : 0 ≤ (Fintype.card G : ℝ) ^ p := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hscale
  rw [weightedAbsMoment_normalizedConvolution_eq,
    weightedAbsMoment_normalizedDifferenceConvolution_eq]
  nlinarith

/-- The concrete comparison in the weighted `L^p` form consumed by the
stopping contradiction. -/
theorem concrete_comparison_lp
    {B : BohrData G} {eta : ℝ≥0} {D E : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (hEsmall : E ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : 0 < p) (heven : Even p) (a : G → ℝ) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator B.carrier)
        (normalizedConvolution a a) p ≤
      2 * BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (normalizedDifferenceConvolution a a) p := by
  have houter : BalancedRestriction.ProbabilityWeight
      (normalizedIndicator B.carrier) :=
    ⟨normalizedIndicator_nonneg B.carrier,
      sum_normalizedIndicator B.carrier_nonempty⟩
  have hnu : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) :=
    ⟨fun x ↦ by
      exact_mod_cast (show 0 ≤ LocalizedUnbalancing.smoothingWeight D E x by
        exact LocalizedUnbalancing.smoothingWeight_nonneg D E x),
      by
        simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ))
          (LocalizedUnbalancing.smoothingWeight_sum hD hE)⟩
  apply BalancedRestriction.weightedLpNorm_le_two_of_moment_le_two
    houter hnu hp
  exact concrete_comparison_moment hreg heta hnarrow hD hE hDsmall hEsmall
    hp.ne' heven a

/-- Root adapter for the moment-form convolution comparison.  The concrete
comparison theorem supplies `hmoment`; this lemma turns its factor two into
the (weaker) factor two between weighted `L^p` norms. -/
theorem weighted_comparison_of_moment
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {outerWeight f g : G → ℝ}
    (houter : BalancedRestriction.ProbabilityWeight outerWeight)
    {p : ℕ} (hp : 0 < p)
    (hmoment : weightedAbsMoment outerWeight f p ≤
      2 * weightedAbsMoment
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) g p) :
    BalancedRestriction.weightedLpNorm outerWeight f p ≤
      2 * BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) g p := by
  let nu := LocalizedUnbalancing.smoothingWeight D E
  have hmass : ∑ x : G, nu x = 1 :=
    LocalizedUnbalancing.smoothingWeight_sum hD hE
  have hnu : BalancedRestriction.ProbabilityWeight ((↑) ∘ nu) :=
    ⟨fun x ↦ by
      exact_mod_cast (show 0 ≤ nu x by
        exact LocalizedUnbalancing.smoothingWeight_nonneg D E x),
      by simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hmass⟩
  apply BalancedRestriction.weightedLpNorm_le_two_of_moment_le_two
      houter hnu hp
  simpa [nu] using hmoment

/-- Specialization of the stopping contradiction to the proved localized
unbalancing theorem. -/
theorem balanced_of_localized_unbalancing
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (B.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    {outerWeight balancedConvolution : G → ℝ}
    (houter : BalancedRestriction.ProbabilityWeight outerWeight)
    (hcomparison :
      BalancedRestriction.weightedLpNorm outerWeight balancedConvolution
          (BalancedRestriction.comparisonExponent p) ≤
        2 * BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ (μ A - μ B.carrier))
          (BalancedRestriction.comparisonExponent p))
    (hstopping :
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) <
        (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm outerWeight balancedConvolution p ≤
      epsilon * (B.carrier.card : ℝ)⁻¹ := by
  let nu := LocalizedUnbalancing.smoothingWeight D E
  have hmass : ∑ x : G, nu x = 1 :=
    LocalizedUnbalancing.smoothingWeight_sum hD hE
  have hnu : BalancedRestriction.ProbabilityWeight ((↑) ∘ nu) :=
    ⟨fun x ↦ by
      exact_mod_cast (show 0 ≤ nu x by
        exact LocalizedUnbalancing.smoothingWeight_nonneg D E x),
      by simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hmass⟩
  have hcard : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  have hmain : 0 < (B.carrier.card : ℝ)⁻¹ := inv_pos.mpr hcard
  apply BalancedRestriction.balanced_convolution_of_stopping
      houter hnu hepsilon hmain hp (by simpa [nu] using hcomparison) _
      (by simpa [nu] using hstopping)
  intro hlarge
  obtain ⟨r, hr, _hreven, hrQ, hrlarge⟩ :=
    LocalizedUnbalancing.localized_unbalancing hreg hA hAB hD hE hkappa
      hsupport hepsilon hepsilon_one hwidth hp (by simpa [nu] using hlarge)
  exact ⟨r, hr, hrQ, by simpa [nu] using hrlarge⟩

/-- Fully concrete balanced-restriction contradiction: both the even-moment
convolution comparison and localized unbalancing are discharged internally.
Only the high-exponent stopping inequality remains as the input produced by
the density-increment construction. -/
theorem balanced_of_concrete_stopping
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (hEsmall : E ⊆ (B.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (B.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hstopping :
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) <
        (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator B.carrier)
        (normalizedConvolution
          (μ_[ℝ] A - μ B.carrier) (μ A - μ B.carrier)) p ≤
      epsilon * (B.carrier.card : ℝ)⁻¹ := by
  let a : G → ℝ := μ_[ℝ] A - μ B.carrier
  have hq : 0 < BalancedRestriction.comparisonExponent p := by
    exact Nat.mul_pos (by norm_num) hp
  have hcomparison := concrete_comparison_lp hreg heta hnarrow hD hE
    hDsmall hEsmall hq (BalancedRestriction.comparisonExponent_even p) a
  rw [normalizedDifferenceConvolution_eq_dddconv] at hcomparison
  apply balanced_of_localized_unbalancing hreg hA hAB hD hE hkappa hsupport
      hepsilon hepsilon_one hwidth hp
      ⟨normalizedIndicator_nonneg B.carrier,
        sum_normalizedIndicator B.carrier_nonempty⟩
  · simpa [a] using hcomparison
  · exact hstopping

/-- The concrete analytic data attached to a located dense-pair endpoint.
All comparison and unbalancing hypotheses are geometric fields; the sole
remaining analytic transition is the high stopping norm to an actual located
controlled increment. -/
structure LocatedAnalyticPackage {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (hdense : DensityStep.HasDensePair s P.childOne P.childTwo epsilon) where
  B : BohrData G
  rankRegular : B.IsRankRegular
  A : Finset G
  A_nonempty : A.Nonempty
  A_subset : A ⊆ B.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow : 4 * eta ≤
    1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (B.dilate eta).carrier
  E_small : E ⊆ (B.dilate eta).carrier
  kappa : ℝ≥0
  rank_width : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier
  boundary_width :
    2 * ((A.card : ℝ)⁻¹ *
        (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (B.carrier.card : ℝ)⁻¹ *
        (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      epsilon / 8 * (B.carrier.card : ℝ)⁻¹
  highNorm_increment :
    (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) →
      ∃ t : DensityStep.LocatedRestriction original,
        BohrStopping.IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
          s.restriction t.restriction

/-- A provenance-preserving terminal certificate: an actual dense pair,
its complete analytic package, and the balanced weighted-norm conclusion. -/
def HasBalancedDensePair {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    (epsilon sizeCost : ℝ) (rankCost p : ℕ) : Prop :=
  ∃ (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost),
    ∃ (hdense : DensityStep.HasDensePair s P.childOne P.childTwo epsilon),
      ∃ Q : LocatedAnalyticPackage (p := p) s P hdense,
        BalancedRestriction.weightedLpNorm (normalizedIndicator Q.B.carrier)
            (normalizedConvolution
              (μ_[ℝ] Q.A - μ Q.B.carrier)
              (μ Q.A - μ Q.B.carrier)) p ≤
          epsilon * (Q.B.carrier.card : ℝ)⁻¹

/-- Located stopping-chain assembly.  Concrete Fourier comparison and
localized unbalancing turn a large balanced norm into the high stopping norm;
the package's `highNorm_increment` field is then the only remaining bridge to
an actual geometric increment.  Failure of that obstruction yields a located
dense-pair terminal certificate. -/
theorem exists_located_balanced_stopping_chain
    {original : Finset G} {epsilon sizeCost : ℝ} {rankCost p fuel : ℕ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) (hp : 0 < p)
    (hsupply : ∀ s : DensityStep.LocatedRestriction original,
      DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (hanalytic : ∀ (s : DensityStep.LocatedRestriction original)
      (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
      (hdense : DensityStep.HasDensePair s P.childOne P.childTwo epsilon),
      LocatedAnalyticPackage (p := p) s P hdense)
    (initial : DensityStep.LocatedRestriction original)
    (hgrowth : 1 < (1 + epsilon / 32) ^ fuel * initial.density) :
    ∃ n ≤ fuel, ∃ t : DensityStep.LocatedRestriction original,
      DensityStep.LocatedControlledChain (1 + epsilon / 32) rankCost sizeCost
          n initial t ∧
      HasBalancedDensePair t epsilon sizeCost rankCost p ∧
      (1 + epsilon / 32) ^ n * initial.density ≤ t.density ∧
      t.rank ≤ initial.rank + n * rankCost ∧
      Real.exp (-(n : ℝ) * sizeCost) * (initial.card : ℝ) ≤ (t.card : ℝ) := by
  let Terminal : DensityStep.LocatedRestriction original → Prop :=
    fun s ↦ HasBalancedDensePair s epsilon sizeCost rankCost p
  have hproduce : DensityStep.ProducesLocatedIncrement
      (fun s : DensityStep.LocatedRestriction original ↦ ¬ Terminal s)
      (1 + epsilon / 32) rankCost sizeCost := by
    intro s hbad
    let P := hsupply s
    rcases DensityStep.certifiedDensePair_or_controlledIncrement s hepsilon P with
      hdense | hincrement
    · obtain ⟨P', hpair⟩ := hdense
      let Q := hanalytic s P' hpair
      by_cases hhigh :
          (1 + epsilon / 8) * (Q.B.carrier.card : ℝ)⁻¹ ≤
            BalancedRestriction.weightedLpNorm
              ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
              (μ_[ℝ] Q.A ○ᵈ μ Q.A)
              (BalancedRestriction.stoppingExponent epsilon p)
      · exact Q.highNorm_increment hhigh
      · have hstop :
            BalancedRestriction.weightedLpNorm
                ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
                (μ_[ℝ] Q.A ○ᵈ μ Q.A)
                (BalancedRestriction.stoppingExponent epsilon p) <
              (1 + epsilon / 8) * (Q.B.carrier.card : ℝ)⁻¹ :=
          lt_of_not_ge hhigh
        have hbalanced := balanced_of_concrete_stopping Q.rankRegular
          Q.A_nonempty Q.A_subset Q.eta_pos Q.eta_narrow
          Q.D_nonempty Q.E_nonempty Q.D_small Q.E_small Q.rank_width
          Q.smoothing_support hepsilon hepsilon_one Q.boundary_width hp hstop
        exact (hbad ⟨P', hpair, Q, hbalanced⟩).elim
    · obtain ⟨t, hdensity, hrank, hcard⟩ := hincrement
      refine ⟨t, ?_, hrank, hcard⟩
      calc
        (1 + epsilon / 32) * s.density ≤
            (1 + epsilon / 2) * s.density := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · exact s.density_pos.le
        _ ≤ t.density := hdensity
  have hq : 0 ≤ 1 + epsilon / 32 := by nlinarith
  obtain ⟨n, hn, t, hchain, hnotbad, hdensity, hrank, hcard⟩ :=
    DensityStep.exists_stopping_located_chain hq hproduce fuel initial hgrowth
  have hterminal : Terminal t := by
    by_contra ht
    exact hnotbad ht
  exact ⟨n, hn, t, hchain, hterminal, hdensity, hrank, hcard⟩

#print axioms balanced_of_localized_unbalancing
#print axioms weighted_comparison_of_moment
#print axioms concrete_comparison_moment
#print axioms balanced_of_concrete_stopping
#print axioms exists_located_balanced_stopping_chain

end
end Erdos140.BalancedRestrictionAssembly
