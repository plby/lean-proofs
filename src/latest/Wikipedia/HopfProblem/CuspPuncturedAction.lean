import Wikipedia.HopfProblem.CuspPuncturedDeck
import Wikipedia.HopfProblem.CuspPuncturedBasic

/-!
# The free holomorphic deck action on the varying logarithmic cover

The explicit logarithmic deck group preserves the open logarithmic
domain.  Its action is holomorphic and, for the proved small-drift cusp
neighborhood, free.  Its orbits are exactly the fibres of the actual
punctured-cusp exponential map.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

theorem logDeckTransform_mem_logDomain (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    logDeckTransform C g x ∈ logDomain ε ↔ x ∈ logDomain ε := by
  simp

def logCoverTransform (g : LogDeck) (x : LogCover ε) : LogCover ε :=
  ⟨logDeckTransform C g x, (logDeckTransform_mem_logDomain C ε g x).mpr x.2⟩

@[simp] theorem logCoverTransform_coe (g : LogDeck) (x : LogCover ε) :
    (logCoverTransform C ε g x : ℂ × ComplexPlane₂) = logDeckTransform C g x := rfl

@[instance_reducible] def logCoverAction : MulAction LogDeck (LogCover ε) where
  smul := logCoverTransform C ε
  one_smul x := Subtype.ext (logDeckTransform_one C x)
  mul_smul g h x := Subtype.ext (logDeckTransform_mul C g h x)

theorem logCoverAction_smul (g : LogDeck) (x : LogCover ε) :
    letI := logCoverAction C ε
    g • x = logCoverTransform C ε g x := rfl

theorem logarithmicPeriod_logDomain_holomorphic
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (i j : Fin 2) : ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 i j) (logDomain ε) := by
  have he : ContDiff ℂ ω (fun x : ℂ × ComplexPlane₂ => exponential x.1) :=
    exponential_holomorphic.comp contDiff_fst
  change ContDiffOn ℂ ω
    (fun x : ℂ × ComplexPlane₂ =>
      x.1 * (B₀.map (Int.castRingHom ℂ)) i j + C (exponential x.1) i j) _
  exact (contDiff_fst.mul contDiff_const).contDiffOn.add
    ((hC i j).comp he.contDiffOn (fun x hx => hx))

theorem logarithmicPeriod_logDomain_mulVec_holomorphic
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (n : Fin 2 → ℤ) : ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ =>
        logarithmicPeriod C x.1 *ᵥ (fun i => (n i : ℂ))) (logDomain ε) := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((logarithmicPeriod_logDomain_holomorphic C ε hC i 0).mul contDiffOn_const).add
    ((logarithmicPeriod_logDomain_holomorphic C ε hC i 1).mul contDiffOn_const)

theorem logDeckTransform_holomorphic
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (g : LogDeck) :
    ContDiffOn ℂ ω (logDeckTransform C g) (logDomain ε) := by
  have hv : ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ =>
        logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ))) (logDomain ε) :=
    logarithmicPeriod_logDomain_mulVec_holomorphic C ε hC g.n
  exact (contDiff_fst.add contDiff_const).contDiffOn.prodMk
    ((contDiff_snd.add contDiff_const).contDiffOn.add hv)

theorem logCover_action_holomorphic
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (g : LogDeck) :
    letI := logCoverAction C ε
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : LogCover ε => g • x) := by
  let := logCoverAction C ε
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun y : LogCover ε => ((g • y : LogCover ε) : ℂ × ComplexPlane₂)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun y : LogCover ε => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h := (logDeckTransform_holomorphic C ε hC g).contMDiffOn
  exact (h.contMDiffAt ((logDomain ε).isOpen.mem_nhds x.2)).comp x contMDiff_subtype_val.contMDiffAt

theorem logCover_continuousConstSMul
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    letI := logCoverAction C ε
    ContinuousConstSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  exact ⟨fun g => (logCover_action_holomorphic C ε hC g).continuous⟩

theorem logCover_free_action (hε1 : ε < 1) (hR : SmallDrift C ε) :
    letI := logCoverAction C ε
    IsCancelSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  have hs : ‖exponential x.1.1‖ < ε := (mem_logDomain ε x).mp x.2
  have hp : 0 < ‖exponential x.1.1‖ := norm_pos_iff.mpr (exponential_ne_zero _)
  apply (logDeckTransform_eq_self_iff C g x
    (logarithmicPeriod_nondegenerate C x.1.1
      (Real.log_neg hp (hs.trans hε1)) (hR _ hp hs))).mp
  exact congrArg Subtype.val hx

theorem totalPeriodRelated_iff_exists_logDeck (p q : ℂ × ComplexPlane₂) :
    TotalPeriodRelated C p q ↔ ∃ g : LogDeck, logDeckTransform C g q = p := by
  constructor
  · rintro ⟨k, m, n, hs, hz⟩
    exact ⟨⟨k, m, n⟩, Prod.ext hs.symm hz.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.k, g.m, g.n, (congrArg Prod.fst hg).symm, (congrArg Prod.snd hg).symm⟩

theorem puncturedCuspCover_eq_iff_orbit (p q : LogCover ε) :
    letI := logCoverAction C ε
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔
      p ∈ MulAction.orbit LogDeck q := by
  let := logCoverAction C ε
  rw [puncturedCuspCover_eq_iff, totalPeriodRelated_iff_exists_logDeck]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

end Wikipedia.HopfProblem.CuspUniformization
