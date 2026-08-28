import Wikipedia.HopfProblem.CuspPuncturedBasic
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Wikipedia.HopfProblem.ExponentialCharts

/-!
# The logarithmic base of the punctured cusp family

The normalized exponential covers the punctured parameter disc. Its deck
action is the clockwise convention `s ↦ s - k`. The logarithmic total space
is identified with the product by the explicit rearrangement of subtypes;
both sides retain their inherited complex atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily

open CuspUniformization

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "Ilog" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual logarithmic preimage of the parameter disc. -/
def logBase (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨exponential ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage exponential_holomorphic.continuous⟩

abbrev LogBase (ε : ℝ) := logBase ε

@[simp] theorem mem_logBase (ε : ℝ) (s : ℂ) :
    s ∈ logBase ε ↔ ‖exponential s‖ < ε := by
  simp [logBase, Metric.mem_ball]

/-- The punctured disc with its inherited open-submanifold structure. -/
def puncturedDisc (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 ε ∩ {t | t ≠ 0},
    Metric.isOpen_ball.inter (isOpen_ne_fun continuous_id continuous_const)⟩

@[simp] theorem mem_puncturedDisc (ε : ℝ) (t : ℂ) :
    t ∈ puncturedDisc ε ↔ ‖t‖ < ε ∧ t ≠ 0 := by
  simp [puncturedDisc, Metric.mem_ball]

def baseExponential (ε : ℝ) (s : LogBase ε) : puncturedDisc ε :=
  ⟨exponential s, s.2, exponential_ne_zero s⟩

@[simp] theorem baseExponential_coe (ε : ℝ) (s : LogBase ε) :
    (baseExponential ε s : ℂ) = exponential s := rfl

theorem baseExponential_surjective (ε : ℝ) : Function.Surjective (baseExponential ε) := by
  intro t
  let s : LogBase ε := ⟨logarithm t, by
    change exponential (logarithm t) ∈ Metric.ball 0 ε
    rw [exponential_logarithm t.2.2]
    exact t.2.1⟩
  exact ⟨s, Subtype.ext (exponential_logarithm t.2.2)⟩

theorem exponential_sub_int (s : ℂ) (k : ℤ) :
    exponential (s - k) = exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, exponential_add, exponential_int, mul_one]

/-- Clockwise logarithm monodromy. -/
def logBaseTranslate (ε : ℝ) (k : ℤ) (s : LogBase ε) : LogBase ε :=
  ⟨(s : ℂ) - k, by
    change exponential ((s : ℂ) - k) ∈ Metric.ball 0 ε
    rw [exponential_sub_int]
    exact s.2⟩

@[simp] theorem logBaseTranslate_coe (ε : ℝ) (k : ℤ) (s : LogBase ε) :
    (logBaseTranslate ε k s : ℂ) = (s : ℂ) - k := rfl

@[instance_reducible] def logBaseAction (ε : ℝ) :
    MulAction (Multiplicative ℤ) (LogBase ε) where
  smul g s := logBaseTranslate ε g.toAdd s
  mul_smul g h s := by
    apply Subtype.ext
    change (s : ℂ) - ((g.toAdd + h.toAdd : ℤ) : ℂ) =
      ((s : ℂ) - h.toAdd) - g.toAdd
    push_cast
    abel
  one_smul s := by
    apply Subtype.ext
    change (s : ℂ) - ((1 : Multiplicative ℤ).toAdd : ℂ) = (s : ℂ)
    simp only [toAdd_one, Int.cast_zero, sub_zero]

@[simp] theorem logBase_smul_coe (ε : ℝ) (g : Multiplicative ℤ) (s : LogBase ε) :
    letI := logBaseAction ε
    ((g • s : LogBase ε) : ℂ) = (s : ℂ) - g.toAdd := rfl

theorem logBaseTranslate_holomorphic (ε : ℝ) (k : ℤ) :
    ContMDiff I₁ I₁ ω (logBaseTranslate ε k) := by
  intro s
  have he : ContMDiffAt I₁ I₁ ω (Subtype.val ∘ logBaseTranslate ε k) s ↔
      ContMDiffAt I₁ I₁ ω (logBaseTranslate ε k) s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.sub contMDiff_const) s)

theorem logBase_action_holomorphic (ε : ℝ) :
    letI := logBaseAction ε
    ∀ g : Multiplicative ℤ, ContMDiff I₁ I₁ ω (fun s : LogBase ε => g • s) := by
  let := logBaseAction ε
  intro g
  exact logBaseTranslate_holomorphic ε g.toAdd

theorem logBase_continuousConstSMul (ε : ℝ) :
    letI := logBaseAction ε
    ContinuousConstSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  exact ⟨fun g => (logBase_action_holomorphic ε g).continuous⟩

theorem logBase_free_action (ε : ℝ) :
    letI := logBaseAction ε
    IsCancelSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  constructor
  intro g h s he
  have hc := congrArg (Subtype.val : LogBase ε → ℂ) he
  change (s : ℂ) - g.toAdd = (s : ℂ) - h.toAdd at hc
  apply Multiplicative.toAdd.injective
  exact_mod_cast sub_right_inj.mp hc

@[simp] theorem baseExponential_smul (ε : ℝ) (g : Multiplicative ℤ) (s : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε (g • s) = baseExponential ε s := by
  let := logBaseAction ε
  apply Subtype.ext
  exact exponential_sub_int s g.toAdd

theorem baseExponential_eq_iff_orbit (ε : ℝ) (s t : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε s = baseExponential ε t ↔
      s ∈ MulAction.orbit (Multiplicative ℤ) t := by
  let := logBaseAction ε
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (exponential_eq_iff (s : ℂ) t).mp (congrArg Subtype.val h)
    refine ⟨Multiplicative.ofAdd (-k), Subtype.ext ?_⟩
    change (t : ℂ) - ((-k : ℤ) : ℂ) = (s : ℂ)
    rw [hk, Int.cast_neg, sub_neg_eq_add]
  · rintro ⟨g, rfl⟩
    exact baseExponential_smul ε g t

/-- A scalar inverse-function chart for the normalized exponential. -/
def scalarExponentialChart (s : ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  exponential_holomorphic.contDiffAt.toOpenPartialHomeomorph exponential
    ((exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (exponential_ne_zero s) exponential_factor_ne_zero)) (by simp)

@[simp] theorem scalarExponentialChart_apply (s t : ℂ) :
    scalarExponentialChart s t = exponential t := rfl

theorem scalarExponentialChart_mem_source (s : ℂ) :
    s ∈ (scalarExponentialChart s).source :=
  exponential_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    ((exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (exponential_ne_zero s) exponential_factor_ne_zero)) (by simp)

theorem scalarExponentialChart_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s) (scalarExponentialChart s).source :=
  exponential_holomorphic.contDiffOn

theorem scalarExponentialChart_symm_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s).symm (scalarExponentialChart s).target := by
  intro t ht
  exact ((scalarExponentialChart s).contDiffAt_symm ht
    ((exponential_hasDerivAt ((scalarExponentialChart s).symm t)).hasFDerivAt_equiv
      (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))
    exponential_holomorphic.contDiffAt).contDiffWithinAt

theorem exponential_isLocalDiffeomorph : IsLocalDiffeomorph I₁ I₁ ω exponential := by
  intro s
  refine ⟨{
    toPartialEquiv := (scalarExponentialChart s).toPartialEquiv
    open_source := (scalarExponentialChart s).open_source
    open_target := (scalarExponentialChart s).open_target
    contMDiffOn_toFun := (scalarExponentialChart_holomorphic s).contMDiffOn
    contMDiffOn_invFun := (scalarExponentialChart_symm_holomorphic s).contMDiffOn },
    scalarExponentialChart_mem_source s, ?_⟩
  intro t _
  rfl

theorem baseExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph I₁ I₁ ω (baseExponential ε) :=
  isLocalDiffeomorph_restrictOpens I₁ I₁ exponential_isLocalDiffeomorph
    (logBase ε) (puncturedDisc ε) (fun s hs => ⟨hs, exponential_ne_zero s⟩)

theorem baseExponential_holomorphic (ε : ℝ) : ContMDiff I₁ I₁ ω (baseExponential ε) :=
  (baseExponential_isLocalDiffeomorph ε).contMDiff

theorem baseExponential_isLocalHomeomorph (ε : ℝ) : IsLocalHomeomorph (baseExponential ε) :=
  (baseExponential_isLocalDiffeomorph ε).isLocalHomeomorph

theorem baseExponential_covering (ε : ℝ) :
    letI := logBaseAction ε
    IsQuotientCoveringMap (baseExponential ε) (Multiplicative ℤ) := by
  let := logBaseAction ε
  let := logBase_continuousConstSMul ε
  let := logBase_free_action ε
  exact quotientCoveringMap_of_localHomeomorph
    (baseExponential_isLocalHomeomorph ε) (baseExponential_surjective ε)
    (baseExponential_eq_iff_orbit ε)

/-- This is the standard product atlas, not an atlas transported from the cusp. -/
instance logBaseProductChartedSpace (ε : ℝ) :
    ChartedSpace (ℂ × ComplexPlane₂) (LogBase ε × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (LogBase ε × ComplexPlane₂))

instance logBaseProductManifold (ε : ℝ) :
    IsManifold Ilog ω (LogBase ε × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) (LogBase ε) ComplexPlane₂

/-- The explicit product decomposition of the logarithmic total space. -/
def logCoverProductEquiv (ε : ℝ) : LogCover ε ≃ (LogBase ε × ComplexPlane₂) where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun p := ⟨((p.1 : ℂ), p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem logCoverProductEquiv_fst_coe (ε : ℝ) (p : LogCover ε) :
    ((logCoverProductEquiv ε p).1 : ℂ) = p.1.1 := rfl

@[simp] theorem logCoverProductEquiv_snd (ε : ℝ) (p : LogCover ε) :
    (logCoverProductEquiv ε p).2 = p.1.2 := rfl

@[simp] theorem logCoverProductEquiv_symm_coe (ε : ℝ) (p : LogBase ε × ComplexPlane₂) :
    ((logCoverProductEquiv ε).symm p : ℂ × ComplexPlane₂) = ((p.1 : ℂ), p.2) := rfl

theorem logCoverProductEquiv_holomorphic (ε : ℝ) :
    ContMDiff Ilog Ilog ω (logCoverProductEquiv ε) := by
  have hb : ContMDiff Ilog I₁ ω (fun p : LogCover ε => p.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have hb' : ContMDiff Ilog I₁ ω
      (fun p : LogCover ε => (⟨p.1.1, p.2⟩ : LogBase ε)) := by
    intro p
    have he : ContMDiffAt Ilog I₁ ω
        (Subtype.val ∘ fun q : LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p ↔
      ContMDiffAt Ilog I₁ ω (fun q : LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp (hb p)
  have hz : ContMDiff Ilog I₂ ω (fun p : LogCover ε => p.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  rw [modelWithCornersSelf_prod]
  exact hb'.prodMk hz

theorem logCoverProductEquiv_symm_holomorphic (ε : ℝ) :
    ContMDiff Ilog Ilog ω (logCoverProductEquiv ε).symm := by
  have hb : ContMDiff Ilog I₁ ω (Prod.fst : LogBase ε × ComplexPlane₂ → LogBase ε) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hz : ContMDiff Ilog I₂ ω (Prod.snd : LogBase ε × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hp : ContMDiff Ilog Ilog ω
      (fun p : LogBase ε × ComplexPlane₂ => ((p.1 : ℂ), p.2)) :=
    (contMDiff_subtype_val.comp hb).prodMk_space hz
  intro p
  have he : ContMDiffAt Ilog Ilog ω
      (Subtype.val ∘ (logCoverProductEquiv ε).symm) p ↔
    ContMDiffAt Ilog Ilog ω (logCoverProductEquiv ε).symm p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hp p)

def logCoverProductBiholomorph (ε : ℝ) :
    Diffeomorph Ilog Ilog (LogCover ε) (LogBase ε × ComplexPlane₂) ω where
  toEquiv := logCoverProductEquiv ε
  contMDiff_toFun := logCoverProductEquiv_holomorphic ε
  contMDiff_invFun := logCoverProductEquiv_symm_holomorphic ε

@[simp] theorem logCoverProductBiholomorph_apply (ε : ℝ) (p : LogCover ε) :
    logCoverProductBiholomorph ε p = logCoverProductEquiv ε p := rfl

@[simp] theorem logCoverProductBiholomorph_symm_apply (ε : ℝ)
    (p : LogBase ε × ComplexPlane₂) :
    (logCoverProductBiholomorph ε).symm p = (logCoverProductEquiv ε).symm p := rfl

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily
