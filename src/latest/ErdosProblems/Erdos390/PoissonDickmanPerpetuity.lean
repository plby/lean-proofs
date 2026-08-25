/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import ErdosProblems.Erdos390.PoissonDickmanConditioning

namespace Erdos390

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance poissonDickmanPerpetuityExpMeasureProbability :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Delete the first exponential gap. -/
def poissonDickmanGapTail
    (e : PoissonDickmanGapSequence) :
    PoissonDickmanGapSequence :=
  fun n ↦ e (n + 1)

/--
The scale factor contributed by the first exponential gap.  It is
uniform on `(0,1)` under the gap law.
-/
def poissonDickmanHeadMultiplier
    (e : PoissonDickmanGapSequence) : ℝ :=
  Real.exp (-max (e 0) 0)

theorem measurable_poissonDickmanGapTail :
    Measurable poissonDickmanGapTail := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

theorem measurable_poissonDickmanHeadMultiplier :
    Measurable poissonDickmanHeadMultiplier := by
  exact ((measurable_pi_apply 0).max measurable_const).neg.exp

theorem poissonDickmanGapTail_comap :
    MeasurableSpace.comap poissonDickmanGapTail
        (inferInstance : MeasurableSpace PoissonDickmanGapSequence) =
      ⨆ n : ℕ,
        MeasurableSpace.comap
          (fun e : PoissonDickmanGapSequence ↦ e (n + 1))
          (inferInstance : MeasurableSpace ℝ) := by
  change
    MeasurableSpace.comap
        (fun e : PoissonDickmanGapSequence ↦
          fun n : ℕ ↦ e (n + 1))
        (inferInstance : MeasurableSpace PoissonDickmanGapSequence) =
      _
  exact
    MeasurableSpace.comap_process_pi
      (X := fun _ : ℕ ↦ ℝ)
      (fun n : ℕ ↦
        fun e : PoissonDickmanGapSequence ↦ e (n + 1))

/--
Deleting the first gap leaves a fresh sequence of independent
rate-one exponential gaps.
-/
theorem map_poissonDickmanGapTail_gapLaw :
    poissonDickmanGapLaw.map poissonDickmanGapTail =
      poissonDickmanGapLaw := by
  unfold poissonDickmanGapLaw poissonDickmanGapTail
  simpa only using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ expMeasure 1)
      Nat.succ_injective)

/-- The first gap has the rate-one exponential law. -/
theorem map_poissonDickmanGapHead_gapLaw :
    poissonDickmanGapLaw.map
        (fun e : PoissonDickmanGapSequence ↦ e 0) =
      expMeasure 1 := by
  unfold poissonDickmanGapLaw
  exact Measure.infinitePi_map_eval _ _

/--
The first exponential gap is independent of the entire remaining
gap sequence.
-/
theorem indepFun_poissonDickmanGapHead_gapTail :
    (fun e : PoissonDickmanGapSequence ↦ e 0)
        ⟂ᵢ[poissonDickmanGapLaw]
      poissonDickmanGapTail := by
  let m : ℕ → MeasurableSpace PoissonDickmanGapSequence :=
    fun i ↦
      MeasurableSpace.comap
        (fun e : PoissonDickmanGapSequence ↦ e i)
        (inferInstance : MeasurableSpace ℝ)
  have hfun :
      iIndepFun
        (fun i : ℕ ↦
          fun e : PoissonDickmanGapSequence ↦ e i)
        poissonDickmanGapLaw := by
    unfold poissonDickmanGapLaw
    exact
      iIndepFun_infinitePi
        (X := fun _ : ℕ ↦ id)
        fun _ ↦ measurable_id
  have hind : iIndep m poissonDickmanGapLaw :=
    hfun
  have hle :
      ∀ i,
        m i ≤
          (inferInstance :
            MeasurableSpace PoissonDickmanGapSequence) := by
    intro i
    exact (measurable_pi_apply i).comap_le
  have hdisj :
      Disjoint ({0} : Set ℕ) (Ioi 0) := by
    rw [Set.disjoint_left]
    intro i hi0 hipos
    simp only [mem_singleton_iff] at hi0
    change 0 < i at hipos
    omega
  have hindGroups :=
    indep_iSup_of_disjoint hle hind hdisj
  have hright :
      (⨆ i ∈ Ioi (0 : ℕ), m i) =
        ⨆ n : ℕ, m (n + 1) := by
    apply le_antisymm
    · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
      obtain ⟨n, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hi)
      exact le_iSup (fun n : ℕ ↦ m (n + 1)) n
    · refine iSup_le fun n ↦ ?_
      exact
        le_iSup_of_le (n + 1) <|
          le_iSup_of_le
            (show n + 1 ∈ Ioi (0 : ℕ) by
              change 0 < n + 1
              omega)
            le_rfl
  change
    Indep
      (MeasurableSpace.comap
        (fun e : PoissonDickmanGapSequence ↦ e 0)
        (inferInstance : MeasurableSpace ℝ))
      (MeasurableSpace.comap poissonDickmanGapTail
        (inferInstance :
          MeasurableSpace PoissonDickmanGapSequence))
      poissonDickmanGapLaw
  rw [poissonDickmanGapTail_comap]
  change
    Indep (m 0) (⨆ n : ℕ, m (n + 1))
      poissonDickmanGapLaw
  simpa only [iSup_singleton, hright] using hindGroups

/--
Consequently the head-tail split of the product gap law is literally
the product of the head exponential law and a fresh gap law.
-/
theorem map_poissonDickmanGapHeadTail_gapLaw :
    poissonDickmanGapLaw.map
        (fun e : PoissonDickmanGapSequence ↦
          (e 0, poissonDickmanGapTail e)) =
      (expMeasure 1).prod poissonDickmanGapLaw := by
  calc
    _ =
        (poissonDickmanGapLaw.map
            (fun e : PoissonDickmanGapSequence ↦ e 0)).prod
          (poissonDickmanGapLaw.map
            poissonDickmanGapTail) :=
      IndepFun.map_prod_eq_prod_map_map
        (measurable_pi_apply 0).aemeasurable
        measurable_poissonDickmanGapTail.aemeasurable
        indepFun_poissonDickmanGapHead_gapTail
    _ = _ := by
      rw [map_poissonDickmanGapHead_gapLaw,
        map_poissonDickmanGapTail_gapLaw]

/-- Lebesgue-uniform probability measure on `(0,1]`. -/
def poissonDickmanUnitUniformLaw : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure poissonDickmanUnitUniformLaw := by
  constructor
  simp [poissonDickmanUnitUniformLaw, Real.volume_Ioc]

theorem expMeasure_one_singleton
    (t : ℝ) :
    expMeasure 1 ({t} : Set ℝ) = 0 := by
  change
    volume.withDensity (exponentialPDF 1) {t} = 0
  rw [withDensity_apply
    (exponentialPDF 1) (measurableSet_singleton t)]
  simp

/-- The rate-one exponential survival function. -/
theorem expMeasure_one_Ici
    (t : ℝ) (ht : 0 ≤ t) :
    expMeasure 1 (Ici t) =
      ENNReal.ofReal (Real.exp (-t)) := by
  have hIic :
      expMeasure 1 (Iic t) =
        expMeasure 1 (Iio t) := by
    calc
      expMeasure 1 (Iic t) =
          expMeasure 1 (Iio t ∪ {t}) := by
        rw [Iio_union_right]
      _ =
          expMeasure 1 (Iio t) +
            expMeasure 1 ({t} : Set ℝ) := by
        rw [measure_union]
        · simp
        · exact measurableSet_singleton t
      _ = expMeasure 1 (Iio t) := by
        rw [expMeasure_one_singleton]
        simp
  have hIicValue :
      expMeasure 1 (Iic t) =
        ENNReal.ofReal
          (1 - Real.exp (-t)) := by
    rw [← ofReal_cdf]
    rw [cdf_expMeasure_eq one_pos]
    simp [ht]
  rw [← compl_Iio,
    measure_compl measurableSet_Iio
      (measure_ne_top _ _),
    hIic.symm, hIicValue]
  rw [measure_univ]
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1]
  · congr 1
    ring
  · exact sub_nonneg.mpr <|
      Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr ht)

/--
Exponentiating the negative of a rate-one exponential variable gives
the Lebesgue-uniform law on `(0,1]`.
-/
theorem map_exp_neg_expMeasure_one :
    (expMeasure 1).map
        (fun x : ℝ ↦ Real.exp (-x)) =
      poissonDickmanUnitUniformLaw := by
  unfold poissonDickmanUnitUniformLaw
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply (by fun_prop)
      measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases ha0 : a ≤ 0
  · have hpre :
        (fun x : ℝ ↦ Real.exp (-x)) ⁻¹'
            Iic a = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic,
        Set.mem_empty_iff_false, iff_false]
      intro h
      exact
        (not_le_of_gt (Real.exp_pos _))
          (h.trans ha0)
    have hinter :
        Iic a ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic,
        mem_Ioc, Set.mem_empty_iff_false,
        iff_false]
      intro h
      linarith
    rw [hpre, hinter]
    simp
  · have ha0' : 0 < a := lt_of_not_ge ha0
    by_cases ha1 : 1 ≤ a
    · have hae :
          (fun x : ℝ ↦ Real.exp (-x)) ⁻¹'
              Iic a =ᵐ[expMeasure 1]
            (Set.univ : Set ℝ) := by
        filter_upwards
          [ae_nonneg_expMeasure_one] with x hx
        apply propext
        change Real.exp (-x) ≤ a ↔ True
        rw [iff_true]
        exact
          (Real.exp_le_one_iff.mpr
            (neg_nonpos.mpr hx)).trans ha1
      have hinter :
          Iic a ∩ Ioc (0 : ℝ) 1 =
            Ioc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic,
          mem_Ioc]
        constructor
        · exact fun h ↦ h.2
        · intro h
          exact ⟨h.2.trans ha1, h⟩
      rw [measure_congr hae, hinter,
        measure_univ, Real.volume_Ioc]
      norm_num
    · have ha1' : a < 1 := lt_of_not_ge ha1
      have ht : 0 ≤ -Real.log a := by
        exact neg_nonneg.mpr <|
          Real.log_nonpos ha0'.le ha1'.le
      have hpre :
          (fun x : ℝ ↦ Real.exp (-x)) ⁻¹'
              Iic a =
            Ici (-Real.log a) := by
        ext x
        simp only [mem_preimage, mem_Iic,
          mem_Ici]
        rw [← Real.le_log_iff_exp_le ha0']
        constructor <;> intro h <;> linarith
      have hinter :
          Iic a ∩ Ioc (0 : ℝ) 1 =
            Ioc 0 a := by
        ext x
        simp only [mem_inter_iff, mem_Iic,
          mem_Ioc]
        constructor
        · intro h
          exact ⟨h.2.1, h.1⟩
        · intro h
          exact
            ⟨h.2, h.1,
              (h.2.trans_lt ha1').le⟩
      rw [hpre, expMeasure_one_Ici _ ht,
        hinter, Real.volume_Ioc]
      rw [show - -Real.log a = Real.log a by
          ring,
        Real.exp_log ha0']
      congr 1
      ring

/-- The first random scale factor is uniform on `(0,1]`. -/
theorem map_poissonDickmanHeadMultiplier_gapLaw :
    poissonDickmanGapLaw.map
        poissonDickmanHeadMultiplier =
      poissonDickmanUnitUniformLaw := by
  let φ : ℝ → ℝ :=
    fun x ↦ Real.exp (-max x 0)
  calc
    poissonDickmanGapLaw.map
        poissonDickmanHeadMultiplier =
        (poissonDickmanGapLaw.map
          (fun e : PoissonDickmanGapSequence ↦
            e 0)).map φ := by
      symm
      change
        (poissonDickmanGapLaw.map
            (fun e : PoissonDickmanGapSequence ↦ e 0)).map φ =
          poissonDickmanGapLaw.map
            (φ ∘
              fun e : PoissonDickmanGapSequence ↦ e 0)
      exact
        Measure.map_map
          (by fun_prop) (measurable_pi_apply 0)
    _ = (expMeasure 1).map φ := by
      rw [map_poissonDickmanGapHead_gapLaw]
    _ =
        (expMeasure 1).map
          (fun x : ℝ ↦ Real.exp (-x)) := by
      apply Measure.map_congr
      filter_upwards
        [ae_nonneg_expMeasure_one] with x hx
      simp [φ, max_eq_left hx]
    _ = poissonDickmanUnitUniformLaw :=
      map_exp_neg_expMeasure_one

/-- Total mass of the fresh configuration generated by the tail gaps. -/
def poissonDickmanTailTotal
    (e : PoissonDickmanGapSequence) : ℝ :=
  poissonDickmanTotalMass
    (poissonDickmanSpacingConfiguration
      (poissonDickmanGapTail e))

theorem measurable_poissonDickmanTailTotal :
    Measurable poissonDickmanTailTotal :=
  measurable_poissonDickmanTotalMass.comp <|
    measurable_poissonDickmanSpacingConfiguration.comp
      measurable_poissonDickmanGapTail

/-- The tail total has the same law as the original total mass. -/
theorem map_poissonDickmanTailTotal_gapLaw :
    poissonDickmanGapLaw.map
        poissonDickmanTailTotal =
      poissonDickmanTotalMassLaw := by
  unfold poissonDickmanTailTotal
  unfold poissonDickmanTotalMassLaw
  unfold poissonDickmanUnconditionedLaw
  calc
    poissonDickmanGapLaw.map
        (fun e : PoissonDickmanGapSequence ↦
          poissonDickmanTotalMass
            (poissonDickmanSpacingConfiguration
              (poissonDickmanGapTail e))) =
        (poissonDickmanGapLaw.map
          poissonDickmanGapTail).map
            (poissonDickmanTotalMass ∘
              poissonDickmanSpacingConfiguration) := by
      symm
      exact
        Measure.map_map
          (measurable_poissonDickmanTotalMass.comp
            measurable_poissonDickmanSpacingConfiguration)
          measurable_poissonDickmanGapTail
    _ =
        poissonDickmanGapLaw.map
          (poissonDickmanTotalMass ∘
            poissonDickmanSpacingConfiguration) := by
      rw [map_poissonDickmanGapTail_gapLaw]
    _ =
        (poissonDickmanGapLaw.map
          poissonDickmanSpacingConfiguration).map
            poissonDickmanTotalMass := by
      symm
      exact
        Measure.map_map
          measurable_poissonDickmanTotalMass
          measurable_poissonDickmanSpacingConfiguration

/--
The uniform first scale factor and the fresh tail total are
independent.
-/
theorem indepFun_poissonDickmanHeadMultiplier_tailTotal :
    poissonDickmanHeadMultiplier
        ⟂ᵢ[poissonDickmanGapLaw]
      poissonDickmanTailTotal := by
  have h :=
    indepFun_poissonDickmanGapHead_gapTail.comp
      (show
        Measurable
          (fun x : ℝ ↦ Real.exp (-max x 0)) by
        fun_prop)
      (measurable_poissonDickmanTotalMass.comp
        measurable_poissonDickmanSpacingConfiguration)
  change
    (fun e : PoissonDickmanGapSequence ↦
      Real.exp (-max (e 0) 0))
        ⟂ᵢ[poissonDickmanGapLaw]
      (fun e : PoissonDickmanGapSequence ↦
        poissonDickmanTotalMass
          (poissonDickmanSpacingConfiguration
            (poissonDickmanGapTail e)))
  exact h

/--
The joint law of the scale factor and tail total is the product of a
uniform `(0,1]` variable and an independent copy of the total mass.
-/
theorem map_poissonDickmanMultiplierTailTotal_gapLaw :
    poissonDickmanGapLaw.map
        (fun e : PoissonDickmanGapSequence ↦
          (poissonDickmanHeadMultiplier e,
            poissonDickmanTailTotal e)) =
      poissonDickmanUnitUniformLaw.prod
        poissonDickmanTotalMassLaw := by
  calc
    _ =
        (poissonDickmanGapLaw.map
          poissonDickmanHeadMultiplier).prod
        (poissonDickmanGapLaw.map
          poissonDickmanTailTotal) :=
      IndepFun.map_prod_eq_prod_map_map
        measurable_poissonDickmanHeadMultiplier.aemeasurable
        measurable_poissonDickmanTailTotal.aemeasurable
        indepFun_poissonDickmanHeadMultiplier_tailTotal
    _ = _ := by
      rw [map_poissonDickmanHeadMultiplier_gapLaw,
        map_poissonDickmanTailTotal_gapLaw]

/-- The map `(x,t) ↦ x(1+t)` in the perpetuity equation. -/
def poissonDickmanPerpetuityMap
    (q : ℝ × ℝ) : ℝ :=
  q.1 * (1 + q.2)

theorem measurable_poissonDickmanPerpetuityMap :
    Measurable poissonDickmanPerpetuityMap := by
  unfold poissonDickmanPerpetuityMap
  fun_prop

theorem poissonDickmanSpacingConfiguration_zero
    (e : PoissonDickmanGapSequence) :
    poissonDickmanSpacingConfiguration e 0 =
      poissonDickmanHeadMultiplier e := by
  simp [poissonDickmanSpacingConfiguration_eq_prod,
    poissonDickmanHeadMultiplier]

/--
After its first atom, the configuration is a scaled fresh copy of
the configuration generated by the remaining gaps.
-/
theorem poissonDickmanSpacingConfiguration_succ
    (e : PoissonDickmanGapSequence) (n : ℕ) :
    poissonDickmanSpacingConfiguration e (n + 1) =
      poissonDickmanHeadMultiplier e *
        poissonDickmanSpacingConfiguration
          (poissonDickmanGapTail e) n := by
  rw [poissonDickmanSpacingConfiguration_eq_prod,
    poissonDickmanSpacingConfiguration_eq_prod]
  unfold poissonDickmanHeadMultiplier poissonDickmanGapTail
  rw [Finset.prod_range_succ']
  rw [mul_comm]

theorem summable_poissonDickmanSpacingConfiguration_iff_tail
    (e : PoissonDickmanGapSequence) :
    Summable (poissonDickmanSpacingConfiguration e) ↔
      Summable
        (poissonDickmanSpacingConfiguration
          (poissonDickmanGapTail e)) := by
  rw [← summable_nat_add_iff 1]
  simp_rw [poissonDickmanSpacingConfiguration_succ]
  constructor
  · intro h
    have hnonzero :
        poissonDickmanHeadMultiplier e ≠ 0 :=
      (Real.exp_pos _).ne'
    exact
      (summable_mul_left_iff hnonzero).mp h
  · intro h
    exact h.mul_left _

/--
The total mass satisfies the perpetuity identity
`T = X (1 + T')`, where `X` is the first scale factor and `T'`
is the total mass generated by the tail gaps.
-/
theorem poissonDickmanTotalMass_spacingConfiguration
    (e : PoissonDickmanGapSequence)
    (he :
      Summable
        (poissonDickmanSpacingConfiguration
          (poissonDickmanGapTail e))) :
    poissonDickmanTotalMass
        (poissonDickmanSpacingConfiguration e) =
      poissonDickmanHeadMultiplier e *
        (1 +
          poissonDickmanTotalMass
            (poissonDickmanSpacingConfiguration
              (poissonDickmanGapTail e))) := by
  have hfull :
      Summable (poissonDickmanSpacingConfiguration e) :=
    (summable_poissonDickmanSpacingConfiguration_iff_tail e).2 he
  have hsplit :=
    hfull.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [poissonDickmanSpacingConfiguration_zero] at hsplit
  have htail :
      (∑' n : ℕ,
          poissonDickmanSpacingConfiguration e (n + 1)) =
        poissonDickmanHeadMultiplier e *
          poissonDickmanTotalMass
            (poissonDickmanSpacingConfiguration
              (poissonDickmanGapTail e)) := by
    simp_rw [poissonDickmanSpacingConfiguration_succ]
    exact he.tsum_mul_left _
  rw [htail] at hsplit
  calc
    poissonDickmanTotalMass
        (poissonDickmanSpacingConfiguration e) =
        poissonDickmanHeadMultiplier e +
          poissonDickmanHeadMultiplier e *
            poissonDickmanTotalMass
              (poissonDickmanSpacingConfiguration
                (poissonDickmanGapTail e)) :=
      hsplit.symm
    _ = _ := by ring

/--
The perpetuity identity holds almost surely under the product gap
law, with the tail total finite and summable.
-/
theorem ae_poissonDickmanTotalMass_perpetuity :
    ∀ᵐ e : PoissonDickmanGapSequence
      ∂poissonDickmanGapLaw,
      Summable
          (poissonDickmanSpacingConfiguration
            (poissonDickmanGapTail e)) ∧
        poissonDickmanTotalMass
            (poissonDickmanSpacingConfiguration e) =
          poissonDickmanHeadMultiplier e *
            (1 +
              poissonDickmanTotalMass
                (poissonDickmanSpacingConfiguration
                  (poissonDickmanGapTail e))) := by
  have htail :
      ∀ᵐ e : PoissonDickmanGapSequence
        ∂poissonDickmanGapLaw,
        Summable
          (poissonDickmanSpacingConfiguration
            (poissonDickmanGapTail e)) := by
    have hbase :
        ∀ᵐ e : PoissonDickmanGapSequence
          ∂poissonDickmanGapLaw,
          IsPoissonDickmanAbsolutelySummableConfiguration
            (poissonDickmanSpacingConfiguration e) := by
      filter_upwards
        [ae_poissonDickmanSpacingTotal_lt_top] with e he
      constructor
      · intro n
        exact
          ⟨(poissonDickmanSpacingConfiguration_mem_Ioc e n).1.le,
            (poissonDickmanSpacingConfiguration_mem_Ioc e n).2⟩
      · simpa only [
          abs_of_pos
            (poissonDickmanSpacingConfiguration_mem_Ioc e _).1] using he
    have habsTail :
        ∀ᵐ e : PoissonDickmanGapSequence
          ∂poissonDickmanGapLaw,
          IsPoissonDickmanAbsolutelySummableConfiguration
            (poissonDickmanSpacingConfiguration
              (poissonDickmanGapTail e)) := by
      have hmap :
          ∀ᵐ x : PoissonDickmanGapSequence
            ∂poissonDickmanGapLaw.map poissonDickmanGapTail,
            IsPoissonDickmanAbsolutelySummableConfiguration
              (poissonDickmanSpacingConfiguration x) := by
        rw [map_poissonDickmanGapTail_gapLaw]
        exact hbase
      exact
        (ae_map_iff
          measurable_poissonDickmanGapTail.aemeasurable
          (measurableSet_isPoissonDickmanAbsolutelySummableConfiguration.preimage
            measurable_poissonDickmanSpacingConfiguration)).1
          hmap
    exact habsTail.mono fun _ h ↦
      h.toSummableConfiguration.2
  exact htail.mono fun e he ↦
    ⟨he, poissonDickmanTotalMass_spacingConfiguration e he⟩

/--
Distributional perpetuity equation for the total mass:
`T` has the same law as `X(1+T')`, where `X` is uniform on `(0,1]`
and `T'` is an independent copy of `T`.
-/
theorem poissonDickmanTotalMassLaw_perpetuity :
    poissonDickmanTotalMassLaw =
      (poissonDickmanUnitUniformLaw.prod
        poissonDickmanTotalMassLaw).map
          poissonDickmanPerpetuityMap := by
  calc
    poissonDickmanTotalMassLaw =
        poissonDickmanGapLaw.map
          (fun e : PoissonDickmanGapSequence ↦
            poissonDickmanTotalMass
              (poissonDickmanSpacingConfiguration e)) := by
      unfold poissonDickmanTotalMassLaw
      unfold poissonDickmanUnconditionedLaw
      exact
        Measure.map_map
          measurable_poissonDickmanTotalMass
          measurable_poissonDickmanSpacingConfiguration
    _ =
        poissonDickmanGapLaw.map
          (fun e : PoissonDickmanGapSequence ↦
            poissonDickmanPerpetuityMap
              (poissonDickmanHeadMultiplier e,
                poissonDickmanTailTotal e)) := by
      apply Measure.map_congr
      exact
        (ae_poissonDickmanTotalMass_perpetuity).mono
          fun e he ↦ by
            simpa [poissonDickmanPerpetuityMap,
              poissonDickmanTailTotal] using he.2
    _ =
        (poissonDickmanGapLaw.map
          (fun e : PoissonDickmanGapSequence ↦
            (poissonDickmanHeadMultiplier e,
              poissonDickmanTailTotal e))).map
          poissonDickmanPerpetuityMap := by
      symm
      exact
        Measure.map_map
          measurable_poissonDickmanPerpetuityMap
          (measurable_poissonDickmanHeadMultiplier.prodMk
            measurable_poissonDickmanTailTotal)
    _ = _ := by
      rw [map_poissonDickmanMultiplierTailTotal_gapLaw]

end

end Erdos390
