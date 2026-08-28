import Wikipedia.HopfProblem.CuspFibreTori

/-!
# The logarithmic cover of the whole punctured cusp

The two fibre logarithms and the logarithm of the base vary together.  The
maps below land in the actual open complements of the central fibres,
with their inherited topology and complex charts.  Their equality criterion
includes both the integer change of base logarithm and the full period lattice.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

def logDomain : TopologicalSpace.Opens (ℂ × ComplexPlane₂) :=
  ⟨(fun p : ℂ × ComplexPlane₂ => exponential p.1) ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage (exponential_holomorphic.continuous.comp continuous_fst)⟩

abbrev LogCover := logDomain ε

@[simp] theorem mem_logDomain (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ ‖exponential p.1‖ < ε := by
  simp [logDomain, Metric.mem_ball]

def puncturedTubeOpen : TopologicalSpace.Opens (Tube (disc ε)) :=
  ⟨{x | time (x : Space) ≠ 0},
    isOpen_ne_fun (time_holomorphic.continuous.comp continuous_subtype_val) continuous_const⟩

abbrev PuncturedTube := puncturedTubeOpen ε

def puncturedQuotientOpen : TopologicalSpace.Opens (QuotientSpace C ε) :=
  ⟨{x | projection C ε x ≠ 0},
    isOpen_ne_fun (projection_continuous C ε) continuous_const⟩

abbrev PuncturedQuotient := puncturedQuotientOpen C ε

def totalExponentialPoint (p : ℂ × ComplexPlane₂) : Space :=
  exponentialPoint (exponential p.1) p.2

@[simp] theorem time_totalExponentialPoint (p : ℂ × ComplexPlane₂) :
    time (totalExponentialPoint p) = exponential p.1 :=
  time_exponentialPoint (exponential_ne_zero p.1) p.2

theorem totalExponentialPoint_mem (p : ℂ × ComplexPlane₂) :
    totalExponentialPoint p ∈ openTorus :=
  exponentialPoint_mem (exponential_ne_zero p.1) p.2

theorem totalExponentialPoint_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω totalExponentialPoint := by
  apply (inclusion_holomorphic referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  apply (monomial_contDiffOn referenceTriangle.dual ω).comp
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
    · exact exponential_holomorphic.comp contDiff_fst
  · intro p _
    exact torus_subset_domain _ (exponentialCoordinates_mem (exponential_ne_zero p.1) p.2)

def totalExponentialLift (p : LogCover ε) : Tube (disc ε) :=
  ⟨totalExponentialPoint p, by
    change time (totalExponentialPoint p) ∈ Metric.ball 0 ε
    rw [time_totalExponentialPoint]
    exact p.2⟩

@[simp] theorem totalExponentialLift_coe (p : LogCover ε) :
    (totalExponentialLift ε p : Space) = totalExponentialPoint p := rfl

def puncturedExponential (p : LogCover ε) : PuncturedTube ε :=
  ⟨totalExponentialLift ε p, by
    change time (totalExponentialPoint p) ≠ 0
    rw [time_totalExponentialPoint]
    exact exponential_ne_zero _⟩

def totalCuspCover (p : LogCover ε) : QuotientSpace C ε :=
  quotientMap C ε (totalExponentialLift ε p)

@[simp] theorem projection_totalCuspCover (p : LogCover ε) :
    projection C ε (totalCuspCover C ε p) = exponential p.1.1 :=
  time_totalExponentialPoint p

def puncturedCuspCover (p : LogCover ε) : PuncturedQuotient C ε :=
  ⟨totalCuspCover C ε p, by
    change projection C ε (totalCuspCover C ε p) ≠ 0
    rw [projection_totalCuspCover]
    exact exponential_ne_zero _⟩

def puncturedQuotientMap (p : PuncturedTube ε) : PuncturedQuotient C ε :=
  ⟨quotientMap C ε p, p.2⟩

@[simp] theorem puncturedQuotientMap_puncturedExponential (p : LogCover ε) :
    puncturedQuotientMap C ε (puncturedExponential ε p) = puncturedCuspCover C ε p := rfl

theorem totalExponentialLift_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  intro p
  have he : ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun q => (totalExponentialLift ε q : Space)) p ↔
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (totalExponentialLift ε) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (totalExponentialPoint_holomorphic.comp contMDiff_subtype_val p)

theorem puncturedExponential_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (puncturedExponential ε) := by
  intro p
  have he : ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun q => (puncturedExponential ε q : Tube (disc ε))) p ↔
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (puncturedExponential ε) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (totalExponentialLift_holomorphic ε p)

theorem puncturedExponential_surjective : Function.Surjective (puncturedExponential ε) := by
  intro x
  let t : ℂ := time (x.1 : Space)
  have ht : t ≠ 0 := x.2
  obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre ht (x := (x.1 : Space)) rfl
  let p : LogCover ε := ⟨(logarithm t, z), by
    change exponential (logarithm t) ∈ Metric.ball 0 ε
    rw [exponential_logarithm ht]
    exact x.1.2⟩
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  change exponentialPoint (exponential (logarithm t)) z = (x.1 : Space)
  rw [exponential_logarithm ht]
  exact hz

theorem puncturedQuotientMap_surjective : Function.Surjective (puncturedQuotientMap C ε) := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.1
  have hp : time (x : Space) ≠ 0 := by
    have h := q.2
    change projection C ε q.1 ≠ 0 at h
    rwa [← hx] at h
  exact ⟨⟨x, hp⟩, Subtype.ext hx⟩

theorem puncturedCuspCover_surjective : Function.Surjective (puncturedCuspCover C ε) :=
  (puncturedQuotientMap_surjective C ε).comp (puncturedExponential_surjective ε)

theorem totalExponentialPoint_eq_iff (p q : ℂ × ComplexPlane₂) :
    totalExponentialPoint p = totalExponentialPoint q ↔
      ∃ (k : ℤ) (m : Fin 2 → ℤ),
        p.1 = q.1 + k ∧ p.2 = q.2 + (fun i => (m i : ℂ)) := by
  constructor
  · intro h
    have hs : exponential p.1 = exponential q.1 := by
      simpa only [time_totalExponentialPoint] using congrArg time h
    obtain ⟨k, hk⟩ := (exponential_eq_iff _ _).mp hs
    change exponentialPoint (exponential p.1) p.2 =
      exponentialPoint (exponential q.1) q.2 at h
    rw [hs] at h
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero q.1) _ _).mp h
    exact ⟨k, m, hk, hm⟩
  · rintro ⟨k, m, hk, hm⟩
    have hs := (exponential_eq_iff p.1 q.1).mpr ⟨k, hk⟩
    change exponentialPoint (exponential p.1) p.2 =
      exponentialPoint (exponential q.1) q.2
    rw [hs]
    exact (exponentialPoint_eq_iff (exponential_ne_zero q.1) _ _).mpr ⟨m, hm⟩

/-- The explicit identifications on the varying logarithmic cover. -/
def TotalPeriodRelated (p q : ℂ × ComplexPlane₂) : Prop :=
  ∃ (k : ℤ) (m n : Fin 2 → ℤ), p.1 = q.1 + k ∧
    p.2 = q.2 + (fun i => (m i : ℂ)) +
      logarithmicPeriod C q.1 *ᵥ (fun i => (n i : ℂ))

theorem totalCuspCover_eq_iff (p q : LogCover ε) :
    totalCuspCover C ε p = totalCuspCover C ε q ↔ TotalPeriodRelated C p q := by
  let := tubeAction C (disc ε)
  constructor
  · intro h
    have hs : exponential p.1.1 = exponential q.1.1 := by
      simpa only [projection_totalCuspCover] using congrArg (projection C ε) h
    obtain ⟨k, hk⟩ := (exponential_eq_iff _ _).mp hs
    have horb := Quotient.exact h
    change totalExponentialLift ε p ∈
      MulAction.orbit LatticeGroup (totalExponentialLift ε q) at horb
    obtain ⟨g, hg⟩ := horb
    have hp : exponentialPoint (exponential q.1.1) p.1.2 =
        exponentialPoint (exponential q.1.1)
          (q.1.2 + logarithmicPeriod C q.1.1 *ᵥ (fun i => (g.toAdd i : ℂ))) := by
      have he := (congrArg Subtype.val hg).symm.trans
        (twistedTranslate_exponentialPoint C q.1.1 g.toAdd q.1.2)
      change exponentialPoint (exponential p.1.1) p.1.2 = _ at he
      rwa [hs] at he
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mp hp
    refine ⟨k, m, g.toAdd, hk, ?_⟩
    rw [hm]
    abel
  · rintro ⟨k, m, n, hk, hmn⟩
    have hs := (exponential_eq_iff p.1.1 q.1.1).mpr ⟨k, hk⟩
    have hp : totalExponentialPoint p =
        twistedTranslate C n (totalExponentialPoint q) := by
      change exponentialPoint (exponential p.1.1) p.1.2 =
        twistedTranslate C n (exponentialPoint (exponential q.1.1) q.1.2)
      rw [hs, twistedTranslate_exponentialPoint]
      apply (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mpr
      refine ⟨m, ?_⟩
      rw [hmn]
      abel
    have hl : totalExponentialLift ε p =
        tubeTranslate C (disc ε) n (totalExponentialLift ε q) := Subtype.ext hp
    change quotientMap C ε (totalExponentialLift ε p) =
      quotientMap C ε (totalExponentialLift ε q)
    rw [hl, quotientMap_translate]

theorem puncturedCuspCover_eq_iff (p q : LogCover ε) :
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔ TotalPeriodRelated C p q := by
  rw [← totalCuspCover_eq_iff C ε p q]
  exact Subtype.ext_iff

end Wikipedia.HopfProblem.CuspUniformization
