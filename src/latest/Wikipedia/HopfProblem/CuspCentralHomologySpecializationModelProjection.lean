import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelBasic

/-!
# The original quotient projection on a literal time fibre

The fixed-time projection is obtained by restricting the existing cusp
quotient map. Its topology and exact fibres are those of the original
quotient, independently of the redundant closed-tube presentation.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (t : ℂ) (htε : ‖t‖ < ε)

/-- The actual quotient map, restricted to the original fixed-time fibre. -/
def fibreProjection : ToricFibre t → ActualQuotientFibre C ε t :=
  quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl ∘ levelProjection C htε t ∘
    toricFibreLevelHomeomorph ‖t‖ t le_rfl

@[simp] theorem fibreProjection_coe (x : ToricFibre t) :
    (fibreProjection C ε t htε x : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.quotientMap C ε ⟨(x : Space), by
        change time (x : Space) ∈ Metric.ball 0 ε
        rw [x.2]
        simpa only [Metric.mem_ball, dist_zero_right] using htε⟩ := rfl

theorem fibreProjection_continuous : Continuous (fibreProjection C ε t htε) :=
  (quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).continuous.comp
    ((levelProjection_continuous C htε t).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).continuous)

theorem fibreProjection_surjective : Function.Surjective (fibreProjection C ε t htε) :=
  (quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).surjective.comp
    ((levelProjection_surjective C htε t).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).surjective)

theorem fibreProjection_isOpenQuotientMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (fibreProjection C ε t htε) :=
  (quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).isOpenQuotientMap.comp
    ((levelProjection_isOpenQuotientMap C htε t hC).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).isOpenQuotientMap)

theorem fibreProjection_isQuotientMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsQuotientMap (fibreProjection C ε t htε) :=
  (fibreProjection_isOpenQuotientMap C ε t htε hC).isQuotientMap

/-- All and only the original twisted integral translations identify fibre points. -/
theorem fibreProjection_eq_iff (x y : ToricFibre t) :
    fibreProjection C ε t htε x = fibreProjection C ε t htε y ↔
      ∃ v : Fin 2 → ℤ, twistedTranslate C v (y : Space) = (x : Space) := by
  change quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
      (levelProjection C htε t (toricFibreLevelHomeomorph ‖t‖ t le_rfl x)) =
    quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
      (levelProjection C htε t (toricFibreLevelHomeomorph ‖t‖ t le_rfl y)) ↔ _
  rw [(quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).injective.eq_iff,
    levelProjection_eq_iff]
  apply exists_congr
  intro v
  exact ⟨fun h => congrArg (fun z : ClosedTube ‖t‖ => (z : Space)) h,
    fun h => Subtype.ext h⟩

/-- Restrict the actual deck translation without choosing another fibre model. -/
def toricFibreTranslate (v : Fin 2 → ℤ) (x : ToricFibre t) : ToricFibre t :=
  ⟨twistedTranslate C v (x : Space), by rw [time_twistedTranslate, x.2]⟩

@[simp] theorem toricFibreTranslate_coe (v : Fin 2 → ℤ) (x : ToricFibre t) :
    (toricFibreTranslate C t v x : Space) = twistedTranslate C v (x : Space) := rfl

@[simp] theorem fibreProjection_translate (v : Fin 2 → ℤ) (x : ToricFibre t) :
    fibreProjection C ε t htε (toricFibreTranslate C t v x) = fibreProjection C ε t htε x :=
  (fibreProjection_eq_iff C ε t htε _ x).mpr ⟨v, rfl⟩

/-- The same original map is obtained in any closed tube containing the level. -/
theorem fibreProjection_eq_levelProjection (η : ℝ) (hηε : η < ε) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) :
    fibreProjection C ε t htε x =
      quotientLevelFibreHomeomorph C ε η t htη
        (levelProjection C hηε t (toricFibreLevelHomeomorph η t htη x)) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
