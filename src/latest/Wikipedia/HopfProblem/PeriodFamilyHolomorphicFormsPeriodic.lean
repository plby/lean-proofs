import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsRestrictions
import Wikipedia.HopfProblem.PeriodTorusQuasiperiodic
import Wikipedia.HopfProblem.PeriodTorusQuasiperiodicPeriods

/-!
# Fibre independence of holomorphic period-family coefficients

These statements concern actual scalar or vector coefficient functions
on the covering product. Each point of the period domain supplies its
proved full lattice. Periodic coefficients are constant in the covering
fibre. Coefficients with constant period increments are also constant
when the two fixed real periods have zero increments. Their resulting
base coefficients are the actual holomorphic zero-section restrictions.
-/

noncomputable section

open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

open PeriodTorusQuasiperiodic

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "IF" => modelWithCornersSelf ℂ F

local instance periodicProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

variable (point : B → PeriodDomain)

/-- Periodicity under the original four integer period directions
forces every entire covering-fibre restriction to be constant. -/
theorem fibre_constant_of_periodic {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f)
    (hper : ∀ b ℓ ζ, f (b, ζ + (point b).periodVector ℓ) = f (b, ζ))
    (b : B) (ζ : ComplexPlane₂) : f (b, ζ) = f (b, 0) := by
  apply eq_at_zero_of_lattice_periodic (point b).lattice
    ((fibreRestriction_contDiff hf b).differentiable (by simp))
  intro z w hw
  obtain ⟨ℓ, rfl⟩ := ((point b).mem_lattice_iff w).mp hw
  exact hper b ℓ z

/-- Constant lattice increments become zero when the two original
identity-column periods have zero increments. -/
theorem fibre_constant_of_quasiperiodic {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f)
    (hinc : ∀ b ℓ, ∃ c : F, ∀ ζ,
      f (b, ζ + (point b).periodVector ℓ) = f (b, ζ) + c)
    (h₂ : ∀ b ζ, f (b, ζ + (point b).periodVector (Pi.single 2 1)) = f (b, ζ))
    (h₃ : ∀ b ζ, f (b, ζ + (point b).periodVector (Pi.single 3 1)) = f (b, ζ))
    (b : B) (ζ : ComplexPlane₂) : f (b, ζ) = f (b, 0) := by
  let fb : ComplexPlane₂ → F := fun z => f (b, z)
  have hfb : ContDiff ℂ 2 fb := (fibreRestriction_contDiff hf b).of_le (by simp)
  have hi : ∀ w ∈ (point b).lattice, ∃ c : F, ∀ z, fb (z + w) = fb z + c := by
    intro w hw
    obtain ⟨ℓ, rfl⟩ := ((point b).mem_lattice_iff w).mp hw
    exact hinc b ℓ
  have hz : fderiv ℂ fb 0 = 0 := by
    apply continuousLinearMap_eq_zero_of_periodColumns (point b)
    · have hshift : ∀ z, fb (z + periodColumn (point b) 2) = fb z + 0 := by
        intro z
        simpa only [PeriodDomain.periodVector_apply, integer_period_single, add_zero]
          using h₂ b z
      exact (increment_eq_fderiv (point b).lattice hfb hi hshift).symm
    · have hshift : ∀ z, fb (z + periodColumn (point b) 3) = fb z + 0 := by
        intro z
        simpa only [PeriodDomain.periodVector_apply, integer_period_single, add_zero]
          using h₃ b z
      exact (increment_eq_fderiv (point b).lattice hfb hi hshift).symm
  exact eq_at_zero_of_lattice_quasiperiodic_of_fderiv_zero
    (point b).lattice hfb hi hz ζ

/-- A displayed additive period law gives the preceding conclusion
as soon as its two fixed-period increments are proved to vanish. -/
theorem fibre_constant_of_period_increment_law {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) (c : B → Lattice → F)
    (hshift : ∀ b ℓ ζ, f (b, ζ + (point b).periodVector ℓ) = f (b, ζ) + c b ℓ)
    (h₂ : ∀ b, c b (Pi.single 2 1) = 0)
    (h₃ : ∀ b, c b (Pi.single 3 1) = 0) :
    ∀ b ζ, f (b, ζ) = f (b, 0) := by
  apply fibre_constant_of_quasiperiodic point hf (fun b ℓ => ⟨c b ℓ, hshift b ℓ⟩)
  · intro b ζ
    simpa only [h₂ b, add_zero] using hshift b (Pi.single 2 1) ζ
  · intro b ζ
    simpa only [h₃ b, add_zero] using hshift b (Pi.single 3 1) ζ

/-- The normal coefficient is a holomorphic function on the actual base. -/
theorem periodic_baseCoefficient {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f)
    (hper : ∀ b ℓ ζ, f (b, ζ + (point b).periodVector ℓ) = f (b, ζ)) :
    ContMDiff I₁ IF ω (baseCoefficient f) ∧
      ∀ b ζ, f (b, ζ) = baseCoefficient f b :=
  ⟨baseCoefficient_holomorphic hf, fibre_constant_of_periodic point hf hper⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
