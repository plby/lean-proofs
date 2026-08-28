import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorGlobal
import Wikipedia.HopfProblem.SpecialPeriodsDiscriminantBounds
import Wikipedia.HopfProblem.SpecialPeriodsConstructionPeriodMapInvariance
import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Period maps from the constructed special functions

The actual holomorphic tau and mu data, together with a holomorphic beta,
give a triple of complex period functions.  The two beta generator laws
are equivalent to the full period-point generator laws, since the tau and
mu laws are already proved fields of the data.  The cusp law follows from
the actual triangle word.

Pointwise admissibility packages this triple as a `HolomorphicPeriodMap`.
It is an explicit input here; neither a uniform discriminant bound nor
admissibility is assumed by the unshifted period-point construction.
Constant shifts, including purely imaginary shifts, retain holomorphy and
all the full period-domain generator equations.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

namespace BetaTorsor.Data

variable (D : BetaTorsor.Data)

/-- The actual three complex functions, before imposing admissibility. -/
def periodPoint (β : ℍ → ℂ) (z : ℍ) : PeriodPoint :=
  ⟨(D.tau z : ℂ), D.mu z, β z⟩

@[simp] theorem periodPoint_tau (β : ℍ → ℂ) (z : ℍ) :
    (D.periodPoint β z).τ = (D.tau z : ℂ) := rfl

@[simp] theorem periodPoint_mu (β : ℍ → ℂ) (z : ℍ) :
    (D.periodPoint β z).μ = D.mu z := rfl

@[simp] theorem periodPoint_beta (β : ℍ → ℂ) (z : ℍ) :
    (D.periodPoint β z).β = β z := rfl

/-- Actual admissible special functions supply the existing holomorphic
period-map structure used by the family of tori. -/
def periodMap (β : ℍ → ℂ) (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible) :
    HolomorphicPeriodMap ℂ ℍ where
  point z := ⟨D.periodPoint β z, hAdm z⟩
  holomorphic_tau := UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic
  holomorphic_mu := D.mu_holomorphic
  holomorphic_beta := hβ

@[simp] theorem periodMap_point_val (β : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible) (z : ℍ) :
    ((D.periodMap β hβ hAdm).point z).val = D.periodPoint β z := rfl

/-- The constant-translated triple is exactly the existing period-point
shift, not a separately specified set of periods. -/
@[simp] theorem periodPoint_add_const (β : ℍ → ℂ) (c : ℂ) (z : ℍ) :
    D.periodPoint (fun w => β w + c) z = (D.periodPoint β z).shiftBeta c := rfl

/-- Package a constant shift once its actual pointwise admissibility has
been established.  In particular `c` can be a negative imaginary constant. -/
def shiftedPeriodMap (β : ℍ → ℂ) (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) :
    HolomorphicPeriodMap ℂ ℍ :=
  D.periodMap (fun z => β z + c) (hβ.add contMDiff_const) hAdm

@[simp] theorem shiftedPeriodMap_point_val (β : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) (z : ℍ) :
    ((D.shiftedPeriodMap β hβ c hAdm).point z).val =
      (D.periodPoint β z).shiftBeta c := rfl

end BetaTorsor.Data

namespace Construction

variable (D : BetaTorsor.Data) {β : ℍ → ℂ}

/-- The upper-half-plane target supplies the positivity needed by the
discriminant and by the algebraic period transformations. -/
theorem periodPoint_im_tau_pos (β : ℍ → ℂ) (z : ℍ) :
    0 < (D.periodPoint β z).τ.im := (D.tau z).im_pos

/-- For the first generator, the remaining component equation is exactly
the actual beta torsor equation. -/
theorem periodPoint_generator₁_iff (z : ℍ) :
    D.periodPoint β (Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ ↔
      β (Triangle.generatorOneSL • z) = β z + BetaTorsor.phiOne D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [BetaTorsor.Data.periodPoint, PeriodPoint.step₁, BetaTorsor.phiOne,
      sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.1 z
    · exact D.mu_one z
    · simpa only [BetaTorsor.Data.periodPoint, PeriodPoint.step₁, BetaTorsor.phiOne,
        sub_eq_add_neg, add_assoc] using hb

/-- The second full period-point equation has precisely the second beta
torsor equation as its remaining component. -/
theorem periodPoint_generator₂_iff (z : ℍ) :
    D.periodPoint β (Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ ↔
      β (Triangle.generatorTwoSL • z) = β z + BetaTorsor.phiTwo D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [BetaTorsor.Data.periodPoint, PeriodPoint.step₂, BetaTorsor.phiTwo,
      sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.2 z
    · exact D.mu_two z
    · simpa only [BetaTorsor.Data.periodPoint, PeriodPoint.step₂, BetaTorsor.phiTwo,
        sub_eq_add_neg, add_assoc] using hb

/-- The two actual scalar beta laws are equivalent to the two full triple
equations, with no additional covariance assumptions. -/
theorem periodPoint_generator_laws_iff :
    ((∀ z : ℍ, D.periodPoint β (Triangle.generatorOneSL • z) =
        (D.periodPoint β z).step₁) ∧
      (∀ z : ℍ, D.periodPoint β (Triangle.generatorTwoSL • z) =
        (D.periodPoint β z).step₂)) ↔ D.GeneratorLaws β := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun z => (periodPoint_generator₁_iff D z).mp (h₁ z),
      fun z => (periodPoint_generator₂_iff D z).mp (h₂ z)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun z => (periodPoint_generator₁_iff D z).mpr (h₁ z),
      fun z => (periodPoint_generator₂_iff D z).mpr (h₂ z)⟩

theorem periodPoint_generator₁ (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ :=
  (periodPoint_generator₁_iff D z).mpr (hβ.1 z)

theorem periodPoint_generator₂ (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ :=
  (periodPoint_generator₂_iff D z).mpr (hβ.2 z)

/-- All three cusp components follow from the actual inverse product word. -/
theorem periodPoint_cusp (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (triangleGeometricRepresentation triangleCuspGenerator z) =
      (D.periodPoint β z).step₀ := by
  apply PeriodPoint.ext
  · exact tau_covariant_cusp_coe D.tau_covariant z
  · exact BetaTorsor.mu_cusp D.tau_covariant D.mu_one D.mu_two z
  · change β (triangleGeometricRepresentation triangleCuspGenerator z) = β z + 1
    simpa only [D.shift_cusp] using hβ.all_words D triangleCuspGenerator z

/-- The exact cusp law in the source's horizontal coordinate. -/
theorem periodPoint_cusp_translation (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β ((-Triangle.width) +ᵥ z) = (D.periodPoint β z).step₀ := by
  simpa only [triangleGeometricRepresentation_cusp_apply] using periodPoint_cusp D hβ z

/-- The raw discriminant is continuous before making any imaginary shift
or assuming a bound on it. -/
theorem continuous_discriminant (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) :
    Continuous (fun z => (D.periodPoint β z).discriminant) := by
  exact continuousOn_univ.mp
    (PeriodPoint.continuousOn_discriminant (D.periodPoint β)
      (UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic).continuous.continuousOn
      D.mu_holomorphic.continuous.continuousOn hβ.continuous.continuousOn
      (fun z _ => (D.tau z).im_pos.ne'))

/-- The two actual beta equations give discriminant invariance for every
triangle word, not only for the two distinguished generators. -/
theorem discriminant_invariant (hβ : D.GeneratorLaws β)
    (g : TriangleGroup) (z : ℍ) :
    (D.periodPoint β (triangleGeometricRepresentation g z)).discriminant =
      (D.periodPoint β z).discriminant :=
  discriminant_invariant_of_generator_laws (D.periodPoint β)
    (periodPoint_im_tau_pos D β) (periodPoint_generator₁ D hβ)
    (periodPoint_generator₂ D hβ) g z

/-- A constant beta shift changes the discriminant by exactly its imaginary
part, while leaving tau and mu unchanged. -/
theorem discriminant_add_const (β : ℍ → ℂ) (c : ℂ) (z : ℍ) :
    (D.periodPoint (fun w => β w + c) z).discriminant =
      (D.periodPoint β z).discriminant + c.im :=
  PeriodPoint.shiftBeta_discriminant (D.periodPoint β z) c

/-- In particular a downward imaginary shift subtracts exactly its height
from every discriminant.  Its size is not presumed to make the result negative. -/
theorem discriminant_negative_imaginary_shift (β : ℍ → ℂ) (M : ℝ) (z : ℍ) :
    ((D.periodPoint β z).shiftBeta (-((M : ℂ) * Complex.I))).discriminant =
      (D.periodPoint β z).discriminant - M := by
  simp [sub_eq_add_neg]

/-- The first actual generator law as equality in the admissible period
domain, which is the interface required by the torus-family construction. -/
theorem periodMap_generator₁ (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (Triangle.generatorOneSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₁ :=
  Subtype.ext (periodPoint_generator₁ D hgen z)

/-- The second actual generator law in the admissible period domain. -/
theorem periodMap_generator₂ (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (Triangle.generatorTwoSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₂ :=
  Subtype.ext (periodPoint_generator₂ D hgen z)

/-- The actual cusp law in the admissible period domain. -/
theorem periodMap_cusp (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (triangleGeometricRepresentation triangleCuspGenerator z) =
      ((D.periodMap β hβ hAdm).point z).step₀ :=
  Subtype.ext (periodPoint_cusp D hgen z)

/-- Every constant shift retains the first full generator law. -/
theorem shiftedPeriodMap_generator₁ (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (Triangle.generatorOneSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₁ :=
  periodMap_generator₁ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

/-- Every constant shift retains the second full generator law. -/
theorem shiftedPeriodMap_generator₂ (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (Triangle.generatorTwoSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₂ :=
  periodMap_generator₂ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

/-- Every constant shift retains the full cusp law. -/
theorem shiftedPeriodMap_cusp (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point
        (triangleGeometricRepresentation triangleCuspGenerator z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₀ :=
  periodMap_cusp D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

end Construction

end Wikipedia.HopfProblem.SpecialPeriods
