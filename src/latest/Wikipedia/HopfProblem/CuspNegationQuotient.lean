import Wikipedia.HopfProblem.CuspNegationToric
import Wikipedia.HopfProblem.CuspQuotient

/-!
# Negation on the full original cusp quotient

The toric involution preserves every time tube and respects the actual
corrected lattice orbit relation. Its descended homeomorphism is defined
on the entire original radius, for every correction function and radius.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNegation

open ToricSpace CuspQuotient

def tubeNegation (D : TopologicalSpace.Opens ℂ) (x : Tube D) : Tube D :=
  ⟨toricNegation x, by
    change time (toricNegation x) ∈ D
    rw [time_toricNegation]
    exact x.2⟩

@[simp] theorem tubeNegation_coe (D : TopologicalSpace.Opens ℂ) (x : Tube D) :
    (tubeNegation D x : Space) = toricNegation x := rfl

theorem tubeNegation_involutive (D : TopologicalSpace.Opens ℂ) :
    Function.Involutive (tubeNegation D) :=
  fun x => Subtype.ext (toricNegation_involutive x)

theorem tubeNegation_continuous (D : TopologicalSpace.Opens ℂ) : Continuous (tubeNegation D) :=
  (toricNegation_holomorphic.continuous.comp continuous_subtype_val).subtype_mk _

def tubeHomeomorph (D : TopologicalSpace.Opens ℂ) : Tube D ≃ₜ Tube D where
  toFun := tubeNegation D
  invFun := tubeNegation D
  left_inv := tubeNegation_involutive D
  right_inv := tubeNegation_involutive D
  continuous_toFun := tubeNegation_continuous D
  continuous_invFun := tubeNegation_continuous D

theorem tubeNegation_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ) (x : Tube D) :
    tubeNegation D (tubeTranslate C D v x) = tubeTranslate C D (-v) (tubeNegation D x) :=
  Subtype.ext (toricNegation_twistedTranslate C v x)

theorem tubeNegation_related (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    {x y : Tube (disc ε)} (hxy : (relation C ε).r x y) :
    (relation C ε).r (tubeNegation (disc ε) x) (tubeNegation (disc ε) y) := by
  letI := tubeAction C (disc ε)
  change x ∈ MulAction.orbit LatticeGroup y at hxy
  change tubeNegation (disc ε) x ∈ MulAction.orbit LatticeGroup (tubeNegation (disc ε) y)
  obtain ⟨g, rfl⟩ := hxy
  refine ⟨Multiplicative.ofAdd (-g.toAdd), ?_⟩
  exact (tubeNegation_translate C (disc ε) g.toAdd y).symm

def quotientNegation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    QuotientSpace C ε → QuotientSpace C ε :=
  Quotient.map (tubeNegation (disc ε)) (fun _ _ h => tubeNegation_related C ε h)

@[simp] theorem quotientNegation_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (x : Tube (disc ε)) :
    quotientNegation C ε (quotientMap C ε x) = quotientMap C ε (tubeNegation (disc ε) x) := rfl

theorem quotientNegation_involutive (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Function.Involutive (quotientNegation C ε) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
      change quotientMap C ε (tubeNegation (disc ε) (tubeNegation (disc ε) x)) =
        quotientMap C ε x
      rw [tubeNegation_involutive (disc ε) x]

theorem quotientNegation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientNegation C ε) :=
  ((quotientMap_continuous C ε).comp (tubeNegation_continuous (disc ε))).quotient_lift _

def quotientHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    QuotientSpace C ε ≃ₜ QuotientSpace C ε where
  toFun := quotientNegation C ε
  invFun := quotientNegation C ε
  left_inv := quotientNegation_involutive C ε
  right_inv := quotientNegation_involutive C ε
  continuous_toFun := quotientNegation_continuous C ε
  continuous_invFun := quotientNegation_continuous C ε

@[simp] theorem projection_quotientNegation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (q : QuotientSpace C ε) :
    projection C ε (quotientNegation C ε q) = projection C ε q := by
  induction q using Quotient.inductionOn with
  | h x => exact time_toricNegation x

@[simp] theorem baseMap_quotientNegation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (q : QuotientSpace C ε) :
    baseMap C ε (quotientNegation C ε q) = baseMap C ε q :=
  Subtype.ext (projection_quotientNegation C ε q)

end Wikipedia.HopfProblem.CuspNegation
