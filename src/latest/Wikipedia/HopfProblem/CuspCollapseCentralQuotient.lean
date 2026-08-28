import Wikipedia.HopfProblem.CuspCollapseCentralDeck
import Wikipedia.HopfProblem.CuspCollapseCentralProjection

/-!
# An actual phase-collapse model of the central cusp fibre

The relation on compact phases and positive central points is explicit:
first apply a positive lattice translation and its fixed compact phase,
then identify phases in the actual stabilizer of the positive point.
The quotient by this relation is homeomorphic to the literal central
fibre of the existing cusp quotient. Both topology and the exact maps
are inherited from the constructed toric space and its quotient map.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCollapse

open ToricSpace CuspRetraction CuspPositiveRetraction

abbrev PhasePositiveSpace := CompactFibreTorus × PositiveCentralFibre

/-- The actual central map on compact phases and positive central points. -/
def centralCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePositiveSpace → QuotientCentralFibre C ε :=
  centralProject C ε hε ∘ centralPolarMap

theorem centralCollapseMap_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (centralCollapseMap C ε hε) :=
  (centralProject_continuous C ε hε).comp centralPolarMap_continuous

theorem centralCollapseMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Function.Surjective (centralCollapseMap C ε hε) :=
  (centralProject_surjective C ε hε).comp centralPolarMap_surjective

theorem centralCollapseMap_isQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    IsQuotientMap (centralCollapseMap C ε hε) :=
  (centralProject_isQuotientMap C ε hε hC).comp centralPolarMap_isQuotientMap

/-- Lattice translation followed by the actual stratum-dependent
phase collapse. The data depends only on the central correction matrix. -/
def centralCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : PhasePositiveSpace) : Prop :=
  ∃ v : Fin 2 → ℤ, p.2 = positiveCentralTranslate C₀ v q.2 ∧
    p.1⁻¹ * (deckFibrePhase C₀ v * q.1) ∈
      MulAction.stabilizer CompactFibreTorus (p.2.1 : Space)

/-- The displayed relation is exactly the fibre relation of the genuine
central cusp map, including all double and triple strata. -/
theorem centralCollapseMap_eq_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p q : PhasePositiveSpace) :
    centralCollapseMap C ε hε p = centralCollapseMap C ε hε q ↔
      centralCollapseRelation (C 0) p q := by
  change centralProject C ε hε (centralPolarMap p) =
      centralProject C ε hε (centralPolarMap q) ↔ _
  rw [centralProject_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) := by
      apply Subtype.ext
      exact ((centralPolarMap_phaseDeckMap C v q).trans hv).symm
    exact ⟨v, (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mp hpq⟩
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) :=
      (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mpr hv
    refine ⟨v, ?_⟩
    rw [← centralPolarMap_phaseDeckMap C v q]
    exact congrArg Subtype.val hpq.symm

/-- The explicit relation is an equivalence relation; no extra
identifications are generated beyond those stated in its definition. -/
def centralCollapseSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Setoid PhasePositiveSpace where
  r := centralCollapseRelation C₀
  iseqv := by
    let f := centralCollapseMap (fun _ => C₀) 1 zero_lt_one
    have he (p q : PhasePositiveSpace) : f p = f q ↔ centralCollapseRelation C₀ p q :=
      centralCollapseMap_eq_iff (fun _ => C₀) 1 zero_lt_one p q
    exact
      { refl := fun p => (he p p).mp rfl
        symm := fun {p q} h => (he q p).mp ((he p q).mpr h).symm
        trans := fun {p q r} hpq hqr =>
          (he p r).mp (((he p q).mpr hpq).trans ((he q r).mpr hqr)) }

abbrev CentralCollapseModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (centralCollapseSetoid C₀)

/-- The map from the explicit collapse quotient to the actual central fibre. -/
def centralCollapseModelMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) → QuotientCentralFibre C ε :=
  Quotient.lift (centralCollapseMap C ε hε)
    (fun p q h => (centralCollapseMap_eq_iff C ε hε p q).mpr h)

@[simp] theorem centralCollapseModelMap_mk
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : PhasePositiveSpace) :
    centralCollapseModelMap C ε hε (Quotient.mk (centralCollapseSetoid (C 0)) p) =
      centralCollapseMap C ε hε p := rfl

theorem centralCollapseModelMap_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (centralCollapseModelMap C ε hε) :=
  (centralCollapseMap_continuous C ε hε).quotient_lift _

theorem centralCollapseModelMap_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Function.Bijective (centralCollapseModelMap C ε hε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        intro h
        exact Quotient.sound ((centralCollapseMap_eq_iff C ε hε p q).mp h)
  · intro x
    obtain ⟨p, hp⟩ := centralCollapseMap_surjective C ε hε x
    exact ⟨Quotient.mk (centralCollapseSetoid (C 0)) p, hp⟩

def centralCollapseEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) ≃ QuotientCentralFibre C ε :=
  Equiv.ofBijective (centralCollapseModelMap C ε hε) (centralCollapseModelMap_bijective C ε hε)

@[simp] theorem centralCollapseEquiv_symm_map
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : PhasePositiveSpace) :
    (centralCollapseEquiv C ε hε).symm (centralCollapseMap C ε hε p) =
      Quotient.mk (centralCollapseSetoid (C 0)) p := by
  apply (centralCollapseEquiv C ε hε).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- A genuine homeomorphism from the explicit phase/lattice collapse
model to the literal central fibre of the original cusp quotient. -/
def centralCollapseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    CentralCollapseModel (C 0) ≃ₜ QuotientCentralFibre C ε where
  toEquiv := centralCollapseEquiv C ε hε
  continuous_toFun := centralCollapseModelMap_continuous C ε hε
  continuous_invFun := by
    apply (centralCollapseMap_isQuotientMap C ε hε hC).continuous_iff.mpr
    change Continuous ((centralCollapseEquiv C ε hε).symm ∘ centralCollapseMap C ε hε)
    have he : (centralCollapseEquiv C ε hε).symm ∘ centralCollapseMap C ε hε =
        Quotient.mk (centralCollapseSetoid (C 0)) :=
      funext (centralCollapseEquiv_symm_map C ε hε)
    rw [he]
    exact continuous_quotient_mk'

@[simp] theorem centralCollapseHomeomorph_mk
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (p : PhasePositiveSpace) :
    centralCollapseHomeomorph C ε hε hC (Quotient.mk (centralCollapseSetoid (C 0)) p) =
      centralProject C ε hε (centralPolarMap p) := rfl

end Wikipedia.HopfProblem.CuspCollapse
