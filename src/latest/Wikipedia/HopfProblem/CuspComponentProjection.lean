import Wikipedia.HopfProblem.ToricDivisors
import Wikipedia.HopfProblem.CuspStrata

/-!
# Projection of the component at the origin

The restriction of the cusp quotient map to `E₀` covers the entire central
fibre. Its fibres are in bijection with the ray components through a lift,
so their cardinalities are exactly the previously defined branch counts.
This constructs the map used in Proposition 4.6; the identification of `E₀`
with the degree-six del Pezzo surface and the analytic normalization property
are separate results, not assumed here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

@[simp] theorem cuspVector_neg (v : Fin 2 → ℤ) : cuspVector (-v) = -cuspVector v := by
  ext i
  fin_cases i <;> simp [cuspVector]

@[simp] theorem cuspVector_cuspVector (v : Fin 2 → ℤ) : cuspVector (cuspVector v) = -v := by
  ext i
  fin_cases i <;> simp [cuspVector]

theorem cuspVector_injective : Function.Injective cuspVector := by
  intro v w h
  have h' := congrArg cuspVector h
  simpa only [cuspVector_cuspVector, neg_inj] using h'

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

def componentLift (x : rayDivisor 0) : Tube (disc ε) :=
  ⟨x, by
    change time (x : Space) ∈ Metric.ball 0 ε
    rw [time_eq_zero_of_mem_rayDivisor x.2]
    simpa using hε⟩

theorem componentLift_continuous : Continuous (componentLift ε hε) :=
  continuous_subtype_val.subtype_mk _

/-- The actual quotient projection restricted to the central component `E₀`. -/
def componentProjection : rayDivisor 0 → QuotientSpace C ε :=
  quotientMap C ε ∘ componentLift ε hε

theorem componentProjection_continuous : Continuous (componentProjection C ε hε) :=
  (quotientMap_continuous C ε).comp (componentLift_continuous ε hε)

@[simp] theorem projection_componentProjection (x : rayDivisor 0) :
    projection C ε (componentProjection C ε hε x) = 0 :=
  time_eq_zero_of_mem_rayDivisor x.2

/-- Translate a chosen branch at a lift to the component with vertex zero. -/
def branchRepresentative (a : Tube (disc ε)) (v : branchVertices (a : Space)) : rayDivisor 0 :=
  ⟨twistedTranslate C (cuspVector v) a, by
    rw [twistedTranslate_mem_rayDivisor, cuspVector_cuspVector]
    simp only [zero_sub, neg_neg]
    exact v.2⟩

@[simp] theorem componentLift_branchRepresentative (a : Tube (disc ε))
    (v : branchVertices (a : Space)) :
    componentLift ε hε (branchRepresentative C ε a v) =
      tubeTranslate C (disc ε) (cuspVector v) a := rfl

@[simp] theorem componentProjection_branchRepresentative (a : Tube (disc ε))
    (v : branchVertices (a : Space)) :
    componentProjection C ε hε (branchRepresentative C ε a v) = quotientMap C ε a := by
  change quotientMap C ε (componentLift ε hε (branchRepresentative C ε a v)) = _
  rw [componentLift_branchRepresentative, quotientMap_translate]

theorem componentProjection_range :
    range (componentProjection C ε hε) = projection C ε ⁻¹' {0} := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    exact projection_componentProjection C ε hε x
  · intro x hx
    induction x using Quotient.inductionOn with
    | h a =>
      have ha : time (a : Space) = 0 := hx
      obtain ⟨v, hv⟩ := (branchVertices_nonempty (a : Space)).mpr ha
      exact ⟨branchRepresentative C ε a ⟨v, hv⟩,
        componentProjection_branchRepresentative C ε hε a ⟨v, hv⟩⟩

def componentFibreMap (a : Tube (disc ε)) : branchVertices (a : Space) →
    (componentProjection C ε hε ⁻¹' {quotientMap C ε a}) := fun v =>
  ⟨branchRepresentative C ε a v, componentProjection_branchRepresentative C ε hε a v⟩

theorem componentFibreMap_surjective (a : Tube (disc ε)) :
    Function.Surjective (componentFibreMap C ε hε a) := by
  let := tubeAction C (disc ε)
  intro y
  have hy := Quotient.exact y.2
  change componentLift ε hε y.1 ∈ MulAction.orbit LatticeGroup a at hy
  obtain ⟨g, hg⟩ := hy
  have he : twistedTranslate C g.toAdd (a : Space) = (y.1 : Space) := congrArg Subtype.val hg
  let v : Fin 2 → ℤ := -cuspVector g.toAdd
  have hv : v ∈ branchVertices (a : Space) := by
    have hm : twistedTranslate C g.toAdd (a : Space) ∈ rayDivisor 0 := by
      rw [he]
      exact y.1.2
    have h := (twistedTranslate_mem_rayDivisor C g.toAdd 0 a).mp hm
    change (a : Space) ∈ rayDivisor v
    simpa only [zero_sub] using h
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change twistedTranslate C (cuspVector v) (a : Space) = (y.1 : Space)
  have hv' : cuspVector v = g.toAdd := by simp [v]
  rw [hv']
  exact he

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

theorem componentFibreMap_injective (a : Tube (disc ε)) :
    Function.Injective (componentFibreMap C ε hε a) := by
  let := tubeAction C (disc ε)
  let := free_action C ε hε hε1 hC hR
  intro v w h
  have he : (Multiplicative.ofAdd (cuspVector v) : LatticeGroup) • a =
      (Multiplicative.ofAdd (cuspVector w) : LatticeGroup) • a := by
    have he' := congrArg (fun y => componentLift ε hε y.1) h
    exact he'
  have hg := IsCancelSMul.right_cancel _ _ a he
  apply Subtype.ext
  exact cuspVector_injective (congrArg Multiplicative.toAdd hg)

def componentFibreEquiv (a : Tube (disc ε)) : branchVertices (a : Space) ≃
    (componentProjection C ε hε ⁻¹' {quotientMap C ε a}) :=
  Equiv.ofBijective (componentFibreMap C ε hε a)
    ⟨componentFibreMap_injective C ε hε hε1 hC hR a,
      componentFibreMap_surjective C ε hε a⟩

theorem componentProjection_fibre_finite (x : QuotientSpace C ε) :
    (componentProjection C ε hε ⁻¹' {x}).Finite := by
  induction x using Quotient.inductionOn with
  | h a =>
    let : Finite (branchVertices (a : Space)) := (branchVertices_finite (a : Space)).to_subtype
    exact Set.finite_coe_iff.mp
      (Finite.of_equiv _ (componentFibreEquiv C ε hε hε1 hC hR a))

theorem componentProjection_fibre_card (x : QuotientSpace C ε) :
    (componentProjection C ε hε ⁻¹' {x}).ncard = branchCount C ε x := by
  induction x using Quotient.inductionOn with
  | h a =>
    have h := Nat.card_congr (componentFibreEquiv C ε hε hε1 hC hR a)
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, branchVertices_ncard] at h
    exact h.symm

theorem componentProjection_fibre_card_le_three (x : QuotientSpace C ε) :
    (componentProjection C ε hε ⁻¹' {x}).ncard ≤ 3 := by
  rw [componentProjection_fibre_card C ε hε hε1 hC hR]
  exact branchCount_le_three C ε x

end Wikipedia.HopfProblem.CuspQuotient
