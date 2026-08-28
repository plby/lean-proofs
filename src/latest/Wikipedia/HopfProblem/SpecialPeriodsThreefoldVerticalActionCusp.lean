import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspTube
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Wikipedia.HopfProblem.CuspPuncturedManifold
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalProductLocal

/-!
# The vertical holomorphic flow on the actual cusp quotient

The extended toric cocharacter commutes with the original twisted lattice
action, so it descends to the actual orbit quotient.  Its analytic
statements use the original cusp quotient atlas.  Joint holomorphicity
descends through the product of the genuine covering map with a complex
line.  No new manifold structure is imposed on the quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open ToricCharts ToricSpace

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- The vertical additive flow on the genuine twisted cusp quotient. -/
def flow (s : ℂ) : CuspQuotient.QuotientSpace C ε → CuspQuotient.QuotientSpace C ε :=
  Quotient.lift
    (fun x => CuspQuotient.quotientMap C ε (tubeFlow (CuspQuotient.disc ε) s x)) (by
      let := tubeAction C (CuspQuotient.disc ε)
      intro x y hxy
      change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hxy
      obtain ⟨g, rfl⟩ := hxy
      change CuspQuotient.quotientMap C ε
        (tubeFlow (CuspQuotient.disc ε) s
          (tubeTranslate C (CuspQuotient.disc ε) g.toAdd y)) = _
      rw [tubeFlow_translate, CuspQuotient.quotientMap_translate])

@[simp] theorem flow_quotientMap (s : ℂ) (x : Tube (CuspQuotient.disc ε)) :
    flow C ε s (CuspQuotient.quotientMap C ε x) =
      CuspQuotient.quotientMap C ε (tubeFlow (CuspQuotient.disc ε) s x) := rfl

@[simp] theorem flow_zero (x : CuspQuotient.QuotientSpace C ε) : flow C ε 0 x = x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_zero _ x)

theorem flow_add (s t : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε (s + t) x = flow C ε s (flow C ε t x) := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_add _ s t x)

@[simp] theorem flow_int_cast (n : ℤ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε (n : ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_int_cast _ n x)

@[simp] theorem flow_neg_left (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε (-s) (flow C ε s x) = x := by
  rw [← flow_add, neg_add_cancel, flow_zero]

@[simp] theorem flow_neg_right (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε s (flow C ε (-s) x) = x := by
  rw [← flow_add, add_neg_cancel, flow_zero]

/-- The cusp projection is unchanged by the vertical flow, including on the central fibre. -/
@[simp] theorem projection_flow (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    CuspQuotient.projection C ε (flow C ε s x) = CuspQuotient.projection C ε x := by
  induction x using Quotient.inductionOn with
  | h x => exact toricFlow_time s x

theorem flow_continuous (s : ℂ) : Continuous (flow C ε s) :=
  ((CuspQuotient.quotientMap_continuous C ε).comp
    (tubeFlow_holomorphic (CuspQuotient.disc ε) s).continuous).quotient_lift _

/-- Every time map is an actual homeomorphism, even before any analytic
regularity assumption on the cusp correction has been used. -/
def flowHomeomorph (s : ℂ) :
    CuspQuotient.QuotientSpace C ε ≃ₜ CuspQuotient.QuotientSpace C ε where
  toFun := flow C ε s
  invFun := flow C ε (-s)
  left_inv := flow_neg_left C ε s
  right_inv := flow_neg_right C ε s
  continuous_toFun := flow_continuous C ε s
  continuous_invFun := flow_continuous C ε (-s)

@[simp] theorem flowHomeomorph_apply (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    flowHomeomorph C ε s x = flow C ε s x := rfl

section Analytic

variable (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The original quotient covering is locally biholomorphic for the
original cusp quotient atlas. -/
theorem quotientMap_isLocalDiffeomorph :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph I₃ I₃ ω (CuspQuotient.quotientMap C ε) := by
  let := tubeAction C (CuspQuotient.disc ε)
  exact CoveringQuotient.project_isLocalDiffeomorph
    (CuspQuotient.quotientMap_covering C ε hε hε1 hC hR)
    (fun v => tubeTranslate_holomorphic C (CuspQuotient.disc ε) v.toAdd hC)

/-- The descended vertical flow is holomorphic jointly in the point and
the complex time.  The time parameter is the second product factor. -/
theorem flow_joint_holomorphic :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff ((I₃).prod I₁) I₃ ω
      (fun p : CuspQuotient.QuotientSpace C ε × ℂ => flow C ε p.2 p.1) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  have hq := CanonicalProduct.isLocalDiffeomorph_prodLine
    (quotientMap_isLocalDiffeomorph C ε hε hε1 hC hR)
  have hs : Function.Surjective (fun p : Tube (CuspQuotient.disc ε) × ℂ =>
      (CuspQuotient.quotientMap C ε p.1, p.2)) := by
    rintro ⟨q, s⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact ⟨(x, s), rfl⟩
  apply contMDiff_of_comp_localDiffeomorph ((I₃).prod I₁) ((I₃).prod I₁) I₃ hq hs
  exact (CuspQuotient.quotientMap_holomorphic C ε hε hε1 hC hR).comp
    (tubeFlow_joint_holomorphic (CuspQuotient.disc ε))

theorem flow_holomorphic (s : ℂ) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff I₃ I₃ ω (flow C ε s) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact ContMDiff.comp (I := I₃) (I' := (I₃).prod I₁) (I'' := I₃)
    (f := fun x : CuspQuotient.QuotientSpace C ε => (x, s))
    (g := fun p : CuspQuotient.QuotientSpace C ε × ℂ => flow C ε p.2 p.1)
    (flow_joint_holomorphic C ε hε hε1 hC hR)
    (contMDiff_id.prodMk contMDiff_const)

/-- Each time map is biholomorphic, with inverse given by the negative time. -/
def flowBiholomorph (s : ℂ) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Diffeomorph I₃ I₃ (CuspQuotient.QuotientSpace C ε)
      (CuspQuotient.QuotientSpace C ε) ω := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    { toEquiv := (flowHomeomorph C ε s).toEquiv
      contMDiff_toFun := flow_holomorphic C ε hε hε1 hC hR s
      contMDiff_invFun := flow_holomorphic C ε hε hε1 hC hR (-s) }

@[simp] theorem flowBiholomorph_apply (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    flowBiholomorph C ε hε hε1 hC hR s x = flow C ε s x := rfl

end Analytic

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
