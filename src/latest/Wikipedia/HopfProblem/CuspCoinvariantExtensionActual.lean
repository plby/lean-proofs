import Wikipedia.HopfProblem.CuspCoinvariantExtensionPaste
import Wikipedia.HopfProblem.CuspCoinvariantExtensionFlow
import Wikipedia.HopfProblem.CuspCoinvariantExtensionShell
import Wikipedia.HopfProblem.CuspCoinvariantExtensionPuncturedFlow
import Wikipedia.HopfProblem.CuspCoinvariantExtensionCentralBasic
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHeight

/-!
# Pasting on the full original cusp cap

An original closed-core gamma map with its proved whole-shell marking
is pasted to the original gamma coordinate on the entire outer punctured
region.  The resulting continuous map has the original central value and
is invariant under the original real vertical flow whenever its core is.
No new filling space, atlas, or circle action is introduced.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open CuspUniformization CuspRetraction CuspBoundaryTopVanishing
open SpecialPeriods.CuspFamily ThreefoldHomologyFinitenessCusp

/-- The original punctured gamma map on the equivalent positive-norm subtype. -/
def positiveGamma (D : Data) :
    C({q : FullSpace D // 0 < parameterNorm D q}, AddCircle (1 : ℝ)) where
  toFun q := puncturedGamma D ⟨q.val, norm_pos_iff.mp q.property⟩
  continuous_toFun := (puncturedGamma D).continuous.comp
    (continuous_subtype_val.subtype_mk _)

@[simp] theorem positiveGamma_apply (D : Data)
    (q : {q : FullSpace D // 0 < parameterNorm D q}) :
    positiveGamma D q = puncturedGamma D ⟨q.val, norm_pos_iff.mp q.property⟩ := rfl

variable (D : Data) {η : ℝ} (hη : 0 < η) (hηr : η < D.radius)
variable (core : C(ClosedQuotient D.correction D.radius η, AddCircle (1 : ℝ)))
variable (hshell : ∀ (s : LogBase D.radius) (hsη : ‖exponential (s : ℂ)‖ ≤ η)
    (x : RealPlane₄), ‖exponential (s : ℂ)‖ = η →
      core (closedQuotientMap D.correction hηr
        (periodPointPunctured D η s hsη x).1) = (x 0 : AddCircle (1 : ℝ)))

include hη hηr hshell

/-- The representative equality is exactly the hypothesis needed for
closed-shell pasting in the original quotient topology. -/
theorem positiveGamma_shell_agreement (q : FullSpace D) (hq : parameterNorm D q = η) :
    core ⟨q, hq.le⟩ = positiveGamma D ⟨q, hη.trans_eq hq.symm⟩ :=
  coreGamma_eq_puncturedGamma_on_shell D hηr core hshell
    ⟨q, norm_pos_iff.mp (hη.trans_eq hq.symm)⟩ hq

/-- The full native cap map, with the original punctured gamma map as its
literal outer branch. -/
def capGammaFromCore : C(FullSpace D, AddCircle (1 : ℝ)) :=
  radiusPaste (parameterNorm D) η hη core (positiveGamma D)
    (positiveGamma_shell_agreement D hη hηr core hshell)

theorem capGammaFromCore_inner (q : FullSpace D) (hq : parameterNorm D q ≤ η) :
    capGammaFromCore D hη hηr core hshell q = core ⟨q, hq⟩ :=
  radiusPasteFun_inner (parameterNorm D) η hη core (positiveGamma D) q hq

/-- Agreement is on the full outer region, hence on every outer collar
above the chosen shell. -/
theorem capGammaFromCore_outer (q : PuncturedQuotient D.correction D.radius)
    (hq : η ≤ parameterNorm D q.val) :
    capGammaFromCore D hη hηr core hshell q.val = puncturedGamma D q :=
  radiusPasteFun_outer (parameterNorm D) η hη core (positiveGamma D)
    (positiveGamma_shell_agreement D hη hηr core hshell) q.val hq

/-- The pasted map retains the marked coordinate on the actual central fibre. -/
theorem capGammaFromCore_central
    (hcentral : core.comp (quotientCentralIntoClosed D.correction D.radius η hη.le) =
      centralGamma D.correction D.radius D.radius_pos D.holomorphic)
    (q : QuotientCentralFibre D.correction D.radius) :
    capGammaFromCore D hη hηr core hshell q.val =
      centralGamma D.correction D.radius D.radius_pos D.holomorphic q := by
  have hq : parameterNorm D q.val ≤ η := by
    change ‖CuspQuotient.projection D.correction D.radius q.val‖ ≤ η
    rw [q.property, norm_zero]
    exact hη.le
  rw [capGammaFromCore_inner D hη hηr core hshell q.val hq]
  exact ContinuousMap.congr_fun hcentral q

/-- The actual real delta flow preserves the whole pasted cap map,
including the central fibre. -/
theorem capGammaFromCore_realFlow
    (hphase : ∀ (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
      ∀ x : ClosedTube η,
        core (closedQuotientMap D.correction hηr (closedFibreAction η u x)) =
          core (closedQuotientMap D.correction hηr x))
    (t : ℝ) (q : FullSpace D) :
    capGammaFromCore D hη hηr core hshell
      (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ) q) =
        capGammaFromCore D hη hηr core hshell q := by
  have hradius : ∀ x : FullSpace D,
      parameterNorm D
        (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ) x) =
          parameterNorm D x := by
    intro x
    change ‖CuspQuotient.projection D.correction D.radius
      (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ) x)‖ =
        ‖CuspQuotient.projection D.correction D.radius x‖
    rw [SpecialPeriods.Threefold.VerticalAction.Cusp.projection_flow]
  exact radiusPaste_invariant (parameterNorm D) η hη core (positiveGamma D)
    (positiveGamma_shell_agreement D hη hηr core hshell)
    (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ))
    hradius
    (fun x => invariant_closedFlow_real_of_fibreAction D.correction hηr core hphase t x)
    (fun x => puncturedGamma_realFlow D t ⟨x.val, norm_pos_iff.mp x.property⟩) q

end Wikipedia.HopfProblem.CuspCoinvariantExtension
