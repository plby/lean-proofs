import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspToric
import Wikipedia.HopfProblem.CuspQuotient

/-!
# The vertical flow on the actual toric cusp tube

Fibre multipliers commute with the integral toric shears and with the
parameter-dependent exponential multipliers.  The vertical torus flow
therefore preserves every original cusp tube and commutes with its
actual twisted lattice action.  Its joint holomorphicity uses the
inherited open-submanifold atlas of that tube.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open ToricCharts ToricSpace

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem fibreMultiplier_variableMultiplier_commute (u : Fin 2 → ℂˣ)
    (v : ℂ → Fin 2 → ℂˣ) (x : ToricSpace.Space) :
    torusAction (fibreMultiplier u) (variableMultiplier v x) =
      variableMultiplier v (torusAction (fibreMultiplier u) x) := by
  simp only [variableMultiplier, time_fibreMultiplier, torusAction_mul]
  rw [mul_comm]

/-- Constant fibre multipliers commute with the actual parameter-dependent cusp action. -/
theorem fibreMultiplier_twistedTranslate_commute
    (u : Fin 2 → ℂˣ) (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    torusAction (fibreMultiplier u) (twistedTranslate C v x) =
      twistedTranslate C v (torusAction (fibreMultiplier u) x) := by
  unfold twistedTranslate
  rw [fibreMultiplier_variableMultiplier_commute, fibreMultiplier_translate]

theorem toricFlow_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    toricFlow s (twistedTranslate C v x) = twistedTranslate C v (toricFlow s x) :=
  fibreMultiplier_twistedTranslate_commute _ C v x

/-- Restriction of the literal toric vertical flow to an original open cusp tube. -/
def tubeFlow (D : TopologicalSpace.Opens ℂ) (s : ℂ) (x : Tube D) : Tube D :=
  ⟨toricFlow s x, by
    change time (toricFlow s x) ∈ D
    rw [toricFlow_time]
    exact x.property⟩

@[simp] theorem tubeFlow_coe (D : TopologicalSpace.Opens ℂ) (s : ℂ) (x : Tube D) :
    (tubeFlow D s x : ToricSpace.Space) = toricFlow s x := rfl

@[simp] theorem tubeFlow_zero (D : TopologicalSpace.Opens ℂ) (x : Tube D) :
    tubeFlow D 0 x = x := Subtype.ext (toricFlow_zero x)

theorem tubeFlow_add (D : TopologicalSpace.Opens ℂ) (s t : ℂ) (x : Tube D) :
    tubeFlow D (s + t) x = tubeFlow D s (tubeFlow D t x) :=
  Subtype.ext (toricFlow_add s t x)

@[simp] theorem tubeFlow_int_cast (D : TopologicalSpace.Opens ℂ) (n : ℤ) (x : Tube D) :
    tubeFlow D (n : ℂ) x = x := Subtype.ext (toricFlow_int_cast n x)

theorem tubeFlow_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (s : ℂ) (v : Fin 2 → ℤ) (x : Tube D) :
    tubeFlow D s (tubeTranslate C D v x) = tubeTranslate C D v (tubeFlow D s x) :=
  Subtype.ext (toricFlow_twistedTranslate C s v x)

/-- Joint holomorphicity in the unchanged native tube atlas, with the flow parameter last. -/
theorem tubeFlow_joint_holomorphic (D : TopologicalSpace.Opens ℂ) :
    ContMDiff ((I₃).prod I₁) I₃ ω (fun p : Tube D × ℂ => tubeFlow D p.2 p.1) := by
  intro p
  have he : ContMDiffAt ((I₃).prod I₁) I₃ ω
      (fun q : Tube D × ℂ => (tubeFlow D q.2 q.1 : ToricSpace.Space)) p ↔
      ContMDiffAt ((I₃).prod I₁) I₃ ω (fun q : Tube D × ℂ => tubeFlow D q.2 q.1) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (toricFlow_joint_holomorphic.comp
    (contMDiff_snd.prodMk (contMDiff_subtype_val.comp contMDiff_fst)) p)

theorem tubeFlow_holomorphic (D : TopologicalSpace.Opens ℂ) (s : ℂ) :
    ContMDiff I₃ I₃ ω (tubeFlow D s) := by
  exact ContMDiff.comp (I := I₃) (I' := (I₃).prod I₁) (I'' := I₃)
    (f := fun x : Tube D => (x, s))
    (g := fun p : Tube D × ℂ => tubeFlow D p.2 p.1)
    (tubeFlow_joint_holomorphic D) (contMDiff_id.prodMk contMDiff_const)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
