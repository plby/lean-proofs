import Mathlib.Topology.Homotopy.HomotopyGroup

/-! # Continuity and evaluation of native cubical concatenation -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] {x : X}

theorem continuous_genLoop_transAt (i : N) :
    Continuous (fun z : GenLoop N X x × GenLoop N X x => GenLoop.transAt i z.1 z.2) := by
  have h : Continuous (fun z : GenLoop N X x × GenLoop N X x =>
      GenLoop.fromLoop i ((GenLoop.toLoop i z.1).trans (GenLoop.toLoop i z.2))) :=
    (GenLoop.continuous_fromLoop i).comp
    (((GenLoop.continuous_toLoop i).comp continuous_fst).path_trans
      ((GenLoop.continuous_toLoop i).comp continuous_snd))
  simpa only [Function.comp_def, GenLoop.fromLoop_trans_toLoop] using h

/-- Native concatenation, packaged as a continuous map of the two loop spaces. -/
def genLoopTransAtMap (i : N) : C(GenLoop N X x × GenLoop N X x, GenLoop N X x) :=
  ⟨fun z => GenLoop.transAt i z.1 z.2, continuous_genLoop_transAt i⟩

theorem genLoop_transAt_apply (i : N) (p q : GenLoop N X x) (u : N → I) :
    GenLoop.transAt i p q u =
      if (u i : ℝ) ≤ 1 / 2 then
        p (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * u i)))
      else q (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * u i - 1))) := rfl

theorem genLoop_transAt_const (i : N) :
    GenLoop.transAt i (GenLoop.const : GenLoop N X x) GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simp only [genLoop_transAt_apply, GenLoop.const_apply, ite_self]

end Wikipedia.HomotopyGroupsOfSpheres
