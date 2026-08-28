import Wikipedia.HopfProblem.CuspRetractionPolar

/-!
# The compact fibre torus acting on the actual toric space

The two phase coordinates act by the existing fibre multiplier. This
action preserves the complex base parameter and the actual positive
modulus, and its action map is proper by compactness of the torus.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts

abbrev CompactFibreTorus := Fin 2 → Circle

def compactFibreUnits : CompactFibreTorus →* (Fin 2 → ℂˣ) where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

@[simp] theorem compactFibreUnits_coe (u : CompactFibreTorus) (i : Fin 2) :
    (compactFibreUnits u i : ℂ) = (u i : ℂ) := rfl

/-- The fibre torus embeds in the full compact torus with last phase one. -/
def compactFibrePhase (u : CompactFibreTorus) : CompactTorus := ![u 0, u 1, 1]

@[simp] theorem compactFibrePhase_zero (u : CompactFibreTorus) :
    compactFibrePhase u 0 = u 0 := rfl

@[simp] theorem compactFibrePhase_one (u : CompactFibreTorus) :
    compactFibrePhase u 1 = u 1 := rfl

@[simp] theorem compactFibrePhase_two (u : CompactFibreTorus) :
    compactFibrePhase u 2 = 1 := rfl

theorem compactFibrePhase_continuous : Continuous compactFibrePhase := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

theorem compactTorusUnits_compactFibrePhase (u : CompactFibreTorus) :
    compactTorusUnits (compactFibrePhase u) = fibreMultiplier (compactFibreUnits u) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact Circle.toUnits.map_one

def compactFibreAction (u : CompactFibreTorus) (x : Space) : Space :=
  torusAction (fibreMultiplier (compactFibreUnits u)) x

theorem compactFibreAction_eq_compact (u : CompactFibreTorus) (x : Space) :
    compactFibreAction u x = compactTorusAction (compactFibrePhase u) x := by
  rw [compactTorusAction, compactTorusUnits_compactFibrePhase]
  rfl

@[simp] theorem compactFibreAction_one (x : Space) : compactFibreAction 1 x = x := by
  simp only [compactFibreAction, map_one, fibreMultiplier_one, torusAction_one]

theorem compactFibreAction_mul (u v : CompactFibreTorus) (x : Space) :
    compactFibreAction u (compactFibreAction v x) = compactFibreAction (u * v) x := by
  simp only [compactFibreAction, map_mul, fibreMultiplier_mul, torusAction_mul]

instance compactFibreMulAction : MulAction CompactFibreTorus Space where
  smul := compactFibreAction
  one_smul := compactFibreAction_one
  mul_smul u v x := (compactFibreAction_mul u v x).symm

theorem compactFibreAction_continuous :
    Continuous (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) := by
  have h := compactTorusAction_continuous.comp
    ((compactFibrePhase_continuous.comp continuous_fst).prodMk continuous_snd)
  exact h.congr (fun _ => (compactFibreAction_eq_compact _ _).symm)

instance compactFibreContinuousSMul : ContinuousSMul CompactFibreTorus Space :=
  ⟨compactFibreAction_continuous⟩

@[simp] theorem time_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    time (compactFibreAction u x) = time x := time_fibreMultiplier _ x

@[simp] theorem modulus_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    modulus (compactFibreAction u x) = modulus x := by
  rw [compactFibreAction_eq_compact, modulus_compactTorusAction]

def compactFibreActionShear : CompactFibreTorus × Space ≃ₜ CompactFibreTorus × Space where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

theorem compactFibreAction_isProperMap :
    IsProperMap (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) :=
  isProperMap_snd_of_compactSpace.comp compactFibreActionShear.isProperMap

theorem compactFibreAction_isClosedMap :
    IsClosedMap (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) :=
  compactFibreAction_isProperMap.isClosedMap

end Wikipedia.HopfProblem.ToricSpace
