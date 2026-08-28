import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotationGeometry

/-!
# A genuine based homotopy from a square to its quarter turn

Every intermediate coordinate map preserves the whole square perimeter.
Composing with an arbitrary native generalized loop therefore gives a
homotopy relative to the entire boundary, without connectedness hypotheses.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- Convert the centered sup-norm unit ball back to the native square. -/
def rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) : Fin 2 → I :=
  ![⟨(v.1 + 1) / 2, by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2, by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

theorem rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1} {hw : ‖w‖ ≤ 1}
    (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

theorem rotationUncenter_centered (u : Fin 2 → I) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

theorem rotationUncenter_vector (u : Fin 2 → I) :
    rotationUncenter (rotationVector (rotationCentered u))
      (by simpa using rotationCentered_norm_le u) = quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
    dsimp [rotationUncenter, rotationVector, rotationCentered,
      unitInterval.symm] <;> ring

theorem rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) (he : ‖v‖ = 1) :
    rotationUncenter v hv ∈ Cube.boundary (Fin 2) := by
  have hm : 1 ≤ max |v.1| |v.2| := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using he.ge
  rcases le_max_iff.mp hm with ha | hb
  · have hn : |v.1| = 1 := le_antisymm ((norm_fst_le v).trans hv) ha
    by_cases hp : 0 ≤ v.1
    · have h : v.1 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.1 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
  · have hn : |v.2| = 1 := le_antisymm ((norm_snd_le v).trans hv) hb
    by_cases hp : 0 ≤ v.2
    · have h : v.2 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.2 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith

/-- An explicit continuous deformation of square coordinates through
perimeter-preserving maps. -/
def quarterTurnHomotopyMap : C(I × (Fin 2 → I), Fin 2 → I) where
  toFun z := rotationUncenter (rotationNormalized z.1 z.2)
    (rotationNormalized_norm_le z.1 z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      change Continuous (fun z : I × (Fin 2 → I) =>
        ((rotationNormalized z.1 z.2).1 + 1) / 2)
      exact (rotationNormalized_continuous.fst.add continuous_const).div_const 2
    · apply Continuous.subtype_mk
      change Continuous (fun z : I × (Fin 2 → I) =>
        ((rotationNormalized z.1 z.2).2 + 1) / 2)
      exact (rotationNormalized_continuous.snd.add continuous_const).div_const 2

@[simp] theorem quarterTurnHomotopyMap_zero (u : Fin 2 → I) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
    (rotationNormalized_zero u)).trans
    (rotationUncenter_centered u)

@[simp] theorem quarterTurnHomotopyMap_one (u : Fin 2 → I) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
    (rotationNormalized_one u)).trans
    (rotationUncenter_vector u)

theorem quarterTurnHomotopyMap_boundary (t : I) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual homotopy of native generalized loops, relative to the whole
boundary; no Hurewicz or degree theorem is used. -/
def rotatedSquareLoop_homotopy (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2)) where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans
    (p.property u hu).symm

/-- A clockwise square rotation acts trivially on the native second homotopy group. -/
theorem rotatedSquareLoop_class (p : GenLoop (Fin 2) X x) :
    (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound (show GenLoop.Homotopic p (rotatedSquareLoop p) from
      ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
