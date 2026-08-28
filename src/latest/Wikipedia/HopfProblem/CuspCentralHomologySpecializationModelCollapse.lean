import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelPolar
import Wikipedia.HopfProblem.CuspHoneycombCollapse

/-!
# The prescribed collapse in actual positive-level polar coordinates

At a positive real time the compact base phase is one. Inserting the
literal positive-fibre polar coordinates into the independently defined
prescribed collapse therefore gives the original honeycomb polar map.
No chosen retraction or endpoint property is used in these identities.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspHoneycomb

theorem positiveLevel_norm_le (ρ : ℝ) (hρ : 0 ≤ ρ) (η : ℝ) (hρη : ρ ≤ η) :
    ‖(ρ : ℂ)‖ ≤ η := by
  rwa [Complex.norm_of_nonneg hρ]

/-- A literal nonzero time fibre sits in every punctured closed tube containing its level. -/
def toricFibrePunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) : PuncturedClosedTube η :=
  levelToPunctured η t ht (toricFibreLevelHomeomorph η t htη x)

@[simp] theorem toricFibrePunctured_coe (η : ℝ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) : ((toricFibrePunctured η t ht htη x).1 : Space) = (x : Space) := rfl

/-- The positive fixed-height fibre is the actual positive polar slice in the closed tube. -/
def positiveFibrePunctured (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (q : PositiveFibre ρ) : PuncturedPositiveTube η :=
  ⟨⟨q.1, by rw [q.2, Complex.norm_of_nonneg hρ.le]; exact hρη⟩,
    by rw [q.2]; exact Complex.ofReal_ne_zero.mpr hρ.ne'⟩

@[simp] theorem positiveFibrePunctured_coe (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (q : PositiveFibre ρ) : ((positiveFibrePunctured ρ hρ η hρη q).1.1 : Space) =
      (q.1 : Space) := rfl

theorem toricFibrePunctured_positiveFibrePolarMap
    (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (φ : CompactFibreTorus) (q : PositiveFibre ρ) :
    toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
        (positiveLevel_norm_le ρ hρ.le η hρη) (positiveFibrePolarMap ρ (φ, q)) =
      puncturedPolarMap η (compactFibrePhase φ, positiveFibrePunctured ρ hρ η hρη q) := by
  apply Subtype.ext
  apply Subtype.ext
  exact compactFibreAction_eq_compact φ (q.1 : Space)

theorem prescribedCollapse_positiveFibrePolarMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (φ : CompactFibreTorus) (q : PositiveFibre ρ) :
    prescribedCollapse C₀ η
        (toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
          (positiveLevel_norm_le ρ hρ.le η hρη) (positiveFibrePolarMap ρ (φ, q))) =
      honeycombPolarMap C₀ (φ, normalizedPosition C₀ (q.1 : Space)) := by
  apply Subtype.ext
  rw [toricFibrePunctured_positiveFibrePolarMap ρ hρ η hρη φ q, prescribedCollapse_polar]
  change compactTorusAction (compactFibrePhase φ)
      ((honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))).1 : Space) =
    compactFibreAction φ
      ((honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))).1 : Space)
  exact (compactFibreAction_eq_compact φ _).symm

/-- Freezing an already constant twist introduces no straightening motion. -/
theorem straightenedPrescribedCollapse_const
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (x : PuncturedClosedTube η) :
    straightenedPrescribedCollapse (fun _ => C₀) η x = prescribedCollapse C₀ η x := by
  have hx : puncturedStraightening (fun _ => C₀) η x = x := by
    apply Subtype.ext
    apply Subtype.ext
    change changeTwist (fun _ => C₀) (fun _ => C₀) (x.1 : Space) = (x.1 : Space)
    exact changeTwist_self (fun _ => C₀) (x.1 : Space)
  change prescribedCollapse C₀ η (puncturedStraightening (fun _ => C₀) η x) = _
  rw [hx]

/-- The independent prescribed representative map, not a chosen deformation endpoint,
has the original honeycomb formula on each positive-level polar representative. -/
theorem prescribedFibreUpstairs_positiveFibrePolarMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (φ : CompactFibreTorus) (q : PositiveFibre ρ) :
    prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ)
        (Complex.ofReal_ne_zero.mpr hρ.ne')
        (toricFibreLevelHomeomorph η (ρ : ℂ) (positiveLevel_norm_le ρ hρ.le η hρη)
          (positiveFibrePolarMap ρ (φ, q))) =
      honeycombCollapseMap (fun _ => C₀) ε hε
        (φ, normalizedPosition C₀ (q.1 : Space)) := by
  change centralProject (fun _ => C₀) ε hε
    (straightenedPrescribedCollapse (fun _ => C₀) η
      (toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
        (positiveLevel_norm_le ρ hρ.le η hρη) (positiveFibrePolarMap ρ (φ, q)))) = _
  rw [straightenedPrescribedCollapse_const,
    prescribedCollapse_positiveFibrePolarMap C₀ ρ hρ η hρη φ q]
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
