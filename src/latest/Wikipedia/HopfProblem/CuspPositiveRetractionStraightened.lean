import Wikipedia.HopfProblem.CuspRetractionHomeomorph
import Mathlib.Topology.Homotopy.Basic

/-!
# Transporting an actual frozen-twist homotopy

The explicit homeomorphism of Lemma 7.5 conjugates a supplied homotopy
for the frozen twist into one for the original twist.  Continuity,
central-fibre properties, parameter bounds, and equivariance are preserved.
This file is a transport construction: it makes no existence assertion
about the supplied frozen homotopy.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricSpace CuspRetraction

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
variable (hε : 0 < ε) (hε1 : ε < 1)
variable (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
variable (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (hηε : η < ε)

/-- The already proved, explicit straightening of the actual closed toric tube. -/
def closedFrozenStraightening : ClosedTube η ≃ₜ ClosedTube η :=
  closedTubeHomeomorph C (frozen C) hε hε1 hC (fun _ _ => continuousOn_const)
    rfl hRC hRD hηε

local notation "G" => closedFrozenStraightening C hε hε1 hC hRC hRD hηε

theorem closedFrozenStraightening_base (x : ClosedTube η) :
    time (G x : Space) = time (x : Space) :=
  closedTubeHomeomorph_base C (frozen C) hε hε1 hC (fun _ _ => continuousOn_const)
    rfl hRC hRD hηε x

theorem closedFrozenStraightening_symm_base (x : ClosedTube η) :
    time ((G).symm x : Space) = time (x : Space) := by
  have h := closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε ((G).symm x)
  rw [(G).apply_symm_apply] at h
  exact h.symm

theorem closedFrozenStraightening_fixed (x : ClosedTube η) (hx : time (x : Space) = 0) :
    G x = x :=
  closedTubeHomeomorph_fixes_central C (frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε x hx

theorem closedFrozenStraightening_equivariant (v : Fin 2 → ℤ) (x : ClosedTube η) :
    G (closedTranslate C η v x) = closedTranslate (frozen C) η v (G x) :=
  closedTubeHomeomorph_equivariant C (frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε v x

theorem closedFrozenStraightening_symm_equivariant (v : Fin 2 → ℤ) (x : ClosedTube η) :
    (G).symm (closedTranslate (frozen C) η v x) = closedTranslate C η v ((G).symm x) := by
  apply (G).injective
  rw [(G).apply_symm_apply, closedFrozenStraightening_equivariant, (G).apply_symm_apply]

theorem closedFrozenStraightening_fibre_torus (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    G (closedFibreAction η u x) = closedFibreAction η u (G x) :=
  closedTubeHomeomorph_fibre_torus C (frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε u hu x

theorem closedFrozenStraightening_symm_fibre_torus (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    (G).symm (closedFibreAction η u x) = closedFibreAction η u ((G).symm x) := by
  apply (G).injective
  rw [(G).apply_symm_apply, closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu,
    (G).apply_symm_apply]

variable (H : C(unitInterval × ClosedTube η, ClosedTube η))

/-- Conjugation `G⁻¹ ∘ H(s, ·) ∘ G`, as a jointly continuous map. -/
def straightenedHomotopy : C(unitInterval × ClosedTube η, ClosedTube η) where
  toFun p := (G).symm (H (p.1, G p.2))
  continuous_toFun := (G).symm.continuous.comp
    (H.continuous.comp (continuous_fst.prodMk ((G).continuous.comp continuous_snd)))

@[simp] theorem straightenedHomotopy_apply (s : unitInterval) (x : ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) = (G).symm (H (s, G x)) := rfl

theorem straightenedHomotopy_continuous :
    Continuous (straightenedHomotopy C hε hε1 hC hRC hRD hηε H) :=
  (straightenedHomotopy C hε hε1 hC hRC hRD hηε H).continuous

theorem straightenedHomotopy_time (s : unitInterval) (x : ClosedTube η) :
    time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : Space) =
      time (H (s, G x) : Space) :=
  closedFrozenStraightening_symm_base C hε hε1 hC hRC hRD hηε _

theorem straightenedHomotopy_zero (hzero : ∀ x : ClosedTube η, H (0, x) = x)
    (x : ClosedTube η) : straightenedHomotopy C hε hε1 hC hRC hRD hηε H (0, x) = x := by
  rw [straightenedHomotopy_apply, hzero, (G).symm_apply_apply]

theorem straightenedHomotopy_fixed
    (hfixed : ∀ (s : unitInterval) (x : ClosedTube η),
      time (x : Space) = 0 → H (s, x) = x)
    (s : unitInterval) (x : ClosedTube η) (hx : time (x : Space) = 0) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) = x := by
  have hGx : time (G x : Space) = 0 :=
    (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x).trans hx
  rw [straightenedHomotopy_apply, hfixed s (G x) hGx, (G).symm_apply_apply]

theorem straightenedHomotopy_one_central
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0) (x : ClosedTube η) :
    time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x) : Space) = 0 := by
  rw [straightenedHomotopy_time]
  exact hone (G x)

theorem straightenedHomotopy_norm_time_le
    (hnorm : ∀ (s : unitInterval) (x : ClosedTube η),
      ‖time (H (s, x) : Space)‖ ≤ ‖time (x : Space)‖)
    (s : unitInterval) (x : ClosedTube η) :
    ‖time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : Space)‖ ≤
      ‖time (x : Space)‖ := by
  rw [straightenedHomotopy_time]
  exact (hnorm s (G x)).trans_eq
    (congrArg norm (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x))

theorem straightenedHomotopy_equivariant
    (hequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate (frozen C) η v x) = closedTranslate (frozen C) η v (H (s, x)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, closedTranslate C η v x) =
      closedTranslate C η v (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply, closedFrozenStraightening_equivariant, hequiv,
    closedFrozenStraightening_symm_equivariant]

theorem straightenedHomotopy_fibre_torus_equivariant
    (hequiv : ∀ (s : unitInterval) (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
      ∀ x : ClosedTube η, H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x)))
    (s : unitInterval) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, closedFibreAction η u x) =
      closedFibreAction η u (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply,
    closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu, hequiv s u hu,
    closedFrozenStraightening_symm_fibre_torus C hε hε1 hC hRC hRD hηε u hu]

end Wikipedia.HopfProblem.CuspPositiveRetraction
