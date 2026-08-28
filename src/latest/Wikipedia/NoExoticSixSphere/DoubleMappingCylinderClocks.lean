import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Endpoint-preserving clocks for the double-cylinder open cover

One clock decreases every height and collapses the lower two thirds to
zero at its final time. Its reflected clock increases every height and
collapses the upper two thirds to one. Both fix the two endpoints at
every time, so their families descend through both cylinder gluings.
-/

noncomputable section

open Set Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder.Clock

def lowerEndpoint : C(I, I) :=
  ⟨fun t ↦ ⟨max 0 (3 * (t : ℝ) - 2), le_max_left _ _,
    max_le zero_le_one (by have ht := t.property.2; linarith)⟩,
    (continuous_const.max
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)).subtype_mk _⟩

theorem lowerEndpoint_zero : lowerEndpoint 0 = 0 := by
  apply Subtype.ext
  norm_num [lowerEndpoint]

theorem lowerEndpoint_one : lowerEndpoint 1 = 1 := by
  apply Subtype.ext
  norm_num [lowerEndpoint]

theorem lowerEndpoint_le (t : I) : lowerEndpoint t ≤ t := by
  change max 0 (3 * (t : ℝ) - 2) ≤ (t : ℝ)
  exact max_le t.property.1 (by have ht := t.property.2; linarith)

theorem lowerEndpoint_eq_zero (t : I) (ht : (t : ℝ) ≤ 2 / 3) : lowerEndpoint t = 0 := by
  apply Subtype.ext
  change max 0 (3 * (t : ℝ) - 2) = 0
  exact max_eq_left (by linarith)

def lowerClock : C(I × I, I) :=
  ⟨fun p ↦ Set.Icc.convexComb (lowerEndpoint p.2) p.2 (σ p.1),
    Set.Icc.continuous_convexComb_prod.comp
      ((lowerEndpoint.continuous.comp continuous_snd).prodMk
        (continuous_snd.prodMk (continuous_symm.comp continuous_fst)))⟩

theorem lowerClock_initial (t : I) : lowerClock (0, t) = t := by
  change Set.Icc.convexComb (lowerEndpoint t) t (σ 0) = t
  rw [symm_zero, Set.Icc.convexComb_one]

theorem lowerClock_terminal (t : I) : lowerClock (1, t) = lowerEndpoint t := by
  change Set.Icc.convexComb (lowerEndpoint t) t (σ 1) = lowerEndpoint t
  rw [symm_one, Set.Icc.convexComb_zero]

theorem lowerClock_zero (s : I) : lowerClock (s, 0) = 0 := by
  change Set.Icc.convexComb (lowerEndpoint 0) 0 (σ s) = 0
  rw [lowerEndpoint_zero, Set.Icc.convexComb_eq]

theorem lowerClock_one (s : I) : lowerClock (s, 1) = 1 := by
  change Set.Icc.convexComb (lowerEndpoint 1) 1 (σ s) = 1
  rw [lowerEndpoint_one, Set.Icc.convexComb_eq]

theorem lowerClock_le (s t : I) : lowerClock (s, t) ≤ t :=
  Set.Icc.convexComb_le (lowerEndpoint_le t) (σ s)

theorem lowerClock_terminal_zero (t : I) (ht : (t : ℝ) ≤ 2 / 3) : lowerClock (1, t) = 0 := by
  rw [lowerClock_terminal, lowerEndpoint_eq_zero t ht]

def upperClock : C(I × I, I) :=
  ⟨fun p ↦ σ (lowerClock (p.1, σ p.2)), continuous_symm.comp
    (lowerClock.continuous.comp (continuous_fst.prodMk (continuous_symm.comp continuous_snd)))⟩

theorem upperClock_initial (t : I) : upperClock (0, t) = t := by
  change σ (lowerClock (0, σ t)) = t
  rw [lowerClock_initial, symm_symm]

theorem upperClock_zero (s : I) : upperClock (s, 0) = 0 := by
  change σ (lowerClock (s, σ 0)) = 0
  rw [symm_zero, lowerClock_one, symm_one]

theorem upperClock_one (s : I) : upperClock (s, 1) = 1 := by
  change σ (lowerClock (s, σ 1)) = 1
  rw [symm_one, lowerClock_zero, symm_zero]

theorem le_upperClock (s t : I) : t ≤ upperClock (s, t) := by
  have h : (lowerClock (s, σ t) : ℝ) ≤ 1 - (t : ℝ) := lowerClock_le s (σ t)
  change (t : ℝ) ≤ 1 - (lowerClock (s, σ t) : ℝ)
  linarith

theorem upperClock_terminal_one (t : I) (ht : (1 : ℝ) / 3 ≤ t) : upperClock (1, t) = 1 := by
  change σ (lowerClock (1, σ t)) = 1
  have h : (σ t : ℝ) ≤ 2 / 3 := by change 1 - (t : ℝ) ≤ 2 / 3; linarith
  rw [lowerClock_terminal_zero (σ t) h, symm_zero]

end NoExoticSixSphere.DoubleMappingCylinder.Clock
