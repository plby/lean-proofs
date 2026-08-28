import Wikipedia.NoExoticSixSphere.EnergyControlledHomotopy
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Global lowering from crossings of every level

If the desired endpoint could not be reached, its energy would bound below
all reachable uniform energy bounds. Crossing the infimum of those bounds
contradicts its defining lower-bound property. No infinite concatenation or
limiting homotopy is used: the proof produces a finite concatenation.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]

theorem lowering_of_level_crossings (energy : Y → ℝ) (admissible : Set Y)
    (floor minimum cap target : ℝ) (hfloor : floor < target) (htarget : minimum < target)
    (hcross : ∀ level : ℝ, minimum < level → floor < level → level < cap →
      ∃ δ > 0, ∀ q : C(M, Y), (∀ x, q x ∈ admissible) →
        (∀ x, energy (q x) ≤ level + δ / 4) →
        ∃ r : C(M, Y), (∀ x, energy (r x) < level - δ / 2) ∧
          ControlledReachable energy admissible floor cap q r)
    (p : C(M, Y)) (hp : ∀ x, p x ∈ admissible)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy (p x) ≤ start) :
    ∃ q : C(M, Y), (∀ x, energy (q x) < target) ∧
      ControlledReachable energy admissible floor cap p q := by
  classical
  by_contra hnone
  let A : Set ℝ := {a | ∃ q : C(M, Y), (∀ x, energy (q x) ≤ a) ∧
    ControlledReachable energy admissible floor cap p q}
  have hstartA : start ∈ A :=
    ⟨p, hpstart, ControlledReachable.refl hp (fun x ↦ (hpstart x).trans hstart.le)⟩
  have hA : A.Nonempty := ⟨start, hstartA⟩
  have hbound : ∀ a ∈ A, target ≤ a := by
    intro a ha
    by_contra hle
    obtain ⟨q, hq, hreach⟩ := ha
    exact hnone ⟨q, fun x ↦ (hq x).trans_lt (lt_of_not_ge hle), hreach⟩
  have hAbdd : BddBelow A := ⟨target, hbound⟩
  have htargetInf : target ≤ sInf A := le_csInf hA hbound
  have hInfCap : sInf A < cap := (csInf_le hAbdd hstartA).trans_lt hstart
  obtain ⟨δ, hδ, hcrossδ⟩ := hcross (sInf A) (htarget.trans_le htargetInf)
    (hfloor.trans_le htargetInf) hInfCap
  obtain ⟨a, ha, haInf⟩ := exists_lt_of_csInf_lt hA
    (show sInf A < sInf A + δ / 4 by linarith)
  obtain ⟨q, hq, hreach⟩ := ha
  obtain ⟨r, hr, hreach'⟩ := hcrossδ q hreach.endpoint_mem
    (fun x ↦ (hq x).trans haInf.le)
  have hrA : sInf A - δ / 2 ∈ A :=
    ⟨r, fun x ↦ (hr x).le, hreach.trans hreach'⟩
  have := csInf_le hAbdd hrA
  linarith

end NoExoticSixSphere.FiniteControlledLowering
