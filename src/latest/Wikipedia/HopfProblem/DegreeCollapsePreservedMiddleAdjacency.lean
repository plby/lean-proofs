import Wikipedia.HopfProblem.DegreeCollapseUnitBasinCancellation

/-!
# A first middle handle is consecutive to the preserved last index-two handle

Index ordering leaves only indices two or three between the selected
points. The first-middle property excludes index three. Preserved lower
values and the original last handle's isolated window exclude index two.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}

theorem consecutive_last_two_first_three
    (S : SurgeryWindows E f) (p : criticalPoints E f)
    (hp : nativeMorseIndex E f p = 2)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hindices : ∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z)
    (hfixed : ∀ z ∈ criticalPoints E f, nativeMorseIndex E f z ≠ 3 → g z = f z)
    (hcut : ∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 → f z < S.upper p)
    (horder : ∀ x y : criticalPoints E g, g x < g y →
      nativeMorseIndex E g x ≤ nativeMorseIndex E g y)
    (q : criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hfirst : ∀ z : criticalPoints E g, nativeMorseIndex E g z = 3 → z ≠ q → g q < g z) :
    ∀ z : criticalPoints E g, ¬(g p < g z ∧ g z < g q) := by
  let pg : criticalPoints E g := ⟨p.val, hcrit.symm ▸ p.property⟩
  have hpg : nativeMorseIndex E g pg = 2 := (hindices p p.property).trans hp
  have hgp : g p = f p := hfixed p p.property (by omega)
  intro z hz
  have hle : nativeMorseIndex E g z ≤ 3 := (horder z q hz.2).trans_eq hq
  have hge : 2 ≤ nativeMorseIndex E g z := hpg.symm.trans_le (horder pg z hz.1)
  have hcases : nativeMorseIndex E g z = 2 ∨ nativeMorseIndex E g z = 3 := by omega
  rcases hcases with hi2 | hi3
  · let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
    have hfidx : nativeMorseIndex E f zf = 2 := (hindices z zf.property).symm.trans hi2
    have hgz : g z = f z := hfixed z zf.property (by change nativeMorseIndex E f zf ≠ 3; omega)
    have hvalue : f p < f z := by
      have hh := hz.1
      rwa [hgp, hgz] at hh
    have hupper : f z < S.upper p := hcut zf (by omega)
    have heq : z.val = p.val := S.isolated p z zf.property
      ⟨((S.lower_lt_value p).trans hvalue).le, hupper.le⟩
    exact hvalue.ne (congrArg f heq).symm
  · have hne : z ≠ q := fun heq => hz.2.ne (congrArg (fun x : criticalPoints E g => g x) heq)
    exact (hfirst z hi3 hne).not_gt hz.2

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
