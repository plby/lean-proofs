import Wikipedia.HopfProblem.DegreeCollapseEqualNativeLevels
import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex

/-!
# Critical-value and index control at a lower cut after a two-point birth

The exact critical-set description and retained old function germs give
the lower index bound, the gap below the first new value, and preservation
of the unique index-zero point. These are consequences of the birth data,
not additional geometric hypotheses on its adapted descending flow.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}

theorem birth_preserves_lower_index_bound {a : ℝ} {k : ℕ}
    (hcrit : ∀ z ∈ criticalPoints E g, z ∈ criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : a < g p) (hq : a < g q)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k) :
    ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ k := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · rw [nativeMorseIndex_congr_germ (hkeep z.val hold)]
    apply hlow ⟨z.val, hold⟩
    rwa [← (hkeep z.val hold).self_of_nhds]
  · exact False.elim (hp.not_ge (hzp ▸ hz))
  · exact False.elim (hq.not_ge (hzq ▸ hz))

theorem birth_first_new_value_gap {a b : ℝ}
    (hcrit : ∀ z ∈ criticalPoints E g, z ∈ criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hreg : ∀ z, f z = a → z ∉ criticalPoints E f)
    (hband : ∀ z, f z ∈ Ioo a b → z ∉ criticalPoints E f)
    (hp : g p < b) (hpq : g p < g q) :
    ∀ z : criticalPoints E g, g z < g p → g z < a := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · have hzb : g z < b := hz.trans hp
    have heq := (hkeep z.val hold).self_of_nhds
    by_contra hnot
    have haz : a ≤ f z := by rw [← heq]; exact le_of_not_gt hnot
    have hne : a ≠ f z := fun h => hreg z.val h.symm hold
    exact hband z.val ⟨lt_of_le_of_ne haz hne, by rwa [← heq]⟩ hold
  · exact False.elim ((hzp ▸ hz : g p < g p).false)
  · exact False.elim (hpq.not_gt (hzq ▸ hz))

theorem birth_preserves_unique_index_zero (m : criticalPoints E f)
    (hcrit : ∀ z ∈ criticalPoints E g, z ∈ criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : nativeMorseIndex E g p ≠ 0) (hq : nativeMorseIndex E g q ≠ 0)
    (hunique : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∀ z ∈ criticalPoints E g, nativeMorseIndex E g z = 0 → z = m.val := by
  intro z hz hi
  rcases hcrit z hz with hold | rfl | rfl
  · have hiold : nativeMorseIndex E f z = 0 :=
      (nativeMorseIndex_congr_germ (hkeep z hold)).symm.trans hi
    exact congrArg Subtype.val (hunique ⟨z, hold⟩ hiold)
  · exact False.elim (hp hi)
  · exact False.elim (hq hi)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
