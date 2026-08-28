import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation
import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows

/-!
# Excellence and indexed counts after exchanging two critical values

Exchanging two values is composition with the actual transposition on the
critical set, so injectivity of the critical values is retained. Preserving
the critical set and intrinsic indices preserves every indexed count.
The new excellent Morse function therefore has a newly constructed
compatible surgery system for the next finite reduction step.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem injOn_of_exchanged_values {X Y : Type*} {f g : X → Y} {S : Set X} {p q : X}
    (hinj : InjOn f S) (hp : p ∈ S) (hq : q ∈ S)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ S, x ≠ p → x ≠ q → g x = f x) : InjOn g S := by
  classical
  have hform (x : X) (hx : x ∈ S) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hothers x hx hxp hxq
  have hmaps : MapsTo (Equiv.swap p q) S S := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hq
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hp
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hx
  intro x hx y hy hxy
  apply (Equiv.swap p q).injective
  apply hinj (hmaps hx) (hmaps hy)
  rw [← hform x hx, ← hform y hy]
  exact hxy

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}

theorem nativeMorseCount_eq_of_preserved_indices
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hindex : ∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x)
    (k : ℕ) : nativeMorseCount E g k = nativeMorseCount E f k := by
  have heq : {x : M | x ∈ criticalPoints E g ∧ nativeMorseIndex E g x = k} =
      {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = k} := by
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hcrit]
    by_cases hx : x ∈ criticalPoints E f
    · rw [hindex x hx]
    · simp only [hx, false_and]
  exact congrArg Set.ncard heq

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem adapted_surgery_system_after_value_exchange
    (S : AdaptedSurgeryWindows E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : IsMorse E g)
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) :
    InjOn g (criticalPoints E g) ∧ Nonempty (AdaptedSurgeryWindows E g) := by
  have hinj : InjOn g (criticalPoints E g) := by
    rw [hcrit]
    exact injOn_of_exchanged_values S.distinct hp hq hgp hgq
      (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  exact ⟨hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
