import Wikipedia.HopfProblem.DegreeCollapseNativeIndexDisorder

/-!
# Global native Morse index ordering by a finite decreasing disorder

Choose an excellent Morse function of least finite index disorder among
those with the original critical set and intrinsic indices. Any ordering
failure contains an adjacent strict inversion. The constructed geometric
exchange preserves this class and lowers the natural-valued disorder,
contradicting minimality. Thus a genuinely index-ordered native Morse
function and compatible surgery system are constructed, without an
ordering hypothesis and without changing any indexed critical count.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_index_ordered_morse_system_preserving_critical_points {f₀ : M → ℝ}
    (S₀ : AdaptedSurgeryWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : IsMorse E f₀) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      criticalPoints E f = criticalPoints E f₀ ∧
      (∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by
  classical
  let P : ℕ → Prop := fun n => ∃ f : M → ℝ,
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
    criticalPoints E f = criticalPoints E f₀ ∧
    (∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
    InjOn f (criticalPoints E f) ∧ nativeIndexDisorder E f = n
  have hex : ∃ n, P n :=
    ⟨nativeIndexDisorder E f₀, f₀, hf₀, hm₀, rfl, fun _ _ => rfl, S₀.distinct, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hindices, hinj, hdisorder⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  have horder : ∀ p q : criticalPoints E f,
      f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
    by_contra hnot
    let _ := S.finite.fintype
    obtain ⟨p, q, hpq, hconsecutive, hinversion⟩ := exists_adjacent_index_inversion
      (h := fun x : criticalPoints E f => f x)
      (fun x y h => Subtype.ext (hinj x.property y.property h))
      (fun x : criticalPoints E f => nativeMorseIndex E f x) hnot
    obtain ⟨g, hg, hmg, hcritg, hgp, hgq, -, hothers, hinjg, -, hindicesg, -⟩ :=
      S.exchange_nonincreasing_native_indices hf hm p q hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder E g < nativeIndexDisorder E f :=
      nativeIndexDisorder_exchange_lt S.finite hinj p q hpq hconsecutive hinversion
        hcritg hgp hgq hothers hindicesg
    have hindicesg₀ (x : M) (hx : x ∈ criticalPoints E f₀) :
        nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hminimal := Nat.find_min' hex
      ⟨g, hg, hmg, hcritg.trans hcrit, hindicesg₀, hinjg, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hindices, S, horder,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

variable (E M) in
theorem exists_index_ordered_native_morse_system :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        ∀ p q : criticalPoints E f, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
  obtain ⟨f₀, hf₀, hm₀, ⟨S₀⟩⟩ := exists_morse_function_with_adaptedSurgeryWindows E M
  obtain ⟨f, hf, hm, -, -, S, horder, -⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points S₀ hf₀ hm₀
  exact ⟨f, hf, hm, S, horder⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
