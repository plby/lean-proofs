import Wikipedia.HopfProblem.DegreeCollapseCommonCutFamily

/-!
# Reorder a labelled middle family without changing its geometric matrix

The full compact basin image provides the native canonical sphere needed
for no-connection rearrangement. The selected adjacent values are exchanged
with the exact same flow. Every old parameter map survives at the literal
common cut, and its matrix is exactly unchanged in the transported basis.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f g : M → ℝ}

theorem native_index_order_of_equal_index_exchange
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p q : criticalPoints E f) (hequal : nativeMorseIndex E f p = nativeMorseIndex E f q)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ criticalPoints E f, x ≠ p.val → x ≠ q.val → g x = f x)
    (hindices : ∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) :
    ∀ x y : criticalPoints E g, g x < g y →
      nativeMorseIndex E g x ≤ nativeMorseIndex E g y := by
  classical
  have hform (x : criticalPoints E f) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using
      hothers x x.property (fun h => hxp (Subtype.ext h)) (fun h => hxq (Subtype.ext h))
  have hind (x : criticalPoints E f) :
      nativeMorseIndex E f (Equiv.swap p q x) = nativeMorseIndex E f x := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hequal.symm
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hequal
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  intro x y hxy
  let x' : criticalPoints E f := ⟨x.val, hcrit ▸ x.property⟩
  let y' : criticalPoints E f := ⟨y.val, hcrit ▸ y.property⟩
  have hxy' : f (Equiv.swap p q x') < f (Equiv.swap p q y') := by
    rw [← hform, ← hform]
    exact hxy
  have hh := horder (Equiv.swap p q x') (Equiv.swap p q y') hxy'
  rw [hind, hind] at hh
  rw [hindices x x'.property, hindices y y'.property]
  exact hh

variable [PreconnectedSpace M] [Nonempty M]

theorem AdaptedSurgeryWindows.exists_middle_family_value_exchange
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec)
    (i j : Fin n) (hij : f (p i) < f (p j))
    (hconsecutive : ∀ z : criticalPoints E f, ¬(f (p i) < f z ∧ f z < f (p j))) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        InjOn g (criticalPoints E g) ∧ g (p i) = f (p j) ∧ g (p j) = f (p i) ∧
        (∀ z ∈ criticalPoints E f, z ≠ (p i).val → z ≠ (p j).val → g z = f z) ∧
        (∀ x y : criticalPoints E g, g x < g y →
          nativeMorseIndex E g x ≤ nativeMorseIndex E g y) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ T : AdaptedSurgeryWindows E g,
          T.field = S.field ∧ T.flow = S.flow ∧
          (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
          let p' : Fin n → criticalPoints E g :=
            fun k => ⟨(p k).val, hcrit.symm ▸ (p k).property⟩
          let B' := B.trans (equalCutHomologyEquiv hsub)
          let γ' := fun k => equalCutSection hlevel (γ k)
          (∀ k, nativeMorseIndex E g (p' k) = 3) ∧
          (∀ k, a < T.toSurgeryWindows.lower (p' k)) ∧
          IsNativeMiddleBasinFamily T hg hga p' (fun k => γ' k) ∧
          (∀ k x, (γ' k x).val = (γ k x).val) ∧
          canonicalMiddleMatrix B' γ' = canonicalMiddleMatrix B γ ∧
          Surjective (canonicalMiddleMatrix B' γ').mulVec := by
  obtain ⟨δ, -, -, -, -, horbit, -⟩ := S.exists_canonical_basin_sphere hf (p j) (hp j) ha
    (γ j) (Hemisphere.point true ⟨0, by simp⟩) (hγ.2.2.2.2 j)
  obtain ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, -, hothers, hindices, hcounts,
      hsub, hlevel, hgerm, hga, T, hfield, hflow, -, habove⟩ :=
    S.exists_common_cut_value_exchange hf hm ha (p i) (p j) hij hconsecutive
      (hp j) (hlower i) δ horbit
  have hneworder := native_index_order_of_equal_index_exchange horder (p i) (p j)
    ((hp i).trans (hp j).symm) hcrit hgp hgq
    (fun x hx hxi hxj => (hothers x hx hxi hxj).self_of_nhds) hindices
  have hheight (k : Fin n) : a < g (p k) := by
    by_cases hki : (p k).val = (p i).val
    · rw [hki, hgp]
      exact (hlower j).trans (S.toSurgeryWindows.lower_lt_value (p j))
    by_cases hkj : (p k).val = (p j).val
    · rw [hkj, hgq]
      exact (hlower i).trans (S.toSurgeryWindows.lower_lt_value (p i))
    rw [(hothers (p k) (p k).property hki hkj).self_of_nhds]
    exact (hlower k).trans (S.toSurgeryWindows.lower_lt_value (p k))
  have hmatrix := canonicalMiddleMatrix_equalCut hsub hlevel B γ
  refine ⟨g, hg, hmg, hcrit, hinj, hgp, hgq,
    (fun z hz hzi hzj => (hothers z hz hzi hzj).self_of_nhds),
    hneworder, hindices, hcounts,
    hsub, hlevel, hga, T, hfield, hflow, hgerm, ?_, ?_, ?_, ?_, hmatrix, ?_⟩
  · intro k
    exact (hindices (p k) (p k).property).trans (hp k)
  · intro k
    exact habove ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hheight k)
  · exact nativeMiddleBasinFamily_equalCut S T hf hg ha hga hcrit hlevel hflow p γ hγ
  · intro k x
    rfl
  · rw [hmatrix]
    exact hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
