import Wikipedia.HopfProblem.DegreeCollapseLabelledIntegerSlide

/-!
# Every labelled integer column addition has an actual native realization

First move the selected source critical value below the other middle
values, retaining the common cut and original sphere parameters. Recover
the actual regular band, perform the integer slide, and restore the
original labels. All data required to repeat this operation are retained.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_arbitrary_column_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hcut : ∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hcomplete : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec)
    (q i : Fin n) (hqi : q ≠ i) (k : ℤ) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        (∀ x y : criticalPoints E g, g x < g y →
          nativeMorseIndex E g x ≤ nativeMorseIndex E g y) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ d, nativeMorseCount E g d = nativeMorseCount E f d) ∧
        (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z) ∧
        (∀ z : criticalPoints E g, nativeMorseIndex E g z < 3 → g z < a) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ T : AdaptedSurgeryWindows E g,
          (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
          (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
          let p' : Fin n → criticalPoints E g :=
            fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
          let B' := B.trans (equalCutHomologyEquiv hsub)
          (∀ j, nativeMorseIndex E g (p' j) = 3) ∧
          (∀ z : criticalPoints E g, nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
          ∃ Γ : Fin n → C(S₂, {y : M // g y = a}),
            IsNativeMiddleBasinFamily T hg hga p' (fun j => Γ j) ∧
            (∀ j, j ≠ i → Γ j = equalCutSection hlevel (γ j)) ∧
            canonicalMiddleMatrix (M := M) (f := g) (a := a) (r := r) (n := n) B' Γ =
              canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B γ *
                Matrix.transvection q i k ∧
            Surjective (canonicalMiddleMatrix B' Γ).mulVec ∧
            ∀ z : M, f z ≤ a →
              (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
                Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
              (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
                range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
              ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
                Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ n =>
    obtain ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hfirst,
        hsub, hlevel, hga, T, hfield, hflow, hgerm, hpg, hglower, hfamily, -, hmatrix, hgsurj⟩ :=
      S.exists_first_middle_pivot hf hm ha horder p hp hcomplete hlower B γ hγ hsurj q
    let pg : Fin (n + 1) → criticalPoints E g :=
      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (equalCutHomologyEquiv hsub)
    let γg := fun j => equalCutSection hlevel (γ j)
    have hgcut := low_index_cut_of_preserved_other_values hcrit hindices p hp houtside hcut
    have hgcomplete : ∀ z : criticalPoints E g, nativeMorseIndex E g z = 3 → ∃ j, pg j = z := by
      intro z hz
      let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : nativeMorseIndex E f zf = 3 := (hindices z zf.property).symm.trans hz
      obtain ⟨j, hj⟩ := hcomplete zf hzf
      exact ⟨j, Subtype.ext (congrArg (fun z : criticalPoints E f => z.val) hj)⟩
    have hband := SurgeryWindows.regular_before_first_middle_pivot T.toSurgeryWindows
      hgorder hgcut pg hpg hgcomplete q hfirst
    obtain ⟨U, -, -, ugerms, ulower, Γ, hΓ, uother, -, umatrix, usurj, ukeep⟩ :=
      T.exists_labelled_integer_slide hg hmg hdim hgorder hga pg hpg hglower Bg γg
        hfamily hgsurj q i hqi hfirst hband k
    refine ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut,
      hsub, hlevel, hga, U, ?_, hgerm, hpg, hgcomplete, ulower, Γ, hΓ, uother, ?_, usurj, ?_⟩
    · intro z hz
      filter_upwards [ugerms z (hcrit.symm ▸ hz)] with y hy
      exact hy.trans (congrFun hfield y)
    · exact umatrix.trans (congrArg (fun A => A * Matrix.transvection q i k) hmatrix)
    · intro z hz
      have hheight : g z ≤ g (pg q) := ((hsub z).mpr hz).trans
        ((hglower q).trans (T.toSurgeryWindows.lower_lt_value (pg q))).le
      simpa only [hflow] using ukeep z hheight

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
