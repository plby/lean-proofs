import Wikipedia.HopfProblem.DegreeCollapseLabelledFourIntegerSlide

/-!
# Any integer column addition realized between the original protected cuts

Move the selected source to the first four-handle value by actual bounded
exchanges, recover its genuine regular lower band and three/four prefix,
then perform the integer slide with the original labels. Both outer
function germs and the native data needed to repeat the operation survive.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalFourMatrix

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_bounded_four_column_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (m : criticalPoints E f)
    (hprefix : ∀ z : criticalPoints E f, f z < b → z = m ∨
      nativeMorseIndex E f z = 3 ∨ nativeMorseIndex E f z = 4)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hvalues : ∀ j, a < f (p j) ∧ f (p j) < b)
    (hcomplete : ∀ z : criticalPoints E f, a < f z → f z < b → ∃ j, p j = z)
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(S₃, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalFourMatrix B γ).mulVec)
    (q i : Fin n) (hqi : q ≠ i) (k : ℤ) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        InjOn g (criticalPoints E g) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ d, nativeMorseCount E g d = nativeMorseCount E f d) ∧
        (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g =ᶠ[𝓝 z] f) ∧
        (∀ z : criticalPoints E g, g z < b →
          z = ⟨m.val, hcrit.symm ▸ m.property⟩ ∨
          nativeMorseIndex E g z = 3 ∨ nativeMorseIndex E g z = 4) ∧
        (∀ j, j ≠ q → g (p q) < g (p j)) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        (∀ y, g y < b ↔ f y < b) ∧ (∀ y, g y = b ↔ f y = b) ∧
        (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧ (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ _hgb : ∀ y, g y = b → y ∉ criticalPoints E g,
        ∃ T : AdaptedSurgeryWindows E g,
          (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
          let p' : Fin n → criticalPoints E g :=
            fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
          let B' := B.trans (equalFourCutHomologyEquiv hsub)
          (∀ j, nativeMorseIndex E g (p' j) = 4) ∧
          (∀ z : criticalPoints E g, a < g z → g z < b → ∃ j, p' j = z) ∧
          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
          (∀ j, T.toSurgeryWindows.upper (p' j) < b) ∧
          ∃ Γ : Fin n → C(S₃, {y : M // g y = a}),
            IsNativeFourBasinFamily T hg hga p' (fun j => Γ j) ∧
            (∀ j, j ≠ i → Γ j = equalFourCutSection hlevel (γ j)) ∧
            canonicalFourMatrix (M := M) (f := g) (a := a) (r := r) (n := n) B' Γ =
              canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B γ *
                Matrix.transvection q i k ∧
            Surjective (canonicalFourMatrix B' Γ).mulVec ∧
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
    obtain ⟨g, hg, hmg, hcrit, hinjg, hindices, hcounts, houtside, hfirst,
        hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
        T, hfield, hflow, hpg, hgcomplete, hglower, hgupper, hfamily, -, hmatrix, hgsurj⟩ :=
      S.exists_bounded_first_four_pivot hf hm ha hb p hp hvalues hcomplete B γ hγ hsurj q
    let pg : Fin (n + 1) → criticalPoints E g :=
      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let mg : criticalPoints E g := ⟨m.val, hcrit.symm ▸ m.property⟩
    let Bg := B.trans (equalFourCutHomologyEquiv hsub)
    let γg := fun j => equalFourCutSection hlevel (γ j)
    have hgprefix := three_four_cut_prefix_of_preserved_indices
      hcrit hindices hstrict m hprefix
    have hgqb : g (pg q) < b := (T.toSurgeryWindows.value_lt_upper (pg q)).trans (hgupper q)
    have hband := SurgeryWindows.regular_before_first_bounded_pivot
      T.toSurgeryWindows hga pg hgcomplete q hgqb hfirst
    have hnativeprefix := SurgeryWindows.three_four_prefix_of_bounded_indices
      T.toSurgeryWindows hg mg hgprefix (pg q) hgqb
    obtain ⟨U, -, uradii, ugerms, ulower, Γ, hΓ, uother, -, umatrix, usurj, ukeep⟩ :=
      T.exists_labelled_four_integer_slide hg hmg hdim hga pg hpg hglower Bg γg
        hfamily hgsurj q i hqi hnativeprefix hfirst hband k
    refine ⟨g, hg, hmg, hcrit, hinjg, hindices, hcounts, houtside, hgprefix, hfirst,
      hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
      U, ?_, hpg, hgcomplete, ulower, ?_, Γ, hΓ, uother, ?_, usurj, ?_⟩
    · intro z hz
      filter_upwards [ugerms z (hcrit.symm ▸ hz)] with y hy
      exact hy.trans (congrFun hfield y)
    · intro j
      exact (upper_window_le_of_radius_le T.toSurgeryWindows U.toSurgeryWindows
        (pg j) (uradii _)).trans_lt (hgupper j)
    · exact umatrix.trans (congrArg (fun A => A * Matrix.transvection q i k) hmatrix)
    · intro z hz
      have hheight : g z ≤ g (pg q) := ((hsub z).mpr hz).trans
        ((hglower q).trans (T.toSurgeryWindows.lower_lt_value (pg q))).le
      simpa only [hflow] using ukeep z hheight

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
