import Wikipedia.HopfProblem.DegreeCollapseBoundedFourColumnAddition

/-!
# Exact finite column sequences on the original bounded four-handle family

Compose actual pivot exchanges and integer slides in the prescribed order.
Both literal cut identifications compose, and the integral basis is always
the transport of the original one. Both outer function germs, every
unmentioned source map, and all lower basin orbit sets remain protected.
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

theorem AdaptedSurgeryWindows.exists_bounded_four_column_sequence
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
    (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        InjOn g (criticalPoints E g) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ d, nativeMorseCount E g d = nativeMorseCount E f d) ∧
        (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g =ᶠ[𝓝 z] f) ∧
        (∀ z : criticalPoints E g, g z < b →
          z = ⟨m.val, hcrit.symm ▸ m.property⟩ ∨
          nativeMorseIndex E g z = 3 ∨ nativeMorseIndex E g z = 4) ∧
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
            (∀ j, (∀ op ∈ ops, op.2.1 ≠ j) → Γ j = equalFourCutSection hlevel (γ j)) ∧
            canonicalFourMatrix (M := M) (f := g) (a := a) (r := r) (n := n) B' Γ =
              canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B γ *
                (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod ∧
            Surjective (canonicalFourMatrix B' Γ).mulVec ∧
            ∀ z : M, f z ≤ a →
              (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
                Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
              (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
                range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
              ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
                Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro _hvalid
    obtain ⟨W, hfield, hflow, _, _, _, haboveA, hbelowB, _⟩ :=
      S.exists_same_flow_windows_avoiding_two_levels hf hm ha hb
    have hB : B.trans (equalFourCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl)) = B := by
      rw [equalFourCutHomologyEquiv_refl, LinearEquiv.trans_refl]
    have hfamily : IsNativeFourBasinFamily W hf ha p (fun j => γ j) :=
      nativeFourBasinFamily_equalCut S W hf hf ha ha rfl (fun _ => Iff.rfl) hflow p γ hγ
    refine ⟨f, hf, hm, rfl, S.distinct, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => Filter.EventuallyEq.rfl, hprefix,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
      fun _ _ => Filter.EventuallyEq.rfl, fun _ _ => Filter.EventuallyEq.rfl,
      ha, hb, W, ?_, hp, hcomplete,
      fun j => haboveA (p j) (hvalues j).1, fun j => hbelowB (p j) (hvalues j).2,
      γ, hfamily, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · rw [hB]
      simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
    · rw [hB]
      exact hsurj
    · intro z hz
      rw [hflow]
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 :=
      fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop : op.1 ≠ op.2.1 :=
      hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    obtain ⟨g, hg, hmg, hcrit, hinjg, hindices, hcounts, houtside, hgprefix,
      hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
      T, hgerms, hpg, hgcomplete, hglower, hgupper,
      Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ := ih hprev
    let pg : Fin n → criticalPoints E g :=
      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let mg : criticalPoints E g := ⟨m.val, hcrit.symm ▸ m.property⟩
    let Bg := B.trans (equalFourCutHomologyEquiv hsub)
    have hgvalues (j : Fin n) : a < g (pg j) ∧ g (pg j) < b :=
      ⟨(hglower j).trans (T.toSurgeryWindows.lower_lt_value (pg j)),
        (T.toSurgeryWindows.value_lt_upper (pg j)).trans (hgupper j)⟩
    obtain ⟨u, hu, hmu, hcu, hinju, huindices, hucounts, huoutside, huprefix, -, husub,
      hulevel, hustrict, hulevelB, hulowgerm, huuppergerm, hua, hub,
      U, hugerms, hpu, hucomplete, hulower, huupper, Δ, hΔ, huother, humatrix, husurj, hukeep⟩ :=
      T.exists_bounded_four_column_addition hg hmg hdim hga hgb mg hgprefix pg hpg
        hgvalues hgcomplete Bg Γ hΓ hgsurj op.1 op.2.1 hop op.2.2
    let hsub' : ∀ y, u y ≤ a ↔ f y ≤ a := fun y => (husub y).trans (hsub y)
    let hlevel' : ∀ y, u y = a ↔ f y = a := fun y => (hulevel y).trans (hlevel y)
    have hB : Bg.trans (equalFourCutHomologyEquiv husub) =
        B.trans (equalFourCutHomologyEquiv hsub') := by
      change (B.trans (equalFourCutHomologyEquiv hsub)).trans (equalFourCutHomologyEquiv husub) = _
      rw [LinearEquiv.trans_assoc, equalFourCutHomologyEquiv_trans]
    refine ⟨u, hu, hmu, hcu.trans hcrit, hinju,
      (fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)),
      (fun d => (hucounts d).trans (hcounts d)),
      (fun z hz hzo => (huoutside z (hcrit.symm ▸ hz) hzo).trans (houtside z hz hzo)),
      huprefix, hsub', hlevel', fun y => (hustrict y).trans (hstrict y),
      fun y => (hulevelB y).trans (hlevelB y), ?_, ?_, hua, hub,
      U, ?_, hpu, hucomplete, hulower, huupper, Δ, hΔ, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact (hulowgerm y ((hsub y).mpr hy)).trans (hlowgerm y hy)
    · intro y hy
      have hgy : b ≤ g y := le_of_not_gt (fun h => hy.not_gt ((hstrict y).mp h))
      exact (huuppergerm y hgy).trans (huppergerm y hy)
    · intro z hz
      filter_upwards [hugerms z (hcrit.symm ▸ hz), hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · intro j hj
      have hlast : j ≠ op.2.1 := fun heq =>
        hj op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op))) heq.symm
      have hbefore : ∀ e ∈ ops, e.2.1 ≠ j :=
        fun e he => hj e (List.mem_append.mpr (Or.inl he))
      rw [huother j hlast, hother j hbefore]
      exact equalFourCutSection_trans hlevel hulevel (γ j)
    · rw [← hB, humatrix, hmatrix, Matrix.mul_assoc]
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    · rw [← hB]
      exact husurj
    · intro z hz
      have hUT := hukeep z ((hsub z).mpr hz)
      have hTS := hkeep z hz
      exact ⟨fun x => (hUT.1 x).trans (hTS.1 x),
        fun x hx => (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx),
        fun v => (hUT.2.2 v).trans (hTS.2.2 v)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
