import Wikipedia.HopfProblem.DegreeCollapseArbitraryColumnAddition
import Wikipedia.HopfProblem.DegreeCollapseEqualCutComposition

/-!
# Prescribed finite sequences of arbitrary labelled integer column additions

Each step uses actual native pivot rearrangement and a geometric slide.
Literal cut identifications compose, retaining a single transport from the
original homology basis. The matrix is exactly the requested ordered product.
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

theorem AdaptedSurgeryWindows.exists_arbitrary_column_sequence
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
    (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
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
            (∀ j, (∀ op ∈ ops, op.2.1 ≠ j) → Γ j = equalCutSection hlevel (γ j)) ∧
            canonicalMiddleMatrix (M := M) (f := g) (a := a) (r := r) (n := n) B' Γ =
              canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B γ *
                (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod ∧
            Surjective (canonicalMiddleMatrix B' Γ).mulVec ∧
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
    intro hvalid
    have hB : B.trans (equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl)) = B := by
      rw [equalCutHomologyEquiv_refl, LinearEquiv.trans_refl]
    refine ⟨f, hf, hm, rfl, horder, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, hcut, fun _ => Iff.rfl, fun _ => Iff.rfl, ha, S,
      ?_, fun _ _ => Filter.EventuallyEq.rfl, hp, hcomplete, hlower,
      γ, hγ, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · rw [hB]
      simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
    · rw [hB]
      exact hsurj
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 :=
      fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop : op.1 ≠ op.2.1 :=
      hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    obtain ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut,
      hsub, hlevel, hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower,
      Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ := ih hprev
    let pg : Fin n → criticalPoints E g :=
      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (equalCutHomologyEquiv hsub)
    obtain ⟨u, hu, hmu, hcu, huorder, huindices, hucounts, huoutside, hucut,
      husub, hulevel, hua, U, hugerms, hufgerms, hpu, hucomplete, hulower,
      Δ, hΔ, huother, humatrix, husurj, hukeep⟩ :=
      T.exists_arbitrary_column_addition hg hmg hdim hgorder hga hgcut
        pg hpg hgcomplete hglower Bg Γ hΓ hgsurj op.1 op.2.1 hop op.2.2
    let hsub' : ∀ y, u y ≤ a ↔ f y ≤ a := fun y => (husub y).trans (hsub y)
    let hlevel' : ∀ y, u y = a ↔ f y = a := fun y => (hulevel y).trans (hlevel y)
    have hB : Bg.trans (equalCutHomologyEquiv husub) = B.trans (equalCutHomologyEquiv hsub') := by
      change (B.trans (equalCutHomologyEquiv hsub)).trans (equalCutHomologyEquiv husub) = _
      rw [LinearEquiv.trans_assoc, equalCutHomologyEquiv_trans]
    refine ⟨u, hu, hmu, hcu.trans hcrit, huorder,
      (fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)),
      (fun d => (hucounts d).trans (hcounts d)),
      (fun z hz hzo => (huoutside z (hcrit.symm ▸ hz) hzo).trans (houtside z hz hzo)),
      hucut, hsub', hlevel', hua, U, ?_, ?_, hpu, hucomplete, hulower,
      Δ, hΔ, ?_, ?_, ?_, ?_⟩
    · intro z hz
      filter_upwards [hugerms z (hcrit.symm ▸ hz), hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · intro y hy
      exact (hufgerms y ((hsub y).mpr hy)).trans (hfgerms y hy)
    · intro j hj
      have hlast : j ≠ op.2.1 := fun heq =>
        hj op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op))) heq.symm
      have hbefore : ∀ e ∈ ops, e.2.1 ≠ j :=
        fun e he => hj e (List.mem_append.mpr (Or.inl he))
      rw [huother j hlast, hother j hbefore]
      exact equalCutSection_trans hlevel hulevel (γ j)
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
