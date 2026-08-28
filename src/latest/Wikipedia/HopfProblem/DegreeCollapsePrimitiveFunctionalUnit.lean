import Wikipedia.HopfProblem.DegreeCollapseArbitraryColumnSequence
import Wikipedia.HopfProblem.DegreeCollapseFunctionalRows

/-!
# A primitive functional takes a unit on an actual realized attaching sphere

Apply finite Euclidean column reduction to the functional values, then
realize that exact list by native pivot rearrangements and integer slides.
The resulting unit is evaluated on the actual sphere class through the
literal common-sublevel identification, with all iteration data retained.
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

theorem AdaptedSurgeryWindows.exists_primitive_functional_unit
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
    (L : SingularHomology {y : M // f y ≤ a} 2 →ₗ[ℤ] ℤ) (hL : Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ), (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
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
            (∃ i : Fin n,
              L ((equalCutHomologyEquiv hsub).symm (middleSectionClass (Γ i))) = 1 ∨
              L ((equalCutHomologyEquiv hsub).symm (middleSectionClass (Γ i))) = -1) ∧
            ∀ z : M, f z ≤ a →
              (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
                Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
              (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
                range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
              ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
                Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  let A : Matrix (Fin 1) (Fin n) ℤ := fun _ j => L (middleSectionClass (γ j))
  have hsurj' : Surjective (classCoordinateMatrix B (fun j => middleSectionClass (γ j))).mulVec := by
    simpa only [canonicalMiddleMatrix] using hsurj
  have hA : Surjective A.mulVec :=
    functional_class_row_surjective B (fun j => middleSectionClass (γ j)) hsurj' L hL
  obtain ⟨ops, hvalid, i, hi⟩ := primitive_row_has_unit_after_column_additions A hA
  obtain ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut,
    hsub, hlevel, hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower,
    Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
    S.exists_arbitrary_column_sequence hf hm hdim horder ha hcut p hp hcomplete hlower
      B γ hγ hsurj ops hvalid
  have hcoord : classCoordinateMatrix (B.trans (equalCutHomologyEquiv hsub))
      (fun j => middleSectionClass (Γ j)) =
      classCoordinateMatrix B (fun j => middleSectionClass (γ j)) *
        (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod := by
    simpa only [canonicalMiddleMatrix] using hmatrix
  have hrows := functional_rows_of_matrix_product B (equalCutHomologyEquiv hsub)
    (fun j => middleSectionClass (γ j)) (fun j => middleSectionClass (Γ j)) _ hcoord L
  have hentry := congrFun (congrFun hrows 0) i
  refine ⟨ops, hvalid, g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut,
    hsub, hlevel, hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower,
    Γ, hΓ, hother, hmatrix, hgsurj, ⟨i, ?_⟩, hkeep⟩
  exact hi.elim (fun h => Or.inl (hentry.trans h)) (fun h => Or.inr (hentry.trans h))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
