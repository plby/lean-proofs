import Wikipedia.HopfProblem.DegreeCollapseBoundedFourColumnSequence
import Wikipedia.HopfProblem.DegreeCollapseFunctionalRows

/-!
# An actual four-handle sphere with unit primitive collapse coordinate

Euclidean reduction of the primitive functional row produces a finite
list of integer column additions. Realize that exact list between the
original protected cuts. The unit is evaluated on the resulting actual
sphere through the literal identity of the common sublevels; it is not
an arbitrarily chosen homology representative.
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

theorem AdaptedSurgeryWindows.exists_bounded_four_functional_unit
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
    (L : SingularHomology {y : M // f y ≤ a} 3 →ₗ[ℤ] ℤ) (hL : Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ), (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
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
            (∃ i : Fin n,
              L ((equalFourCutHomologyEquiv hsub).symm (threeSectionClass (Γ i))) = 1 ∨
              L ((equalFourCutHomologyEquiv hsub).symm (threeSectionClass (Γ i))) = -1) ∧
            ∀ z : M, f z ≤ a →
              (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
                Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
              (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
                range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
              ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
                Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  let A : Matrix (Fin 1) (Fin n) ℤ := fun _ j => L (threeSectionClass (γ j))
  have hsurj' : Surjective (classCoordinateMatrix B (fun j => threeSectionClass (γ j))).mulVec := by
    simpa only [canonicalFourMatrix] using hsurj
  have hA : Surjective A.mulVec :=
    functional_class_row_surjective B (fun j => threeSectionClass (γ j)) hsurj' L hL
  obtain ⟨ops, hvalid, i, hi⟩ := primitive_row_has_unit_after_column_additions A hA
  obtain ⟨g, hg, hmg, hcrit, hinjg, hindices, hcounts, houtside, hgprefix,
    hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
    T, hgerms, hpg, hgcomplete, hglower, hgupper, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
    S.exists_bounded_four_column_sequence hf hm hdim ha hb m hprefix p hp hvalues hcomplete
      B γ hγ hsurj ops hvalid
  have hcoord : classCoordinateMatrix (B.trans (equalFourCutHomologyEquiv hsub))
      (fun j => threeSectionClass (Γ j)) =
      classCoordinateMatrix B (fun j => threeSectionClass (γ j)) *
        (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod := by
    simpa only [canonicalFourMatrix] using hmatrix
  have hrows := functional_rows_of_matrix_product B (equalFourCutHomologyEquiv hsub)
    (fun j => threeSectionClass (γ j)) (fun j => threeSectionClass (Γ j)) _ hcoord L
  have hentry := congrFun (congrFun hrows 0) i
  refine ⟨ops, hvalid, g, hg, hmg, hcrit, hinjg, hindices, hcounts, houtside, hgprefix,
    hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
    T, hgerms, hpg, hgcomplete, hglower, hgupper, Γ, hΓ, hother, hmatrix, hgsurj, ⟨i, ?_⟩, hkeep⟩
  exact hi.elim (fun h => Or.inl (hentry.trans h)) (fun h => Or.inr (hentry.trans h))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
