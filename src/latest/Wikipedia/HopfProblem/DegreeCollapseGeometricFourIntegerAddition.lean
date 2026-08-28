import Wikipedia.HopfProblem.DegreeCollapseIntegerFourColumnSlide
import Wikipedia.HopfProblem.DegreeCollapseGeometricFourColumnAddition

/-!
# Every integer first-column addition on the actual four-handle matrix

The finite geometric iteration has its exact elementary matrix in the
unchanged basis. Its inverse preserves surjectivity. All cut hypotheses,
protected maps, critical chart germs and lower basin orbit sets are retained.
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
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_geometric_four_integer_column_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    (hprefix : ∀ j : Fin S.toSurgeryWindows.count, 0 < j.val →
      f (S.toSurgeryWindows.point j) ≤ f q →
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower q) → y ∉ criticalPoints E f)
    {r n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (αq : C(S₃, {y : M // f y = a})) (α : Fin n → C(S₃, {y : M // f y = a}))
    (hfamily : IsNativeFourBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j)))
    (hsurj : Surjective (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r)
      (n := n + 1) B (Fin.cases αq α)).mulVec) (k : ℤ) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      a < T.toSurgeryWindows.lower q ∧
      (∀ y, f y ∈ Icc a (T.toSurgeryWindows.lower q) → y ∉ criticalPoints E f) ∧
      (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
      ∃ Γ : Fin n → C(S₃, {y : M // f y = a}),
        IsNativeFourBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
          (Fin.cases αq Γ) =
          canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
            (Fin.cases αq α) * Matrix.transvection 0 i.succ k ∧
        Surjective (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r)
          (n := n + 1) B (Fin.cases αq Γ)).mulVec ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  obtain ⟨T, hcharts, hradii, hgerms, hcut, hregular, hseparated,
      Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_integer_four_column_slide hf hm hdim q hq hprefix ha hal hband
      p i hp hhigh αq α hfamily k
  have hmatrix := canonicalFourMatrix_family_slide (f := f) (a := a) B αq α Γ i k hother hclass
  refine ⟨T, hcharts, hradii, hgerms, hcut, hregular, hseparated,
    Γ, hΓ, hother, hmatrix, ?_, hkeep⟩
  rw [hmatrix]
  exact mul_transvection_surjective _ 0 i.succ (Fin.succ_ne_zero i).symm k hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
