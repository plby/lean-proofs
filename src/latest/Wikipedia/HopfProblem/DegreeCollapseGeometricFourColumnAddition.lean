import Wikipedia.HopfProblem.DegreeCollapseCommonCutFourFamilySlide
import Wikipedia.HopfProblem.DegreeCollapseFourSectionSpanning
import Wikipedia.HopfProblem.DegreeCollapseMatrixColumnAlgebra

/-!
# A prescribed elementary column addition on the actual native four-handle family

Keep the original common cut and its integral basis. Exactly the chosen
higher column receives the requested signed original central column. The
constructed complete flow retains the whole labelled basin family and all
lower critical basins. Only the actual prefix is constrained in index.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalFourMatrix

local notation "S₃" => Hemisphere.Sphere 3

section Matrix

variable {M : Type} [TopologicalSpace M] {f : M → ℝ}

theorem canonicalFourMatrix_family_slide {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (αq : C(S₃, {y : M // f y = a})) (α Γ : Fin n → C(S₃, {y : M // f y = a}))
    (i : Fin n) (k : ℤ) (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : threeSectionClass (Γ i) = threeSectionClass (α i) + k • threeSectionClass αq) :
    canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ) =
      canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
        (Fin.cases αq α) * Matrix.transvection 0 i.succ k := by
  refine @eq_mul_transvection_of_columns r (n + 1)
    (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq α))
    (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ))
    0 i.succ k ?_ ?_
  · intro u
    simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_succ, Fin.cases_zero]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    cases j using Fin.cases with
    | zero => simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_zero]
    | succ j =>
      have hj : j ≠ i := fun h => hji (congrArg Fin.succ h)
      simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_succ, hother j hj]

end Matrix

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_geometric_four_prescribed_column_addition
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
      (n := n + 1) B (Fin.cases αq α)).mulVec)
    (k : ℤ) (hk : k = 1 ∨ k = -1)
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < ε z) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
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
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_four_family_slide hf hm hdim q hq hprefix ha hal hband
      p i hp hhigh αq α hfamily k hk ε hε
  have hmatrix := canonicalFourMatrix_family_slide (f := f) (a := a) B αq α Γ i k hother hclass
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hmatrix, ?_, hkeep⟩
  rw [hmatrix]
  exact mul_transvection_surjective _ 0 i.succ (Fin.succ_ne_zero i).symm k hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
