import Wikipedia.HopfProblem.DegreeCollapseCommonCutFamilySlide
import Wikipedia.HopfProblem.DegreeCollapseMatrixColumnAlgebra

/-!
# The realized common-cut slide is an actual elementary matrix operation

The old basis is unchanged. Exactly one higher column receives a signed
copy of the retained central column; all others are unchanged. The inverse
transvection proves that surjectivity survives this concrete geometric move.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

-- Keep matching from expanding the homology maps through unknown finite indices.
-- The coefficient calculations below unfold the matrix explicitly.
attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem canonicalMiddleMatrix_family_slide {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (αq : C(S₂, {y : M // f y = a})) (α Γ : Fin n → C(S₂, {y : M // f y = a}))
    (i : Fin n) (k : ℤ) (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass αq) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ) =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
        (Fin.cases αq α) * Matrix.transvection 0 i.succ k := by
  refine @eq_mul_transvection_of_columns r (n + 1)
    (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq α))
    (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ))
    0 i.succ k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_succ, Fin.cases_zero]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    cases j using Fin.cases with
    | zero => simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_zero]
    | succ j =>
      have hj : j ≠ i := fun h => hji (congrArg Fin.succ h)
      simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_succ, hother j hj]

variable [PathConnectedSpace M]

theorem AdaptedSurgeryWindows.exists_geometric_column_addition
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower q) → y ∉ criticalPoints E f)
    {r n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (αq : C(S₂, {y : M // f y = a})) (α : Fin n → C(S₂, {y : M // f y = a}))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j)))
    (hsurj : Surjective (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r)
      (n := n + 1) B (Fin.cases αq α)).mulVec)
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < ε z) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      ∃ Γ : Fin n → C(S₂, {y : M // f y = a}),
        IsNativeMiddleBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
          canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
            (Fin.cases αq Γ) =
            canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
              (Fin.cases αq α) * Matrix.transvection 0 i.succ k ∧
          Surjective (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r)
            (n := n + 1) B (Fin.cases αq Γ)).mulVec := by
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, ⟨k, hk, hclass⟩, -⟩ :=
    S.exists_common_cut_family_slide hf hm hdim horder q hq ha hal hband p i hp hhigh
      αq α hfamily ε hε
  have hmatrix := canonicalMiddleMatrix_family_slide (f := f) (a := a) B αq α Γ i k hother hclass
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, k, hk, hmatrix, ?_⟩
  rw [hmatrix]
  exact mul_transvection_surjective _ 0 i.succ (Fin.succ_ne_zero i).symm k hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
