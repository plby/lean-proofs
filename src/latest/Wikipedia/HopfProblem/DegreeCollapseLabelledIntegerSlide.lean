import Wikipedia.HopfProblem.DegreeCollapseMiddlePivotTools

/-!
# Integer slides with arbitrary original labels at a first pivot

The source label need not be zero. Reindex only to apply the actual
first-pivot construction, then restore every original label and parameter.
The resulting full matrix has precisely the requested elementary factor.
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

theorem AdaptedSurgeryWindows.exists_labelled_integer_slide
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {r n : ℕ} (p : Fin (n + 1) → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin (n + 1) → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec)
    (q i : Fin (n + 1)) (hqi : q ≠ i)
    (hfirst : ∀ j, j ≠ q → f (p q) < f (p j))
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower (p q)) →
      y ∉ criticalPoints E f) (k : ℤ) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      (∀ j, a < T.toSurgeryWindows.lower (p j)) ∧
      ∃ Γ : Fin (n + 1) → C(S₂, {y : M // f y = a}),
        IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) ∧
        (∀ j, j ≠ i → Γ j = γ j) ∧
        middleSectionClass (Γ i) = middleSectionClass (γ i) + k • middleSectionClass (γ q) ∧
        canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B Γ =
          canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B γ *
            Matrix.transvection q i k ∧
        Surjective (canonicalMiddleMatrix B Γ).mulVec ∧
        ∀ z : M, f z ≤ f (p q) →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  classical
  let e := Equiv.swap (0 : Fin (n + 1)) q
  have he0 : e 0 = q := Equiv.swap_apply_left _ _
  have heq : e q = 0 := Equiv.swap_apply_right _ _
  have hee (j : Fin (n + 1)) : e (e j) = j := Equiv.swap_apply_self _ _ _
  have hne : e i ≠ 0 := fun hi => hqi (e.injective (heq.trans hi.symm))
  obtain ⟨l, hl⟩ := Fin.exists_succ_eq_of_ne_zero hne
  have hel : e l.succ = i := by rw [hl, hee]
  have hpcases : Fin.cases (p q) (fun j => p (e j.succ)) = p ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hγcases : Fin.cases (γ q) (fun j => γ (e j.succ)) = γ ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hfamily : IsNativeMiddleBasinFamily S hf ha
      (Fin.cases (p q) (fun j => p (e j.succ)))
      (Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x)) := by
    have hmaps : Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x) =
        (fun j x => γ j x) ∘ e := by
      funext j x
      cases j using Fin.cases with
      | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
      | succ j => rfl
    rw [hpcases, hmaps]
    exact nativeMiddleBasinFamily_reindex S hf ha p (fun j => γ j) hγ e e.injective
  have hhigh (j : Fin n) : S.toSurgeryWindows.upper (p q) < f (p (e j.succ)) := by
    have hjq : e j.succ ≠ q := by
      intro hj
      have hzero : j.succ = 0 := e.injective (hj.trans he0.symm)
      exact Fin.succ_ne_zero j hzero
    exact (S.toSurgeryWindows.upper_lt_lower (p q) (p (e j.succ)) (hfirst _ hjq)).trans
      (S.toSurgeryWindows.lower_lt_value _)
  obtain ⟨T, hcharts, hradii, hgerms, -, -, -, Δ, hΔ, hother, hclass, hkeep⟩ :=
    S.exists_integer_column_slide hf hm hdim horder (p q) (hp q) ha (hlower q) hband
      (fun j => p (e j.succ)) l (fun j => hp (e j.succ)) hhigh
      (γ q) (fun j => γ (e j.succ)) hfamily k
  let δ : Fin (n + 1) → C(S₂, {y : M // f y = a}) := Fin.cases (γ q) Δ
  let Γ := δ ∘ e
  have hΓ : IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := by
    have hh := nativeMiddleBasinFamily_reindex T hf ha
      (Fin.cases (p q) (fun j => p (e j.succ)))
      (Fin.cases (fun x => γ q x) (fun j x => Δ j x)) hΔ e e.injective
    have hlabels : (Fin.cases (p q) (fun j => p (e j.succ))) ∘ e = p := by
      rw [hpcases]
      funext j
      exact congrArg p (hee j)
    rw [hlabels] at hh
    have hmaps : (Fin.cases (fun x => γ q x) (fun j x => Δ j x)) ∘ e =
        (fun j x => Γ j x) := by
      funext j x
      change Fin.cases (motive := fun _ : Fin (n + 1) => S₂ → {y : M // f y = a})
        (fun x => γ q x) (fun j x => Δ j x) (e j) x =
        (Fin.cases (motive := fun _ : Fin (n + 1) => C(S₂, {y : M // f y = a}))
          (γ q) Δ (e j)) x
      cases e j using Fin.cases <;> rfl
    rw [hmaps] at hh
    exact hh
  have hΓother (j : Fin (n + 1)) (hji : j ≠ i) : Γ j = γ j := by
    change Fin.cases (γ q) Δ (e j) = γ j
    by_cases hjzero : e j = 0
    · have hjq : j = q := e.injective (hjzero.trans heq.symm)
      rw [hjzero, Fin.cases_zero, hjq]
    · obtain ⟨v, hv⟩ := Fin.exists_succ_eq_of_ne_zero hjzero
      have hvl : v ≠ l := by
        intro hvl
        apply hji
        exact e.injective (hv.symm.trans ((congrArg Fin.succ hvl).trans hl))
      rw [← hv, Fin.cases_succ, hother v hvl]
      exact congrArg γ (by rw [hv, hee])
  have hΓclass : middleSectionClass (Γ i) =
      middleSectionClass (γ i) + k • middleSectionClass (γ q) := by
    change middleSectionClass (Fin.cases (γ q) Δ (e i)) = _
    rw [← hl, Fin.cases_succ]
    simpa only [hel] using hclass
  have hmatrix := canonicalMiddleMatrix_single_class_addition (f := f) (a := a)
    B γ Γ q i k hΓother hΓclass
  refine ⟨T, hcharts, hradii, hgerms, ?_, Γ, hΓ, hΓother, hΓclass, hmatrix, ?_, hkeep⟩
  · intro j
    exact (hlower j).trans_le
      (lower_window_le_of_radius_le S.toSurgeryWindows T.toSurgeryWindows (p j) (hradii _))
  · rw [hmatrix]
    exact mul_transvection_surjective _ q i hqi k hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
