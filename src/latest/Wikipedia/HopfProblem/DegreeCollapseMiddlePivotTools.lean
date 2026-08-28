import Wikipedia.HopfProblem.DegreeCollapseMiddlePivotReordering
import Wikipedia.HopfProblem.DegreeCollapseGeometricIntegerColumnAddition

/-! # Reindex native families and recover the regular band below a first pivot -/

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
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem nativeMiddleBasinFamily_reindex
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n m : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → S₂ → {y : M // f y = a})
    (hγ : IsNativeMiddleBasinFamily S hf ha p γ)
    (e : Fin m → Fin n) (he : Injective e) :
    IsNativeMiddleBasinFamily S hf ha (p ∘ e) (γ ∘ e) := by
  obtain ⟨hs, hi, hd, hpair, hfull⟩ := hγ
  exact ⟨fun j => hs (e j), fun j => hi (e j), fun j => hd (e j),
    fun i j hij => hpair (fun h => hij (he h)), fun j => hfull (e j)⟩

theorem canonicalMiddleMatrix_single_class_addition [Nonempty M] {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (α Γ : Fin n → C(S₂, {y : M // f y = a})) (q i : Fin n) (k : ℤ)
    (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass (α q)) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B Γ =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B α *
        Matrix.transvection q i k := by
  refine eq_mul_transvection_of_columns _ _ q i k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, hother j hji]

theorem SurgeryWindows.regular_before_first_middle_pivot
    (S : SurgeryWindows E f)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    {a : ℝ} (hcut : ∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hcomplete : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (q : Fin n) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j)) :
    ∀ y, f y ∈ Icc a (S.lower (p q)) → y ∉ criticalPoints E f := by
  intro y hy hcrit
  let z : criticalPoints E f := ⟨y, hcrit⟩
  have hlt : f z < f (p q) := hy.2.trans_lt (S.lower_lt_value (p q))
  have hle : nativeMorseIndex E f z ≤ 3 := (horder z (p q) hlt).trans_eq (hp q)
  have heq : nativeMorseIndex E f z = 3 := by
    apply Nat.le_antisymm hle
    by_contra hnot
    exact (hcut z (lt_of_not_ge hnot)).not_ge hy.1
  obtain ⟨j, hj⟩ := hcomplete z heq
  by_cases hjq : j = q
  · exact (ne_of_lt hlt) (congrArg f (congrArg Subtype.val (hj.symm.trans (congrArg p hjq))))
  · have hreverse : f (p q) < f z := by simpa only [hj] using hfirst j hjq
    exact hlt.not_gt hreverse

theorem low_index_cut_of_preserved_other_values {g : M → ℝ} {a : ℝ}
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hindices : ∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (houtside : ∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z)
    (hcut : ∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a) :
    ∀ z : criticalPoints E g, nativeMorseIndex E g z < 3 → g z < a := by
  intro z hz
  let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
  have hidx : nativeMorseIndex E f zf < 3 := by
    rw [← hindices z zf.property]
    exact hz
  have hother : ∀ j, z.val ≠ (p j).val := by
    intro j hj
    have heq : zf = p j := Subtype.ext hj
    rw [heq, hp j] at hidx
    exact (lt_irrefl _ hidx)
  rw [houtside z zf.property hother]
  exact hcut zf hidx

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
