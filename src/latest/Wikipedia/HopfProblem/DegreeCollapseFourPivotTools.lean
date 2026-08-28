import Wikipedia.HopfProblem.DegreeCollapseBoundedFourPivot
import Wikipedia.HopfProblem.DegreeCollapseGeometricFourIntegerAddition

/-!
# Original labels, bounded regular bands, and three/four prefixes

Recover the actual regular band below a first pivot from completeness in
the two-cut band. Convert the intrinsic below-cut index restriction into
the original ordered-window prefix, without imposing any condition on the
untouched upper region. Identity on critical points transports this
restriction through the bounded exchanges.
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

omit [T2Space M] [CompactSpace M] in
theorem nativeFourBasinFamily_reindex
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n m : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → S₃ → {y : M // f y = a})
    (hγ : IsNativeFourBasinFamily S hf ha p γ)
    (e : Fin m → Fin n) (he : Injective e) :
    IsNativeFourBasinFamily S hf ha (p ∘ e) (γ ∘ e) := by
  obtain ⟨hs, hi, hd, hpair, hfull⟩ := hγ
  exact ⟨fun j => hs (e j), fun j => hi (e j), fun j => hd (e j),
    fun i j hij => hpair (fun h => hij (he h)), fun j => hfull (e j)⟩

omit [T2Space M] [CompactSpace M] in
theorem canonicalFourMatrix_single_class_addition {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (α Γ : Fin n → C(S₃, {y : M // f y = a})) (q i : Fin n) (k : ℤ)
    (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : threeSectionClass (Γ i) = threeSectionClass (α i) + k • threeSectionClass (α q)) :
    canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B Γ =
      canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B α *
        Matrix.transvection q i k := by
  refine eq_mul_transvection_of_columns _ _ q i k ?_ ?_
  · intro u
    simp only [canonicalFourMatrix, classCoordinateMatrix]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    simp only [canonicalFourMatrix, classCoordinateMatrix, hother j hji]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem SurgeryWindows.regular_before_first_bounded_pivot
    (S : SurgeryWindows E f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hcomplete : ∀ z : criticalPoints E f, a < f z → f z < b → ∃ j, p j = z)
    (q : Fin n) (hqb : f (p q) < b)
    (hfirst : ∀ j, j ≠ q → f (p q) < f (p j)) :
    ∀ y, f y ∈ Icc a (S.lower (p q)) → y ∉ criticalPoints E f := by
  intro y hy hcrit
  let z : criticalPoints E f := ⟨y, hcrit⟩
  have hlt : f z < f (p q) := hy.2.trans_lt (S.lower_lt_value (p q))
  have haz : a < f z := lt_of_le_of_ne hy.1 (fun h => ha y h.symm hcrit)
  obtain ⟨j, hj⟩ := hcomplete z haz (hlt.trans hqb)
  by_cases hjq : j = q
  · have he : f (p q) = f z := by simpa only [hjq] using congrArg (fun z => f z.val) hj
    exact hlt.ne he.symm
  · have hreverse : f (p q) < f z := by simpa only [hj] using hfirst j hjq
    exact hlt.not_gt hreverse

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem SurgeryWindows.three_four_prefix_of_bounded_indices
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (m : criticalPoints E f)
    (hprefix : ∀ z : criticalPoints E f, f z < b → z = m ∨
      nativeMorseIndex E f z = 3 ∨ nativeMorseIndex E f z = 4)
    (q : criticalPoints E f) (hqb : f q < b) :
    ∀ j : Fin S.count, 0 < j.val → f (S.point j) ≤ f q →
      Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates = 4 := by
  intro j hj hjq
  have hn : 0 < S.count := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hfirstzero : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hfirstm : S.first hn = m := by
    rcases hprefix (S.first hn) ((S.value_first_le hn q).trans_lt hqb) with h | h | h
    · exact h
    · omega
    · omega
  rcases hprefix (S.point j) (hjq.trans_lt hqb) with h | h | h
  · have he : j.val = 0 := congrArg Fin.val (S.point.injective (h.trans hfirstm.symm))
    omega
  · exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans h)
  · exact Or.inr ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans h)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem three_four_cut_prefix_of_preserved_indices {g : M → ℝ} {b : ℝ}
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hindices : ∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z)
    (hstrict : ∀ y, g y < b ↔ f y < b) (m : criticalPoints E f)
    (hprefix : ∀ z : criticalPoints E f, f z < b → z = m ∨
      nativeMorseIndex E f z = 3 ∨ nativeMorseIndex E f z = 4) :
    ∀ z : criticalPoints E g, g z < b →
      z = ⟨m.val, hcrit.symm ▸ m.property⟩ ∨
      nativeMorseIndex E g z = 3 ∨ nativeMorseIndex E g z = 4 := by
  intro z hz
  let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
  rcases hprefix zf ((hstrict z).mp hz) with he | h3 | h4
  · exact Or.inl (Subtype.ext (congrArg (fun z : criticalPoints E f => z.val) he))
  · exact Or.inr (Or.inl ((hindices z zf.property).trans h3))
  · exact Or.inr (Or.inr ((hindices z zf.property).trans h4))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem upper_window_le_of_radius_le (S T : SurgeryWindows E f)
    (q : criticalPoints E f) (hr : (T.data q).radius ≤ (S.data q).radius) :
    T.upper q ≤ S.upper q := by
  have hs : (T.data q).radius ^ 2 ≤ (S.data q).radius ^ 2 :=
    (sq_le_sq₀ (T.data q).radius_pos.le (S.data q).radius_pos.le).mpr hr
  change f q + (T.data q).radius ^ 2 ≤ f q + (S.data q).radius ^ 2
  linarith only [hs]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
