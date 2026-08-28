import Wikipedia.NoExoticSixSphere.ManifoldLevelNormalForm
import Wikipedia.NoExoticSixSphere.SuperlevelAtlas

/-!
# Constructing superlevel charts from regularity

At zeroes, the regular-level normal form supplies the defining function as
the first coordinate. At positive points, a translated ordinary chart is
restricted to an open neighborhood on which both first coordinates are
positive. Thus no regularity away from the zero set is required.
-/

noncomputable section

open Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere

section Restriction

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

def partialDiffeomorphRestrOpen (Φ : PartialDiffeomorph I J M N ∞)
    (U : Set M) (hU : IsOpen U) : PartialDiffeomorph I J M N ∞ where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left

def translatedLinearDiffeomorph (L : E ≃L[ℝ] F) (c : E) (d : F) : E ≃ₘ[ℝ] F where
  toFun y := L (y - c) + d
  invFun z := L.symm (z - d) + c
  left_inv y := by simp
  right_inv z := by simp
  contMDiff_toFun :=
    ((L.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const).contMDiff
  contMDiff_invFun :=
    ((L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const).contMDiff

end Restriction

variable {B H M K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

omit [FiniteDimensional ℝ B] in
theorem exists_positiveSuperlevelNormalForm {f : M → ℝ} (hf : Continuous f)
    (L : B ≃L[ℝ] ℝ × K) {x : M} (hx : 0 < f x) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, ℝ × K) M (ℝ × K) ∞,
      x ∈ Φ.source ∧ ∀ y ∈ Φ.source, 0 < (Φ y).1 ∧ 0 < f y := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let d := translatedLinearDiffeomorph L (c x) (1, 0)
  let Φ := c.trans d.toPartialDiffeomorph
  have hcx : x ∈ c.source := mem_extChartAt_source x
  have hΦx : x ∈ Φ.source := ⟨hcx, mem_univ _⟩
  have hΦval : Φ x = (1, 0) := by
    change L (c x - c x) + (1, 0) = (1, 0)
    rw [sub_self, map_zero, zero_add]
  let U := (Φ.source ∩ Φ ⁻¹' {z : ℝ × K | 0 < z.1}) ∩ {y : M | 0 < f y}
  have hU : IsOpen U :=
    (Φ.toOpenPartialHomeomorph.isOpen_inter_preimage
      (isOpen_lt continuous_const continuous_fst)).inter (isOpen_lt continuous_const hf)
  refine ⟨partialDiffeomorphRestrOpen Φ U hU, ⟨hΦx, ?_⟩, ?_⟩
  · refine ⟨⟨hΦx, ?_⟩, hx⟩
    change 0 < (Φ x).1
    rw [hΦval]
    exact zero_lt_one
  · intro y hy
    exact ⟨hy.2.1.2, hy.2.2⟩

theorem nonempty_superlevelAtlas {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x))
    (k : ℕ) (hd : finrank ℝ B = 1 + k) :
    Nonempty (SuperlevelAtlas (K := EuclideanSpace ℝ (Fin k)) I f) := by
  let L : B ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin k) :=
    (LinearEquiv.ofFinrankEq B (ℝ × EuclideanSpace ℝ (Fin k)) (by
      simpa only [finrank_prod, finrank_self, finrank_euclideanSpace_fin] using hd)
      ).toContinuousLinearEquiv
  have hex (x : {x : M // 0 ≤ f x}) :
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin k))
          M (ℝ × EuclideanSpace ℝ (Fin k)) ∞,
        x.val ∈ Φ.source ∧
        (∀ y ∈ Φ.source, 0 ≤ (Φ y).1 ↔ 0 ≤ f y) ∧
        (∀ y ∈ Φ.source, (Φ y).1 = 0 ↔ f y = 0) := by
    by_cases hx : f x.val = 0
    · obtain ⟨Φ, hΦx, _, hfirst, _⟩ := exists_manifoldLevelNormalForm
        isOpen_univ (mem_univ x.val) hf.contMDiffOn (hreg x.val hx) k (by
          simpa only [finrank_self] using hd)
      exact ⟨Φ, hΦx, fun y hy ↦ by rw [hfirst y hy],
        fun y hy ↦ by rw [hfirst y hy]⟩
    · obtain ⟨Φ, hΦx, hpos⟩ := exists_positiveSuperlevelNormalForm (I := I) hf.continuous L
        (lt_of_le_of_ne x.property (Ne.symm hx))
      refine ⟨Φ, hΦx, ?_, ?_⟩
      · intro y hy
        exact iff_of_true (hpos y hy).1.le (hpos y hy).2.le
      · intro y hy
        exact iff_of_false (ne_of_gt (hpos y hy).1) (ne_of_gt (hpos y hy).2)
  choose Φ hsource hsign hzero using hex
  exact ⟨⟨Φ, hsource, hsign, hzero⟩⟩

end NoExoticSixSphere
