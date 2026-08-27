import ErdosProblems.Erdos587.HooleySeedBody
import ErdosProblems.Erdos587.DenseFiberBlocks

/-! # Turning a lattice seed and disjoint remaining elements into a convex subset-sum body -/

open scoped BigOperators Pointwise

namespace Erdos587.GeneralizedAP

lemma deltaSeedBody_rounding {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) (hR : ∀ i, 2 ≤ R i) :
    ∀ x : Fin d → ℝ, ∃ z : Fin d → ℤ,
      x - intCastVec z ∈ bodyDilate (1 / 4 : ℝ) (deltaSeedBody v R) := by
  apply delta_rounding_of_projected_cube (LinearMap.id : (Fin d → ℤ) →ₗ[ℤ] _)
    Function.surjective_id
  intro e he
  rw [delta_intLinearMapRealExtension_id, LinearMap.id_apply]
  refine ⟨(4 : ℝ) • e, deltaSeedBody_box v R ?_, ?_⟩
  · have hb (i : Fin d) : |4 * e i| ≤ R i := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact (mul_le_mul_of_nonneg_left (he i) (by norm_num)).trans (by linarith [hR i])
    exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩
  · rw [smul_smul]
    norm_num

noncomputable def deltaSeedProgression {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (f : (Fin d → ℤ) →+ ℤ) (c : Fin d → ℤ)
    (R : Fin d → ℝ) (hR : ∀ i, 2 ≤ R i) : ConvexProgression :=
  deltaConvexProgression (f c) f (deltaSeedBody v R)
    (deltaSeedBody_compact v R) (deltaSeedBody_zero v R (fun i => by linarith [hR i]))
    (deltaSeedBody_convex v R) (deltaSeedBody_neg v R)
    (deltaSeedBody_full v R (fun i => by linarith [hR i])) (deltaSeedBody_rounding v R hR)

theorem deltaSeedProgression_carrier_subset {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (f : (Fin d → ℤ) →+ ℤ) (c₀ c : Fin d → ℤ)
    (L R : Fin d → ℝ) (hL : ∀ j, 0 ≤ L j) (hR : ∀ i, 2 ≤ R i)
    (hv : ∀ i j, |(v i j : ℝ)| ≤ L j)
    (hc : ∀ j, |(c j : ℝ) - (∑ i, (v i j : ℝ)) / 2| ≤ (1 / 2 : ℝ))
    (A : Finset ℤ)
    (hseed : ∀ w : Fin d → ℤ, (∀ j, |(w j : ℝ)| ≤ R j + (d : ℝ) * L j + 1 / 2) →
      f (c₀ + w) ∈ A.subsetSum)
    (hinj : Function.Injective (fun i => f (v i)))
    (hdisjoint : Disjoint A (Finset.univ.image (fun i => f (v i)))) :
    (deltaSeedProgression v f (c₀ + c) R hR).carrier ⊆
      ((A ∪ Finset.univ.image (fun i => f (v i))).subsetSum : Set ℤ) := by
  classical
  change (fun y : Fin d → ℤ => f (c₀ + c) + f y) ''
    {y | intCastVec y ∈ deltaSeedBody v R} ⊆ _
  rintro z ⟨y, hy, rfl⟩
  change intCastVec y ∈ deltaSeedBody v R at hy
  have hy' : intCastVec ((c + y) - c) ∈ deltaSeedBody v R := by
    simpa only [add_sub_cancel_left] using hy
  obtain ⟨S, w, hw, heq⟩ :=
    deltaSeedBody_lattice_decomposition_of_center v L R hL hv c (c + y) hc hy'
  have hsum : (∑ i ∈ S, f (v i)) ∈ (Finset.univ.image (fun i => f (v i))).subsetSum := by
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨S.image (fun i => f (v i)), Finset.image_mono _ (Finset.subset_univ S), ?_⟩
    exact Finset.sum_image (fun i _ j _ h => hinj h)
  have heval : f (c₀ + c) + f y = f (c₀ + w) + ∑ i ∈ S, f (v i) := by
    rw [← map_sum, ← map_add, ← map_add]
    congr 1
    calc
      (c₀ + c) + y = c₀ + (c + y) := add_assoc _ _ _
      _ = c₀ + (w + ∑ i ∈ S, v i) := by rw [heq]
      _ = _ := (add_assoc _ _ _).symm
  change f (c₀ + c) + f y ∈ _
  rw [heval]
  exact CFP.subsetSum_add_subset_union hdisjoint
    (Finset.mem_add.mpr ⟨f (c₀ + w), hseed w hw, ∑ i ∈ S, f (v i), hsum, rfl⟩)

theorem deltaSeedProgression_base_mass {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (f : (Fin d → ℤ) →+ ℤ) (c₀ c : Fin d → ℤ)
    (R : Fin d → ℝ) (hR : ∀ i, 2 ≤ R i) (C : ℝ)
    (hseed : (f c₀ : ℝ) ≤ C * ∑ i, (f (v i) : ℝ))
    (hcenter : (f c : ℝ) ≤ (∑ i, (f (v i) : ℝ)) / 2) :
    ((deltaSeedProgression v f (c₀ + c) R hR).base : ℝ) ≤
      (C + 1 / 2) * ∑ i, (f (v i) : ℝ) := by
  change (f (c₀ + c) : ℝ) ≤ _
  rw [map_add, Int.cast_add]
  nlinarith

end Erdos587.GeneralizedAP
