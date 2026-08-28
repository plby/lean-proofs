import Wikipedia.SmoothSixDPoincare.NonzeroFieldExtension

/-!
# Extend and complete one prescribed normal column in rank three

A linear map from a real one-dimensional space is injective precisely when
it is nonzero. The space of such maps has the dimension of the target normal
model. Relative nonzero-field extension therefore supplies the column in rank
three, and smooth orthogonal range transport constructs its complementary
two-frame without changing the prescribed column germs.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {A F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A nonzero linear map from a one-dimensional real space is injective. -/
theorem injective_iff_ne_zero_of_finrank_one (hA : Module.finrank ℝ A = 1)
    (L : A →L[ℝ] F) : Injective L ↔ L ≠ 0 := by
  constructor
  · intro hi hzero
    let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply hi
    rw [hzero]
    rfl
  · intro hne
    have hr : L.range ≠ ⊥ := by
      intro hbot
      have hz : L.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
      apply hne
      ext x
      exact congrArg (fun f : A →ₗ[ℝ] F => f x) hz
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    have hpos : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr hr
    have hk : Module.finrank ℝ L.ker = 0 := by
      rw [hA] at hrank
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

omit [FiniteDimensional ℝ F] in
/-- The parameter space for one normal column has the dimension of the normal model. -/
theorem finrank_one_column (hA : Module.finrank ℝ A = 1) :
    Module.finrank ℝ (A →L[ℝ] F) = Module.finrank ℝ F := by
  rw [← (LinearMap.toContinuousLinearMap : (A →ₗ[ℝ] F) ≃ₗ[ℝ] (A →L[ℝ] F)).finrank_eq,
    Module.finrank_linearMap, hA, one_mul]

/-- Extend an actual local one-column field across the planar compact region while preserving
all its prescribed germs, in every normal dimension at least three. -/
theorem exists_one_column_extension_of_local_field (hA : Module.finrank ℝ A = 1)
    {L : Plane → (A →L[ℝ] F)} {U C K : Set Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hK : IsCompact K) (hi : ∀ x ∈ K ∩ C, Injective (L x))
    (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ L' : Plane → (A →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∀ x ∈ K, Injective (L' x) := by
  have hne : ∀ x ∈ K ∩ C, L x ≠ 0 :=
    fun x hx => (injective_iff_ne_zero_of_finrank_one hA (L x)).mp (hi x hx)
  have hdim' : 3 ≤ Module.finrank ℝ (A →L[ℝ] F) := by
    rwa [finrank_one_column hA]
  obtain ⟨L', hL', heq, hne'⟩ :=
    exists_nonzero_extension_of_local_field hU hL hC hCU hK hne hdim'
  exact ⟨L', hL', heq, fun x hx =>
    (injective_iff_ne_zero_of_finrank_one hA (L' x)).mpr (hne' x hx)⟩

end Wikipedia.SmoothSixDPoincare.FrameField

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {A F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Retain the prescribed one-column germs and construct the complementary two-frame near
the whole compact star-convex disk in a three-dimensional normal model. -/
theorem exists_completed_one_column_frame (hA : Module.finrank ℝ A = 1)
    {L : Plane → (A →L[ℝ] F)} {U C K : Set Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : Plane) K) (h0 : (0 : Plane) ∈ K)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) (hdim : Module.finrank ℝ F = 3) :
    ∃ L' : Plane → (A →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∃ V : Set Plane, IsOpen V ∧ K ⊆ V ∧
        ∃ B : Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
          ContDiffOn ℝ ∞ B V ∧
          (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
          ∀ x ∈ V, Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_one_column_extension_of_local_field hA hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ A + 2 = Module.finrank ℝ F := by rw [hA, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

end Wikipedia.SmoothSixDPoincare.FrameField
