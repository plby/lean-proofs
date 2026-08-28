import Wikipedia.SmoothSixDPoincare.ReferenceSphereChartInversion

/-!
# A native smooth chart parametrizing the complementary reference disk

The formula uses only a linear scaling, the original full-source chart,
and the antipodal diffeomorphism. Its source is all of Euclidean space.
Away from zero it is exactly the original chart after unit inversion.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereCoordinates

def antipodal (n : ℕ) :
    Diffeomorph (𝓡 n) (𝓡 n) (Hemisphere.Sphere n) (Hemisphere.Sphere n) ∞ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact {
    toFun := Neg.neg
    invFun := Neg.neg
    left_inv := neg_neg
    right_inv := neg_neg
    contMDiff_toFun := contMDiff_neg_sphere
    contMDiff_invFun := contMDiff_neg_sphere }

def complementScaling (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞ where
  toFun := fun w => (-4 : ℝ) • w
  invFun := fun w => (-1 / 4 : ℝ) • w
  left_inv w := by simp only [smul_smul]; norm_num
  right_inv w := by simp only [smul_smul]; norm_num
  contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (n : ℕ) (hdim : Module.finrank ℝ F = n)

def referenceComplementChart :
    PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F (Hemisphere.Sphere n) ∞ :=
  ((complementScaling F).toPartialDiffeomorph.trans (referenceChart F n hdim)).trans
    (antipodal n).toPartialDiffeomorph

theorem referenceComplementChart_apply (w : F) :
    referenceComplementChart F n hdim w = -referenceChart F n hdim ((-4 : ℝ) • w) := rfl

theorem referenceComplementChart_source : (referenceComplementChart F n hdim).source = univ := by
  ext w
  change ((w ∈ (univ : Set F) ∧ (-4 : ℝ) • w ∈ (referenceChart F n hdim).source) ∧
    referenceChart F n hdim ((-4 : ℝ) • w) ∈ (univ : Set (Hemisphere.Sphere n))) ↔ w ∈ univ
  rw [referenceChart_source]
  simp only [mem_univ, and_self]

theorem referenceComplementChart_target :
    (referenceComplementChart F n hdim).target = {referencePole n}ᶜ := by
  ext y
  change (y ∈ (univ : Set (Hemisphere.Sphere n)) ∧
    (-y ∈ (referenceChart F n hdim).target ∧
      (referenceChart F n hdim).symm (-y) ∈ (univ : Set F))) ↔ y ∈ {referencePole n}ᶜ
  rw [referenceChart_target]
  simp only [mem_univ, and_true, true_and, mem_compl_iff, mem_singleton_iff, neg_inj]

theorem referenceComplementChart_zero : referenceComplementChart F n hdim (0 : F) =
    -referencePole n := by
  rw [referenceComplementChart_apply, smul_zero, referenceChart_zero]

theorem referenceComplementChart_inversion {w : F} (hw : w ≠ 0) :
    referenceComplementChart F n hdim w = referenceChart F n hdim ((‖w‖ ^ 2)⁻¹ • w) :=
  (referenceChart_inversion F n hdim hw).symm

theorem referenceComplementChart_boundary {w : F} (hw : ‖w‖ = 1) :
    referenceComplementChart F n hdim w = referenceChart F n hdim w := by
  have hw₀ : w ≠ 0 := norm_ne_zero_iff.mp (hw ▸ one_ne_zero)
  rw [referenceComplementChart_inversion F n hdim hw₀, hw, one_pow, inv_one, one_smul]

theorem referenceComplementChart_contMDiff :
    ContMDiff 𝓘(ℝ, F) (𝓡 n) ∞ (referenceComplementChart F n hdim) := by
  rw [← contMDiffOn_univ, ← referenceComplementChart_source F n hdim]
  exact (referenceComplementChart F n hdim).contMDiffOn_toFun

end Wikipedia.SmoothSixDPoincare.SphereCoordinates
