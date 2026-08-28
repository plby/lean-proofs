import Wikipedia.NoExoticSixSphere.RadialTubeShapeHomotopy

/-!
# Independence of the positive radius of a round framed collapse

Two open round tubes with the same core and ordered frame have based
homotopic collapses. The proof shrinks the larger tube by the explicit
radial open-embedding family; no tubular-neighborhood uniqueness theorem
or assumed collapse-choice invariance is used.
-/

noncomputable section

open Function Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.RoundTubeRadiusHomotopy

variable {M K F : Type*} [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace F]
  (j : M → F) (B : M → K →L[ℝ] F)

def tube (r : ℝ) (p : M × K) : F :=
  j p.1 + B p.1 (OpenPartialHomeomorph.univBall (0 : K) r p.2)

def collapseMap (r : ℝ) (hE : IsOpenEmbedding (tube j B r)) : C(OnePoint F, OnePoint K) :=
  ⟨OpenFiberCollapse.collapseOnePoint (tube j B r),
    OpenFiberCollapse.continuous_collapseOnePoint _ hE⟩

theorem exists_based_homotopy_of_le (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hle : r ≤ R)
    (hEr : IsOpenEmbedding (tube j B r)) (hER : IsOpenEmbedding (tube j B R)) :
    ∃ H : (collapseMap j B R hER).Homotopy (collapseMap j B r hEr),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  let L : M → K ≃L[ℝ] K := fun _ ↦ ContinuousLinearEquiv.refl ℝ K
  let s := r / R
  have hs : 0 < s := div_pos hr hR
  have hb : ∀ m v, s * ‖L m v‖ ≤ ‖v‖ := by
    intro m v
    exact mul_le_of_le_one_left (norm_nonneg v) ((div_le_one hR).mpr hle)
  have hc : Continuous (fun p : M × K ↦ L p.1 p.2) := continuous_snd
  have hi : Continuous (fun p : M × K ↦ (L p.1).symm p.2) := continuous_snd
  have hzero : RadialTubeShapeHomotopy.tube L s hs (tube j B R) 0 = tube j B R := by
    funext p
    exact RadialTubeShapeHomotopy.tube_zero L s hs (tube j B R) p
  have hone : RadialTubeShapeHomotopy.tube L s hs (tube j B R) 1 = tube j B r := by
    funext p
    rw [RadialTubeShapeHomotopy.tube_one]
    change j p.1 + B p.1 (OpenPartialHomeomorph.univBall (0 : K) R
      (RadialShapeChange.finalCoordinates (L p.1).toContinuousLinearMap s p.2)) = _
    rw [RadialShapeChange.univBall_finalCoordinates _ _ hs (hb p.1) R hR]
    have hrs : R * s = r := by dsimp [s]; field_simp
    rw [hrs]
    rfl
  let H : (collapseMap j B R hER).Homotopy (collapseMap j B r hEr) := {
    toContinuousMap := RadialTubeShapeHomotopy.collapseFamily L s hs hc hi hb (tube j B R) hER
    map_zero_left := fun z ↦
      (RadialTubeShapeHomotopy.collapseFamily_apply L s hs hc hi hb (tube j B R) hER 0 z).trans
        (by rw [hzero]; rfl)
    map_one_left := fun z ↦
      (RadialTubeShapeHomotopy.collapseFamily_apply L s hs hc hi hb (tube j B R) hER 1 z).trans
        (by rw [hone]; rfl) }
  exact ⟨H, fun t ↦ RadialTubeShapeHomotopy.collapseFamily_infty L s hs hc hi hb (tube j B R) hER t⟩

theorem exists_based_homotopy (r₀ r₁ : ℝ) (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (hE₀ : IsOpenEmbedding (tube j B r₀)) (hE₁ : IsOpenEmbedding (tube j B r₁)) :
    ∃ H : (collapseMap j B r₀ hE₀).Homotopy (collapseMap j B r₁ hE₁),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  rcases le_total r₀ r₁ with h | h
  · obtain ⟨H, hH⟩ := exists_based_homotopy_of_le j B r₀ r₁ h₀ h₁ h hE₀ hE₁
    refine ⟨H.symm, ?_⟩
    intro t
    rw [ContinuousMap.Homotopy.symm_apply]
    exact hH _
  · exact exists_based_homotopy_of_le j B r₁ r₀ h₁ h₀ h hE₁ hE₀

end NoExoticSixSphere.RoundTubeRadiusHomotopy
