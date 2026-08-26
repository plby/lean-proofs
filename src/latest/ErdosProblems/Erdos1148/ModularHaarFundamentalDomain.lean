import ErdosProblems.Erdos1148.ModularHaarDomain

/-! # The finite modular matrix domain is a Haar fundamental domain -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Filter
open scoped MatrixGroups ENNReal Pointwise

instance integralSpecialLinearCountable : Countable SL(2, ℤ) := by
  letI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact inferInstanceAs (Countable {g : Matrix (Fin 2) (Fin 2) ℤ // g.det = 1})

theorem specialLinear_haar_fd_boundary_null :
    (Measure.haar (G := SL(2, ℝ)))
      ((fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹'
        (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
  have h := invariant_upperHalfPlane_fd_boundary_eq_zero upperHalfPlaneHaarImage
  rwa [upperHalfPlaneHaarImage, Measure.map_apply measurable_smul_I
    (ModularGroup.isClosed_fd.measurableSet.diff ModularGroup.isOpen_fdo.measurableSet)] at h

theorem modularHaarDomain_ae_covers : ∀ᵐ g ∂(Measure.haar (G := SL(2, ℝ))),
    ∃ γ : SL(2, ℤ), γ • g ∈ modularHaarDomain := by
  have hae : ∀ᵐ g ∂(Measure.haar (G := SL(2, ℝ))), ∀ γ : SL(2, ℤ),
      (γ • g) • UpperHalfPlane.I ∉ ModularGroup.fd \ ModularGroup.fdo := by
    apply ae_all_iff.mpr
    intro γ
    apply ae_iff.mpr
    simpa only [Set.preimage, Set.mem_setOf_eq, not_not] using
      measure_preimage_smul_null specialLinear_haar_fd_boundary_null γ
  filter_upwards [hae] with g hg
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd (g • UpperHalfPlane.I)
  have hfd : (γ • g) • UpperHalfPlane.I ∈ ModularGroup.fdo := by
    by_contra hnot
    exact hg γ ⟨by rwa [integral_frame_smul_I], hnot⟩
  rcases matrixHalfSign_or_neg (γ • g) with hsign | hsign
  · exact ⟨γ, hfd, hsign⟩
  · refine ⟨-γ, ?_, ?_⟩
    · rwa [integral_frame_smul_I, ModularGroup.SL_neg_smul, ← integral_frame_smul_I]
    · simpa [integralRealMatrix_smul] using hsign

theorem modularHaarDomain_isFundamentalDomain :
    IsFundamentalDomain SL(2, ℤ) modularHaarDomain (Measure.haar (G := SL(2, ℝ))) := by
  apply IsFundamentalDomain.mk'' measurableSet_modularHaarDomain.nullMeasurableSet
    modularHaarDomain_ae_covers
  · intro γ hγ
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    rintro g ⟨h, hh, rfl⟩ hg
    exact hγ (modularHaarDomain_translate_unique hh hg)
  · intro γ
    exact (measurePreserving_smul γ (Measure.haar (G := SL(2, ℝ)))).quasiMeasurePreserving

theorem modularHaarDomain_mass_pos :
    0 < (Measure.haar (G := SL(2, ℝ))) modularHaarDomain :=
  pos_iff_ne_zero.mpr (modularHaarDomain_isFundamentalDomain.measure_ne_zero (by
    intro hzero
    have hp := IsOpen.measure_pos (Measure.haar (G := SL(2, ℝ))) isOpen_univ
      (Set.univ_nonempty : (Set.univ : Set SL(2, ℝ)).Nonempty)
    simpa [hzero] using hp))

end Erdos1148.DukeArithmetic
