import Wikipedia.SmoothSixDPoincare.SmoothComplementQuotient
import Wikipedia.SmoothSixDPoincare.PlanarFrameGermJoin
import Wikipedia.SmoothSixDPoincare.LinearFrameGermJoin
import Wikipedia.SmoothSixDPoincare.ComplementCoefficientSigns

/-!
# Join actual complementary-frame germs by correcting their quotient coefficients

All quotient operators are constructed from the given smooth splitting.
Same-sign endpoint coefficient determinants give an invertible coefficient
join; the exact correction makes it an actual complement and retains both
full prescribed frame germs. The sign hypothesis remains explicit.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Construct an actual complementary frame preserving the prescribed whole corner germs. -/
theorem exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U) (h1U : (1 : ℝ) ∈ U)
    (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Bijective ((G t).coprod (C t)))
    (hsign : 0 < ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
      ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F), ContDiffOn ℝ ∞ H U ∧
      (∀ t ∈ U, Bijective ((G t).coprod (H t))) ∧
      (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ U, ((G t).coprod (C t)).IsInvertible :=
    fun t ht => isInvertible_coprod_of_bijective (G t) (C t) (hi t ht)
  let K (t : ℝ) := (complementQuotient (G t) (C t)).comp (L t)
  have hK : ContDiffOn ℝ ∞ K U := (contDiffOn_complementQuotient hU hG hC hinv).clm_comp hL
  have hjoin := hdim.elim
    (fun hd => exists_smooth_invertible_join_of_finrank_one hd hK hK hU hU h0U h1U hsign)
    (fun hd => exists_smooth_invertible_join_of_finrank_two hd hK hK hU hU h0U h1U hsign)
  obtain ⟨K', hK', hiK', _, hleft, hright⟩ := hjoin
  let H (t : ℝ) := correctedComplement (G t) (C t) (L t) (K' t)
  have hH : ContDiffOn ℝ ∞ H U :=
    contDiffOn_correctedComplement hU hG hC hL hK'.contDiffOn hinv
  refine ⟨H, hH, fun t ht => bijective_coprod_correctedComplement
    (G t) (C t) (L t) (K' t) (hinv t ht) (hiK' t), ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)
  · filter_upwards [hright] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)

/-- The sign condition can be stated on the actual full frames, independently of the complement. -/
theorem exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Icc (0 : ℝ) 1 ⊆ U)
    (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Bijective ((G t).coprod (C t)))
    (hsign : 0 < (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F), ContDiffOn ℝ ∞ H U ∧
      (∀ t ∈ U, Bijective ((G t).coprod (H t))) ∧
      (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible :=
    fun t ht => isInvertible_coprod_of_bijective _ _ (hi t (hIU ht))
  have hcoeff := (same_sign_frames_iff_coefficients j (hG.mono hIU) (hC.mono hIU) hinv).mp hsign
  exact exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two hdim hU
    (hIU (by simp)) (hIU (by simp)) hG hC hL hi hcoeff

/-- The original rank-two coefficient specialization. -/
theorem exists_smooth_complement_with_endpoint_germs
    (hdim : Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U) (h1U : (1 : ℝ) ∈ U)
    (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Bijective ((G t).coprod (C t)))
    (hsign : 0 < ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
      ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F), ContDiffOn ℝ ∞ H U ∧
      (∀ t ∈ U, Bijective ((G t).coprod (H t))) ∧
      (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) :=
  exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    (Or.inr hdim) hU h0U h1U hG hC hL hi hsign

/-- The original rank-two specialization with signs on the actual full frames. -/
theorem exists_smooth_complement_with_germs_of_frame_sign
    (hdim : Module.finrank ℝ Z = 2) (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Icc (0 : ℝ) 1 ⊆ U)
    (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Bijective ((G t).coprod (C t)))
    (hsign : 0 < (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F), ContDiffOn ℝ ∞ H U ∧
      (∀ t ∈ U, Bijective ((G t).coprod (H t))) ∧
      (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) :=
  exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    (Or.inr hdim) j hU hIU hG hC hL hi hsign

end Wikipedia.SmoothSixDPoincare.FrameField
