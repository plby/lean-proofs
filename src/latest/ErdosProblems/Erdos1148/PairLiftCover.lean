import ErdosProblems.Erdos1148.PacketPairImages
import ErdosProblems.Erdos1148.SignedPairLifts

/-! # Covering close lifts by the image indexed by their integral pair orbit -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma scaled_formAction_integral_mul {ρ : ℝ} {t : ℤ × ℤ × ℤ} {g : SL(2, ℝ)}
    (hg : ρ • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (γ : SL(2, ℤ)) :
    ρ • formAction ((γ : SL(2, ℝ)) * g) (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) (formAction γ t) := by
  rw [formAction_mul, ← formAction_smul, hg, mapCoeffs_formAction]

lemma formAction_eq_of_scaled_eq {ρ : ℝ} (hρ : ρ ≠ 0) {g h : SL(2, ℝ)}
    (heq : ρ • formAction g (splitForm ℝ) = ρ • formAction h (splitForm ℝ)) :
    formAction g (splitForm ℝ) = formAction h (splitForm ℝ) := by
  have h := congrArg (fun v : ℝ × ℝ × ℝ => ρ⁻¹ • v) heq
  simpa only [smul_smul, inv_mul_cancel₀ hρ, one_smul] using h

theorem integral_pair_close_mem_packetPairImage {d ℓ : ℤ} (hd : 0 < d)
    (p : FormPair ℤ d ℓ) {g h : SL(2, ℝ)} {η : ℝ}
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) p.1.1)
    (hh : Real.sqrt (d : ℝ) • formAction h (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) p.1.2)
    (hclose : EntryCloseOne η (g⁻¹ * h)) :
    (modularMk g, modularMk h) ∈ packetPairImage hd (Quotient.mk _ p) η := by
  let q : IntegralPairOrbits d ℓ := Quotient.mk _ p
  let f := chooseIntegralPairFrame hd q.out
  have hrel : MulAction.orbitRel SL(2, ℤ) (FormPair ℤ d ℓ) p q.out :=
    Quotient.exact (Quotient.out_eq q).symm
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hγ₁ : formAction γ q.out.1.1 = p.1.1 :=
    congrArg (fun v : FormPair ℤ d ℓ => v.1.1) hγ
  have hγ₂ : formAction γ q.out.1.2 = p.1.2 :=
    congrArg (fun v : FormPair ℤ d ℓ => v.1.2) hγ
  have hfirst := scaled_formAction_integral_mul f.first_form γ
  have hsecond := scaled_formAction_integral_mul f.second_form γ
  rw [hγ₁] at hfirst
  rw [hγ₂] at hsecond
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hmem := close_pair_mem_chosen_lift_image
    (formAction_eq_of_scaled_eq hρ (hfirst.trans hg.symm))
    (formAction_eq_of_scaled_eq hρ (hsecond.trans hh.symm)) hclose
  rw [finPairFlowCurve_integral_mul] at hmem
  change (modularMk g, modularMk h) ∈ finPairFlowCurve f.first f.second ''
    signedCloseDiagonalFlowTimes (f.first⁻¹ * f.second) η
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hmem

theorem integral_pair_close_mem_noncentral_cover {d ℓ : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) (p : FormPair ℤ d ℓ) (hne : p.1.1 ≠ p.1.2)
    {g h : SL(2, ℝ)} {η : ℝ}
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) p.1.1)
    (hh : Real.sqrt (d : ℝ) • formAction h (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) p.1.2)
    (hclose : EntryCloseOne η (g⁻¹ * h)) :
    ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1 ∧
      (modularMk g, modularMk h) ∈ packetPairImage hd (Quotient.mk _ p) η := by
  have hℓ : ℓ ≠ 2 * d := fun hℓ =>
    hne (eq_of_pairing_eq_two_mul hns p.2.1 p.2.2.1 (p.2.2.2.trans hℓ))
  let f : IntegralPairFrame p := ⟨g, h, hg, hh⟩
  exact ⟨close_pairing_mem_noncentralMultiples hd hℓ hclose (f.relative_pairing hd),
    integral_pair_close_mem_packetPairImage hd p hg hh hclose⟩

end Erdos1148.DukeArithmetic
