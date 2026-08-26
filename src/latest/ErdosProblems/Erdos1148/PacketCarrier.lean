import ErdosProblems.Erdos1148.PairLiftCover
import ErdosProblems.Erdos1148.ClosedOrbitCarrier

/-! # Integral forms and the disjoint compact components of a packet -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma scaled_formAction_mul_flow {ρ : ℝ} {t : ℤ × ℤ × ℤ} {g : SL(2, ℝ)}
    (hg : ρ • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) (s : ℝ) :
    ρ • formAction (g * diagonalFlow s) (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t := by
  rw [formAction_mul, formAction_diagonalFlow_splitForm, hg]

theorem integral_form_of_mem_packet_carrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {q : IntegralFormOrbits d} {g : SL(2, ℝ)}
    (hg : modularMk g ∈ (packetOrbit hd hns q).carrier) :
    ∃ t : IntegralDiscrForm d, integralFormOrbitMk t = q ∧
      Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 := by
  obtain ⟨s, hs⟩ := hg
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff _ g).mp hs
  refine ⟨γ • q.out, (integralFormOrbitMk_action γ q.out).trans (Quotient.out_eq q), ?_⟩
  have h := scaled_formAction_integral_mul
    (scaled_formAction_mul_flow (packetOrbit_form hd hns q) s) γ
  rw [hγ] at h
  exact h

theorem mem_packet_carrier_of_integral_form {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {q : IntegralFormOrbits d} (t : IntegralDiscrForm d) (ht : integralFormOrbitMk t = q)
    {g : SL(2, ℝ)}
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t.1) :
    modularMk g ∈ (packetOrbit hd hns q).carrier := by
  have hrep : integralFormOrbitMk q.out = integralFormOrbitMk t :=
    (Quotient.out_eq q).trans ht.symm
  obtain ⟨γ, hγ⟩ := (integralFormOrbitMk_eq_iff q.out t).mp hrep
  have h := scaled_formAction_integral_mul (packetOrbit_form hd hns q) γ
  rw [hγ] at h
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  obtain ⟨s, hs | hs⟩ := exists_signed_flow_of_formAction_eq
    (formAction_eq_of_scaled_eq hρ (h.trans hg.symm))
  · refine ⟨s, ?_⟩
    rw [hs, mul_assoc, modularMk_integral_mul]
    rfl
  · refine ⟨s, ?_⟩
    rw [hs, modularMk_neg, mul_assoc, modularMk_integral_mul]
    rfl

theorem packet_carriers_pairwise_disjoint {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    Pairwise (fun p q : IntegralFormOrbits d =>
      Disjoint (packetOrbit hd hns p).carrier (packetOrbit hd hns q).carrier) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hx : modularMk x.out = x := Quotient.out_eq x
  rw [← hx] at hxp hxq
  obtain ⟨t, ht, htg⟩ := integral_form_of_mem_packet_carrier hd hns hxp
  obtain ⟨u, hu, hug⟩ := integral_form_of_mem_packet_carrier hd hns hxq
  have htu : t = u := Subtype.ext
    (mapCoeffs_injective (Int.castRingHom ℝ) Int.cast_injective (htg.symm.trans hug))
  exact hpq (ht.symm.trans ((congrArg integralFormOrbitMk htu).trans hu))

theorem packetPairImage_subset_carriers {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) (η : ℝ) :
    packetPairImage hd q η ⊆ (packetOrbit hd hns (pairOrbitFirst q)).carrier ×ˢ
      (packetOrbit hd hns (pairOrbitSecond q)).carrier := by
  rintro x ⟨s, _, rfl⟩
  let f := chooseIntegralPairFrame hd q.out
  constructor
  · exact mem_packet_carrier_of_integral_form hd hns (pairFirstForm q.out)
      (pairOrbitFirst_out q).symm (scaled_formAction_mul_flow f.first_form (s 0))
  · exact mem_packet_carrier_of_integral_form hd hns (pairSecondForm q.out)
      (pairOrbitSecond_out q).symm (scaled_formAction_mul_flow f.second_form (s 1))

end Erdos1148.DukeArithmetic
