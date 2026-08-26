import ErdosProblems.Erdos1148.PacketCarrier

/-! # A lower bound on nonzero lattice-vector lengths along discriminant packets -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma evalForm_mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : R × R × R) (u v : R) :
    evalForm (mapCoeffs φ t) (φ u) (φ v) = φ (evalForm t u v) := by
  simp [evalForm, mapCoeffs]

lemma evalForm_smul (r : ℝ) (t : ℝ × ℝ × ℝ) (u v : ℝ) :
    evalForm (r • t) u v = r * evalForm t u v := by
  dsimp [evalForm]
  ring

lemma evalForm_split (u v : ℝ) : evalForm (splitForm ℝ) u v = u * v := by
  simp [evalForm, splitForm]

theorem integral_evalForm_ne_zero {d : ℤ} (hns : ¬IsSquare d) {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) : evalForm t u v ≠ 0 := by
  intro heval
  have hidentity : d * v ^ 2 = (2 * t.1 * u + t.2.1 * v) ^ 2 := by
    dsimp only [discr] at ht
    dsimp only [evalForm] at heval
    linear_combination -v ^ 2 * ht - 4 * t.1 * heval
  have hv := eq_zero_of_nonsquare_mul_sq hns hidentity
  have ha := fst_ne_zero_of_nonsquare_discr hns ht
  rw [hv] at heval
  simp only [evalForm, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at heval
  have hu : u = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp ((mul_eq_zero.mp heval).resolve_left ha)
  exact huv.elim (fun h => h hu) (fun h => h hv)

noncomputable def modularVector (g : SL(2, ℝ)) (u v : ℤ) : ℝ × ℝ :=
  ((g⁻¹ : SL(2, ℝ)) 0 0 * u + (g⁻¹ : SL(2, ℝ)) 0 1 * v,
    (g⁻¹ : SL(2, ℝ)) 1 0 * u + (g⁻¹ : SL(2, ℝ)) 1 1 * v)

noncomputable def modularVectorLengthSq (g : SL(2, ℝ)) (u v : ℤ) : ℝ :=
  (modularVector g u v).1 ^ 2 + (modularVector g u v).2 ^ 2

theorem integral_form_vector_lengthSq_lower {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) {g : SL(2, ℝ)}
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) :
    2 ≤ Real.sqrt (d : ℝ) * modularVectorLengthSq g u v := by
  have hρ : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hval : Real.sqrt (d : ℝ) * ((modularVector g u v).1 * (modularVector g u v).2) =
      ((evalForm t u v : ℤ) : ℝ) := by
    have h := congrArg (fun q : ℝ × ℝ × ℝ => evalForm q (u : ℝ) (v : ℝ)) hg
    rw [evalForm_smul, formAction, evalForm_transform, evalForm_split] at h
    change _ = evalForm (mapCoeffs (Int.castRingHom ℝ) t)
      ((Int.castRingHom ℝ) u) ((Int.castRingHom ℝ) v) at h
    rw [evalForm_mapCoeffs] at h
    exact h
  have hnonzero := integral_evalForm_ne_zero hns ht huv
  have h1Z : (1 : ℤ) ≤ |evalForm t u v| := by
    have hpos := abs_pos.mpr hnonzero
    omega
  have h1 : (1 : ℝ) ≤ |((evalForm t u v : ℤ) : ℝ)| := by exact_mod_cast h1Z
  rw [← hval, abs_mul, abs_of_pos hρ] at h1
  have hsq : 2 * |(modularVector g u v).1 * (modularVector g u v).2| ≤
      modularVectorLengthSq g u v := by
    rw [abs_mul]
    dsimp only [modularVectorLengthSq]
    nlinarith [sq_nonneg (|(modularVector g u v).1| - |(modularVector g u v).2|),
      sq_abs (modularVector g u v).1, sq_abs (modularVector g u v).2]
  have hscaled := mul_le_mul_of_nonneg_left hsq hρ.le
  nlinarith

theorem packet_vector_lengthSq_lower {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {q : IntegralFormOrbits d} {g : SL(2, ℝ)}
    (hg : modularMk g ∈ (packetOrbit hd hns q).carrier) {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) :
    2 ≤ Real.sqrt (d : ℝ) * modularVectorLengthSq g u v := by
  obtain ⟨t, _, ht⟩ := integral_form_of_mem_packet_carrier hd hns hg
  exact integral_form_vector_lengthSq_lower hd hns t.2 ht huv

end Erdos1148.DukeArithmetic
