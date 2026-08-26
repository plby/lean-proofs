import ErdosProblems.Erdos1148.SpecialOrbits

/-!
# Congruent frames and integral isometries

These calculations prepare the finite local counting problem at primes dividing
the binary discriminant. They do not provide the sharp ramified-prime bound.
-/

namespace Erdos1148.DukeArithmetic

def coeffMatrixMap {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    (R × R × R) →ₗ[R] (R × R × R) :=
  (coeffVecEquiv R).symm.toLinearMap.comp
    ((Matrix.toLin' M).comp (coeffVecEquiv R).toLinearMap)

lemma coeffMatrixMap_one {R : Type*} [CommRing R] :
    coeffMatrixMap (1 : Matrix (Fin 3) (Fin 3) R) = LinearMap.id := by
  apply LinearMap.ext
  intro t
  simp [coeffMatrixMap]

lemma coeffMatrixMap_mul {R : Type*} [CommRing R]
    (M N : Matrix (Fin 3) (Fin 3) R) :
    coeffMatrixMap (M * N) = (coeffMatrixMap M).comp (coeffMatrixMap N) := by
  apply LinearMap.ext
  intro t
  simp only [coeffMatrixMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Matrix.toLin'_mul_apply]

lemma coeffMatrixMap_smul_one {R : Type*} [CommRing R] (a : R) (t : R × R × R) :
    coeffMatrixMap (a • (1 : Matrix (Fin 3) (Fin 3) R)) t = a • t := by
  simp [coeffMatrixMap]

lemma coeffMatrixMap_pairFrame {R : Type*} [CommRing R] (t u v : R × R × R) :
    coeffMatrixMap (pairFrame t u) v =
      v.1 • t + v.2.1 • u + v.2.2 • pairNormal t u := by
  ext <;> simp [coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLin'_apply, pairFrame] <;> ring

lemma discr_coeffMatrixMap_pairFrame_eq {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ) (v : R × R × R) :
    discr (coeffMatrixMap (pairFrame p.1.1 p.1.2) v) =
      discr (coeffMatrixMap (pairFrame q.1.1 q.1.2) v) := by
  simp only [coeffMatrixMap_pairFrame, discr_three_combination,
    pairing_normal_left, pairing_normal_right, p.2.1, p.2.2.1, p.2.2.2,
    q.2.1, q.2.2.1, q.2.2.2, discr_pairNormal_eq p q]

def relativeFrameMatrix {R : Type*} [CommRing R]
    (P B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  1 + B * P.adjugate

lemma relativeFrameMatrix_mul {R : Type*} [CommRing R]
    (P B : Matrix (Fin 3) (Fin 3) R) :
    relativeFrameMatrix P B * P = P + P.det • B := by
  rw [relativeFrameMatrix, add_mul, one_mul, mul_assoc, Matrix.adjugate_mul,
    mul_smul_comm, mul_one]

lemma det_relativeFrameMatrix {R : Type*} [CommRing R] [NoZeroDivisors R]
    (P B : Matrix (Fin 3) (Fin 3) R) (hP : P.det ≠ 0)
    (hdet : (P + P.det • B).det = P.det) : (relativeFrameMatrix P B).det = 1 := by
  have h := congrArg Matrix.det (relativeFrameMatrix_mul P B)
  rw [Matrix.det_mul, hdet] at h
  apply mul_right_cancel₀ hP
  simpa only [one_mul] using h

lemma discr_smul {R : Type*} [CommRing R] (a : R) (t : R × R × R) :
    discr (a • t) = a ^ 2 * discr t := by
  dsimp [discr]
  ring

lemma discr_preserved_of_map_frame {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (G : Matrix (Fin 3) (Fin 3) R)
    (hG : G * pairFrame p.1.1 p.1.2 = pairFrame q.1.1 q.1.2) (t : R × R × R) :
    discr (coeffMatrixMap G t) = discr t := by
  let P := pairFrame p.1.1 p.1.2
  have hscale : coeffMatrixMap P (coeffMatrixMap P.adjugate t) = P.det • t := by
    rw [← LinearMap.comp_apply, ← coeffMatrixMap_mul, Matrix.mul_adjugate,
      coeffMatrixMap_smul_one]
  have hsame : discr (coeffMatrixMap G (P.det • t)) = discr (P.det • t) := by
    rw [← hscale, ← LinearMap.comp_apply, ← coeffMatrixMap_mul, hG]
    exact (discr_coeffMatrixMap_pairFrame_eq p q _).symm
  rw [map_smul, discr_smul, discr_smul] at hsame
  exact mul_left_cancel₀ (pow_ne_zero 2 (det_pairFrame_ne_zero p hnd)) hsame

lemma det_coeffMatrixMap {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    LinearMap.det (coeffMatrixMap M) = M.det := by
  calc
    _ = LinearMap.det (Matrix.toLin' M) := by
      simpa only [coeffMatrixMap, LinearEquiv.symm_symm, LinearMap.comp_assoc] using
        LinearMap.det_conj (Matrix.toLin' M) (coeffVecEquiv R).symm
    _ = M.det := LinearMap.det_toLin' M

noncomputable def coeffMatrixEquiv {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (hM : IsUnit M.det) :
    (R × R × R) ≃ₗ[R] (R × R × R) :=
  (coeffVecEquiv R).trans
    ((Matrix.toLinearEquiv (Pi.basisFun R (Fin 3)) M hM).trans (coeffVecEquiv R).symm)

lemma coeffMatrixEquiv_toLinearMap {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (hM : IsUnit M.det) :
    (coeffMatrixEquiv M hM).toLinearMap = coeffMatrixMap M := by
  apply LinearMap.ext
  intro t
  simp [coeffMatrixEquiv, coeffMatrixMap, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']

lemma coeffMatrixEquiv_apply {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (hM : IsUnit M.det) (t : R × R × R) :
    coeffMatrixEquiv M hM t = coeffMatrixMap M t :=
  congrArg (fun f : (R × R × R) →ₗ[R] (R × R × R) => f t) (coeffMatrixEquiv_toLinearMap M hM)

theorem exists_specialPairAction_of_frame_difference {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (B : Matrix (Fin 3) (Fin 3) R)
    (hB : pairFrame q.1.1 q.1.2 =
      pairFrame p.1.1 p.1.2 + (pairFrame p.1.1 p.1.2).det • B) :
    ∃ g : specialDiscrGroup R, g • p = q := by
  let P := pairFrame p.1.1 p.1.2
  let G := relativeFrameMatrix P B
  have hGP : G * P = pairFrame q.1.1 q.1.2 := (relativeFrameMatrix_mul P B).trans hB.symm
  have hdetG : G.det = 1 := by
    apply det_relativeFrameMatrix P B (det_pairFrame_ne_zero p hnd)
    rw [← hB, det_pairFrame_eq q p]
  have hunitG : IsUnit G.det := by rw [hdetG]; exact isUnit_one
  let g := coeffMatrixEquiv G hunitG
  have hg : g ∈ specialDiscrGroup R := by
    constructor
    · intro t
      rw [coeffMatrixEquiv_apply]
      exact discr_preserved_of_map_frame p q hnd G hGP t
    · rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdetG]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change g p.1.1 = q.1.1
    rw [coeffMatrixEquiv_apply]
    have h := congrArg (fun M => coeffMatrixMap M (1, 0, 0)) hGP
    rw [coeffMatrixMap_mul, LinearMap.comp_apply] at h
    simpa only [P, coeffMatrixMap_pairFrame, one_smul, zero_smul, add_zero] using h
  · change g p.1.2 = q.1.2
    rw [coeffMatrixEquiv_apply]
    have h := congrArg (fun M => coeffMatrixMap M (0, 1, 0)) hGP
    rw [coeffMatrixMap_mul, LinearMap.comp_apply] at h
    simpa only [P, coeffMatrixMap_pairFrame, one_smul, zero_smul, zero_add, add_zero] using h

lemma exists_matrix_of_dvd_sub {R : Type*} [CommRing R]
    (P Q : Matrix (Fin 3) (Fin 3) R)
    (h : ∀ i j, P.det ∣ Q i j - P i j) : ∃ B, Q = P + P.det • B := by
  choose B hB using h
  refine ⟨B, ?_⟩
  ext i j
  change Q i j = P i j + P.det * B i j
  linear_combination hB i j

theorem specialPairOrbit_eq_of_frame_congruent {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p q : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2)
    (hcongr : ∀ i j, (pairFrame p.1.1 p.1.2).det ∣
      pairFrame q.1.1 q.1.2 i j - pairFrame p.1.1 p.1.2 i j) :
    (Quotient.mk _ p : SpecialPairOrbits R d ℓ) = Quotient.mk _ q := by
  obtain ⟨B, hB⟩ := exists_matrix_of_dvd_sub (pairFrame p.1.1 p.1.2)
    (pairFrame q.1.1 q.1.2) hcongr
  obtain ⟨g, hg⟩ := exists_specialPairAction_of_frame_difference p q hnd B hB
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, inv_smul_smul]

/-- Residues of a chosen representative; invariance is not needed for this encoding. -/
noncomputable def orbitFrameResidues {R S : Type*} [CommRing R] [CommRing S]
    {d ℓ : R} (φ : R →+* S) (x : SpecialPairOrbits R d ℓ) : Matrix (Fin 3) (Fin 3) S :=
  (pairFrame x.out.1.1 x.out.1.2).map φ

lemma orbitFrameResidues_injective {R S : Type*} [CommRing R] [CommRing S]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (φ : R →+* S)
    (hker : ∀ a, φ a = 0 → (pairFrame base.1.1 base.1.2).det ∣ a) :
    Function.Injective (orbitFrameResidues (d := d) (ℓ := ℓ) φ) := by
  intro x y hxy
  have horbit := specialPairOrbit_eq_of_frame_congruent x.out y.out hnd (by
    intro i j
    rw [det_pairFrame_eq x.out base]
    apply hker
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact (congrArg (fun M => M i j) hxy).symm)
  simpa only [Quotient.out_eq] using horbit

theorem finite_specialPairOrbits_of_residue_map {R S : Type*} [CommRing R] [CommRing S]
    [NoZeroDivisors R] [CharZero R] [Finite S] {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (φ : R →+* S)
    (hker : ∀ a, φ a = 0 → (pairFrame base.1.1 base.1.2).det ∣ a) :
    Finite (SpecialPairOrbits R d ℓ) :=
  Finite.of_injective _ (orbitFrameResidues_injective base hnd φ hker)

/-- A coarse finite bound, preceding the sharper local estimates in the source proof. -/
theorem card_specialPairOrbits_le_residue_card_pow {R S : Type*} [CommRing R] [CommRing S]
    [NoZeroDivisors R] [CharZero R] [Finite S] {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (φ : R →+* S)
    (hker : ∀ a, φ a = 0 → (pairFrame base.1.1 base.1.2).det ∣ a) :
    Nat.card (SpecialPairOrbits R d ℓ) ≤ Nat.card S ^ 9 := by
  have h := Nat.card_le_card_of_injective _ (orbitFrameResidues_injective base hnd φ hker)
  simpa only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul, show 3 * 3 = 9 by decide] using h

lemma int_frame_residue_kernel (D a : ℤ) (ha : (a : ZMod D.natAbs) = 0) : D ∣ a := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd a D.natAbs).mp ha
  simpa only [Int.natCast_natAbs, abs_dvd] using h

theorem finite_integer_specialPairOrbits {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Finite (SpecialPairOrbits ℤ d ℓ) := by
  let D := (pairFrame base.1.1 base.1.2).det
  let : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr (det_pairFrame_ne_zero base hnd)⟩
  exact finite_specialPairOrbits_of_residue_map base hnd (Int.castRingHom (ZMod D.natAbs))
    (int_frame_residue_kernel D)

theorem card_integer_specialPairOrbits_le {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits ℤ d ℓ) ≤ (pairFrame base.1.1 base.1.2).det.natAbs ^ 9 := by
  let D := (pairFrame base.1.1 base.1.2).det
  let : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr (det_pairFrame_ne_zero base hnd)⟩
  have h := card_specialPairOrbits_le_residue_card_pow base hnd
    (Int.castRingHom (ZMod D.natAbs)) (int_frame_residue_kernel D)
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using h

lemma padic_frame_residue_kernel (p : ℕ) [Fact p.Prime] (D : PadicInt p) (hD : D ≠ 0)
    (a : PadicInt p) (ha : PadicInt.toZModPow D.valuation a = 0) : D ∣ a := by
  have hmem : a ∈ RingHom.ker (PadicInt.toZModPow D.valuation) := ha
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  rw [PadicInt.unitCoeff_spec hD]
  exact Units.mul_left_dvd.mpr hmem

theorem finite_padic_specialPairOrbits (p : ℕ) [Fact p.Prime] {d ℓ : PadicInt p}
    (base : FormPair (PadicInt p) d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Finite (SpecialPairOrbits (PadicInt p) d ℓ) := by
  let D := (pairFrame base.1.1 base.1.2).det
  exact finite_specialPairOrbits_of_residue_map base hnd (PadicInt.toZModPow D.valuation)
    (padic_frame_residue_kernel p D (det_pairFrame_ne_zero base hnd))

/-- This exponent is only a finiteness bound; it is not the sharp basic-lemma estimate. -/
theorem card_padic_specialPairOrbits_le (p : ℕ) [Fact p.Prime] {d ℓ : PadicInt p}
    (base : FormPair (PadicInt p) d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits (PadicInt p) d ℓ) ≤
      p ^ ((pairFrame base.1.1 base.1.2).det.valuation * 9) := by
  let D := (pairFrame base.1.1 base.1.2).det
  have h := card_specialPairOrbits_le_residue_card_pow base hnd (PadicInt.toZModPow D.valuation)
    (padic_frame_residue_kernel p D (det_pairFrame_ne_zero base hnd))
  simpa only [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul] using h

end Erdos1148.DukeArithmetic
