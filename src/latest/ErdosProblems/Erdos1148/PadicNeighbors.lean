import ErdosProblems.Erdos1148.NeighborLifting
import ErdosProblems.Erdos1148.CoefficientLattices
import ErdosProblems.Erdos1148.IsotropicDirections

/-!
# Neighbors selected by isotropic reduction

At an odd prime, the reduction of a primitive vector with square-divisible
discriminant selects a neighboring lattice containing that vector divided
by the prime. Orthogonal isotropic reductions select the same neighbor.
-/

namespace Erdos1148.DukeArithmetic

lemma padic_dvd_iff_reduction_zero (p : ℕ) [Fact p.Prime] (x : PadicInt p) :
    (p : PadicInt p) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]

lemma padic_unit_of_reduction_ne_zero (p : ℕ) [Fact p.Prime]
    (x : PadicInt p) (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hunit
  apply hx
  change x ∈ RingHom.ker PadicInt.toZMod
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
  exact hunit

lemma zmod_two_ne_zero_of_gt (p : ℕ) (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact Nat.not_dvd_of_pos_of_lt (by decide) hp hdiv

lemma padic_prime_ne_zero (p : ℕ) [Fact p.Prime] : (p : Padic p) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

noncomputable def padicNeighborIsometry (p : ℕ) [Fact p.Prime]
    (x : Option (ZMod p)) : specialDiscrGroup (Padic p) :=
  match x with
  | none => normalizedTransformIsometry (infinityNeighborMatrix (p : Padic p))
      (by rw [det_infinityNeighborMatrix]; exact padic_prime_ne_zero p)
  | some z => normalizedTransformIsometry (neighborMatrix (p : Padic p) (z.val : Padic p))
      (by rw [det_neighborMatrix]; exact padic_prime_ne_zero p)

def padicNeighborLattice (p : ℕ) [Fact p.Prime] (x : Option (ZMod p)) :
    Set (Padic p × Padic p × Padic p) :=
  coefficientLattice (algebraMap (PadicInt p) (Padic p)) (padicNeighborIsometry p x)⁻¹

theorem divided_mem_neighbor_of_direction (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t : PadicInt p × PadicInt p × PadicInt p)
    (hd : (p : PadicInt p) ^ 2 ∣ discr t) (a : ZMod p) (ha : a ≠ 0)
    (x : Option (ZMod p)) (hx : mapCoeffs PadicInt.toZMod t = a • isotropicDirection x) :
    (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈
      padicNeighborLattice p x := by
  let φ := algebraMap (PadicInt p) (Padic p)
  have hπ : φ (p : PadicInt p) ≠ 0 := by
    simpa only [map_natCast] using padic_prime_ne_zero p
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [show (2 : ZMod p) * 2 = 4 by norm_num]
      using mul_ne_zero (zmod_two_ne_zero_of_gt p hp) (zmod_two_ne_zero_of_gt p hp)
  have hu4 : IsUnit (4 : PadicInt p) :=
    padic_unit_of_reduction_ne_zero p _ (by simpa only [map_ofNat] using h4)
  cases x with
  | none =>
    have hb0 : PadicInt.toZMod t.2.1 = 0 := by
      simpa [mapCoeffs, isotropicDirection] using congrArg (fun v => v.2.1) hx
    have hc0 : PadicInt.toZMod t.2.2 = a := by
      simpa [mapCoeffs, isotropicDirection] using congrArg (fun v => v.2.2) hx
    have hu : IsUnit (4 * t.2.2) :=
      hu4.mul (padic_unit_of_reduction_ne_zero p _ (hc0 ▸ ha))
    have hb := (padic_dvd_iff_reduction_zero p t.2.1).mpr hb0
    have hfirst := square_dvd_first_of_isotropic_reduction (p : PadicInt p) t hu hb hd
    apply (mem_coefficientLattice_inv_iff _ _ _).mpr
    simpa only [padicNeighborIsometry, map_natCast] using
      infinityNeighbor_contains_divided_vector φ (p : PadicInt p) hπ t hfirst hb
  | some z =>
    have ha0 : PadicInt.toZMod t.1 = a := by
      simpa [mapCoeffs, isotropicDirection] using congrArg Prod.fst hx
    have hb0 : PadicInt.toZMod t.2.1 = a * (2 * z) := by
      simpa [mapCoeffs, isotropicDirection] using congrArg (fun v => v.2.1) hx
    have hu : IsUnit (4 * t.1) :=
      hu4.mul (padic_unit_of_reduction_ne_zero p _ (ha0 ▸ ha))
    have hb : (p : PadicInt p) ∣ t.2.1 - 2 * t.1 * (z.val : PadicInt p) := by
      apply (padic_dvd_iff_reduction_zero p _).mpr
      simp only [map_sub, map_mul, map_ofNat, map_natCast, ZMod.natCast_zmod_val, ha0, hb0]
      ring
    have hc := square_dvd_neighborRemainder (p : PadicInt p) (z.val : PadicInt p) t hu hb hd
    apply (mem_coefficientLattice_inv_iff _ _ _).mpr
    simpa only [padicNeighborIsometry, map_natCast] using
      neighbor_contains_divided_vector φ (p : PadicInt p) (z.val : PadicInt p) hπ t hb hc

lemma reduction_discr_zero_of_square_dvd (p : ℕ) [Fact p.Prime]
    (t : PadicInt p × PadicInt p × PadicInt p) (hd : (p : PadicInt p) ^ 2 ∣ discr t) :
    discr (mapCoeffs PadicInt.toZMod t) = 0 := by
  obtain ⟨q, hq⟩ := hd
  rw [discr_mapCoeffs, hq]
  simp

theorem common_neighbor_of_primitive_orthogonal (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t u : PadicInt p × PadicInt p × PadicInt p)
    (ht : (p : PadicInt p) ^ 2 ∣ discr t) (hu : (p : PadicInt p) ^ 2 ∣ discr u)
    (hpair : pairing t u = 0)
    (htprim : mapCoeffs PadicInt.toZMod t ≠ 0)
    (huprim : mapCoeffs PadicInt.toZMod u ≠ 0) :
    ∃ x : Option (ZMod p),
      (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈
        padicNeighborLattice p x ∧
      (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈
        padicNeighborLattice p x := by
  have ht0 := reduction_discr_zero_of_square_dvd p t ht
  have hu0 := reduction_discr_zero_of_square_dvd p u hu
  have hpair0 : pairing (mapCoeffs PadicInt.toZMod t) (mapCoeffs PadicInt.toZMod u) = 0 := by
    rw [pairing_mapCoeffs, hpair, map_zero]
  obtain ⟨a, ha, x, hx⟩ := exists_isotropicDirection (zmod_two_ne_zero_of_gt p hp) ht0 htprim
  obtain ⟨c, hc⟩ := isotropic_orthogonal_collinear (zmod_two_ne_zero_of_gt p hp)
    ht0 hu0 htprim hpair0
  have hc0 : c ≠ 0 := by
    intro hz
    apply huprim
    rw [hc, hz, zero_smul]
  refine ⟨x, divided_mem_neighbor_of_direction p hp t ht a ha x hx, ?_⟩
  apply divided_mem_neighbor_of_direction p hp u hu (c * a) (mul_ne_zero hc0 ha) x
  rw [hc, hx, smul_smul]

lemma divided_integral_of_reduction_zero (p : ℕ) [Fact p.Prime]
    (t : PadicInt p × PadicInt p × PadicInt p) (ht : mapCoeffs PadicInt.toZMod t = 0) :
    (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈
      integralCoeffSet (algebraMap (PadicInt p) (Padic p)) := by
  have ha : (p : PadicInt p) ∣ t.1 := (padic_dvd_iff_reduction_zero p _).mpr
    (congrArg Prod.fst ht)
  have hb : (p : PadicInt p) ∣ t.2.1 := (padic_dvd_iff_reduction_zero p _).mpr
    (congrArg (fun v => v.2.1) ht)
  have hc : (p : PadicInt p) ∣ t.2.2 := (padic_dvd_iff_reduction_zero p _).mpr
    (congrArg (fun v => v.2.2) ht)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  refine ⟨(a, b, c), ?_⟩
  ext <;> simp [mapCoeffs, ha, hb, hc, ← mul_assoc]

/-- The three alternatives in the odd-prime local lattice recurrence. -/
theorem local_neighbor_recurrence (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t u : PadicInt p × PadicInt p × PadicInt p)
    (ht : (p : PadicInt p) ^ 2 ∣ discr t) (hu : (p : PadicInt p) ^ 2 ∣ discr u)
    (hpair : pairing t u = 0) :
    ((p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈
      integralCoeffSet (algebraMap (PadicInt p) (Padic p))) ∨
    ((p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈
      integralCoeffSet (algebraMap (PadicInt p) (Padic p))) ∨
    ∃ x : Option (ZMod p),
      (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈
        padicNeighborLattice p x ∧
      (p : Padic p)⁻¹ • mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈
        padicNeighborLattice p x := by
  by_cases htprim : mapCoeffs PadicInt.toZMod t = 0
  · exact Or.inl (divided_integral_of_reduction_zero p t htprim)
  by_cases huprim : mapCoeffs PadicInt.toZMod u = 0
  · exact Or.inr (Or.inl (divided_integral_of_reduction_zero p u huprim))
  exact Or.inr (Or.inr (common_neighbor_of_primitive_orthogonal p hp t u ht hu hpair htprim huprim))

theorem mem_padicNeighbor_iff_pairing_zero (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t : PadicInt p × PadicInt p × PadicInt p) (x : Option (ZMod p)) :
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicNeighborLattice p x ↔
      pairing (mapCoeffs PadicInt.toZMod t) (isotropicDirection x) = 0 := by
  let φ := algebraMap (PadicInt p) (Padic p)
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)
  have hπ : φ (p : PadicInt p) ≠ 0 := by
    simpa only [map_natCast] using padic_prime_ne_zero p
  have h4 : (-4 : ZMod p) ≠ 0 := by
    have h := mul_ne_zero (zmod_two_ne_zero_of_gt p hp) (zmod_two_ne_zero_of_gt p hp)
    norm_num at h ⊢
    exact h
  rw [padicNeighborLattice, mem_coefficientLattice_inv_iff]
  cases x with
  | none =>
    have hiff := infinityNeighbor_contains_integral_iff φ hφ (p : PadicInt p) hπ t
    simp only [map_natCast] at hiff
    rw [padicNeighborIsometry, hiff, padic_dvd_iff_reduction_zero,
      pairing_isotropicDirection_none]
    rw [mul_eq_zero]
    simp only [h4, false_or, mapCoeffs]
  | some z =>
    have hiff := neighbor_contains_integral_iff φ hφ (p : PadicInt p) (z.val : PadicInt p) hπ t
    simp only [map_natCast] at hiff
    rw [padicNeighborIsometry, hiff, padic_dvd_iff_reduction_zero,
      pairing_isotropicDirection_some]
    rw [mul_eq_zero]
    simp only [h4, false_or]
    have hrem := neighborRemainder_mapCoeffs PadicInt.toZMod (z.val : PadicInt p) t
    simpa only [map_natCast, ZMod.natCast_zmod_val, neighborRemainder] using
      Iff.of_eq (congrArg (fun a : ZMod p => a = 0) hrem).symm

open Classical in
theorem card_padicNeighbors_containing_primitive_le_two (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t : PadicInt p × PadicInt p × PadicInt p)
    (ht : mapCoeffs PadicInt.toZMod t ≠ 0) :
    (Finset.univ.filter (fun x : Option (ZMod p) =>
      mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicNeighborLattice p x)).card ≤ 2 := by
  classical
  apply card_orthogonal_directions_le_two (zmod_two_ne_zero_of_gt p hp) ht
  intro x hx
  exact (mem_padicNeighbor_iff_pairing_zero p hp t x).mp (Finset.mem_filter.mp hx).2

theorem existsUnique_padicNeighbor_of_primitive_isotropic (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t : PadicInt p × PadicInt p × PadicInt p)
    (ht : mapCoeffs PadicInt.toZMod t ≠ 0) (hd : (p : PadicInt p) ∣ discr t) :
    ∃! x : Option (ZMod p),
      mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicNeighborLattice p x := by
  have hd0 : discr (mapCoeffs PadicInt.toZMod t) = 0 := by
    rw [discr_mapCoeffs]
    exact (padic_dvd_iff_reduction_zero p _).mp hd
  simpa only [mem_padicNeighbor_iff_pairing_zero p hp] using
    existsUnique_orthogonal_direction_of_isotropic (zmod_two_ne_zero_of_gt p hp) hd0 ht

noncomputable def padicDirectionLift (p : ℕ) [Fact p.Prime] (x : Option (ZMod p)) :
    PadicInt p × PadicInt p × PadicInt p :=
  match x with
  | none => (0, 0, 1)
  | some z => (1, 2 * (z.val : PadicInt p), (z.val : PadicInt p) ^ 2)

lemma reduction_padicDirectionLift (p : ℕ) [Fact p.Prime] (x : Option (ZMod p)) :
    mapCoeffs PadicInt.toZMod (padicDirectionLift p x) = isotropicDirection x := by
  cases x <;> simp [padicDirectionLift, mapCoeffs, isotropicDirection, map_ofNat]

lemma discr_padicDirectionLift (p : ℕ) [Fact p.Prime] (x : Option (ZMod p)) :
    discr (padicDirectionLift p x) = 0 := by
  cases x <;> dsimp [padicDirectionLift, discr] <;> ring

theorem padicNeighborLattice_injective (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    Function.Injective (padicNeighborLattice p) := by
  intro x y hxy
  have hmem : mapCoeffs (algebraMap (PadicInt p) (Padic p)) (padicDirectionLift p x) ∈
      padicNeighborLattice p x := by
    rw [mem_padicNeighbor_iff_pairing_zero p hp, reduction_padicDirectionLift]
    exact (pairing_isotropicDirection_eq_zero_iff (zmod_two_ne_zero_of_gt p hp) x x).mpr rfl
  rw [hxy, mem_padicNeighbor_iff_pairing_zero p hp, reduction_padicDirectionLift] at hmem
  exact (pairing_isotropicDirection_eq_zero_iff (zmod_two_ne_zero_of_gt p hp) x y).mp hmem

open Classical in
theorem card_padicNeighborLattices (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (Finset.univ.image (padicNeighborLattice p)).card = p + 1 := by
  rw [Finset.card_image_of_injective _ (padicNeighborLattice_injective p hp)]
  simp [Fintype.card_option, ZMod.card]

end Erdos1148.DukeArithmetic
