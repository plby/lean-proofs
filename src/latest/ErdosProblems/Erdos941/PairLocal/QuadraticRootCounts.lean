/- Adapted from the checked repository proof in Erdos1148/QuadraticRootCounts.lean. -/
import ErdosProblems.Erdos941.PairLocal.SquareRootCounts
import ErdosProblems.Erdos941.PairLocal.AffineResidueFibers
import ErdosProblems.Erdos941.PairLocal.NeighborLifting

/-!
# Quadratic congruences with unit leading coefficient

Completing the square maps roots to square roots. The affine map has fibers
of size at most two, including at the prime two.
-/

namespace Erdos941.PairLocal

noncomputable def quadraticRootResidues (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) : Finset (ZMod (p ^ n)) :=
  Finset.univ.filter (fun x => neighborRemainder x (mapCoeffs (PadicInt.toZModPow n) t) = 0)

lemma mem_quadraticRootResidues_iff (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) (x : ZMod (p ^ n)) :
    x ∈ quadraticRootResidues p n t ↔
      (p : PadicInt p) ^ n ∣ neighborRemainder (x.val : PadicInt p) t := by
  rw [quadraticRootResidues, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  have h := padic_pow_dvd_sub_iff_reduction_eq p n (neighborRemainder (x.val : PadicInt p) t) 0
  simp only [sub_zero, map_zero] at h
  rw [h, ← neighborRemainder_mapCoeffs, map_natCast, ZMod.natCast_zmod_val]

lemma neighborRemainder_smul {R : Type*} [CommRing R] (a z : R) (t : R × R × R) :
    neighborRemainder z (a • t) = a * neighborRemainder z t := by
  dsimp [neighborRemainder]
  ring

lemma pow_dvd_pow_mul_iff {R : Type*} [CommRing R] [NoZeroDivisors R]
    (π : R) (hπ : π ≠ 0) (n r : ℕ) (hr : r ≤ n) (x : R) :
    π ^ n ∣ π ^ r * x ↔ π ^ (n - r) ∣ x := by
  conv_lhs => lhs; rw [← Nat.add_sub_of_le hr, pow_add]
  exact mul_dvd_mul_iff_left (pow_ne_zero r hπ)

lemma completed_square_identity {R : Type*} [CommRing R] (t : R × R × R) (x : R) :
    (2 * t.1 * x - t.2.1) ^ 2 = discr t + 4 * t.1 * neighborRemainder x t := by
  dsimp [discr, neighborRemainder]
  ring

lemma valuation_of_unit (p : ℕ) [Fact p.Prime] (a : PadicInt p) (ha : IsUnit a) :
    a.valuation = 0 := by
  have hnorm : ‖a‖ = 1 := PadicInt.isUnit_iff.mp ha
  have hpow : (p : PadicInt p) ^ a.valuation ∣ a := padic_pow_valuation_dvd p a
  by_contra hval
  have hpdiv : (p : PadicInt p) ∣ a := by
    have h := (pow_dvd_pow (p : PadicInt p) (by omega : 1 ≤ a.valuation)).trans hpow
    simpa only [pow_one] using h
  have hn := (PadicInt.norm_lt_one_iff_dvd a).mpr hpdiv
  linarith

theorem quadraticRootResidues_card_le_of_unit (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p)
    (ha : IsUnit t.1) (hD : discr t ≠ 0) :
    (quadraticRootResidues p n t).card ≤ 8 * p ^ ((discr t).valuation / 2) := by
  classical
  let ρ := PadicInt.toZModPow n (p := p)
  let f : ZMod (p ^ n) → ZMod (p ^ n) := fun x => ρ (2 * t.1) * x + -ρ t.2.1
  have hmap : ∀ x ∈ quadraticRootResidues p n t, f x ∈ squareRootResidues p n (discr t) := by
    intro x hx
    have hroot := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change f x ^ 2 = ρ (discr t)
    have h := completed_square_identity (mapCoeffs ρ t) x
    rw [hroot, mul_zero, add_zero, discr_mapCoeffs] at h
    simpa only [f, map_mul, map_ofNat, mapCoeffs, sub_eq_add_neg] using h
  have htwo : (2 : PadicInt p) ≠ 0 := by norm_num
  have hcoeff : 2 * t.1 ≠ 0 := mul_ne_zero htwo ha.ne_zero
  have hval : (2 * t.1).valuation = (2 : PadicInt p).valuation := by
    rw [PadicInt.valuation_mul htwo ha.ne_zero, valuation_of_unit p t.1 ha, add_zero]
  have hpow : p ^ (2 * t.1).valuation ≤ 2 := by
    rw [hval]
    exact Nat.le_of_dvd (by decide) ((padic_pow_dvd_natCast_iff p _ 2).mp
      (padic_pow_valuation_dvd p 2))
  have hfiber (b : ZMod (p ^ n)) :
      ((quadraticRootResidues p n t).filter (fun x => f x = b)).card ≤ 2 := by
    calc
      _ ≤ (Finset.univ.filter (fun x => f x = b)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      _ ≤ p ^ (2 * t.1).valuation := affine_residue_fiber_card_le p n _ hcoeff (-ρ t.2.1) b
      _ ≤ 2 := hpow
  have h := finite_fiber_card_bound (quadraticRootResidues p n t)
    (squareRootResidues p n (discr t)) f 2 hmap (fun b _ => hfiber b)
  have hsq := squareRootResidues_card_le p n (discr t) hD
  omega

theorem quadraticRootResidues_card_le_of_scaled (p : ℕ) [Fact p.Prime] (n r : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) (hD : discr t ≠ 0) (C : ℕ) (hC : 1 ≤ C)
    (hbound : ∀ m, (quadraticRootResidues p m t).card ≤ C * p ^ ((discr t).valuation / 2)) :
    (quadraticRootResidues p n ((p : PadicInt p) ^ r • t)).card ≤
      C * p ^ ((discr ((p : PadicInt p) ^ r • t)).valuation / 2) := by
  classical
  have hπ : (p : PadicInt p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hval : (discr ((p : PadicInt p) ^ r • t)).valuation = 2 * r + (discr t).valuation := by
    rw [discr_smul, PadicInt.valuation_mul (pow_ne_zero 2 (pow_ne_zero r hπ)) hD,
      PadicInt.valuation_pow, PadicInt.valuation_pow, PadicInt.valuation_p]
    omega
  by_cases hnr : n ≤ r
  · have hcard : (quadraticRootResidues p n ((p : PadicInt p) ^ r • t)).card ≤ p ^ n := by
      simpa only [Finset.card_univ, ZMod.card] using
        Finset.card_le_card
          (Finset.subset_univ (quadraticRootResidues p n ((p : PadicInt p) ^ r • t)))
    have hpow : p ^ n ≤ p ^ ((2 * r + (discr t).valuation) / 2) :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    rw [hval]
    exact hcard.trans (hpow.trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right
        (p ^ ((2 * r + (discr t).valuation) / 2)) hC))
  have hr : r ≤ n := by omega
  let m := n - r
  have hm : m ≤ n := Nat.sub_le _ _
  let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
  have hmap : ∀ x ∈ quadraticRootResidues p n ((p : PadicInt p) ^ r • t),
      f x ∈ quadraticRootResidues p m t := by
    intro x hx
    have hdiv := (mem_quadraticRootResidues_iff p n _ x).mp hx
    rw [neighborRemainder_smul, pow_dvd_pow_mul_iff _ hπ n r hr] at hdiv
    have hred := (padic_pow_dvd_sub_iff_reduction_eq p m
      (neighborRemainder (x.val : PadicInt p) t) 0).mp (by simpa only [sub_zero] using hdiv)
    rw [map_zero, ← neighborRemainder_mapCoeffs,
      padic_residue_lift_reduction p n m hm] at hred
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hred⟩
  have hfiber (b : ZMod (p ^ m)) :
      ((quadraticRootResidues p n ((p : PadicInt p) ^ r • t)).filter (fun x => f x = b)).card ≤
        p ^ r := by
    calc
      _ ≤ (Finset.univ.filter (fun x => f x = b)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      _ = p ^ (n - m) := card_zmod_reduction_fiber p n m hm b
      _ = p ^ r := by congr 1; dsimp [m]; omega
  have h := finite_fiber_card_bound (quadraticRootResidues p n ((p : PadicInt p) ^ r • t))
    (quadraticRootResidues p m t) f (p ^ r) hmap (fun b _ => hfiber b)
  have hsmall := hbound m
  calc
    _ ≤ (quadraticRootResidues p m t).card * p ^ r := h
    _ ≤ (C * p ^ ((discr t).valuation / 2)) * p ^ r := Nat.mul_le_mul_right _ hsmall
    _ = C * p ^ ((discr ((p : PadicInt p) ^ r • t)).valuation / 2) := by
      rw [mul_assoc, ← pow_add, hval]
      congr 2
      omega

theorem quadraticRootResidues_card_le_of_scaled_unit (p : ℕ) [Fact p.Prime] (n r : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) (ha : IsUnit t.1) (hD : discr t ≠ 0) :
    (quadraticRootResidues p n ((p : PadicInt p) ^ r • t)).card ≤
      8 * p ^ ((discr ((p : PadicInt p) ^ r • t)).valuation / 2) :=
  quadraticRootResidues_card_le_of_scaled p n r t hD 8 (by decide)
    (fun m => quadraticRootResidues_card_le_of_unit p m t ha hD)

end Erdos941.PairLocal
