import Mathlib.NumberTheory.Bertrand
import ErdosProblems.Erdos538.GlobalPaletteCap

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

noncomputable section

/-- Bertrand supplies an odd prime field of size at most `4k`; choosing a
quadratic-size ground set turns the general safe-kernel theorem into an
explicit `Omega(1/k)` cap-two daisy palette. -/
theorem exists_linear_density_capTwo_palette
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (p m : ℕ) (F : Finset (UniformChildren m (k - 1))),
      p.Prime ∧ 2 * k < p ∧ p ≤ 4 * k ∧
      m = p ^ 2 / 2 ∧
      Nat.choose m k ≤ 64 * k * F.card ∧
      ∀ T : Finset (Fin m), ∀ hT : T.card = (k - 1) + 2,
        (Finset.univ.filter fun x : T =>
          parentFacet T hT x ∈ F).card ≤ 2 := by
  obtain ⟨p, hp, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * k) (by omega)
  have hp4 : p ≤ 4 * k := by
    calc
      p ≤ 2 * (2 * k) := hple
      _ = 4 * k := by ring
  letI : Fact p.Prime := ⟨hp⟩
  let m := p ^ 2 / 2
  have hd : 0 < k - 1 := by omega
  have hqsize : 2 * ((k - 1) + 1) ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have houtside : 2 * (m - ((k - 1) + 1)) ≤
      (Nat.card (ZMod p)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    calc
      2 * (m - ((k - 1) + 1)) ≤ 2 * m := by gcongr; omega
      _ ≤ p ^ 2 := by
        exact Nat.mul_div_le (p ^ 2) 2
  obtain ⟨F, hmass, hcap⟩ :=
    exists_dense_rangeSelectedFamily (K := ZMod p) (m := m) (d := k - 1)
      hd htwo hqsize houtside
  refine ⟨p, m, F, hp, hpgt, hp4, rfl, ?_, hcap⟩
  have hcard : Fintype.card (UniformChildren m (k - 1)) = Nat.choose m k := by
    rw [Fintype.card_finset_len]
    simp
    congr 1
    omega
  rw [hcard] at hmass
  calc
    Nat.choose m k ≤ 16 * Fintype.card (ZMod p) * F.card := hmass
    _ = 16 * p * F.card := by rw [ZMod.card]
    _ ≤ 64 * k * F.card := by
      have hcoef : 16 * p ≤ 64 * k := by omega
      exact Nat.mul_le_mul_right F.card hcoef

/-- A version on exactly `2k²` colors, aligned with the existing weighted
half-rainbow coloring theorem. -/
theorem exists_balanced_linear_density_capTwo_palette
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (p : ℕ) (F : Finset (UniformChildren (2 * k * k) (k - 1))),
      p.Prime ∧ 2 * k < p ∧ p ≤ 4 * k ∧
      Nat.choose (2 * k * k) k ≤ 64 * k * F.card ∧
      ∀ T : Finset (Fin (2 * k * k)), ∀ hT : T.card = (k - 1) + 2,
        (Finset.univ.filter fun x : T =>
          parentFacet T hT x ∈ F).card ≤ 2 := by
  obtain ⟨p, hp, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * k) (by omega)
  have hp4 : p ≤ 4 * k := by
    calc
      p ≤ 2 * (2 * k) := hple
      _ = 4 * k := by ring
  letI : Fact p.Prime := ⟨hp⟩
  have hd : 0 < k - 1 := by omega
  have hqsize : 2 * ((k - 1) + 1) ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have houtside : 2 * ((2 * k * k) - ((k - 1) + 1)) ≤
      (Nat.card (ZMod p)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    have hsquare : (2 * k) * (2 * k) < p * p :=
      Nat.mul_self_lt_mul_self hpgt
    calc
      2 * ((2 * k * k) - ((k - 1) + 1)) ≤ 2 * (2 * k * k) := by
        gcongr
        omega
      _ = (2 * k) * (2 * k) := by ring
      _ ≤ p ^ 2 := by simpa [pow_two] using hsquare.le
  obtain ⟨F, hmass, hcap⟩ :=
    exists_dense_rangeSelectedFamily (K := ZMod p)
      (m := 2 * k * k) (d := k - 1) hd htwo hqsize houtside
  refine ⟨p, F, hp, hpgt, hp4, ?_, hcap⟩
  have hcard : Fintype.card (UniformChildren (2 * k * k) (k - 1)) =
      Nat.choose (2 * k * k) k := by
    rw [Fintype.card_finset_len]
    simp
    congr 1
    omega
  rw [hcard] at hmass
  calc
    Nat.choose (2 * k * k) k ≤ 16 * Fintype.card (ZMod p) * F.card := hmass
    _ = 16 * p * F.card := by rw [ZMod.card]
    _ ≤ 64 * k * F.card := by
      have hcoef : 16 * p ≤ 64 * k := by omega
      exact Nat.mul_le_mul_right F.card hcoef

end

end Erdos538.IsotropicKernel
