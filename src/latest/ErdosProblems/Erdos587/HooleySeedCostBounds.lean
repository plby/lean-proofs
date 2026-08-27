import ErdosProblems.Erdos587.PolynomialDenseStandard
import ErdosProblems.Erdos587.HooleyAdaptedSeed

/-! # Polynomial bounds for the full lattice-seed width and deletion costs -/

namespace Erdos587.CFP

def deltaSeedPower (d : ℕ) : ℕ := 32 * (d + 1) ^ 2

def deltaSeedSideConstant (d : ℕ) : ℕ := (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d

def deltaSeedStepConstant (d : ℕ) : ℕ := 512 * d * deltaSeedSideConstant d

def deltaSeedCostConstant (d : ℕ) : ℕ :=
  256 * d + deltaSeedStepConstant d ^ (d * 2) +
    deltaSeedSideConstant d *
      (3 * GeneralizedAP.deltaSeedLatticeFactor d + deltaSeedStepConstant d ^ d + 1) + 1

lemma deltaSeedCostConstant_pos (d : ℕ) : 0 < deltaSeedCostConstant d := by
  unfold deltaSeedCostConstant
  positivity

lemma delta_coarse_filling_polynomial_bounds (d D : ℕ) (hD : 0 < D) :
    let q := denseBoxCount D d
    let F := nvDenseFactor D d * (q + 1) ^ d
    let J := (2 * q * F) ^ d
    q ≤ 256 * d * D ^ 4 ∧ F ≤ deltaSeedSideConstant d * D ^ (9 * d) ∧
      J ≤ deltaSeedStepConstant d ^ d * D ^ ((9 * d + 4) * d) := by
  let q := denseBoxCount D d
  let F := nvDenseFactor D d * (q + 1) ^ d
  have hproper : nvDenseFactor D d ≤ denseProperFactor D d := by
    unfold denseProperFactor
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hstandard : F ≤ denseStandardFactor D d :=
    Nat.mul_le_mul_right ((q + 1) ^ d) hproper
  have hF : F ≤ deltaSeedSideConstant d * D ^ (9 * d) :=
    hstandard.trans (denseStandardFactor_le hD d)
  have hB : 2 * q * F ≤ deltaSeedStepConstant d * D ^ (9 * d + 4) := by
    have hh : 2 * q * F ≤ denseStepBound D d := Nat.mul_le_mul_left (2 * q) hstandard
    exact hh.trans (denseStepBound_le hD d)
  refine ⟨denseBoxCount_le hD d, hF, ?_⟩
  calc
    (2 * q * F) ^ d ≤ (deltaSeedStepConstant d * D ^ (9 * d + 4)) ^ d :=
      Nat.pow_le_pow_left hB d
    _ = deltaSeedStepConstant d ^ d * D ^ ((9 * d + 4) * d) := by rw [mul_pow, ← pow_mul]

lemma delta_seed_cost_exponents (d : ℕ) :
    5 ≤ deltaSeedPower d ∧ ((9 * d + 4) * d) * 2 ≤ deltaSeedPower d ∧
      d ≤ (9 * d + 4) * d ∧ 9 * d + (9 * d + 4) * d ≤ deltaSeedPower d := by
  have hd : 0 ≤ d := Nat.zero_le d
  dsimp only [deltaSeedPower]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem delta_seed_budgets_of_power_bound (d D c h I : ℕ) (hD : 0 < D) (hc : c ≤ D)
    (hI : I ≤ D ^ d) (hpower : deltaSeedCostConstant d * D ^ deltaSeedPower d ≤ h) :
    let q := denseBoxCount D d
    let F := nvDenseFactor D d * (q + 1) ^ d
    let J := (2 * q * F) ^ d
    q * (c * h) + J ^ 2 ≤ h ^ 2 ∧
      ∀ L : Fin d → ℕ, (∀ i, 0 < L i) → ∀ i,
        2 * F * (GeneralizedAP.deltaSeedLatticeFactor d * (I * (L i + 1) + 1) +
          J * L i + 1) ≤ 2 * (h * L i) := by
  let q := denseBoxCount D d
  let F := nvDenseFactor D d * (q + 1) ^ d
  let J := (2 * q * F) ^ d
  let b := (9 * d + 4) * d
  let K := GeneralizedAP.deltaSeedLatticeFactor d
  obtain ⟨hq, hF, hJ⟩ := delta_coarse_filling_polynomial_bounds d D hD
  change q ≤ 256 * d * D ^ 4 at hq
  change F ≤ deltaSeedSideConstant d * D ^ (9 * d) at hF
  change J ≤ deltaSeedStepConstant d ^ d * D ^ b at hJ
  obtain ⟨hE5, hE2, hdb, hEb⟩ := delta_seed_cost_exponents d
  have hh : 0 < h := (Nat.mul_pos (deltaSeedCostConstant_pos d)
    (pow_pos hD _)).trans_le hpower
  have hJ2 : J ^ 2 ≤ deltaSeedStepConstant d ^ (d * 2) * D ^ deltaSeedPower d := by
    calc
      _ ≤ (deltaSeedStepConstant d ^ d * D ^ b) ^ 2 := Nat.pow_le_pow_left hJ 2
      _ = deltaSeedStepConstant d ^ (d * 2) * D ^ (b * 2) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ deltaSeedStepConstant d ^ (d * 2) * D ^ deltaSeedPower d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD hE2)
  have hcost : q * (c * h) ≤ (256 * d) * D ^ deltaSeedPower d * h := by
    calc
      _ = (q * c) * h := by ring
      _ ≤ ((256 * d * D ^ 4) * D) * h := Nat.mul_le_mul_right h (Nat.mul_le_mul hq hc)
      _ = (256 * d) * D ^ 5 * h := by rw [pow_succ]; ring
      _ ≤ (256 * d) * D ^ deltaSeedPower d * h :=
        Nat.mul_le_mul_right h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD hE5))
  have hI' : I ≤ D ^ b := hI.trans (Nat.pow_le_pow_right hD hdb)
  have hone : 1 ≤ D ^ b := one_le_pow₀ hD
  have hmargin : K * (2 * I + 1) + J + 1 ≤
      (3 * K + deltaSeedStepConstant d ^ d + 1) * D ^ b := by
    have hfirst : K * (2 * I + 1) ≤ (3 * K) * D ^ b := by
      calc
        _ ≤ K * (3 * D ^ b) := Nat.mul_le_mul_left K (by omega)
        _ = _ := by ring
    calc
      _ ≤ (3 * K) * D ^ b + deltaSeedStepConstant d ^ d * D ^ b + D ^ b :=
        Nat.add_le_add (Nat.add_le_add hfirst hJ) hone
      _ = _ := by ring
  have hwidth : F * (K * (2 * I + 1) + J + 1) ≤ h := by
    calc
      _ ≤ (deltaSeedSideConstant d * D ^ (9 * d)) *
          ((3 * K + deltaSeedStepConstant d ^ d + 1) * D ^ b) := Nat.mul_le_mul hF hmargin
      _ = (deltaSeedSideConstant d * (3 * K + deltaSeedStepConstant d ^ d + 1)) *
          D ^ (9 * d + b) := by rw [pow_add]; ring
      _ ≤ (deltaSeedSideConstant d * (3 * K + deltaSeedStepConstant d ^ d + 1)) *
          D ^ deltaSeedPower d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD hEb)
      _ ≤ deltaSeedCostConstant d * D ^ deltaSeedPower d := by
        apply Nat.mul_le_mul_right
        dsimp only [deltaSeedCostConstant, K]
        omega
      _ ≤ h := hpower
  constructor
  · calc
      q * (c * h) + J ^ 2 ≤ (256 * d) * D ^ deltaSeedPower d * h +
          (deltaSeedStepConstant d ^ (d * 2) * D ^ deltaSeedPower d) * h :=
        Nat.add_le_add hcost (hJ2.trans (Nat.le_mul_of_pos_right _ hh))
      _ = (256 * d + deltaSeedStepConstant d ^ (d * 2)) * D ^ deltaSeedPower d * h := by ring
      _ ≤ deltaSeedCostConstant d * D ^ deltaSeedPower d * h := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        dsimp only [deltaSeedCostConstant]
        omega
      _ ≤ h * h := Nat.mul_le_mul_right h hpower
      _ = h ^ 2 := (pow_two _).symm
  · intro L hL i
    have hinner : I * (L i + 1) + 1 ≤ (2 * I + 1) * L i := by have := hL i; nlinarith
    have hsmall : K * (I * (L i + 1) + 1) + J * L i + 1 ≤
        (K * (2 * I + 1) + J + 1) * L i := by
      have hh' := Nat.mul_le_mul_left K hinner
      have := hL i
      nlinarith
    calc
      _ ≤ 2 * F * ((K * (2 * I + 1) + J + 1) * L i) := Nat.mul_le_mul_left _ hsmall
      _ = 2 * (F * (K * (2 * I + 1) + J + 1)) * L i := by ring
      _ ≤ 2 * h * L i := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hwidth)
      _ = 2 * (h * L i) := by ring

end Erdos587.CFP
