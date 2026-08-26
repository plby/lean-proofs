import ErdosProblems.Erdos327.Analytic.Regularity
import ErdosProblems.Erdos327.AnalyticAssembly
import ErdosProblems.Erdos327.SourceCoordinates

/-!
# Coordinates for a deleted source vertex

This file strengthens the elementary source-conflict parametrization with
the interval and score inequalities used by the analytic estimate.
-/

namespace Erdos327

open Finset
open scoped ArithmeticFunction.Omega

/-- A score-oriented conflict from the canonical regular source admits
positive coprime coordinates and a positive residual factor.  The
generous bounds `v ≤ 3u` and `u+v ≤ 4u` absorb the one-point floor issue
at the lower endpoint `N/2`. -/
theorem sourceBad_coordinates
    {L N b : ℕ} {A K : ℝ} (hN : 2 ≤ N)
    (hb : b ∈ rankBad (upto N)
      (Analytic.regularSource L A K N)
      ArithmeticFunction.cardFactors) :
    ∃ g u v d : ℕ,
      0 < g ∧ 0 < u ∧ 0 < v ∧ 0 < d ∧
      Nat.Coprime u v ∧
      b = g * u ∧
      2 * b = u * (u + v) * d ∧
      u ≤ N ∧ v ≤ 3 * u ∧ u + v ≤ 4 * u ∧
      ArithmeticFunction.cardFactors v ≤
        ArithmeticFunction.cardFactors u ∧
      (u, v) ≠ (1, 1) ∧
      Analytic.Rough L b ∧
      Analytic.CutoffRegular L A K b := by
  rcases mem_rankBad.mp hb with
    ⟨hbSource, c, hcU, hcb, hscore, hconflict⟩
  have hbData := Analytic.mem_regularSource.mp hbSource
  have hbpos : 0 < b := by omega
  have hcBounds := mem_upto.mp hcU
  have hcpos : 0 < c := by omega
  rcases sawin_coordinates_of_conflictTwo hbpos hconflict with
    ⟨g, u, v, _hgcd, hbu, hcv, hcop, hproduct⟩
  have hg : 0 < g := by
    by_contra h
    have : g = 0 := Nat.eq_zero_of_not_pos h
    rw [hbu, this, zero_mul] at hbpos
    omega
  have hu : 0 < u := by
    by_contra h
    have : u = 0 := Nat.eq_zero_of_not_pos h
    rw [hbu, this, mul_zero] at hbpos
    omega
  have hv : 0 < v := by
    by_contra h
    have : v = 0 := Nat.eq_zero_of_not_pos h
    rw [hcv, this, mul_zero] at hcpos
    omega
  rcases hproduct with ⟨d, hdEq⟩
  have htwoEq : 2 * b = u * (u + v) * d := hdEq
  have hd : 0 < d := by
    by_contra h
    have : d = 0 := Nat.eq_zero_of_not_pos h
    have htwoPos : 0 < 2 * b := by omega
    rw [htwoEq, this, mul_zero] at htwoPos
    omega
  have huB : u ≤ b := by
    rw [hbu]
    exact Nat.le_mul_of_pos_left u hg
  have huN : u ≤ N := huB.trans hbData.2.1
  have hNle3b : N ≤ 3 * b := by
    have hbLower := hbData.1
    omega
  have hc3b : c ≤ 3 * b := hcBounds.2.trans hNle3b
  have hgvgu : g * v ≤ g * (3 * u) := by
    calc
      g * v = c := hcv.symm
      _ ≤ 3 * b := hc3b
      _ = g * (3 * u) := by rw [hbu]; ring
  have hv3u : v ≤ 3 * u :=
    le_of_mul_le_mul_left hgvgu (by exact_mod_cast hg)
  have hx4u : u + v ≤ 4 * u := by omega
  have hOmega : ArithmeticFunction.cardFactors v ≤
      ArithmeticFunction.cardFactors u := by
    rw [hbu, hcv,
      ArithmeticFunction.cardFactors_mul hg.ne' hu.ne',
      ArithmeticFunction.cardFactors_mul hg.ne' hv.ne'] at hscore
    omega
  have hpair : (u, v) ≠ (1, 1) := by
    intro huv
    have hu1 : u = 1 := congrArg Prod.fst huv
    have hv1 : v = 1 := congrArg Prod.snd huv
    apply hcb
    rw [hbu, hcv, hu1, hv1]
  exact ⟨g, u, v, d, hg, hu, hv, hd, hcop, hbu, htwoEq,
    huN, hv3u, hx4u, hOmega, hpair, hbData.2.2.1,
    hbData.2.2.2⟩

end Erdos327
