import ErdosProblems.Erdos1148.PadicCongruences
import ErdosProblems.Erdos1148.ResidueFibers

/-!
# Uniform square-root counts modulo prime powers

If `D` is nonzero, the number of square roots of `D` modulo `p^n` is at most
`4 * p^(valuation(D)/2)`, uniformly in `n`, including the prime two.
-/

namespace Erdos1148.DukeArithmetic

noncomputable def squareRootResidues (p : ℕ) [Fact p.Prime] (n : ℕ) (D : PadicInt p) :
    Finset (ZMod (p ^ n)) := Finset.univ.filter (fun x => x ^ 2 = PadicInt.toZModPow n D)

lemma mem_squareRootResidues_iff (p : ℕ) [Fact p.Prime] (n : ℕ)
    (D : PadicInt p) (x : ZMod (p ^ n)) :
    x ∈ squareRootResidues p n D ↔ (p : PadicInt p) ^ n ∣ (x.val : PadicInt p) ^ 2 - D := by
  rw [squareRootResidues, Finset.mem_filter, and_iff_right (Finset.mem_univ _),
    padic_pow_dvd_sub_iff_reduction_eq]
  simp only [map_pow, map_natCast, ZMod.natCast_zmod_val]

lemma squareRootResidues_card_of_depth_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (D : PadicInt p) (hD : D ≠ 0) (hn : n ≤ D.valuation) :
    (squareRootResidues p n D).card ≤ p ^ (D.valuation / 2) := by
  classical
  let m := (n + 1) / 2
  have hm : m ≤ n := by dsimp [m]; omega
  let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
  have hsub : squareRootResidues p n D ⊆ Finset.univ.filter (fun x => f x = 0) := by
    intro x hx
    have hcongr := (mem_squareRootResidues_iff p n D x).mp hx
    have hDdiv := (padic_pow_dvd_iff_le_valuation p D hD n).mpr hn
    have hsq : (p : PadicInt p) ^ n ∣ (x.val : PadicInt p) ^ 2 := by
      simpa only [sub_add_cancel] using dvd_add hcongr hDdiv
    have hdiv : (p : PadicInt p) ^ m ∣ (x.val : PadicInt p) := by
      by_cases hx0 : (x.val : PadicInt p) = 0
      · simp [hx0]
      have hval := (padic_pow_dvd_iff_le_valuation p _ (pow_ne_zero 2 hx0) n).mp hsq
      rw [PadicInt.valuation_pow] at hval
      apply (padic_pow_dvd_iff_le_valuation p _ hx0 m).mpr
      dsimp [m]
      omega
    have hred : PadicInt.toZModPow m (x.val : PadicInt p) = 0 := by
      have h := (padic_pow_dvd_sub_iff_reduction_eq p m (x.val : PadicInt p) 0).mp
        (by simpa only [sub_zero] using hdiv)
      simpa only [map_zero] using h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rwa [padic_residue_lift_reduction p n m hm] at hred
  calc
    _ ≤ (Finset.univ.filter (fun x => f x = 0)).card := Finset.card_le_card hsub
    _ = p ^ (n - m) := card_zmod_reduction_fiber p n m hm 0
    _ ≤ p ^ (D.valuation / 2) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (by dsimp [m]; omega)

theorem squareRootResidues_card_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (D : PadicInt p) (hD : D ≠ 0) :
    (squareRootResidues p n D).card ≤ 4 * p ^ (D.valuation / 2) := by
  classical
  by_cases hn : n ≤ D.valuation
  · exact (squareRootResidues_card_of_depth_le p n D hD hn).trans (by omega)
  by_cases hempty : (squareRootResidues p n D).Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  obtain ⟨y, hy⟩ := hempty
  have hcongrY := (mem_squareRootResidues_iff p n D y).mp hy
  have hvalY := valuation_eq_of_deep_congruence p ((y.val : PadicInt p) ^ 2) D hD n
    (by omega) hcongrY
  have hy0 : (y.val : PadicInt p) ≠ 0 := fun h => hvalY.1 (by simp [h])
  have hval : (y.val : PadicInt p).valuation = D.valuation / 2 := by
    rw [PadicInt.valuation_pow] at hvalY
    omega
  let m := n - (D.valuation / 2 + (2 : PadicInt p).valuation)
  have hm : m ≤ n := Nat.sub_le _ _
  let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
  let b := PadicInt.toZModPow m (y.val : PadicInt p)
  let Splus := Finset.univ.filter (fun x : ZMod (p ^ n) => f x = b)
  let Sminus := Finset.univ.filter (fun x : ZMod (p ^ n) => f x = -b)
  have hsub : squareRootResidues p n D ⊆ Splus ∪ Sminus := by
    intro x hx
    have hcongrX := (mem_squareRootResidues_iff p n D x).mp hx
    have hxy : (p : PadicInt p) ^ n ∣
        (x.val : PadicInt p) ^ 2 - (y.val : PadicInt p) ^ 2 := by
      convert dvd_sub hcongrX hcongrY using 1
      ring
    have hclose := square_congruence_close_to_sign p (x.val : PadicInt p)
      (y.val : PadicInt p) hy0 n hxy
    rw [hval] at hclose
    rcases hclose with hminus | hplus
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have h := (padic_pow_dvd_sub_iff_reduction_eq p m _ _).mp hminus
      rwa [padic_residue_lift_reduction p n m hm] at h
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hd : (p : PadicInt p) ^ m ∣ (x.val : PadicInt p) - -(y.val : PadicInt p) := by
        simpa only [sub_neg_eq_add] using hplus
      have h := (padic_pow_dvd_sub_iff_reduction_eq p m _ _).mp hd
      rwa [padic_residue_lift_reduction p n m hm, map_neg] at h
  have hcplus : Splus.card = p ^ (n - m) := card_zmod_reduction_fiber p n m hm b
  have hcminus : Sminus.card = p ^ (n - m) := card_zmod_reduction_fiber p n m hm (-b)
  have hv2 : p ^ (2 : PadicInt p).valuation ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    exact (padic_pow_dvd_natCast_iff p _ 2).mp (padic_pow_valuation_dvd p 2)
  have hpow : p ^ (n - m) ≤ p ^ (D.valuation / 2) * p ^ (2 : PadicInt p).valuation := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    dsimp [m]
    omega
  calc
    _ ≤ (Splus ∪ Sminus).card := Finset.card_le_card hsub
    _ ≤ Splus.card + Sminus.card := Finset.card_union_le _ _
    _ = 2 * p ^ (n - m) := by rw [hcplus, hcminus]; omega
    _ ≤ 4 * p ^ (D.valuation / 2) := by
      have hmul := Nat.mul_le_mul_left (p ^ (D.valuation / 2)) hv2
      omega

end Erdos1148.DukeArithmetic
