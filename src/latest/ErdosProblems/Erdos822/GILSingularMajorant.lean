/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.DeterminantSize

/-! # The singular-factor majorant on the constructed GIL family -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_gil_singularFactor_le_charge {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ k r q m' h U : ℕ,
      (k, r, q) ∈ oddCofactorTriples N → k * r * q ∈ gilCofactors N S C →
      m' ∈ gilCofactors N S C → k * r * q ≠ m' →
      (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty →
      h ∣ shiftedTotient m' → Nat.log 2 N ≤ U →
      Erdos851.singularFactor (reducedTotientDet (k * r * q) m') (b1Cutoff N) U ≤
        K * (1 + ((b1DoubleLog N : ℝ) / Real.log (b1DoubleLog N : ℝ)) *
          smallDeterminantMass (Nat.log 2 N) (b1DoubleLog N) k r q m' h) := by
  obtain ⟨D, hD, hmajor⟩ := exists_singularFactor_cutoff_majorant
  obtain ⟨M, hM, hMertens⟩ := Erdos851.exists_oneShift_dimension_bound
  let E := Real.exp (2 * (59 + C))
  let K := 8 * M * E * (Real.exp 2 + 2 * D)
  have hE : 0 < E := Real.exp_pos _
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 2,
    eventually_gilCofactors_full_primeMass_le hS C] with N hN hy hmass
  let y := b1Cutoff N
  let Z := b1DoubleLog N
  let L := Nat.log 2 N
  have hyZ : y ≤ Z := nthRoot_le_self_of_pos (by norm_num : 0 < 4)
  have hZL : Z ≤ L := Nat.log_le_self 2 L
  have hZ : 2 ≤ Z := hy.trans hyZ
  have hL : 2 ≤ L := hZ.trans hZL
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hratioLow : Real.log (Z : ℝ) / Real.log (y : ℝ) ≤ 8 := by
    simpa [y, Z, b1Cutoff] using
      (log_div_log_slowSieveCutoff_le (N := b1DoubleLog N) (S := 1)
        (by norm_num) (by simpa [b1Cutoff] using hy))
  have hV : Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity y Z ≤ 8 * M := by
    have h := hMertens y Z hy hyZ
    have h' := mul_le_mul_of_nonneg_left hratioLow hM.le
    nlinarith only [h, h']
  have hratioMid : Real.log (L : ℝ) / Real.log (Z : ℝ) ≤ 2 * ((Z : ℝ) / Real.log (Z : ℝ)) := by
    have hlog := realLog_le_twice_natLog hL
    have h := div_le_div_of_nonneg_right hlog hlogZ.le
    simpa only [Z, L, b1DoubleLog, mul_div_assoc] using h
  intro k r q m' h U ht hm hm' hne hsupport hh hLU
  let m := k * r * q
  let H := reducedTotientDet m m'
  let f := smallDeterminantMass L Z k r q m' h
  have hf : 0 ≤ f := smallDeterminantMass_nonneg _ _ _ _ _ _ _
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmraw' := gilCofactors_subset_oddRaw N S C hm'
  have hmpos := oddRawCofactors_pos hmraw
  have hmpos' := oddRawCofactors_pos hmraw'
  have hHpos : 0 < H := reducedTotientDet_pos_of_odd_supported hN hmraw hmraw' hne hsupport
  have hHsize : H ≤ N ^ 28 := reducedTotientDet_le_pow_twenty_eight hmraw hmraw'
  have hφne : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr hmpos).ne'
  have hsne : shiftedTotient m' ≠ 0 := by dsimp [shiftedTotient]; omega
  have htail := sum_inv_primeTail_at_natLog_le_fifty_six hN hHpos hHsize
  have hφtail := gilCofactors_totientTail hm
  have hfull := hmass m' hm'
  have hExp : Real.exp (2 * ((∑ p ∈ primeFactorsAbove H L, (1 : ℝ) / p) +
      (∑ p ∈ primeFactorsAbove (Nat.totient m) Z, (1 : ℝ) / p) +
        primeDivisorReciprocalMass (shiftedTotient m'))) ≤ E := by
    apply Real.exp_le_exp.mpr
    dsimp [m, H, L, Z] at *
    linarith only [htail, hφtail, hfull]
  have hgood := goodDeterminantPrimeMass_le_smallDeterminantMass (U := L) (z := Z) hN ht hh
  have hinner : Real.exp 2 + (D * (Real.log (L : ℝ) / Real.log (Z : ℝ))) *
      (∑ p ∈ goodDeterminantPrimes H (Nat.totient m) (shiftedTotient m') Z L, (1 : ℝ) / p) ≤
        (Real.exp 2 + 2 * D) * (1 + ((Z : ℝ) / Real.log (Z : ℝ)) * f) := by
    have hR0 : 0 ≤ (Z : ℝ) / Real.log (Z : ℝ) := by positivity
    have hRf : 0 ≤ ((Z : ℝ) / Real.log (Z : ℝ)) * f := mul_nonneg hR0 hf
    calc
      _ ≤ Real.exp 2 + (D * (2 * ((Z : ℝ) / Real.log (Z : ℝ)))) * f :=
        add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left hratioMid hD.le) hgood
          (by positivity) (by positivity))
      _ ≤ _ := by nlinarith only [hRf, hD, Real.exp_pos (2 : ℝ)]
  have hbase := hmajor H (Nat.totient m) (shiftedTotient m') y Z L U
    hHpos.ne' hφne hsne hy hyZ hZL hLU
  apply hbase.trans
  calc
    _ ≤ (8 * M) * E * ((Real.exp 2 + 2 * D) * (1 + ((Z : ℝ) / Real.log (Z : ℝ)) * f)) := by
      apply mul_le_mul (mul_le_mul hV hExp (Real.exp_pos _).le (by positivity)) hinner
        (by positivity) (by positivity)
    _ = _ := by dsimp [K, f, Z]; ring

#print axioms exists_eventually_gil_singularFactor_le_charge

theorem exists_eventually_gil_fullSingularFactor_le_charge {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ k r q m' h U : ℕ,
      (k, r, q) ∈ oddCofactorTriples N → k * r * q ∈ gilCofactors N S C →
      m' ∈ gilCofactors N S C → k * r * q ≠ m' →
      (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty →
      h ∣ shiftedTotient m' → Nat.log 2 N ≤ U →
      Erdos851.singularFactor (reducedTotientDet (k * r * q) m') 2 U ≤
        K * Real.log (b1Cutoff N : ℝ) *
          (1 + ((b1DoubleLog N : ℝ) / Real.log (b1DoubleLog N : ℝ)) *
            smallDeterminantMass (Nat.log 2 N) (b1DoubleLog N) k r q m' h) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_gil_singularFactor_le_charge hS C
  obtain ⟨M, hM, hMertens⟩ := Erdos851.exists_oneShift_dimension_bound
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨K * M / Real.log 2, by positivity, ?_⟩
  filter_upwards [hbound, tendsto_b1Cutoff_atTop.eventually_ge_atTop 2] with N hbound hy
  intro k r q m' h U ht hm hm' hne hsupport hh hLU
  have hyZ : b1Cutoff N ≤ b1DoubleLog N := nthRoot_le_self_of_pos (by norm_num : 0 < 4)
  have hyU : b1Cutoff N ≤ U := hyZ.trans ((Nat.log_le_self 2 (Nat.log 2 N)).trans hLU)
  have hlogy : 0 < Real.log (b1Cutoff N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b1Cutoff N))
  have hlogZ : 0 < Real.log (b1DoubleLog N : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < b1DoubleLog N by omega))
  have hsmall : Erdos851.singularFactor (reducedTotientDet (k * r * q) m') 2 (b1Cutoff N) ≤
      M * (Real.log (b1Cutoff N : ℝ) / Real.log 2) := by
    rw [singularFactor_eq_primeSingularProduct]
    exact (primeSingularProduct_le_inverseEuler (Finset.filter_subset _ _)).trans
      (hMertens 2 (b1Cutoff N) (by norm_num) hy)
  rw [singularFactor_split _ hy hyU]
  calc
    _ ≤ (M * (Real.log (b1Cutoff N : ℝ) / Real.log 2)) *
        (K * (1 + ((b1DoubleLog N : ℝ) / Real.log (b1DoubleLog N : ℝ)) *
          smallDeterminantMass (Nat.log 2 N) (b1DoubleLog N) k r q m' h)) :=
      mul_le_mul hsmall (hbound k r q m' h U ht hm hm' hne hsupport hh hLU)
        (singularFactor_nonneg _ _ _) (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_gil_fullSingularFactor_le_charge

end Erdos822
