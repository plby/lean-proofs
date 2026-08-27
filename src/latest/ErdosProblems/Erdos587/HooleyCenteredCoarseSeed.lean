import ErdosProblems.Erdos587.HooleyCoarseCoordinateSeed
import ErdosProblems.Erdos587.HooleyProductSides
import ErdosProblems.Erdos587.CoordinateResidueCorrection

/-! # A symmetric coarse-lattice seed with bounded coordinate multipliers -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

lemma delta_fullGAP_axis_eval {d : ℕ} (P : NVFullGAP d) (haxis : P.AxisAligned)
    (x : Fin d → ℕ) (j : Fin d) : P.eval x j = P.base j + (x j : ℤ) * P.step j j := by
  simp only [NVFullGAP.eval, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_eq_single j
  · intro i _ hij
    rw [haxis i j (fun h => hij (Fin.ext h)), mul_zero]
  · simp

theorem delta_fullGAP_centered_box {d : ℕ} (P : NVFullGAP d) (haxis : P.AxisAligned)
    (ha : ∀ i, P.step i i ≠ 0) (R : Fin d → ℕ) (hR : ∀ i, 2 * R i ≤ P.length i) :
    ∃ c ∈ P.carrier, ∀ w ∈ coordinateMultiples (fun i => P.step i i),
      (∀ i, |w i| ≤ (R i : ℤ)) → c + w ∈ P.carrier := by
  classical
  let mid : Fin d → ℕ := fun i => P.length i / 2
  have hmid : mid ∈ P.coeffBox := by
    rw [NVFullGAP.coeffBox, Finset.mem_Icc, Pi.le_def]
    exact ⟨fun _ => Nat.zero_le _, fun i => Nat.div_le_self _ _⟩
  refine ⟨P.eval mid, NVFullGAP.mem_carrier_iff.mpr ⟨mid, hmid, rfl⟩, ?_⟩
  intro w hw hbounds
  have hdiv : ∀ i, P.step i i ∣ w i := hw
  choose k hk using hdiv
  have hkbound (i : Fin d) : |k i| ≤ (R i : ℤ) := by
    have hprod : |P.step i i| * |k i| ≤ (R i : ℤ) := by
      have hbi := hbounds i
      rwa [hk i, abs_mul] at hbi
    have hstep := Int.one_le_abs (ha i)
    have hk0 := abs_nonneg (k i)
    nlinarith
  have hcoeff (i : Fin d) : 0 ≤ (mid i : ℤ) + k i ∧ (mid i : ℤ) + k i ≤ P.length i := by
    have hmidlow : R i ≤ mid i := by dsimp [mid]; have := hR i; omega
    have hmidhigh : mid i + R i ≤ P.length i := by dsimp [mid]; have := hR i; omega
    have hlo : (R i : ℤ) ≤ mid i := by exact_mod_cast hmidlow
    have hhi : (mid i : ℤ) + R i ≤ P.length i := by exact_mod_cast hmidhigh
    obtain ⟨hkl, hku⟩ := abs_le.mp (hkbound i)
    omega
  let x : Fin d → ℕ := fun i => ((mid i : ℤ) + k i).toNat
  have hxcast (i : Fin d) : (x i : ℤ) = (mid i : ℤ) + k i := Int.toNat_of_nonneg (hcoeff i).1
  have hx : x ∈ P.coeffBox := by
    rw [NVFullGAP.coeffBox, Finset.mem_Icc, Pi.le_def]
    refine ⟨fun _ => Nat.zero_le _, fun i => ?_⟩
    exact Int.toNat_le.mpr (hcoeff i).2
  apply NVFullGAP.mem_carrier_iff.mpr
  refine ⟨x, hx, ?_⟩
  funext i
  change P.eval x i = P.eval mid i + w i
  rw [delta_fullGAP_axis_eval P haxis, delta_fullGAP_axis_eval P haxis, hxcast, hk i]
  ring

theorem delta_centered_coarse_seed_of_bounds {d : ℕ} (U : Finset (Fin d → ℤ))
    (z : Fin d → ℤ) (P : NVFullGAP d) (hproper : P.Proper) (haxis : P.AxisAligned)
    (hsub : ({z} : Finset (Fin d → ℤ)) + P.carrier ⊆ U.subsetSum)
    (L R : Fin d → ℕ) (F q : ℕ) (hF : 0 < F)
    (hcard : (nvCoordBox L).card ≤ F * P.carrier.card)
    (hexc : ∀ i, |(P.length i : ℤ) * P.step i i| ≤ (q : ℤ) * L i)
    (hlarge : ∀ i, 2 * (F * (q + 1) ^ d) * (R i + 1) ≤ L i) :
    ∃ a : Fin d → ℤ, (∀ i, a i ≠ 0 ∧ |a i| ≤ (2 * q * (F * (q + 1) ^ d) : ℕ)) ∧
      ∃ c ∈ U.subsetSum, ∀ w ∈ coordinateMultiples a,
        (∀ i, |w i| ≤ (R i : ℤ)) → c + w ∈ U.subsetSum := by
  let B := F * (q + 1) ^ d
  have hB : 0 < B := by dsimp [B]; positivity
  have hside := delta_coarse_coordinate_side_bound P hproper haxis L F q hcard hexc
  have hsteps := delta_coarse_step_bound P hproper haxis L B q hB hside hexc
    (fun i => (Nat.le_mul_of_pos_right (2 * B) (Nat.succ_pos _)).trans (hlarge i))
  have hR (i : Fin d) : 2 * R i ≤ P.length i :=
    delta_coarse_radius_bound hB (hside i) (hlarge i)
  obtain ⟨c, hc, hbox⟩ := delta_fullGAP_centered_box P haxis (fun i => (hsteps i).2.1) R hR
  refine ⟨fun i => P.step i i, fun i => (hsteps i).2, z + c,
    hsub (Finset.mem_add.mpr ⟨z, Finset.mem_singleton_self _, c, hc, rfl⟩), ?_⟩
  intro w hw hbounds
  exact hsub (Finset.mem_add.mpr
    ⟨z, Finset.mem_singleton_self _, c + w, hbox w hw hbounds, (add_assoc _ _ _).symm⟩)

end Erdos587.CFP
