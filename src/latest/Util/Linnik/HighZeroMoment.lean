import Util.Linnik.FiniteMoment
import ErdosProblems.Erdos48.GallagherPowerDensity

/-!
# The uniform high-zero exponential moment

Apply log-free density to the full finite family of primitive zeros with
real part at least `15/16`.  The bound is absolute once the exponential
moment parameter dominates the density exponent.
-/

namespace Linnik

open Complex Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

local instance conductorSubtype_neZero {Q : ℕ} (q : ↥(Finset.Ioc 1 Q)) : NeZero q.val :=
  ⟨by have hq := (Finset.mem_Ioc.mp q.property).1; omega⟩

noncomputable abbrev upperHighZeroIndex (Q : ℕ) (T : ℝ) :=
  (q : ↥(Finset.Ioc 1 Q)) × (psi : primitiveCharacters q.val) ×
    ↥(highZeroRectangle (Finset.mem_Ioc.mp q.property).1 psi.1 psi.2 (1 / 16) T)

noncomputable instance upperHighZeroIndex_fintype (Q : ℕ) (T : ℝ) :
    Fintype (upperHighZeroIndex Q T) := by
  unfold upperHighZeroIndex
  infer_instance

noncomputable def upperHighZeroGap {Q : ℕ} {T : ℝ} (i : upperHighZeroIndex Q T) : ℝ :=
  1 - i.2.2.val.re

noncomputable def upperHighZeroWeight {Q : ℕ} {T : ℝ} (i : upperHighZeroIndex Q T) : ℝ :=
  analyticOrderNatAt (DirichletCharacter.LFunction i.2.1.1) i.2.2.val

theorem upperHighZeroGap_bounds {Q : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (i : upperHighZeroIndex Q T) :
    0 ≤ upperHighZeroGap i ∧ upperHighZeroGap i ≤ 1 / 16 := by
  have h := (mem_highZeroRectangle_iff (Finset.mem_Ioc.mp i.1.property).1
    i.2.1.1 i.2.1.2 (by norm_num : (1 / 16 : ℝ) ≤ 1) hT i.2.2.val).mp i.2.2.property
  unfold upperHighZeroGap
  constructor <;> linarith [h.2.1, h.2.2.1]

theorem filtered_smallRectangle_mass_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (psi : primitiveCharacters q) {T H eta : ℝ}
    (hT : 0 ≤ T) (hH : 0 < H) (heta : eta ≤ 1) (j : ℕ)
    (hEta : (j : ℝ) + 1 = eta * H) :
    (∑ rho ∈ (highZeroRectangle hq psi.1 psi.2 (1 / 16) T).filter
      (fun rho ↦ H * (1 - rho.re) < j + 1),
      (analyticOrderNatAt (DirichletCharacter.LFunction psi.1) rho : ℝ)) ≤
      (highZeroRectangleMass hq psi.1 psi.2 eta T : ℝ) := by
  have hsub : (highZeroRectangle hq psi.1 psi.2 (1 / 16) T).filter
      (fun rho ↦ H * (1 - rho.re) < j + 1) ⊆ highZeroRectangle hq psi.1 psi.2 eta T := by
    intro rho hrho
    obtain ⟨hrho, hgap⟩ := Finset.mem_filter.mp hrho
    have h := (mem_highZeroRectangle_iff hq psi.1 psi.2
      (by norm_num : (1 / 16 : ℝ) ≤ 1) hT rho).mp hrho
    apply (mem_highZeroRectangle_iff hq psi.1 psi.2 heta hT rho).mpr
    refine ⟨h.1, ?_, h.2.2⟩
    rw [hEta, mul_comm H] at hgap
    have hdelta := (mul_lt_mul_iff_of_pos_right hH).mp hgap
    linarith
  simp only [highZeroRectangleMass, Nat.cast_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.cast_nonneg _)

theorem upperHighZero_cumulative_weight_le
    {Q : ℕ} {T H eta : ℝ} (hT : 0 ≤ T) (hH : 0 < H)
    (heta : eta ≤ 1) (j : ℕ) (hEta : (j : ℝ) + 1 = eta * H) :
    (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).filter
      (fun i ↦ H * upperHighZeroGap i < j + 1), upperHighZeroWeight i) ≤
      (primitiveHighZeroMass Q eta T : ℝ) := by
  rw [Finset.sum_filter]
  simp only [upperHighZeroIndex, upperHighZeroGap, upperHighZeroWeight]
  unfold primitiveHighZeroMass
  push_cast
  rw [Finset.sum_subtype (Finset.Ioc 1 Q) (fun _ ↦ Iff.rfl)]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum
  intro psi _
  rw [primitiveHighZeroMassAt_eq (Finset.mem_Ioc.mp q.property).1]
  have h := filtered_smallRectangle_mass_le (Finset.mem_Ioc.mp q.property).1
    psi hT hH heta j hEta
  rw [Finset.sum_filter, Finset.sum_subtype
    (highZeroRectangle (Finset.mem_Ioc.mp q.property).1 psi.1 psi.2 (1 / 16) T)
    (fun _ ↦ Iff.rfl)] at h
  exact h

theorem upperHighZero_moment_le_of_density
    {Q : ℕ} {T H C c : ℝ} (hT : 0 ≤ T) (hH : 16 ≤ H)
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hdensity : ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 → 1 ≤ eta * H →
      (primitiveHighZeroMass Q eta T : ℝ) ≤ C * Real.exp (c * eta * H)) :
    (∑ i : upperHighZeroIndex Q T,
      upperHighZeroWeight i * Real.exp (-(c + 2) * (H * upperHighZeroGap i))) ≤
      2 * C * Real.exp c := by
  let N : ℕ := ⌊H / 16⌋₊
  have hH₀ : 0 < H := by linarith
  have hN : (N : ℝ) ≤ H / 16 := Nat.floor_le (by positivity)
  apply exp_moment_le_of_cumulative_bound Finset.univ
    (fun i : upperHighZeroIndex Q T ↦ H * upperHighZeroGap i) upperHighZeroWeight N hC hc
  · intro i _
    exact Nat.cast_nonneg _
  · intro i _
    exact mul_nonneg hH₀.le (upperHighZeroGap_bounds hT i).1
  · intro i _
    have hgap := (upperHighZeroGap_bounds hT i).2
    have hfloor : H / 16 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith
  · intro j hj
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    let eta : ℝ := ((j : ℝ) + 1) / H
    have hEta : (j : ℝ) + 1 = eta * H := (div_mul_cancel₀ _ hH₀.ne').symm
    have heta₀ : 0 < eta := by dsimp [eta]; positivity
    have heta₈ : eta ≤ 1 / 8 := by
      apply (div_le_iff₀ hH₀).mpr
      linarith
    have hetaH : 1 ≤ eta * H := by rw [← hEta]; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hcumulative := upperHighZero_cumulative_weight_le (Q := Q) hT hH₀
      (heta₈.trans (by norm_num)) j hEta
    apply hcumulative.trans
    have h := hdensity eta heta₀ heta₈ hetaH
    have heq : c * eta * H = c * ((j : ℝ) + 1) := by rw [hEta]; ring
    simpa only [heq] using h

/-- Gallagher's log-free density gives an absolute exponential moment,
uniformly once the logarithmic scale exceeds an absolute threshold. -/
theorem exists_upperHighZero_moment_bound :
    ∃ H₀ C c : ℝ, 16 ≤ H₀ ∧ 0 < C ∧ 0 < c ∧
      ∀ Q T : ℕ, 2 ≤ Q → 2 ≤ T →
        H₀ ≤ Real.log ((Q : ℝ) * ((T : ℝ) + 2)) →
        (∑ i : upperHighZeroIndex Q T,
          upperHighZeroWeight i * Real.exp (-c *
            (Real.log ((Q : ℝ) * ((T : ℝ) + 2)) * upperHighZeroGap i))) ≤ C := by
  obtain ⟨K, Camp, C, c, hK, hC, hc, hdensity⟩ :=
    exists_gallagher_logFreeDensity_power_bound (by norm_num : (0 : ℝ) < 1)
  have hlog := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 40 by norm_num)
  obtain ⟨H₁, hH₁⟩ := Filter.eventually_atTop.mp hlog
  let D : ℝ := 20 * (K + Camp + 2 + Real.log 2)
  let H₀ : ℝ := max 16 (max H₁ (2 * max D 0))
  refine ⟨H₀, 2 * C * Real.exp c, c + 2, le_max_left _ _, by positivity,
    by linarith, ?_⟩
  intro Q T hQ hT hH
  let H : ℝ := Real.log ((Q : ℝ) * ((T : ℝ) + 2))
  have hH₁₆ : 16 ≤ H := (le_max_left 16 _).trans hH
  have hH₀ : 0 ≤ H := by linarith
  have hlogH := hH₁ H ((le_max_left H₁ _).trans ((le_max_right 16 _).trans hH))
  have hlogNonneg : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  simp only [id, Real.norm_of_nonneg hH₀, Real.norm_of_nonneg hlogNonneg] at hlogH
  have hD : 2 * max D 0 ≤ H :=
    (le_max_right H₁ _).trans ((le_max_right 16 _).trans hH)
  have hamp : 20 * (K + (Real.log H + Camp + 2) + Real.log 2) ≤ H := by
    have hDle : D ≤ max D 0 := le_max_left _ _
    dsimp [D] at hDle
    linarith
  apply upperHighZero_moment_le_of_density (by positivity) hH₁₆ hC.le hc.le
  intro eta heta heta₈ hetaH
  have h := hdensity Q T hQ hT eta heta heta₈ hetaH
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using (show 2 ≤ H by linarith))
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hamp)
  have hB : 0 < (Q : ℝ) * ((T : ℝ) + 2) := by
    have : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    positivity
  rw [Real.rpow_def_of_pos hB] at h
  convert h using 1
  congr 2
  dsimp [H]
  ring

end Linnik
