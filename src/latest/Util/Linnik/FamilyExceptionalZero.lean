import Util.Linnik.HighZeroMoment
import Util.Linnik.CrossLevelRepulsion
import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalExceptionalZero

/-!
# The unique exceptional member of a finite primitive family

The zero-free region is synchronized at one conductor-height scale.  There
is at most one index in the innermost strip; if present, its zero is real,
simple, and belongs to a quadratic character.
-/

namespace Linnik

open Complex Erdos48 BoundedGaps.Maynard

local instance {Q : ℕ} (q : ↥(Finset.Ioc 1 Q)) : NeZero q.val :=
  ⟨by have hq := (Finset.mem_Ioc.mp q.property).1; omega⟩

theorem upperHighZeroIndex_eq_of_lifts_eq
    {Q : ℕ} {T : ℝ} (i j : upperHighZeroIndex Q T)
    (hchi : ¬ goldfeldCharactersDistinct i.2.1.1 j.2.1.1)
    (hrho : i.2.2.val = j.2.2.val) : i = j := by
  classical
  have heq : i.2.1.1.changeLevel (Nat.dvd_lcm_left i.1.val j.1.val) =
      j.2.1.1.changeLevel (Nat.dvd_lcm_right i.1.val j.1.val) := not_ne_iff.mp hchi
  have hq : i.1.val = j.1.val := by
    have hcond := congrArg DirichletCharacter.conductor heq
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hcond
    exact i.2.1.2.symm.trans (hcond.trans j.2.1.2)
  rcases i with ⟨⟨q, hqmem⟩, ⟨chi, hchiPrim⟩, ⟨rho, hrhoMem⟩⟩
  rcases j with ⟨⟨q', hqmem'⟩, ⟨chi', hchiPrim'⟩, ⟨rho', hrhoMem'⟩⟩
  dsimp only at hq hrho heq hchi
  subst q'
  let : NeZero q := ⟨by have h := (Finset.mem_Ioc.mp hqmem).1; omega⟩
  have hchar : chi = chi' := by
    exact not_ne_iff.mp ((goldfeldCharactersDistinct_same_level_iff chi chi').not.mp hchi)
  subst chi'
  subst rho'
  rfl

theorem synchronized_near_one
    {M : ℕ} (hM : 1 ≤ M) {H G delta : ℝ}
    (hG : 0 < G) (hGH : G ≤ 2 * H)
    (hdelta : 0 ≤ delta) (hnear : H * delta ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    delta ≤ 1 / ((M : ℝ) ^ 2 * G) := by
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hM₀
  apply (le_div_iff₀ (mul_pos hsq hG)).mpr
  have h := (le_div_iff₀ (by positivity : 0 < 2 * (M : ℝ) ^ 2)).mp hnear
  have hprod := mul_le_mul_of_nonneg_right hGH hdelta
  nlinarith

theorem upperHighZero_lifted_zero
    {Q d : ℕ} [NeZero d] {T : ℝ} (hT : 0 ≤ T)
    (i : upperHighZeroIndex Q T) (hid : i.1.val ∣ d) :
    IsNonprincipalNontrivialLFunctionZero
      (i.2.1.1.changeLevel hid) i.2.2.val := by
  have hq := (Finset.mem_Ioc.mp i.1.property).1
  have h := (mem_highZeroRectangle_iff hq i.2.1.1 i.2.1.2
    (by norm_num : (1 / 16 : ℝ) ≤ 1) hT i.2.2.val).mp i.2.2.property
  have hchi := primitiveCharacter_ne_one_of_one_lt hq i.2.1
  apply (isNonprincipalNontrivialLFunctionZero_iff _ _).mpr
  refine ⟨(DirichletCharacter.changeLevel_eq_one_iff hid).not.mpr hchi, ?_, ?_, ?_⟩
  · rw [DirichletCharacter.LFunction_changeLevel hid i.2.1.1 (.inl hchi), h.1, zero_mul]
  · linarith [h.2.1]
  · exact LFunction_zero_re_lt_one_of_isPrimitive hq i.2.1.1 i.2.1.2 h.1

theorem upperHighZero_zero_data
    {Q : ℕ} {T : ℝ} (hT : 0 ≤ T) (i : upperHighZeroIndex Q T) :
    DirichletCharacter.LFunction i.2.1.1 i.2.2.val = 0 ∧
      0 < i.2.2.val.re ∧ i.2.2.val.re < 1 ∧ |i.2.2.val.im| ≤ T := by
  have h := (mem_highZeroRectangle_iff (Finset.mem_Ioc.mp i.1.property).1
    i.2.1.1 i.2.1.2 (by norm_num : (1 / 16 : ℝ) ≤ 1) hT i.2.2.val).mp i.2.2.property
  refine ⟨h.1, by linarith [h.2.1], ?_, ?_⟩
  · exact LFunction_zero_re_lt_one_of_isPrimitive (Finset.mem_Ioc.mp i.1.property).1
      i.2.1.1 i.2.1.2 h.1
  · rw [abs_of_nonneg h.2.2.2.1]
    exact h.2.2.2.2

/-- A single positive width works for both the shape and uniqueness of
exceptional zeros in every finite primitive conductor-height family. -/
theorem exists_family_exceptional_width :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa ≤ 1 ∧
      ∀ Q : ℕ, ∀ T : ℝ, 0 ≤ T →
        let H := Real.log ((Q : ℝ) * (T + 2))
        (∀ i : upperHighZeroIndex Q T, H * upperHighZeroGap i ≤ kappa →
          i.2.1.1 ^ 2 = 1 ∧ i.2.2.val.im = 0 ∧ upperHighZeroWeight i = 1) ∧
        (∀ i j : upperHighZeroIndex Q T,
          H * upperHighZeroGap i ≤ kappa → H * upperHighZeroGap j ≤ kappa → i = j) := by
  obtain ⟨Ms, hMs, hshape⟩ := exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  obtain ⟨Mu, hMu, hunique⟩ := exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq
  let M := max Ms Mu
  have hM₁ : 1 ≤ M := (by omega : 1 ≤ Ms).trans (le_max_left _ _)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM₁
  let kappa : ℝ := 1 / (2 * (M : ℝ) ^ 2)
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  refine ⟨kappa, hkappa, ?_, ?_⟩
  · dsimp [kappa]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ) ^ 2)).mpr
    nlinarith
  intro Q T hT
  let H := Real.log ((Q : ℝ) * (T + 2))
  have hnear (i j : upperHighZeroIndex Q T)
      (hi : H * upperHighZeroGap i ≤ kappa) (m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) :
      1 - 1 / ((m : ℝ) ^ 2 *
        Real.log ((Nat.lcm i.1.val j.1.val : ℝ) * (|i.2.2.val.im| + 2))) ≤ i.2.2.val.re := by
    have hzero := (mem_highZeroRectangle_iff (Finset.mem_Ioc.mp i.1.property).1
      i.2.1.1 i.2.1.2 (by norm_num : (1 / 16 : ℝ) ≤ 1) hT i.2.2.val).mp i.2.2.property
    have hheight : |i.2.2.val.im| ≤ T := by rw [abs_of_nonneg hzero.2.2.2.1]; exact hzero.2.2.2.2
    have hlog := log_lcm_height_le_twice (Finset.mem_Ioc.mp i.1.property).2
      (Finset.mem_Ioc.mp j.1.property).2 hT hheight
    have hlog₀ : 0 < Real.log
        ((Nat.lcm i.1.val j.1.val : ℝ) * (|i.2.2.val.im| + 2)) := by
      apply Real.log_pos
      have hlcm : (1 : ℝ) ≤ Nat.lcm i.1.val j.1.val := by
        exact_mod_cast Nat.lcm_pos (NeZero.pos i.1.val) (NeZero.pos j.1.val)
      nlinarith [abs_nonneg i.2.2.val.im]
    have hdelta := synchronized_near_one hM₁ hlog₀ hlog (upperHighZeroGap_bounds hT i).1 hi
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
    have hinv : 1 / ((M : ℝ) ^ 2 * Real.log ((Nat.lcm i.1.val j.1.val : ℝ) *
        (|i.2.2.val.im| + 2))) ≤ 1 / ((m : ℝ) ^ 2 *
        Real.log ((Nat.lcm i.1.val j.1.val : ℝ) * (|i.2.2.val.im| + 2))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (by nlinarith) hlog₀.le
    dsimp [upperHighZeroGap] at hdelta
    linarith
  constructor
  · intro i hi
    have hn := hnear i i hi Ms (by omega) (le_max_left _ _)
    simp only [Nat.lcm_self] at hn
    have hz := upperHighZero_lifted_zero hT i (dvd_refl i.1.val)
    simp only [DirichletCharacter.changeLevel_self] at hz
    obtain ⟨hsquare, him, horder⟩ := hshape i.1.val i.2.1.1 i.2.2.val hz hn
    exact ⟨hsquare, him, by simp only [upperHighZeroWeight, horder, Nat.cast_one]⟩
  · intro i j hi hj
    let d := Nat.lcm i.1.val j.1.val
    let : NeZero d := ⟨Nat.lcm_ne_zero (NeZero.ne i.1.val) (NeZero.ne j.1.val)⟩
    have hn₁ := hnear i j hi Mu (by omega) (le_max_right _ _)
    have hn₂ := hnear j i hj Mu (by omega) (le_max_right _ _)
    rw [Nat.lcm_comm j.1.val i.1.val] at hn₂
    have heq := hunique d _ _ i.2.2.val j.2.2.val
      (upperHighZero_lifted_zero hT i (Nat.dvd_lcm_left _ _))
      (upperHighZero_lifted_zero hT j (Nat.dvd_lcm_right _ _)) hn₁ hn₂
    exact upperHighZeroIndex_eq_of_lifts_eq i j (not_ne_iff.mpr heq.1) heq.2

end Linnik
