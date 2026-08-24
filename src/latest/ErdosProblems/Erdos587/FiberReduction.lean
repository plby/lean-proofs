import ErdosProblems.Erdos587.PrimitiveParameters

/-! Restricting to a unit-step fiber, with explicit loss of length. -/

namespace Erdos587

lemma exists_affine_zero_residue {u v : ℕ} (hu : 0 < u) (hvu : v.Coprime u) (t : ℕ) :
    ∃ y < u, u ∣ t + v * y := by
  letI : NeZero u := ⟨hu.ne'⟩
  let e := ZMod.unitOfCoprime v hvu
  let z : ZMod u := -(e⁻¹ : (ZMod u)ˣ) * (t : ZMod u)
  have hvcast : (v : ZMod u) = (e : ZMod u) := (ZMod.coe_unitOfCoprime v hvu).symm
  have hz : (t : ZMod u) + (v : ZMod u) * z = 0 := by
    dsimp [z]
    rw [hvcast, ← mul_assoc, mul_neg, ← Units.val_mul]
    simp
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hz

lemma fiber_quotient_bounds {u J y : ℕ} (hu : 0 < u) (hy : y < u) (hJ : 4 * u ≤ J) :
    0 < (J - y) / u ∧ y + u * ((J - y) / u) ≤ J ∧
      J < y + u * ((J - y) / u + 1) ∧
      (J : ℝ) / (2 * u) ≤ (((J - y) / u : ℕ) : ℝ) := by
  have hyJ : y ≤ J := by omega
  have hrem := Nat.mod_lt (J - y) hu
  have hdiv := Nat.mod_add_div (J - y) u
  have hpos : 0 < (J - y) / u := by
    apply Nat.div_pos
    · omega
    · exact hu
  have hlo : y + u * ((J - y) / u) ≤ J := by omega
  have hhi : J < y + u * ((J - y) / u + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hstep : J < u * (((J - y) / u) + 2) := by nlinarith
  have hstepR : (J : ℝ) < u * ((((J - y) / u : ℕ) : ℝ) + 2) := by exact_mod_cast hstep
  have hJR : 4 * (u : ℝ) ≤ J := by exact_mod_cast hJ
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  apply (div_le_iff₀ (show 0 < 2 * (u : ℝ) by positivity)).mpr
  nlinarith

theorem exists_unit_step_fiber {u v J : ℕ} (hu : 0 < u) (hvu : v.Coprime u)
    (t : ℕ) (hJ : 4 * u ≤ J) :
    ∃ y₀ t' J' : ℕ, y₀ < u ∧ u * t' = t + v * y₀ ∧ 0 < J' ∧
      (J : ℝ) / (2 * u) ≤ J' ∧ y₀ + u * J' ≤ J ∧ J < y₀ + u * (J' + 1) ∧
      (∀ x j : ℕ, u * (t' + x + v * j) = t + u * x + v * (y₀ + u * j)) ∧
      (∀ j ≤ J', y₀ + u * j ≤ J) := by
  obtain ⟨y₀, hy₀, hdiv⟩ := exists_affine_zero_residue hu hvu t
  let t' := (t + v * y₀) / u
  let J' := (J - y₀) / u
  have ht' : u * t' = t + v * y₀ := Nat.mul_div_cancel' hdiv
  obtain ⟨hJ'pos, hJ'lo, hJ'hi, hJ'bound⟩ := fiber_quotient_bounds hu hy₀ hJ
  refine ⟨y₀, t', J', hy₀, ht', hJ'pos, hJ'bound, hJ'lo, hJ'hi, ?_, ?_⟩
  · intro x j
    nlinarith [ht']
  · intro j hj
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left u hj) y₀).trans hJ'lo

end Erdos587
