import ErdosProblems.Erdos633b.CoprimeMiddleInterval

/-! Lifting a prescribed primitive residue through a divisor of the
ambient modulus, using proved surjectivity on modular unit groups. -/

namespace Erdos633b

theorem coprime_multiplier_residue (M D j r : ℕ) (hM : 0 < M) (hDM : D ∣ M)
    (hj : j.Coprime D) (hr : r.Coprime D) :
    ∃ k : ℕ, k.Coprime M ∧ Nat.ModEq D (k * j) r := by
  let : NeZero M := ⟨hM.ne'⟩
  let u : (ZMod D)ˣ := ZMod.unitOfCoprime r hr * (ZMod.unitOfCoprime j hj)⁻¹
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hDM u
  let k := (v : ZMod M).val
  have hk : k.Coprime M := ZMod.val_coe_unit_coprime v
  have hcast : (k : ZMod D) = (u : ZMod D) := by
    rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val]
  have he : ((k * j : ℕ) : ZMod D) = (r : ZMod D) := by
    rw [Nat.cast_mul, hcast]
    have hu : u * ZMod.unitOfCoprime j hj = ZMod.unitOfCoprime r hr := by
      dsimp only [u]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    simpa only [Units.val_mul, ZMod.coe_unitOfCoprime] using
      congrArg (fun v : (ZMod D)ˣ => (v : ZMod D)) hu
  exact ⟨k, hk, (ZMod.natCast_eq_natCast_iff _ _ _).mp he⟩

end Erdos633b
