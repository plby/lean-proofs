import ErdosProblems.Erdos336.FourierDirectionCircle

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

variable {N : ℕ} [NeZero N]

/-- The character indexed by `k` factors through a surjective cyclic quotient
whose cardinality is exactly the additive order of `k`. -/
theorem exists_frequency_quotient (k : ZMod N) (hk : k ≠ 0) :
    ∃ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      ∃ π : ZMod N →+ ZMod m,
        Function.Surjective π ∧ m = addOrderOf k ∧
        ∀ x : ZMod N, ZMod.toCircle (π x) = ZMod.toCircle (-(x * k)) := by
  let g : ℕ := N.gcd k.val
  let m : ℕ := N / g
  let u : ℕ := k.val / g
  have hNpos : 0 < N := NeZero.pos N
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left _ hNpos
  have hgle : g ≤ N := by
    dsimp [g]
    exact Nat.gcd_le_left _ hNpos
  have hm : 0 < m := Nat.div_pos hgle hgpos
  letI : NeZero m := ⟨hm.ne'⟩
  have hdiv : m ∣ N := by
    dsimp [m]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left N k.val)
  have hcop : u.Coprime m := by
    dsimp [u, m, g]
    exact (Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left k.val hNpos)).symm
  let π : ZMod N →+ ZMod m :=
    { toFun := fun x => -(u : ZMod m) * ZMod.castHom hdiv (ZMod m) x
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [map_add]
        ring }
  have hπ : Function.Surjective π := by
    let v : (ZMod m)ˣ := ZMod.unitOfCoprime u hcop
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective hdiv
      (-(↑(v⁻¹) : ZMod m) * y)
    refine ⟨x, ?_⟩
    change -(u : ZMod m) * ZMod.castHom hdiv (ZMod m) x = y
    rw [hx]
    change -(↑v : ZMod m) * (-(↑(v⁻¹) : ZMod m) * y) = y
    simp
  have hmorder : m = addOrderOf k := by
    have h := ZMod.addOrderOf_coe k.val (NeZero.ne N)
    rw [ZMod.natCast_zmod_val] at h
    exact h.symm
  refine ⟨m, hm, ?_⟩
  dsimp
  refine ⟨π, hπ, hmorder, ?_⟩
  intro x
  apply Subtype.ext
  have hgMulN : m * g = N := by
    dsimp [m]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left N k.val)
  have hgMulK : u * g = k.val := by
    dsimp [u]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right N k.val)
  have hπcast : π x = ((-((u * x.val : ℕ) : ℤ) : ℤ) : ZMod m) := by
    dsimp [π]
    rw [ZMod.cast_eq_val]
    push_cast
    ring
  have hkcast : -(x * k) =
      ((-((x.val * k.val : ℕ) : ℤ) : ℤ) : ZMod N) := by
    calc
      -(x * k) = -((x.val : ZMod N) * (k.val : ZMod N)) := by
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = ((-((x.val * k.val : ℕ) : ℤ) : ℤ) : ZMod N) := by
        push_cast
        ring
  rw [hπcast, hkcast]
  rw [ZMod.toCircle_intCast, ZMod.toCircle_intCast]
  congr 1
  push_cast
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hNm : (N : ℂ) = m * g := by exact_mod_cast hgMulN.symm
  have hKu : (k.val : ℂ) = u * g := by exact_mod_cast hgMulK.symm
  rw [hNm, hKu]
  field_simp [hmC, hgC]

end Erdos336
