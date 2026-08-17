/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorModular

/-!
Elementary Hensel lifting for square roots of `-1` modulo odd prime powers.
-/

namespace Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- One elementary Hensel step for `X² + 1`.  Besides producing a root
modulo the next power, the statement records that it reduces to the given
root.  The proof uses the correction
`x' = x + t p^a`, where `m = (1 + x²) / p^a` and
`t = -(2x)⁻¹m (mod p)`. -/
theorem exists_root_lift_succ (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) :
    ∃ mu : Root (p ^ (a + 1)),
      ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) mu.1 = lam.1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let q := p ^ a
  have hqpos : 0 < q := pow_pos hp.pos _
  letI : NeZero q := ⟨hqpos.ne'⟩
  let x := ZMod.val lam.1
  have hxdiv : q ∣ 1 + x ^ 2 := by
    simpa only [q] using root_dvd_one_add_val_sq hqpos.ne' lam
  let m := (1 + x ^ 2) / q
  have hqm : q * m = 1 + x ^ 2 := by
    exact Nat.mul_div_cancel' hxdiv
  have hpq : p ∣ q := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    simp [q, pow_succ]
  have hxroot : ((x : ℕ) : ZMod p) ^ 2 = -1 := by
    have hz : ((1 + x ^ 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (1 + x ^ 2) p).2 (hpq.trans hxdiv)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hz
    linear_combination hz
  have hcop : Nat.Coprime 2 p := by
    apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hpd
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hpd
    exact hp2 (Nat.le_antisymm hle hp.two_le)
  have htwo : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hcop
  have hxunit : IsUnit (x : ZMod p) :=
    root_isUnit (⟨(x : ZMod p), hxroot⟩ : Root p)
  have htwox : IsUnit ((2 : ZMod p) * (x : ZMod p)) := htwo.mul hxunit
  let t : ZMod p := (((2 : ZMod p) * (x : ZMod p))⁻¹) * (-(m : ZMod p))
  have ht : (m : ZMod p) + ((2 : ZMod p) * (x : ZMod p)) * t = 0 := by
    have hmul : ((2 : ZMod p) * (x : ZMod p)) * t = -(m : ZMod p) := by
      dsimp only [t]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ htwox, one_mul]
    rw [hmul, add_neg_cancel]
  have hcorr : p ∣ m + 2 * x * t.val := by
    apply (ZMod.natCast_eq_zero_iff (m + 2 * x * t.val) p).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    simpa only [mul_assoc] using ht
  have hpbracket : p ∣ m + 2 * x * t.val + t.val ^ 2 * q := by
    exact Nat.dvd_add hcorr (dvd_mul_of_dvd_right hpq (t.val ^ 2))
  let y := x + t.val * q
  have hexpand : 1 + y ^ 2 = q * (m + 2 * x * t.val + t.val ^ 2 * q) := by
    dsimp only [y]
    calc
      1 + (x + t.val * q) ^ 2 = (1 + x ^ 2) + 2 * x * t.val * q + t.val ^ 2 * q ^ 2 := by
        ring
      _ = q * m + 2 * x * t.val * q + t.val ^ 2 * q ^ 2 := by rw [hqm]
      _ = q * (m + 2 * x * t.val + t.val ^ 2 * q) := by ring
  have hydiv : p ^ (a + 1) ∣ 1 + y ^ 2 := by
    rw [hexpand]
    simpa only [q, pow_succ] using Nat.mul_dvd_mul_left q hpbracket
  let mu : Root (p ^ (a + 1)) :=
    ⟨(y : ZMod (p ^ (a + 1))), by
      have hz : ((1 + y ^ 2 : ℕ) : ZMod (p ^ (a + 1))) = 0 :=
        (ZMod.natCast_eq_zero_iff (1 + y ^ 2) (p ^ (a + 1))).2 hydiv
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hz
      linear_combination hz⟩
  refine ⟨mu, ?_⟩
  change ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
      (y : ZMod (p ^ (a + 1))) = lam.1
  rw [map_natCast]
  change (y : ZMod q) = lam.1
  simp [y, x, q]

/-- The chosen elementary Hensel lift. -/
def rootLiftSucc (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) : Root (p ^ (a + 1)) :=
  Classical.choose (exists_root_lift_succ p a hp hp2 ha lam)

/-- The chosen lift is compatible with reduction to the preceding power. -/
@[simp] theorem cast_rootLiftSucc (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (lam : Root (p ^ a)) :
    ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
        (rootLiftSucc p a hp hp2 ha lam).1 = lam.1 :=
  Classical.choose_spec (exists_root_lift_succ p a hp hp2 ha lam)

/-- Iterating the elementary step lifts a root from any positive exponent
to every larger exponent, without changing its reduction at the original
prime power. -/
theorem exists_root_lift_pow_of_le (p b a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hb : 0 < b) (hba : b ≤ a) (lam : Root (p ^ b)) :
    ∃ mu : Root (p ^ a),
      ZMod.castHom (Nat.pow_dvd_pow p hba) (ZMod (p ^ b)) mu.1 = lam.1 := by
  induction a, hba using Nat.le_induction with
  | base =>
      refine ⟨lam, ?_⟩
      simp
  | succ a hba ih =>
      rcases ih with ⟨mu, hmu⟩
      have ha : 0 < a := hb.trans_le hba
      rcases exists_root_lift_succ p a hp hp2 ha mu with ⟨nu, hnu⟩
      refine ⟨nu, ?_⟩
      have hcomp := congrArg (fun f ↦ f nu.1)
        (ZMod.castHom_comp
          (Nat.pow_dvd_pow p hba)
          (Nat.pow_dvd_pow p (Nat.le_succ a)))
      calc
        ZMod.castHom (Nat.pow_dvd_pow p (Nat.le.step hba)) (ZMod (p ^ b)) nu.1 =
            ZMod.castHom (Nat.pow_dvd_pow p hba) (ZMod (p ^ b))
              (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) nu.1) := by
                simpa only [RingHom.comp_apply] using hcomp.symm
        _ = ZMod.castHom (Nat.pow_dvd_pow p hba) (ZMod (p ^ b)) mu.1 := by rw [hnu]
        _ = lam.1 := hmu

/-- A recursively compatible tower of roots, starting from a root modulo
`p`.  Entry `n` is a root modulo `p^(n+1)`. -/
def rootTower (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (base : Root p) :
    (n : ℕ) → Root (p ^ (n + 1))
  | 0 => by simpa using base
  | n + 1 => rootLiftSucc p (n + 1) hp hp2 (Nat.succ_pos n) (rootTower p hp hp2 base n)

/-- Consecutive entries of `rootTower` reduce to one another. -/
@[simp] theorem cast_rootTower_succ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (base : Root p) (n : ℕ) :
    ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
        (rootTower p hp hp2 base (n + 1)).1 = (rootTower p hp hp2 base n).1 := by
  exact cast_rootLiftSucc p (n + 1) hp hp2 (Nat.succ_pos n) (rootTower p hp hp2 base n)

/-- A prime congruent to one modulo four has a square root of `-1` modulo
each positive prime power. -/
theorem root_primePower_nonempty_of_mod_four_eq_one (p a : ℕ) (hp : p.Prime)
    (hp1 : p % 4 = 1) (ha : 0 < a) : Nonempty (Root (p ^ a)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : p % 4 ≠ 3 := by omega
  rcases ZMod.exists_sq_eq_neg_one_iff.mpr hn3 with ⟨x, hx⟩
  let base : Root p := ⟨x, by simpa [pow_two] using hx.symm⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  exact ⟨rootTower p hp hp2 base n⟩

end

end Erdos215.Selector.Modular
