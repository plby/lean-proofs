import ErdosProblems.Erdos941.ModularRoots
import ErdosProblems.Erdos941.RootLifting

/-! # Elementary lifting of quadratic roots at good odd prime powers -/

namespace Erdos941

theorem exists_root_step_lift {a p b n : ℕ} (hp : 0 < p) (hpa : p ∣ a)
    (hroot : a ∣ b ^ 2 + n) (hcop : p.Coprime (2 * b)) :
    ∃ B : ℕ, B % a = b % a ∧ a * p ∣ B ^ 2 + n := by
  obtain ⟨k, hk⟩ := hroot
  let r : ℕ := p - k % p
  obtain ⟨t, _, ht⟩ := Nat.exists_mul_mod_eq_of_coprime r hcop.symm hp.ne'
  have hmod : (k + 2 * b * t) % p = 0 := by
    rw [Nat.add_mod, ht]
    have hkp := Nat.mod_lt k hp
    have hkr : k % p + r = p := by dsimp [r]; omega
    calc
      (k % p + r % p) % p = (k % p + r) % p := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = p % p := congrArg (· % p) hkr
      _ = 0 := Nat.mod_self _
  have hd : p ∣ k + 2 * b * t + a * t ^ 2 :=
    dvd_add (Nat.dvd_of_mod_eq_zero hmod) (dvd_mul_of_dvd_left hpa _)
  refine ⟨b + a * t, ?_, ?_⟩
  · simp only [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
  · have he : (b + a * t) ^ 2 + n = a * (k + 2 * b * t + a * t ^ 2) := by
      nlinarith [hk]
    rw [he]
    exact Nat.mul_dvd_mul_left a hd

theorem isUnit_of_prime_reduction {p k : ℕ} [Fact p.Prime] (hk : 0 < k)
    (x : ZMod (p ^ k))
    (hx : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x ≠ 0) : IsUnit x := by
  have hp : p.Prime := Fact.out
  let : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have he : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    exact map_natCast _ _
  rw [he, ne_eq, ZMod.natCast_eq_zero_iff] at hx
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp hk]
  exact hx

theorem modularRootsReduce_prime_injective {n p k : ℕ} [Fact p.Prime]
    (hk : 0 < k) (hcop : p.Coprime (2 * n)) :
    Function.Injective (modularRootsReduce n (dvd_pow_self p hk.ne')) := by
  have hp : p.Prime := Fact.out
  let e := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  intro x y hxy
  have heq : e x.val = e y.val := congrArg Subtype.val hxy
  have hn0 : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp (hcop.of_dvd_right (dvd_mul_left n 2))
  have h20 : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp (hcop.of_dvd_right (dvd_mul_right 2 n))
  have hx0 : e x.val ≠ 0 := by
    intro hz
    have hr := (modularRootsReduce n (dvd_pow_self p hk.ne') x).property
    change (e x.val) ^ 2 = -(n : ZMod p) at hr
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hr
    exact hn0 (neg_eq_zero.mp hr.symm)
  have hu : IsUnit (x.val + y.val) := by
    apply isUnit_of_prime_reduction hk
    change e (x.val + y.val) ≠ 0
    rw [map_add, ← heq, ← two_mul]
    exact mul_ne_zero h20 hx0
  have hh : (x.val + y.val) * (x.val - y.val) = (x.val + y.val) * 0 := by
    calc
      _ = x.val ^ 2 - y.val ^ 2 := by ring
      _ = _ := by rw [x.property, y.property, sub_self, mul_zero]
  exact Subtype.ext (sub_eq_zero.mp (hu.mul_left_cancel hh))

theorem modularRootsReduce_step_surjective {n p k : ℕ} [Fact p.Prime]
    (hk : 0 < k) (hcop : p.Coprime (2 * n)) :
    Function.Surjective (modularRootsReduce n (pow_dvd_pow p (Nat.le_succ k))) := by
  have hp : p.Prime := Fact.out
  let : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  intro x
  let b := x.val.val
  have hroot : p ^ k ∣ b ^ 2 + n := by
    apply (ZMod.natCast_eq_zero_iff _ (p ^ k)).mp
    push_cast
    rw [ZMod.natCast_zmod_val, x.property, neg_add_cancel]
  have hrootp : p ∣ b ^ 2 + n := dvd_trans (dvd_pow_self p hk.ne') hroot
  obtain ⟨B, hB, hBroot⟩ := exists_root_step_lift hp.pos (dvd_pow_self p hk.ne')
    hroot (root_coprime_twice hrootp hcop)
  rw [← pow_succ] at hBroot
  let y : ModularRoots n (p ^ (k + 1)) := ⟨(B : ZMod (p ^ (k + 1))), by
    have hz := (ZMod.natCast_eq_zero_iff (B ^ 2 + n) (p ^ (k + 1))).mpr hBroot
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz⟩
  refine ⟨y, Subtype.ext ?_⟩
  change ZMod.castHom _ (ZMod (p ^ k)) (B : ZMod (p ^ (k + 1))) = x.val
  rw [map_natCast]
  apply ZMod.val_injective
  rw [ZMod.val_natCast, hB, Nat.mod_eq_of_lt (ZMod.val_lt x.val)]

theorem modularRootsReduce_step_injective {n p k : ℕ} [Fact p.Prime]
    (hk : 0 < k) (hcop : p.Coprime (2 * n)) :
    Function.Injective (modularRootsReduce n (pow_dvd_pow p (Nat.le_succ k))) := by
  intro x y hxy
  apply modularRootsReduce_prime_injective (Nat.succ_pos k) hcop
  apply Subtype.ext
  have h := congrArg (fun z : ModularRoots n (p ^ k) =>
    ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z.val) hxy
  have he : (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)).comp
      (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) =
      ZMod.castHom (dvd_pow_self p (Nat.succ_pos k).ne') (ZMod p) :=
    Subsingleton.elim _ _
  change ((ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)).comp
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)))) x.val =
    ((ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)).comp
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)))) y.val at h
  rw [he] at h
  exact h

theorem modularRoots_card_prime_pow (n : ℕ) {p : ℕ} [Fact p.Prime]
    (hcop : p.Coprime (2 * n)) (k : ℕ) :
    Nat.card (ModularRoots n (p ^ (k + 1))) = Nat.card (ModularRoots n p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := Equiv.ofBijective
      (modularRootsReduce n (pow_dvd_pow p (Nat.le_succ (k + 1))))
      ⟨modularRootsReduce_step_injective (Nat.succ_pos k) hcop,
        modularRootsReduce_step_surjective (Nat.succ_pos k) hcop⟩
    exact (Nat.card_congr he).trans ih

end Erdos941
