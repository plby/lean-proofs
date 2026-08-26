import ErdosProblems.Erdos67.StationaryRationalPrimeBudget

/-!
# Prime factors outside a residue subgroup

If a positive integer is coprime to `q` and its residue lies outside a subgroup
of the units modulo `q`, at least one of its prime factors also lies outside.
-/

namespace Erdos67.StationaryModel

noncomputable def residueUnit (q : ℕ+) (n : ℕ) : (ZMod q.val)ˣ :=
  if h : Nat.Coprime n q.val then ZMod.unitOfCoprime n h else 1

theorem residueUnit_of_coprime (q : ℕ+) (n : ℕ) (hn : Nat.Coprime n q.val) :
    residueUnit q n = ZMod.unitOfCoprime n hn := dif_pos hn

theorem coe_residueUnit (q : ℕ+) (n : ℕ) (hn : Nat.Coprime n q.val) :
    (residueUnit q n : ZMod q.val) = n := by
  rw [residueUnit_of_coprime q n hn, ZMod.coe_unitOfCoprime]

theorem residueUnit_one (q : ℕ+) : residueUnit q 1 = 1 := by
  apply Units.ext
  rw [coe_residueUnit q 1 (Nat.coprime_one_left _)]
  simp

theorem residueUnit_mul (q : ℕ+) (m n : ℕ) (hm : Nat.Coprime m q.val)
    (hn : Nat.Coprime n q.val) : residueUnit q (m * n) = residueUnit q m * residueUnit q n := by
  apply Units.ext
  rw [Units.val_mul, coe_residueUnit q (m * n) (hm.mul_left hn),
    coe_residueUnit q m hm, coe_residueUnit q n hn, Nat.cast_mul]

theorem residueUnit_mem_of_prime_factors (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (n : ℕ)
    (hn : 0 < n) (hcop : Nat.Coprime n q.val)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n → residueUnit q p ∈ H) : residueUnit q n ∈ H := by
  induction n using Nat.recOnMul with
  | zero => omega
  | one => simpa only [residueUnit_one] using H.one_mem
  | prime p hp => exact hprime p hp (dvd_refl p)
  | mul a b ha hb =>
    have hca : Nat.Coprime a q.val := hcop.of_dvd_left (dvd_mul_right a b)
    have hcb : Nat.Coprime b q.val := hcop.of_dvd_left (dvd_mul_left b a)
    rw [residueUnit_mul q a b hca hcb]
    apply H.mul_mem
    · apply ha (Nat.pos_of_mul_pos_right hn) hca
      intro p hp hpa
      exact hprime p hp (hpa.trans (dvd_mul_right a b))
    · apply hb (Nat.pos_of_mul_pos_left hn) hcb
      intro p hp hpb
      exact hprime p hp (hpb.trans (dvd_mul_left b a))

def BadResiduePrime (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (p : ℕ) : Prop :=
  p.Prime ∧ Nat.Coprime p q.val ∧ residueUnit q p ∉ H

theorem exists_bad_residue_prime_factor (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (n : ℕ)
    (hn : 0 < n) (hcop : Nat.Coprime n q.val) (hnot : residueUnit q n ∉ H) :
    ∃ p : ℕ, p ∣ n ∧ BadResiduePrime q H p := by
  by_contra he
  push Not at he
  apply hnot
  apply residueUnit_mem_of_prime_factors q H n hn hcop
  intro p hp hpn
  have hpc : Nat.Coprime p q.val := hcop.of_dvd_left hpn
  have hbad := he p hpn
  exact Classical.byContradiction (fun hnp ↦ hbad ⟨hp, hpc, hnp⟩)

end Erdos67.StationaryModel
