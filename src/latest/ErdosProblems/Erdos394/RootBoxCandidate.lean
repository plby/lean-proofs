import ErdosProblems.Erdos394.RootBoxLeastMean
import ErdosProblems.Erdos394.Structural

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Converting a finite root-box hit into an admissible consecutive-product start
-/

open Nat Finset

namespace Erdos394

/-- A simultaneous local block hit for the residue tuple of `m` makes `m*j`
an admissible start modulo `m∏P`. -/
theorem t_le_mul_of_rootBoxGlobalHit
    (P : Finset ℕ) (K m j : ℕ) (hK : 0 < K) (hm : 0 < m)
    (hj : 0 < j) (hprime : ∀ p ∈ P, p.Prime)
    (hcop : m.Coprime (primeProduct P))
    (h : RootBoxMultiplierTuple P)
    (hmh : ∀ p : ↥P, (h p : ZMod p.val) = (m : ZMod p.val))
    (hhit : rootBoxGlobalHit P K j h) :
    t K (m * primeProduct P) ≤ m * j := by
  have hqdiv : primeProduct P ∣ consecutiveProduct K (m * j) := by
    apply (primeProduct_dvd_iff_all_dvd P hprime
      (consecutiveProduct K (m * j))).mpr
    intro p hp
    let pp : ↥P := ⟨p, hp⟩
    obtain ⟨i, hiK, hieq⟩ := hhit pp
    have hz : ((m * j + i : ℕ) : ZMod p) = 0 := by
      calc
        ((m * j + i : ℕ) : ZMod p) =
            (m : ZMod p) * (j : ZMod p) + (i : ZMod p) := by push_cast; rfl
        _ = (h pp : ZMod p) * (j : ZMod p) + (i : ZMod p) := by
          rw [hmh pp]
        _ = 0 := hieq
    have hpd : p ∣ m * j + i :=
      (ZMod.natCast_eq_zero_iff (m * j + i) p).mp hz
    unfold consecutiveProduct
    exact dvd_trans hpd
      (Finset.dvd_prod_of_mem (fun a : ℕ ↦ m * j + a) hiK)
  have hmdiv : m ∣ consecutiveProduct K (m * j) := by
    exact dvd_trans (dvd_mul_right m j) (start_dvd_consecutiveProduct hK)
  have hmqdiv : m * primeProduct P ∣ consecutiveProduct K (m * j) :=
    hcop.mul_dvd_of_dvd_of_dvd hmdiv hqdiv
  exact t_min (Nat.mul_pos hm hj) hmqdiv

/-- Specialization to the least root-box hit time. -/
theorem t_le_mul_rootBoxTupleLeastHit
    (P : Finset ℕ) (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcop : m.Coprime (primeProduct P))
    (h : RootBoxMultiplierTuple P)
    (hmh : ∀ p : ↥P, (h p : ZMod p.val) = (m : ZMod p.val)) :
    t K (m * primeProduct P) ≤
      m * rootBoxTupleLeastHit P K hK hprime h := by
  let j := rootBoxTupleLeastHit P K hK hprime h
  have hjpos : 0 < j := (rootBoxTupleLeastHit_bounds P K hK hprime h).1
  have hjmem := rootBoxTupleLeastHit_mem P K hK hprime h
  have hjhitSet := (Finset.mem_filter.mp hjmem).2
  have hjhit := (mem_rootBoxGlobalHitSet_iff P K j hprime h).mp hjhitSet
  exact t_le_mul_of_rootBoxGlobalHit P K m j hK hm hjpos hprime
    hcop h hmh hjhit

end Erdos394
