import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! # Exact counts of lifts between finite residue rings -/

namespace Erdos421

theorem zmod_cast_fiber_card_mul {N M : ℕ} [NeZero N] [NeZero M]
    (h : M ∣ N) (b : ZMod M) :
    M * ((Finset.univ : Finset (ZMod N)).filter
      (fun a ↦ ZMod.castHom h (ZMod M) a = b)).card = N := by
  let f := ZMod.castHom h (ZMod M)
  have hf : Function.Surjective f := ZMod.castHom_surjective h
  have he (c : ZMod M) :
      ((Finset.univ : Finset (ZMod N)).filter (fun a ↦ f a = c)).card =
        ((Finset.univ : Finset (ZMod N)).filter (fun a ↦ f a = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf c) (hf b)
  calc
    M * ((Finset.univ : Finset (ZMod N)).filter (fun a ↦ f a = b)).card =
        ∑ _c : ZMod M,
          ((Finset.univ : Finset (ZMod N)).filter (fun a ↦ f a = b)).card := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    _ = ∑ c : ZMod M,
        ((Finset.univ : Finset (ZMod N)).filter (fun a ↦ f a = c)).card :=
      Finset.sum_congr rfl (fun c _ ↦ (he c).symm)
    _ = (Finset.univ : Finset (ZMod N)).card :=
      (Finset.card_eq_sum_card_fiberwise (f := f) (fun _ _ ↦ Finset.mem_univ _)).symm
    _ = N := by simp only [Finset.card_univ, ZMod.card]

def primePowerCast (p d e : ℕ) (hed : e ≤ d) : ZMod (p ^ d) →+* ZMod (p ^ e) :=
  ZMod.castHom (pow_dvd_pow p hed) (ZMod (p ^ e))

theorem primePowerCast_fiber_card (p d e : ℕ) [NeZero p] (hed : e ≤ d)
    (b : ZMod (p ^ e)) :
    ((Finset.univ : Finset (ZMod (p ^ d))).filter
      (fun a ↦ primePowerCast p d e hed a = b)).card = p ^ (d - e) := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) e)
  calc
    p ^ e * ((Finset.univ : Finset (ZMod (p ^ d))).filter
        (fun a ↦ primePowerCast p d e hed a = b)).card = p ^ d :=
      zmod_cast_fiber_card_mul (pow_dvd_pow p hed) b
    _ = p ^ e * p ^ (d - e) := by rw [← pow_add, Nat.add_sub_of_le hed]

end Erdos421
