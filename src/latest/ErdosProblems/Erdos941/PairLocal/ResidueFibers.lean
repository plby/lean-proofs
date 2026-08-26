/- Adapted from the checked repository proof in Erdos1148/ResidueFibers.lean. -/
import Mathlib

/-!
# Sizes of prime-power reduction fibers

The additive reduction map is surjective and all its fibers have equal size.
Counting the fibers gives the exact factor needed in the local root bounds.
-/

namespace Erdos941.PairLocal

lemma card_addHom_fiber_mul {A B : Type*} [AddGroup A] [AddGroup B]
    [Fintype A] [Fintype B] [DecidableEq B] (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    (Finset.univ.filter (fun a => f a = b)).card * Fintype.card B = Fintype.card A := by
  classical
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset A) (Finset.univ : Finset B) f
  have heq (b' : B) : (Finset.univ.filter (fun a => f a = b')).card =
      (Finset.univ.filter (fun a => f a = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (Set.mem_range.mpr (hf b'))
      (Set.mem_range.mpr (hf b))
  simpa [heq, mul_comm] using hsum

lemma card_zmod_reduction_fiber (p : ℕ) [Fact p.Prime] (n m : ℕ) (hm : m ≤ n)
    (b : ZMod (p ^ m)) :
    (Finset.univ.filter (fun a : ZMod (p ^ n) =>
      ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m)) a = b)).card = p ^ (n - m) := by
  let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
  have hf : Function.Surjective f := ZMod.castHom_surjective (pow_dvd_pow p hm)
  have h := card_addHom_fiber_mul f.toAddMonoidHom hf b
  simp only [ZMod.card] at h
  have hp : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  apply Nat.eq_of_mul_eq_mul_right hp
  calc
    _ = p ^ n := h
    _ = p ^ (n - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]

lemma padic_residue_lift_reduction (p : ℕ) [Fact p.Prime]
    (n m : ℕ) (hm : m ≤ n) (a : ZMod (p ^ n)) :
    PadicInt.toZModPow m (a.val : PadicInt p) =
      ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m)) a := by
  rw [map_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val a]
  rw [map_natCast]

lemma padic_pow_dvd_sub_iff_reduction_eq (p : ℕ) [Fact p.Prime]
    (n : ℕ) (x y : PadicInt p) :
    (p : PadicInt p) ^ n ∣ x - y ↔ PadicInt.toZModPow n x = PadicInt.toZModPow n y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, sub_eq_zero]

end Erdos941.PairLocal
