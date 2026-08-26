import ErdosProblems.Erdos1148.PadicCongruences
import ErdosProblems.Erdos1148.ResidueFibers

/-!
# Fibers of affine maps on prime-power residues

Multiplication by a nonzero p-adic integer has at most `p^valuation(a)`
preimages of any residue. The bound is uniform in the depth.
-/

namespace Erdos1148.DukeArithmetic

lemma affine_residue_fiber_card_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : PadicInt p) (ha : a ≠ 0) (b c : ZMod (p ^ n)) :
    (Finset.univ.filter (fun x : ZMod (p ^ n) => PadicInt.toZModPow n a * x + b = c)).card ≤
      p ^ a.valuation := by
  classical
  let S := Finset.univ.filter (fun x : ZMod (p ^ n) => PadicInt.toZModPow n a * x + b = c)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨y, hy⟩ := hS
  have hyEq : PadicInt.toZModPow n a * y + b = c := (Finset.mem_filter.mp hy).2
  let m := n - a.valuation
  have hm : m ≤ n := Nat.sub_le _ _
  let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
  have hsub : S ⊆ Finset.univ.filter (fun x => f x = f y) := by
    intro x hx
    have hxEq : PadicInt.toZModPow n a * x + b = c := (Finset.mem_filter.mp hx).2
    have heq : PadicInt.toZModPow n a * x = PadicInt.toZModPow n a * y := by
      exact add_right_cancel (hxEq.trans hyEq.symm)
    have hmul : (p : PadicInt p) ^ n ∣ a * ((x.val : PadicInt p) - (y.val : PadicInt p)) := by
      have h := (padic_pow_dvd_sub_iff_reduction_eq p n
        (a * ((x.val : PadicInt p) - (y.val : PadicInt p))) 0).mpr (by
          simp only [map_mul, map_sub, map_natCast, ZMod.natCast_zmod_val, map_zero, mul_sub]
          exact sub_eq_zero.mpr heq)
      simpa only [sub_zero] using h
    have hdiv := padic_pow_dvd_of_dvd_mul p a _ ha n hmul
    have hred := (padic_pow_dvd_sub_iff_reduction_eq p m _ _).mp hdiv
    rw [padic_residue_lift_reduction p n m hm, padic_residue_lift_reduction p n m hm] at hred
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hred⟩
  calc
    S.card ≤ (Finset.univ.filter (fun x => f x = f y)).card := Finset.card_le_card hsub
    _ = p ^ (n - m) := card_zmod_reduction_fiber p n m hm (f y)
    _ ≤ p ^ a.valuation := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by dsimp [m]; omega)

lemma finite_fiber_card_bound {A B : Type*} [DecidableEq B]
    (s : Finset A) (t : Finset B) (f : A → B) (C : ℕ)
    (hmap : ∀ a ∈ s, f a ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ C) : s.card ≤ t.card * C := by
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _ ∈ t, C := Finset.sum_le_sum hfiber
    _ = t.card * C := by simp

end Erdos1148.DukeArithmetic
