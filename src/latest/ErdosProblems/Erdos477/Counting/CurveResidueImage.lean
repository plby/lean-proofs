/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The number of occupied prime-power classes in a smooth plane-curve chart.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveRootCongruence

namespace Erdos477.Counting

noncomputable def curveResidueImage (p r : ℕ) (S : Finset (Fin 2 → ℤ)) :
    Finset (Fin 2 → ZMod (p ^ r)) := by
  classical
  exact S.image (fun z k => (z k : ZMod (p ^ r)))

theorem card_curveResidueImage_le (p r : ℕ) [NeZero p] (P : MvPolynomial (Fin 2) ℤ)
    (S : Finset (Fin 2 → ℤ)) (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hcop : ∀ z ∈ S, IsCoprime (p : ℤ) (MvPolynomial.eval z (MvPolynomial.pderiv 0 P))) :
    (curveResidueImage p r S).card ≤ p ^ 2 * p ^ r := by
  classical
  let T := curveResidueImage p r S
  have hrep (a : ↥T) : ∃ z ∈ S, (fun k => (z k : ZMod (p ^ r))) = a.val :=
    Finset.mem_image.mp a.property
  choose z hz heq using hrep
  let f : ↥T → (Fin 2 → ZMod p) × ZMod (p ^ r) := fun a =>
    (fun k => (z a k : ZMod p), (z a 1 : ZMod (p ^ r)))
  have hinj : Function.Injective f := by
    intro a b hab
    have hres := congrArg Prod.fst hab
    have hfree := congrArg Prod.snd hab
    have hclass (k) : (p : ℤ) ∣ z b k - z a k :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hres k)
    have hfree' : (p : ℤ) ^ r ∣ z b 1 - z a 1 := by
      simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hfree
    have h0 := pow_dvd_curve_coordinate_sub P (p : ℤ) (z b) (z a) r
      (hcop _ (hz a)) (hroot _ (hz b)) (hroot _ (hz a)) hclass hfree'
    apply Subtype.ext
    rw [← heq a, ← heq b]
    ext k
    fin_cases k
    · apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
      change ((p ^ r : ℕ) : ℤ) ∣ z b 0 - z a 0
      rw [Nat.cast_pow]
      exact h0
    · exact hfree
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card] using hcard

#print axioms card_curveResidueImage_le
-- 'Erdos477.Counting.card_curveResidueImage_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
