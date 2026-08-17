/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorModular

/-!
Primary-component lemmas used to reconstruct the odd-modulus selector.
-/

namespace Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace PrimaryComponent

/-- An element of `ZMod (p ^ a)` is a unit as soon as its reduction modulo
`p` is nonzero.  This is the small local-ring fact used in the root
dichotomy, stated without installing a local-ring instance. -/
private lemma isUnit_of_castHom_ne_zero {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (z : ZMod (p ^ a))
    (hz : ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p) z ≠ 0) : IsUnit z := by
  letI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val z]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp ha]
  intro hpz
  apply hz
  rw [← ZMod.natCast_zmod_val z]
  simpa only [map_natCast] using (ZMod.natCast_eq_zero_iff z.val p).2 hpz

/-- Over an odd prime power, the two roots of `X² + 1` differ only by
sign.  The oddness assumption is supplied in the form used by the selector:
`2` is coprime to the prime-power modulus. -/
theorem root_eq_or_eq_neg {d : ℕ} (c : PrimaryComponent d)
    (hodd : Nat.Coprime 2 c.q) (x y : Root c.q) :
    x.1 = y.1 ∨ x.1 = -y.1 := by
  have hpq : c.p ∣ c.q := dvd_pow_self c.p c.exp_pos.ne'
  let red : ZMod c.q →+* ZMod c.p := ZMod.castHom hpq (ZMod c.p)
  letI : Fact c.p.Prime := ⟨c.prime⟩
  have hxroot : red x.1 ^ 2 = -1 := by
    rw [← map_pow, x.property]
    simp
  have hyroot : red y.1 ^ 2 = -1 := by
    rw [← map_pow, y.property]
    simp
  have hxy : red x.1 = red y.1 ∨ red x.1 = -red y.1 :=
    eq_or_eq_neg_of_sq_eq_sq _ _ (hxroot.trans hyroot.symm)
  have h2p : ¬ c.p ∣ 2 := by
    apply c.prime.coprime_iff_not_dvd.mp
    exact (hodd.of_dvd_right hpq).symm
  have htwo : (2 : ZMod c.p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 c.p).not.mpr h2p
  have hx0 : red x.1 ≠ 0 := by
    intro hx
    rw [hx] at hxroot
    simpa using hxroot
  have hy0 : red y.1 ≠ 0 := by
    intro hy
    rw [hy] at hyroot
    simpa using hyroot
  have hprod : (x.1 - y.1) * (x.1 + y.1) = 0 := by
    calc
      (x.1 - y.1) * (x.1 + y.1) = x.1 ^ 2 - y.1 ^ 2 := by ring
      _ = 0 := by rw [x.property, y.property, sub_self]
  rcases hxy with hsame | hopp
  · have hsum_red : red (x.1 + y.1) ≠ 0 := by
      rw [map_add, hsame]
      intro hzero
      have : (2 : ZMod c.p) * red y.1 = 0 := by
        simpa [two_mul] using hzero
      exact (mul_ne_zero htwo hy0) this
    have hsum_unit : IsUnit (x.1 + y.1) := by
      exact isUnit_of_castHom_ne_zero c.prime c.exp_pos (x.1 + y.1) hsum_red
    left
    apply sub_eq_zero.mp
    calc
      x.1 - y.1 = (x.1 - y.1) * 1 := by simp
      _ = (x.1 - y.1) * ((x.1 + y.1) * (x.1 + y.1)⁻¹) := by
        rw [ZMod.mul_inv_of_unit _ hsum_unit]
      _ = ((x.1 - y.1) * (x.1 + y.1)) * (x.1 + y.1)⁻¹ := by
        rw [mul_assoc]
      _ = 0 := by rw [hprod, zero_mul]
  · have hdiff_red : red (x.1 - y.1) ≠ 0 := by
      rw [map_sub, hopp]
      intro hzero
      have : (2 : ZMod c.p) * (-red y.1) = 0 := by
        simpa [two_mul, sub_eq_add_neg] using hzero
      exact (mul_ne_zero htwo (neg_ne_zero.mpr hy0)) this
    have hdiff_unit : IsUnit (x.1 - y.1) := by
      exact isUnit_of_castHom_ne_zero c.prime c.exp_pos (x.1 - y.1) hdiff_red
    right
    rw [eq_neg_iff_add_eq_zero]
    calc
      x.1 + y.1 = 1 * (x.1 + y.1) := by simp
      _ = ((x.1 - y.1)⁻¹ * (x.1 - y.1)) * (x.1 + y.1) := by
        rw [ZMod.inv_mul_of_unit _ hdiff_unit]
      _ = (x.1 - y.1)⁻¹ * ((x.1 - y.1) * (x.1 + y.1)) := by
        rw [mul_assoc]
      _ = 0 := by rw [hprod, mul_zero]

end PrimaryComponent

/-- A finite list of full primary components whose pairwise-coprime moduli
multiply to the original modulus.  Repetitions are ruled out by
`pairwise`; the equality `product_eq` is the explicit completeness
hypothesis. -/
structure CompleteComponents (d : ℕ) where
  components : List (PrimaryComponent d)
  pairwise : components.Pairwise fun c₁ c₂ : PrimaryComponent d ↦
    Nat.Coprime c₁.q c₂.q
  product_eq : (components.map fun c ↦ c.q).prod = d

namespace CompleteComponents

/-- Complete primary reductions separate points of `ZMod d`.  This is the
finite CRT coverage statement used when independently chosen local signs
are reconstructed globally. -/
theorem eq_of_reduce_eq {d : ℕ} (C : CompleteComponents d) (hd : d ≠ 0)
    (x y : ZMod d)
    (h : ∀ c ∈ C.components, c.reduce x = c.reduce y) : x = y := by
  letI : NeZero d := ⟨hd⟩
  have hlocal : ∀ c ∈ C.components, x.val ≡ y.val [MOD c.q] := by
    intro c hc
    apply (ZMod.natCast_eq_natCast_iff x.val y.val c.q).mp
    have hcast : (ZMod.cast x : ZMod c.q) = ZMod.cast y := by
      simpa only [PrimaryComponent.reduce, ZMod.castHom_apply] using h c hc
    calc
      (x.val : ZMod c.q) = ZMod.cast x := ZMod.natCast_val x
      _ = ZMod.cast y := hcast
      _ = (y.val : ZMod c.q) := (ZMod.natCast_val y).symm
  have hmod : x.val ≡ y.val [MOD d] := by
    have hp := (Nat.modEq_list_map_prod_iff C.pairwise).2 hlocal
    simpa only [C.product_eq] using hp
  calc
    x = (x.val : ZMod d) := (ZMod.natCast_zmod_val x).symm
    _ = (y.val : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff x.val y.val d).2 hmod
    _ = y := ZMod.natCast_zmod_val y

end CompleteComponents

end

end Erdos215.Selector.Modular
