import Util.BinQuadForm

/-!
# Integral coordinate changes for binary quadratic forms

All statements preserve represented integers, rather than the number of their
representations. Determinant one coordinate changes preserve the discriminant,
primitivity, positive definiteness, and the exact counting function.
-/

namespace BinQuadForm

@[ext]
theorem ext {f g : BinQuadForm} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) :
    f = g := by
  cases f
  cases g
  simp_all

/-- Pullback by the integral matrix with rows `(p,q)` and `(r,s)`. -/
def changeVariables (f : BinQuadForm) (p q r s : ℤ) : BinQuadForm where
  a := f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2
  b := 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s
  c := f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2

theorem eval_changeVariables (f : BinQuadForm) (p q r s u v : ℤ) :
    (f.changeVariables p q r s).eval u v = f.eval (p * u + q * v) (r * u + s * v) := by
  simp only [changeVariables, eval]
  ring

theorem discr_changeVariables (f : BinQuadForm) (p q r s : ℤ) :
    (f.changeVariables p q r s).discr = (p * s - q * r) ^ 2 * f.discr := by
  simp only [changeVariables, discr]
  ring

theorem changeVariables_one (f : BinQuadForm) : f.changeVariables 1 0 0 1 = f := by
  ext <;> simp [changeVariables]

theorem changeVariables_comp (f : BinQuadForm) (p q r s t u v w : ℤ) :
    (f.changeVariables p q r s).changeVariables t u v w =
      f.changeVariables (p * t + q * v) (p * u + q * w)
        (r * t + s * v) (r * u + s * w) := by
  ext <;> simp only [changeVariables] <;> ring

theorem changeVariables_inv (f : BinQuadForm) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) :
    (f.changeVariables p q r s).changeVariables s (-q) (-r) p = f := by
  rw [changeVariables_comp]
  have h₁ : p * s + q * -r = 1 := by linarith
  have h₂ : p * -q + q * p = 0 := by ring
  have h₃ : r * s + s * -r = 0 := by ring
  have h₄ : r * -q + s * p = 1 := by nlinarith [hdet]
  rw [h₁, h₂, h₃, h₄, changeVariables_one]

theorem eval_coordinates_surjective {p q r s : ℤ} (hdet : p * s - q * r = 1)
    (u v : ℤ) :
    p * (s * u - q * v) + q * (-r * u + p * v) = u ∧
      r * (s * u - q * v) + s * (-r * u + p * v) = v := by
  constructor
  · calc
      _ = (p * s - q * r) * u := by ring
      _ = u := by rw [hdet, one_mul]
  · calc
      _ = (p * s - q * r) * v := by ring
      _ = v := by rw [hdet, one_mul]

theorem represented_changeVariables_iff (f : BinQuadForm) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) (n : ℤ) :
    (∃ u v : ℤ, (f.changeVariables p q r s).eval u v = n) ↔
      ∃ u v : ℤ, f.eval u v = n := by
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨p * u + q * v, r * u + s * v, (f.eval_changeVariables p q r s u v).symm.trans h⟩
  · rintro ⟨u, v, h⟩
    refine ⟨s * u - q * v, -r * u + p * v, ?_⟩
    rw [eval_changeVariables, (eval_coordinates_surjective hdet u v).1,
      (eval_coordinates_surjective hdet u v).2, h]

theorem B_changeVariables (f : BinQuadForm) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : (f.changeVariables p q r s).B = f.B :=
  B_eq_of_represented_iff fun n => f.represented_changeVariables_iff hdet n

theorem primitive_iff_common_divisor (f : BinQuadForm) :
    f.Primitive ↔ ∀ d : ℤ, d ∣ f.a → d ∣ f.b → d ∣ f.c → d ∣ 1 := by
  unfold Primitive
  rw [Int.gcd_eq_one_iff]
  constructor
  · intro h d ha hb hc
    exact h d ha (Int.dvd_coe_gcd hb hc)
  · intro h d ha hbc
    exact h d ha (hbc.trans (Int.gcd_dvd_left _ _)) (hbc.trans (Int.gcd_dvd_right _ _))

theorem dvd_eval_of_dvd_coeff (f : BinQuadForm) {d : ℤ}
    (ha : d ∣ f.a) (hb : d ∣ f.b) (hc : d ∣ f.c) (u v : ℤ) : d ∣ f.eval u v := by
  exact dvd_add (dvd_add ((ha.mul_right u).mul_right u) ((hb.mul_right u).mul_right v))
    ((hc.mul_right v).mul_right v)

theorem primitive_iff_dvd_eval (f : BinQuadForm) :
    f.Primitive ↔ ∀ d : ℤ, (∀ u v : ℤ, d ∣ f.eval u v) → d ∣ 1 := by
  rw [primitive_iff_common_divisor]
  constructor
  · intro h d hd
    have ha : d ∣ f.a := by simpa [eval] using hd 1 0
    have hc : d ∣ f.c := by simpa [eval] using hd 0 1
    have hb : d ∣ f.b := by
      have hsum : d ∣ f.a + f.b + f.c := by simpa [eval] using hd 1 1
      have hsub := dvd_sub (dvd_sub hsum hc) ha
      simpa only [add_sub_cancel_right, add_sub_cancel_left] using hsub
    exact h d ha hb hc
  · intro h d ha hb hc
    exact h d (f.dvd_eval_of_dvd_coeff ha hb hc)

theorem primitive_changeVariables_iff (f : BinQuadForm) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : (f.changeVariables p q r s).Primitive ↔ f.Primitive := by
  rw [primitive_iff_dvd_eval, primitive_iff_dvd_eval]
  constructor
  · intro h d hd
    apply h d
    intro u v
    rw [eval_changeVariables]
    exact hd _ _
  · intro h d hd
    apply h d
    intro u v
    have hu := hd (s * u - q * v) (-r * u + p * v)
    rwa [eval_changeVariables, (eval_coordinates_surjective hdet u v).1,
      (eval_coordinates_surjective hdet u v).2] at hu

theorem PosDef.changeVariables {f : BinQuadForm} (hf : f.PosDef) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : (f.changeVariables p q r s).PosDef := by
  constructor
  · change 0 < f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2
    have hne : f.eval p r ≠ 0 := by
      intro hzero
      obtain ⟨hp, hr⟩ := (hf.eval_eq_zero_iff p r).mp hzero
      simp [hp, hr] at hdet
    have hpos := lt_of_le_of_ne (hf.eval_nonneg p r) (Ne.symm hne)
    simpa only [eval, pow_two, mul_assoc] using hpos
  · rw [discr_changeVariables, hdet, one_pow, one_mul]
    exact hf.2

/-- Proper integral equivalence of forms. -/
def ProperEquiv (f g : BinQuadForm) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ g = f.changeVariables p q r s

theorem ProperEquiv.refl (f : BinQuadForm) : ProperEquiv f f :=
  ⟨1, 0, 0, 1, by norm_num, f.changeVariables_one.symm⟩

theorem ProperEquiv.symm {f g : BinQuadForm} (h : ProperEquiv f g) : ProperEquiv g f := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact ⟨s, -q, -r, p, by nlinarith [hdet], (f.changeVariables_inv hdet).symm⟩

theorem ProperEquiv.trans {f g h : BinQuadForm} (hfg : ProperEquiv f g)
    (hgh : ProperEquiv g h) : ProperEquiv f h := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := hfg
  obtain ⟨t, u, v, w, hdet', rfl⟩ := hgh
  refine ⟨p * t + q * v, p * u + q * w, r * t + s * v, r * u + s * w, ?_,
    f.changeVariables_comp p q r s t u v w⟩
  calc
    _ = (p * s - q * r) * (t * w - u * v) := by ring
    _ = 1 := by rw [hdet, hdet', one_mul]

theorem ProperEquiv.B_eq {f g : BinQuadForm} (h : ProperEquiv f g) : f.B = g.B := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact (f.B_changeVariables hdet).symm

theorem ProperEquiv.discr_eq {f g : BinQuadForm} (h : ProperEquiv f g) : f.discr = g.discr := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  rw [discr_changeVariables, hdet, one_pow, one_mul]

theorem ProperEquiv.primitive_iff {f g : BinQuadForm} (h : ProperEquiv f g) :
    f.Primitive ↔ g.Primitive := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact (f.primitive_changeVariables_iff hdet).symm

theorem ProperEquiv.posDef {f g : BinQuadForm} (h : ProperEquiv f g) (hf : f.PosDef) :
    g.PosDef := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact hf.changeVariables hdet

end BinQuadForm
