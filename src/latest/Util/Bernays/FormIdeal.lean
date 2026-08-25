import Util.Bernays.QuadraticOrder
import Util.Bernays.Coordinates

/-!
# The invertible ideal attached to a primitive form

For `[a,b,c]` use the order with `ω² = bω-ac` and the ideal `(a,ω)`.
Its norm form is exactly `a` times the original quadratic form.
-/

open scoped nonZeroDivisors

namespace BinQuadForm

abbrev Order (f : BinQuadForm) := QuadraticAlgebra ℤ (-f.a * f.c) f.b

theorem order_discr (f : BinQuadForm) : f.b ^ 2 + 4 * (-f.a * f.c) = f.discr := by
  simp only [discr]
  ring

theorem PosDef.orderIsDomain {f : BinQuadForm} (hf : f.PosDef) : IsDomain f.Order :=
  Bernays.quadraticOrderIsDomain (f.order_discr ▸ hf.2)

def formIdeal (f : BinQuadForm) : Ideal f.Order where
  carrier := {z | f.a ∣ z.re}
  zero_mem' := dvd_zero _
  add_mem' := by intro x y hx hy; exact dvd_add hx hy
  smul_mem' := by
    intro r x hx
    change f.a ∣ r.re * x.re + (-f.a * f.c) * r.im * x.im
    exact dvd_add (hx.mul_left _) (by use -f.c * r.im * x.im; ring)

def conjugateFormIdeal (f : BinQuadForm) : Ideal f.Order where
  carrier := {z | f.a ∣ z.re + f.b * z.im}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change f.a ∣ (x.re + y.re) + f.b * (x.im + y.im)
    rw [show (x.re + y.re) + f.b * (x.im + y.im) =
      (x.re + f.b * x.im) + (y.re + f.b * y.im) by ring]
    exact dvd_add hx hy
  smul_mem' := by
    intro r x hx
    change f.a ∣ r.re * x.re + (-f.a * f.c) * r.im * x.im +
      f.b * (r.re * x.im + r.im * x.re + f.b * r.im * x.im)
    have h := dvd_add (hx.mul_left (r.re + f.b * r.im))
      (show f.a ∣ (-f.a * f.c) * r.im * x.im from by use -f.c * r.im * x.im; ring)
    rw [show r.re * x.re + (-f.a * f.c) * r.im * x.im +
        f.b * (r.re * x.im + r.im * x.re + f.b * r.im * x.im) =
      (r.re + f.b * r.im) * (x.re + f.b * x.im) + (-f.a * f.c) * r.im * x.im by ring]
    exact h

@[simp] theorem mem_formIdeal (f : BinQuadForm) (z : f.Order) :
    z ∈ f.formIdeal ↔ f.a ∣ z.re := Iff.rfl

@[simp] theorem mem_conjugateFormIdeal (f : BinQuadForm) (z : f.Order) :
    z ∈ f.conjugateFormIdeal ↔ f.a ∣ z.re + f.b * z.im := Iff.rfl

theorem quadratic_intCast_dvd {d b : ℤ} (a : ℤ) (z : QuadraticAlgebra ℤ d b) :
    (a : QuadraticAlgebra ℤ d b) ∣ z ↔ a ∣ z.re ∧ a ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id,
      mul_zero, zero_mul, add_zero]
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨u, v⟩, ?_⟩
    ext <;> simp [hu, hv]

theorem primitive_bezout {f : BinQuadForm} (hf : f.Primitive) :
    ∃ r s t : ℤ, r * f.a + s * f.b + t * f.c = 1 := by
  let g : ℤ := Int.gcd f.b f.c
  refine ⟨Int.gcdA f.a g, Int.gcdB f.a g * Int.gcdA f.b f.c,
    Int.gcdB f.a g * Int.gcdB f.b f.c, ?_⟩
  have h₁ := Int.gcd_eq_gcd_ab f.a g
  have h₂ := Int.gcd_eq_gcd_ab f.b f.c
  have hg : Int.gcd f.a g = 1 := hf
  rw [hg] at h₁
  change g = _ at h₂
  linear_combination -h₁ - Int.gcdB f.a g * h₂

theorem formIdeal_mul_conjugate {f : BinQuadForm} (hf : f.Primitive) :
    f.formIdeal * f.conjugateFormIdeal = Ideal.span ({(f.a : f.Order)} : Set f.Order) := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_singleton, quadratic_intCast_dvd]
    constructor
    · change f.a ∣ x.re * y.re + (-f.a * f.c) * x.im * y.im
      exact dvd_add (hx.mul_right _) (by use -f.c * x.im * y.im; ring)
    · change f.a ∣ x.re * y.im + x.im * y.re + f.b * x.im * y.im
      have h := dvd_add (hx.mul_right y.im) (hy.mul_left x.im)
      rw [show x.re * y.im + x.im * y.re + f.b * x.im * y.im =
        x.re * y.im + x.im * (y.re + f.b * y.im) by ring]
      exact h
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    let ω : f.Order := ⟨0, 1⟩
    let ω' : f.Order := ⟨f.b, -1⟩
    have haI : (f.a : f.Order) ∈ f.formIdeal := by simp
    have haJ : (f.a : f.Order) ∈ f.conjugateFormIdeal := by simp
    have hwI : ω ∈ f.formIdeal := by simp [ω]
    have hwJ : ω' ∈ f.conjugateFormIdeal := by simp [ω']
    have haa : ((f.a * f.a : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      simpa only [Int.cast_mul] using Ideal.mul_mem_mul haI haJ
    have hab : ((f.a * f.b : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      have h := (f.formIdeal * f.conjugateFormIdeal).add_mem
        (Ideal.mul_mem_mul haI hwJ) (Ideal.mul_mem_mul hwI haJ)
      convert h using 1 <;> ext <;> simp [ω, ω'] <;> ring
    have hac : ((f.a * f.c : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      have h := Ideal.mul_mem_mul hwI hwJ
      convert h using 1 <;> ext <;> simp [ω, ω'] <;> ring
    obtain ⟨r, s, t, hst⟩ := primitive_bezout hf
    have h := (f.formIdeal * f.conjugateFormIdeal).add_mem
      ((f.formIdeal * f.conjugateFormIdeal).add_mem
        ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (r : f.Order) haa)
        ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (s : f.Order) hab))
      ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (t : f.Order) hac)
    have heq : r * (f.a * f.a) + s * (f.a * f.b) + t * (f.a * f.c) = f.a := by
      linear_combination f.a * hst
    simpa only [← Int.cast_mul, ← Int.cast_add, heq] using h

theorem norm_formIdeal_element (f : BinQuadForm) (u v : ℤ) :
    (⟨f.a * u, v⟩ : f.Order).norm = f.a * f.eval u v := by
  simp only [QuadraticAlgebra.norm_def, eval]
  ring

theorem represented_iff_formIdeal_norm {f : BinQuadForm} (ha : f.a ≠ 0) (n : ℤ) :
    (∃ u v : ℤ, f.eval u v = n) ↔ ∃ z ∈ f.formIdeal, z.norm = f.a * n := by
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨⟨f.a * u, v⟩, dvd_mul_right _ _, by rw [norm_formIdeal_element, h]⟩
  · rintro ⟨z, hz, hn⟩
    obtain ⟨u, hu⟩ := hz
    refine ⟨u, z.im, mul_left_cancel₀ ha ?_⟩
    have hzeq : (⟨f.a * u, z.im⟩ : f.Order) = z := QuadraticAlgebra.ext hu.symm rfl
    rw [← norm_formIdeal_element, hzeq, hn]

end BinQuadForm
