import Util.Bernays.FormIdeal
import Util.Bernays.InvertibleIdeal
import Mathlib.Data.ZMod.Basic

/-!
# Prime ideals of a quadratic order away from the discriminant
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticReduction (d b : ℤ) (q : ℕ) :
    QuadraticAlgebra ℤ d b →+* QuadraticAlgebra (ZMod q) (d : ZMod q) (b : ZMod q) where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem quadraticReduction_surjective (d b : ℤ) (q : ℕ) :
    Function.Surjective (quadraticReduction d b q) := by
  intro z
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective z.re
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective z.im
  exact ⟨⟨u, v⟩, QuadraticAlgebra.ext hu hv⟩

theorem quadraticReduction_ker (d b : ℤ) (q : ℕ) :
    RingHom.ker (quadraticReduction d b q) =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, BinQuadForm.quadratic_intCast_dvd]
  change (QuadraticAlgebra.mk (z.re : ZMod q) (z.im : ZMod q) = 0) ↔ _
  rw [QuadraticAlgebra.ext_iff]
  simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem cardQuot_ker_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) :
    (RingHom.ker φ).cardQuot = Nat.card S :=
  Nat.card_congr (RingHom.quotientKerEquivOfSurjective hφ).toEquiv

theorem quadraticReduction_cardQuot (d b : ℤ) (q : ℕ) [NeZero q] :
    (RingHom.ker (quadraticReduction d b q)).cardQuot = q ^ 2 := by
  rw [cardQuot_ker_of_surjective _ (quadraticReduction_surjective d b q)]
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (d : ZMod q) (b : ZMod q)),
    Nat.card_prod, Nat.card_zmod, pow_two]

theorem inertIdeal_isMaximal (d b : ℤ) (q : ℕ) [Fact q.Prime]
    (hirr : ∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r) :
    (Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b))).IsMaximal := by
  letI : Fact (∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r) := ⟨hirr⟩
  rw [← quadraticReduction_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (quadraticReduction_surjective d b q)

def quadraticEval (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    QuadraticAlgebra ℤ d b →+* ZMod q where
  toFun z := (z.re : ZMod q) + (z.im : ZMod q) * r
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul]
    linear_combination -(x.im : ZMod q) * (y.im : ZMod q) * hr

theorem quadraticEval_surjective (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    Function.Surjective (quadraticEval d b q r hr) := by
  intro a
  obtain ⟨u, rfl⟩ := ZMod.intCast_surjective a
  exact ⟨⟨u, 0⟩, by simp [quadraticEval]⟩

def rootIdeal (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) : Ideal (QuadraticAlgebra ℤ d b) :=
  RingHom.ker (quadraticEval d b q r hr)

theorem rootIdeal_cardQuot (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    (rootIdeal d b q r hr).cardQuot = q := by
  rw [rootIdeal, cardQuot_ker_of_surjective _ (quadraticEval_surjective d b q r hr)]
  exact Nat.card_zmod q

theorem rootIdeal_isMaximal (d b : ℤ) (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    (rootIdeal d b q r hr).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (quadraticEval_surjective d b q r hr)

theorem rootIdeal_ne_of_ne (d b : ℤ) (q : ℕ) [NeZero q] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr ≠ rootIdeal d b q s hs := by
  intro heq
  let z : QuadraticAlgebra ℤ d b := ⟨-(r.val : ℤ), 1⟩
  have hz : z ∈ rootIdeal d b q r hr := by
    simp [rootIdeal, quadraticEval, z, RingHom.mem_ker]
  rw [heq] at hz
  have hz' : -r + s = 0 := by simpa [rootIdeal, quadraticEval, z, RingHom.mem_ker] using hz
  exact hrs (eq_of_sub_eq_zero (by linear_combination -hz'))

theorem rootIdeal_inf (d b : ℤ) (q : ℕ) [Fact q.Prime] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr ⊓ rootIdeal d b q s hs =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  rw [← quadraticReduction_ker]
  ext z
  change ((z.re : ZMod q) + (z.im : ZMod q) * r = 0 ∧
    (z.re : ZMod q) + (z.im : ZMod q) * s = 0) ↔ quadraticReduction d b q z = 0
  constructor
  · rintro ⟨hrz, hsz⟩
    have him : (z.im : ZMod q) = 0 := by
      apply (mul_eq_zero.mp (show (z.im : ZMod q) * (r - s) = 0 from by
        linear_combination hrz - hsz)).resolve_right (sub_ne_zero.mpr hrs)
    have hre : (z.re : ZMod q) = 0 := by simpa [him] using hrz
    exact QuadraticAlgebra.ext hre him
  · intro hz
    have hre := congrArg QuadraticAlgebra.re hz
    have him := congrArg QuadraticAlgebra.im hz
    change (z.re : ZMod q) = 0 at hre
    change (z.im : ZMod q) = 0 at him
    simp [hre, him]

theorem rootIdeal_mul (d b : ℤ) (q : ℕ) [Fact q.Prime] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr * rootIdeal d b q s hs =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  rw [Ideal.mul_eq_inf_of_coprime ((rootIdeal_isMaximal d b q r hr).coprime_of_ne
    (rootIdeal_isMaximal d b q s hs) (rootIdeal_ne_of_ne d b q hr hs hrs))]
  exact rootIdeal_inf d b q hr hs hrs

end Bernays
