import Util.Bernays.GoodQuadraticIdeals

/-!
# Canonical split-prime classes for arbitrary negative quadratic orders
-/

namespace Bernays

def SplitPrime (d b : ℤ) := {q : ℕ // q.Prime ∧ ¬(q : ℤ) ∣ b ^ 2 + 4 * d ∧
  ∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r}

namespace SplitPrime

variable {d b : ℤ}

instance (s : SplitPrime d b) : Fact s.1.Prime := ⟨s.2.1⟩

noncomputable def root (s : SplitPrime d b) : ZMod s.1 := s.2.2.2.choose

theorem root_sq (s : SplitPrime d b) : (root s) ^ 2 =
    (d : ZMod s.1) + (b : ZMod s.1) * root s := s.2.2.2.choose_spec

theorem discr_ne_zero (s : SplitPrime d b) :
    (b : ZMod s.1) ^ 2 + 4 * (d : ZMod s.1) ≠ 0 := by
  intro h
  apply s.2.2.1
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h

noncomputable def orientedRoot (s : SplitPrime d b) (ε : Bool) : ZMod s.1 :=
  if ε then (b : ZMod s.1) - s.root else s.root

theorem orientedRoot_sq (s : SplitPrime d b) (ε : Bool) :
    (s.orientedRoot ε) ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * s.orientedRoot ε := by
  cases ε
  · exact s.root_sq
  · exact quadratic_conjugate_root _ _ _ s.root_sq

noncomputable def ideal (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    InvertibleIdeal (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  ⟨rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε),
    rootIdeal_isUnit hD _ _ (s.orientedRoot_sq ε) s.discr_ne_zero⟩

theorem ideal_cardQuot (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 :=
  rootIdeal_cardQuot d b s.1 _ _

theorem ideal_isMaximal (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal :=
  rootIdeal_isMaximal d b s.1 _ _

noncomputable def idealClass (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  (s.ideal hD false).idealClass

theorem ideal_mul_conjugate (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ((s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)) * (s.ideal hD true : Ideal _)) =
      Ideal.span ({((s.1 : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) := by
  let := quadraticOrderIsDomain hD
  exact rootIdeal_mul d b s.1 s.root_sq (s.orientedRoot_sq true)
    (quadratic_roots_distinct _ _ _ s.root_sq s.discr_ne_zero)

theorem idealClass_conjugate (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD true).idealClass = (s.idealClass hD)⁻¹ := by
  let := quadraticOrderIsDomain hD
  have hq : ((s.1 : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : (s.1 : ℤ) = 0 := by simpa using hr
    exact s.2.1.ne_zero (by exact_mod_cast this)
  have hprod : s.ideal hD false * s.ideal hD true =
      InvertibleIdeal.principal ((s.1 : ℤ) : QuadraticAlgebra ℤ d b) hq :=
    InvertibleIdeal.ext (s.ideal_mul_conjugate hD)
  have hc := congrArg InvertibleIdeal.idealClass hprod
  rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at hc
  change (s.ideal hD true).idealClass = (s.ideal hD false).idealClass⁻¹
  calc
    _ = (s.ideal hD false).idealClass⁻¹ *
        ((s.ideal hD false).idealClass * (s.ideal hD true).idealClass) := by simp
    _ = _ := by rw [hc, mul_one]

theorem root_eq_or_conjugate (s : SplitPrime d b) (r : ZMod s.1)
    (hr : r ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * r) :
    r = s.root ∨ r = (b : ZMod s.1) - s.root := by
  have h : (r - s.root) * (r - ((b : ZMod s.1) - s.root)) = 0 := by
    linear_combination hr - s.root_sq
  exact (mul_eq_zero.mp h).imp sub_eq_zero.mp sub_eq_zero.mp

theorem oriented_idealClass_mem_iff (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), ∀ ε : Bool,
      (s.ideal hD ε).idealClass ∈ H ↔ s.idealClass hD ∈ H := by
  let := quadraticOrderIsDomain hD
  intro H ε
  cases ε
  · rfl
  · rw [s.idealClass_conjugate hD, H.inv_mem_iff]

end SplitPrime

end Bernays
