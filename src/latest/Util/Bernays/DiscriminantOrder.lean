import Util.Bernays.FormIdeal

/-!
# A common order for every form of a given discriminant
-/

namespace Bernays

def discriminantTrace (D : ℤ) : ℤ := D % 2

def discriminantConstant (D : ℤ) : ℤ := (D - (discriminantTrace D) ^ 2) / 4

abbrev DiscriminantOrder (D : ℤ) :=
  QuadraticAlgebra ℤ (discriminantConstant D) (discriminantTrace D)

def quadraticOrderCongr {d b d' b' : ℤ} (hd : d = d') (hb : b = b') :
    QuadraticAlgebra ℤ d b ≃+* QuadraticAlgebra ℤ d' b' := by
  subst d'
  subst b'
  exact RingEquiv.refl _

theorem quadraticOrderCongr_norm {d b d' b' : ℤ} (hd : d = d') (hb : b = b')
    (z : QuadraticAlgebra ℤ d b) : (quadraticOrderCongr hd hb z).norm = z.norm := by
  subst d'
  subst b'
  rfl

end Bernays

namespace BinQuadForm

theorem b_emod_two (f : BinQuadForm) : f.b % 2 = f.discr % 2 := by
  have h : f.b % 2 = 0 ∨ f.b % 2 = 1 := by omega
  rcases h with h | h <;> simp [discr, Int.sub_emod, Int.mul_emod, h]

theorem b_eq_discriminantTrace (f : BinQuadForm) :
    f.b = Bernays.discriminantTrace f.discr + 2 * (f.b / 2) := by
  rw [Bernays.discriminantTrace, ← f.b_emod_two]
  omega

theorem discriminantConstant_eq (f : BinQuadForm) :
    Bernays.discriminantConstant f.discr =
      -f.a * f.c + Bernays.discriminantTrace f.discr * (f.b / 2) + (f.b / 2) ^ 2 := by
  have heq : f.discr - (Bernays.discriminantTrace f.discr) ^ 2 =
      4 * (-f.a * f.c + Bernays.discriminantTrace f.discr * (f.b / 2) + (f.b / 2) ^ 2) := by
    have hD : f.discr = f.b ^ 2 - 4 * f.a * f.c := by simp only [discr, pow_two]
    linear_combination hD +
      (f.b + Bernays.discriminantTrace f.discr + 2 * (f.b / 2)) * f.b_eq_discriminantTrace
  rw [Bernays.discriminantConstant, heq]
  omega

theorem canonical_order_discr (f : BinQuadForm) :
    (Bernays.discriminantTrace f.discr) ^ 2 + 4 * Bernays.discriminantConstant f.discr =
      f.discr := by
  rw [f.discriminantConstant_eq]
  conv_rhs => rw [discr, f.b_eq_discriminantTrace]
  ring

theorem orderConstant_eq_shift (f : BinQuadForm) :
    -f.a * f.c = Bernays.discriminantConstant f.discr -
      Bernays.discriminantTrace f.discr * (f.b / 2) - (f.b / 2) ^ 2 := by
  rw [f.discriminantConstant_eq]
  ring

def orderEquivDiscriminant (f : BinQuadForm) : f.Order ≃+* Bernays.DiscriminantOrder f.discr :=
  (Bernays.quadraticOrderCongr f.orderConstant_eq_shift f.b_eq_discriminantTrace).trans
    (Bernays.quadraticOrderShift (Bernays.discriminantConstant f.discr)
      (Bernays.discriminantTrace f.discr) (f.b / 2))

theorem orderEquivDiscriminant_norm (f : BinQuadForm) (z : f.Order) :
    (f.orderEquivDiscriminant z).norm = z.norm := by
  change (Bernays.quadraticOrderShift _ _ _ (Bernays.quadraticOrderCongr _ _ z)).norm = z.norm
  rw [Bernays.quadraticOrderShift_norm, Bernays.quadraticOrderCongr_norm]

theorem PosDef.discriminantOrderIsDomain {f : BinQuadForm} (hf : f.PosDef) :
    IsDomain (Bernays.DiscriminantOrder f.discr) :=
  Bernays.quadraticOrderIsDomain (f.canonical_order_discr.trans_lt hf.2)

end BinQuadForm
