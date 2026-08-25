import Util.Bernays.DiscriminantOrder
import Util.Bernays.IdealNormCorrespondence
import Util.Bernays.IdealTransport

/-!
# The represented-value problem in the common discriminant class group
-/

namespace BinQuadForm

noncomputable def canonicalIdeal {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    letI := hf.discriminantOrderIsDomain
    Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr) :=
  letI := hf.orderIsDomain
  letI := hf.discriminantOrderIsDomain
  Bernays.InvertibleIdeal.map f.orderEquivDiscriminant ⟨f.formIdeal, formIdeal_isUnit hf hp⟩

noncomputable def canonicalClass {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    letI := hf.discriminantOrderIsDomain
    ClassGroup (Bernays.DiscriminantOrder f.discr) :=
  letI := hf.discriminantOrderIsDomain
  (canonicalIdeal hf hp).idealClass

theorem represented_pos_iff_canonicalClass_norm {f : BinQuadForm}
    (hf : f.PosDef) (hp : f.Primitive) {n : ℕ} (hn : 0 < n) :
    letI := hf.discriminantOrderIsDomain
    (∃ u v : ℤ, f.eval u v = (n : ℤ)) ↔
      ∃ J : Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr),
        J.idealClass * f.canonicalClass hf hp = 1 ∧
          (J : Ideal (Bernays.DiscriminantOrder f.discr)).cardQuot = n := by
  letI := hf.orderIsDomain
  letI := hf.discriminantOrderIsDomain
  let I : Bernays.InvertibleIdeal f.Order := ⟨f.formIdeal, formIdeal_isUnit hf hp⟩
  let e := f.orderEquivDiscriminant
  rw [represented_pos_iff_idealClass_norm hf hp hn]
  change (∃ J : Bernays.InvertibleIdeal f.Order,
    J.idealClass * I.idealClass = 1 ∧ (J : Ideal f.Order).cardQuot = n) ↔
    ∃ J : Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr),
      J.idealClass * (Bernays.InvertibleIdeal.map e I).idealClass = 1 ∧
        (J : Ideal (Bernays.DiscriminantOrder f.discr)).cardQuot = n
  constructor
  · rintro ⟨J, hc, hN⟩
    refine ⟨Bernays.InvertibleIdeal.map e J,
      (Bernays.InvertibleIdeal.map_idealClass_mul_eq_one_iff e J I).mpr hc, ?_⟩
    rwa [Bernays.InvertibleIdeal.cardQuot_map]
  · rintro ⟨J, hc, hN⟩
    refine ⟨Bernays.InvertibleIdeal.map e.symm J, ?_, ?_⟩
    · apply (Bernays.InvertibleIdeal.map_idealClass_mul_eq_one_iff e _ I).mp
      rwa [Bernays.InvertibleIdeal.map_map_symm]
    · rwa [Bernays.InvertibleIdeal.cardQuot_map]

end BinQuadForm
