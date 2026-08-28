import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCocycleSplittingExtension
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCocycleSplittingFree
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycleAlgebra

/-!
# Symmetric lattice cocycles are actual integer coboundaries

The abelian cocycle extension projects onto the lattice.  Lifting the
four coordinate vectors produces an additive section, whose first
coordinate is the required normalized integer cochain.  The final
theorem applies this construction to the difference of two logarithmic
defects with the same alternating commutator.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

namespace SymmetricIntegerCocycle

/-- A lattice marked by four integer coordinates splits its symmetric cocycle extension. -/
theorem exists_coboundary_of_equiv_int_four {Λ : Type*} [AddCommGroup Λ]
    (c : SymmetricIntegerCocycle Λ) (e : Λ ≃+ (Fin 4 → ℤ)) :
    ∃ b : Λ → ℤ, b 0 = 0 ∧ ∀ l m, c.value l m = b (l + m) - b l - b m := by
  let f : c.Extension →+ (Fin 4 → ℤ) := e.toAddMonoidHom.comp c.projection
  have hf : Function.Surjective f := e.surjective.comp c.projection_surjective
  obtain ⟨s, hs⟩ := exists_additive_section_int_four f hf
  let t : Λ →+ c.Extension := s.comp e.toAddMonoidHom
  have ht : c.projection.comp t = AddMonoidHom.id Λ := by
    ext l
    apply e.injective
    exact DFunLike.congr_fun hs (e l)
  exact ⟨fun l => (t l).integer, c.coboundary_of_section t ht⟩

end SymmetricIntegerCocycle

/-- Every normalized symmetric integer two-cocycle on the actual period lattice is a
coboundary, with the positive logarithmic-defect sign convention. -/
theorem exists_integer_coboundary_of_symmetric_cocycle (p : PeriodDomain)
    (c : p.lattice → p.lattice → ℤ)
    (hcocycle : ∀ l m k, c l m + c (l + m) k = c m k + c l (m + k))
    (hzero_left : ∀ l, c 0 l = 0) (hzero_right : ∀ l, c l 0 = 0)
    (hsymm : ∀ l m, c l m = c m l) :
    ∃ b : p.lattice → ℤ, b 0 = 0 ∧ ∀ l m, c l m = b (l + m) - b l - b m := by
  let C : SymmetricIntegerCocycle p.lattice :=
    { value := c
      cocycle := hcocycle
      zero_left := hzero_left
      zero_right := hzero_right
      symmetric := hsymm }
  exact C.exists_coboundary_of_equiv_int_four p.latticeEquiv

namespace HasIntegerLogDefect

/-- Equal alternating commutators force normalized logarithmic integer defects to differ
by an actual integer coboundary. -/
theorem exists_coboundary_of_same_commutator {p : PeriodDomain}
    {b b' : p.lattice → ComplexPlane₂ → ℂ} {n n' : p.lattice → p.lattice → ℤ}
    (h : HasIntegerLogDefect p b n) (h' : HasIntegerLogDefect p b' n')
    (hb : ∀ z, b 0 z = 0) (hb' : ∀ z, b' 0 z = 0)
    (hcomm : ∀ l m, integerLogCommutator n l m = integerLogCommutator n' l m) :
    ∃ a : p.lattice → ℤ, a 0 = 0 ∧ ∀ l m,
      n l m - n' l m = a (l + m) - a l - a m := by
  apply exists_integer_coboundary_of_symmetric_cocycle p (fun l m => n l m - n' l m)
  · intro l m k
    linear_combination h.cocycle l m k - h'.cocycle l m k
  · intro l
    rw [h.zero_left hb, h'.zero_left hb', sub_self]
  · intro l
    rw [h.zero_right hb, h'.zero_right hb', sub_self]
  · intro l m
    have hc := hcomm l m
    simp only [integerLogCommutator] at hc
    linear_combination hc

/-- Equality of the bundled alternating integral forms gives the same coboundary conclusion. -/
theorem exists_coboundary_of_same_alternatingForm {p : PeriodDomain}
    {b b' : p.lattice → ComplexPlane₂ → ℂ} {n n' : p.lattice → p.lattice → ℤ}
    (h : HasIntegerLogDefect p b n) (h' : HasIntegerLogDefect p b' n')
    (hb : ∀ z, b 0 z = 0) (hb' : ∀ z, b' 0 z = 0)
    (hform : integerLogAlternatingForm h = integerLogAlternatingForm h') :
    ∃ a : p.lattice → ℤ, a 0 = 0 ∧ ∀ l m,
      n l m - n' l m = a (l + m) - a l - a m := by
  apply h.exists_coboundary_of_same_commutator h' hb hb'
  intro l m
  exact congrArg (fun E => E l m) hform

end HasIntegerLogDefect

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
