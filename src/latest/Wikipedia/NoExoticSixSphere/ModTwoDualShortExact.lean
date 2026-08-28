import Wikipedia.NoExoticSixSphere.ModTwoDualHomotopy
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Actual mod-two duals of degreewise split chain sequences

Projectivity of the actual right-hand chain modules gives a splitting
in each degree. Opposite duality preserves those splittings, proving
short exactness of the original reversed cochain sequence. No exactness
of the dual functor on arbitrary integer modules is assumed.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.ModTwoDualComplex

theorem map_zero (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) : map (0 : K ⟶ L) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change L.X n →+ ZMod 2 at α
  apply AddMonoidHom.ext
  intro c
  exact α.map_zero

/-- The original chain sequence, dualized in the opposite direction. -/
def sequence (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (map S.g) (map S.f) (by rw [← map_comp, S.zero, map_zero])

/-- Each genuine degree sequence is short exact, via its proved projective splitting. -/
theorem sequence_degree_shortExact (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ))
    (hS : S.ShortExact) (n : ℕ) [Projective (S.X₃.X n)] :
    ((sequence S).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n)).ShortExact := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  let : Projective
      ((S.map (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).X₃) :=
    inferInstanceAs (Projective (S.X₃.X n))
  exact ((hd.splittingOfProjective.op).map moduleDualFunctor).shortExact

/-- Degreewise projectivity of the original quotient terms suffices for dual short exactness. -/
theorem sequence_shortExact (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ))
    (hS : S.ShortExact) [∀ n, Projective (S.X₃.X n)] : (sequence S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact (sequence S)
    (fun n => sequence_degree_shortExact S hS n)

end NoExoticSixSphere.ModTwoDualComplex
