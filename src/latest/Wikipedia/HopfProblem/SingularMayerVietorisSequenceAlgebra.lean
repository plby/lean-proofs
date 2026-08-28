import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Integral homology sequences of actual short exact chain sequences

These helpers express Mathlib's actual connecting homomorphism and its
exactness as integral linear maps. The source sequence is a short complex
of genuine chain complexes, with a proof of short exactness. The later
small-chain Mayer–Vietoris instance supplies that proof from singular
chains; no excision or comparison with full-space homology is assumed here.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- The actual homology functor map, viewed as an integral linear map. -/
abbrev homologyLinearMap (f : K ⟶ L) (n : ℕ) : K.homology n →ₗ[ℤ] L.homology n :=
  (HomologicalComplex.homologyMap f n).hom

theorem homologyLinearMap_comp (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    homologyLinearMap (f ≫ g) n = (homologyLinearMap g n).comp (homologyLinearMap f n) :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp f g n)

@[simp] theorem homologyLinearMap_zero (n : ℕ) :
    homologyLinearMap (0 : K ⟶ L) n = 0 :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_zero K L n)

@[simp] theorem homologyLinearMap_add (f g : K ⟶ L) (n : ℕ) :
    homologyLinearMap (f + g) n = homologyLinearMap f n + homologyLinearMap g n :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_add f g n)

@[simp] theorem homologyLinearMap_neg (f : K ⟶ L) (n : ℕ) :
    homologyLinearMap (-f) n = -homologyLinearMap f n :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_neg f n)

variable {S T : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)

/-- Mathlib's actual connecting homomorphism, from degree `n+1` to degree `n`. -/
def connectingMap (n : ℕ) : S.X₃.homology (n + 1) →ₗ[ℤ] S.X₁.homology n :=
  (hS.δ (n + 1) n (by simp)).hom

theorem connectingMap_comp_first (n : ℕ) :
    (homologyLinearMap S.f n).comp (connectingMap hS n) = 0 :=
  congrArg ModuleCat.Hom.hom (hS.δ_comp (n + 1) n (by simp))

theorem second_comp_connectingMap (n : ℕ) :
    (connectingMap hS n).comp (homologyLinearMap S.g (n + 1)) = 0 :=
  congrArg ModuleCat.Hom.hom (hS.comp_δ (n + 1) n (by simp))

theorem first_comp_second (n : ℕ) :
    (homologyLinearMap S.g n).comp (homologyLinearMap S.f n) = 0 := by
  rw [← homologyLinearMap_comp, S.zero, homologyLinearMap_zero]

/-- Exactness at the homology of the first complex, in every degree. -/
theorem exact_at_leftHomology (n : ℕ) :
    LinearMap.range (connectingMap hS n) = LinearMap.ker (homologyLinearMap S.f n) :=
  (hS.homology_exact₁ (n + 1) n (by simp)).moduleCat_range_eq_ker

include hS in
/-- Exactness at the homology of the middle complex, in every degree. -/
theorem exact_at_middleHomology (n : ℕ) :
    LinearMap.range (homologyLinearMap S.f n) =
      LinearMap.ker (homologyLinearMap S.g n) :=
  (hS.homology_exact₂ n).moduleCat_range_eq_ker

/-- Exactness at positive-degree homology of the third complex. -/
theorem exact_at_rightHomology (n : ℕ) :
    LinearMap.range (homologyLinearMap S.g (n + 1)) =
      LinearMap.ker (connectingMap hS n) :=
  (hS.homology_exact₃ (n + 1) n (by simp)).moduleCat_range_eq_ker

include hS in
/-- The degree-zero map onto the third complex's homology is surjective. -/
theorem homologyLinearMap_second_zero_surjective :
    Function.Surjective (homologyLinearMap S.g 0) := by
  have := hS.epi_g
  have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Naturality of the actual connecting homomorphisms in a morphism of
proved short exact sequences of chain complexes. -/
theorem connectingMap_naturality (φ : S ⟶ T) (hT : T.ShortExact) (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp (connectingMap hS n) =
      (connectingMap hT n).comp (homologyLinearMap φ.τ₃ (n + 1)) :=
  congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality φ hS hT (n + 1) n (by simp))

/-- A cycle's class in the actual categorical homology object. -/
def homologyClassOfCycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) {i : ℕ}
    (z : K.X i) (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j)
    (hz : (K.d i j).hom z = 0) : K.homology i :=
  (K.homologyπ i).hom (K.cyclesMk z j hj hz)

include hS in
/-- In an actual short exact sequence, a lift of the boundary of a lifted
chain is a cycle in the first complex. -/
theorem connectingMap_lift_is_cycle (n : ℕ) (z₂ : S.X₂.X (n + 1))
    (z₁ : S.X₁.X n) (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂)
    (k : ℕ) : (S.X₁.d n k).hom z₁ = 0 :=
  hS.d_eq_zero_of_f_eq_d_apply (n + 1) n z₂ z₁ hz₁ k

/-- The actual connecting homomorphism has the standard lift–boundary
formula on genuine cycle classes. -/
theorem connectingMap_homologyClassOfCycle (n : ℕ)
    (z₃ : S.X₃.X (n + 1)) (hz₃ : (S.X₃.d (n + 1) n).hom z₃ = 0)
    (z₂ : S.X₂.X (n + 1)) (hz₂ : (S.g.f (n + 1)).hom z₂ = z₃)
    (z₁ : S.X₁.X n) (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂) :
    connectingMap hS n
        (homologyClassOfCycle S.X₃ z₃ n
          ((ComplexShape.down ℕ).next_eq' (by simp)) hz₃) =
      homologyClassOfCycle S.X₁ z₁ ((ComplexShape.down ℕ).next n) rfl
        (connectingMap_lift_is_cycle hS n z₂ z₁ hz₁ _) :=
  hS.δ_apply (n + 1) n (by simp) z₃ hz₃ z₂ hz₂ z₁ hz₁ _ rfl

end Wikipedia.HopfProblem.SingularMayerVietoris
