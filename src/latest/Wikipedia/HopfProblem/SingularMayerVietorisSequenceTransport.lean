import Wikipedia.HopfProblem.SingularMayerVietorisSequenceAlgebra
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceProduct

/-!
# Exactness after identifying biproduct homology with a product

The genuine homology sequence of a proved short exact chain sequence is
transported through the proved homology equivalence for its middle biproduct.
The connecting map is unchanged. The two adjacent maps are the actual
induced homology maps, written in product coordinates.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {A K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- The first actual induced homology map, in middle product coordinates. -/
def biprodSequenceFirstMap (f : A ⟶ K ⊞ L) (n : ℕ) :
    A.homology n →ₗ[ℤ] (K.homology n × L.homology n) :=
  (homologyBiprodEquiv K L n).toLinearMap.comp (homologyLinearMap f n)

/-- The second actual induced homology map, from middle product coordinates. -/
def biprodSequenceSecondMap (g : K ⊞ L ⟶ B) (n : ℕ) :
    (K.homology n × L.homology n) →ₗ[ℤ] B.homology n :=
  (homologyLinearMap g n).comp (homologyBiprodEquiv K L n).symm.toLinearMap

@[simp] theorem biprodSequenceFirstMap_apply (f : A ⟶ K ⊞ L) (n : ℕ)
    (a : A.homology n) :
    biprodSequenceFirstMap f n a = homologyBiprodEquiv K L n (homologyLinearMap f n a) :=
  rfl

@[simp] theorem biprodSequenceSecondMap_apply (g : K ⊞ L ⟶ B) (n : ℕ)
    (a : K.homology n × L.homology n) :
    biprodSequenceSecondMap g n a =
      homologyLinearMap g n ((homologyBiprodEquiv K L n).symm a) := rfl

/-- An actual chain-level lift induces the expected pair of homology maps. -/
theorem biprodSequenceFirstMap_lift (f : A ⟶ K) (g : A ⟶ L) (n : ℕ)
    (a : A.homology n) :
    biprodSequenceFirstMap (biprod.lift f g) n a =
      (homologyLinearMap f n a, homologyLinearMap g n a) :=
  homologyBiprodEquiv_lift n f g a

/-- The signed first map of Mayer--Vietoris has signs `(+,-)` on homology. -/
theorem biprodSequenceFirstMap_lift_neg (f : A ⟶ K) (g : A ⟶ L) (n : ℕ)
    (a : A.homology n) :
    biprodSequenceFirstMap (biprod.lift f (-g)) n a =
      (homologyLinearMap f n a, -homologyLinearMap g n a) :=
  homologyBiprodEquiv_lift_neg n f g a

/-- A map out of the biproduct induces the sum of its two homology maps. -/
theorem biprodSequenceSecondMap_desc (f : K ⟶ B) (g : L ⟶ B) (n : ℕ)
    (a : K.homology n × L.homology n) :
    biprodSequenceSecondMap (biprod.desc f g) n a =
      homologyLinearMap f n a.1 + homologyLinearMap g n a.2 :=
  homologyBiprodEquiv_desc n f g a

variable {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
  (hS : (ShortComplex.mk f g hfg).ShortExact)

/-- Exactness at the first homology module after replacing middle homology
by its proved product coordinates. -/
theorem biprodSequence_exact_at_leftHomology (n : ℕ) :
    LinearMap.range (connectingMap hS n) = LinearMap.ker (biprodSequenceFirstMap f n) := by
  rw [exact_at_leftHomology hS n]
  ext a
  change homologyLinearMap f n a = 0 ↔
    homologyBiprodEquiv K L n (homologyLinearMap f n a) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (homologyBiprodEquiv K L n).injective (h.trans (map_zero _).symm)

include hS in
/-- Exactness at the genuine product of the two middle homology modules. -/
theorem biprodSequence_exact_at_middleHomology (n : ℕ) :
    LinearMap.range (biprodSequenceFirstMap f n) =
      LinearMap.ker (biprodSequenceSecondMap g n) := by
  ext a
  change (∃ b, homologyBiprodEquiv K L n (homologyLinearMap f n b) = a) ↔
    homologyLinearMap g n ((homologyBiprodEquiv K L n).symm a) = 0
  constructor
  · rintro ⟨b, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hb : homologyLinearMap f n b ∈ LinearMap.range (homologyLinearMap f n) :=
      ⟨b, rfl⟩
    rw [exact_at_middleHomology hS n] at hb
    exact hb
  · intro ha
    have hb : (homologyBiprodEquiv K L n).symm a ∈
        LinearMap.range (homologyLinearMap f n) := by
      rw [exact_at_middleHomology hS n]
      exact ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, (congrArg (homologyBiprodEquiv K L n) hb).trans
      ((homologyBiprodEquiv K L n).apply_symm_apply a)⟩

/-- Exactness at positive-degree homology of the right complex, with the
middle module in product coordinates. -/
theorem biprodSequence_exact_at_rightHomology (n : ℕ) :
    LinearMap.range (biprodSequenceSecondMap g (n + 1)) =
      LinearMap.ker (connectingMap hS n) := by
  rw [← exact_at_rightHomology hS n]
  ext b
  change (∃ a, homologyLinearMap g (n + 1)
      ((homologyBiprodEquiv K L (n + 1)).symm a) = b) ↔
    ∃ a, homologyLinearMap g (n + 1) a = b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(homologyBiprodEquiv K L (n + 1)).symm a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨homologyBiprodEquiv K L (n + 1) a, ?_⟩
    rwa [LinearEquiv.symm_apply_apply]

include hS in
/-- The product-coordinate map onto degree-zero right homology is surjective. -/
theorem biprodSequence_second_zero_surjective :
    Function.Surjective (biprodSequenceSecondMap g 0) :=
  (homologyLinearMap_second_zero_surjective hS).comp
    (homologyBiprodEquiv K L 0).symm.surjective

end Wikipedia.HopfProblem.SingularMayerVietoris
