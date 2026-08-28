import Wikipedia.HopfProblem.EllipticFirstHomologyAbelianization
import Wikipedia.HopfProblem.EllipticFirstHomologyPrimitive
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Rank two and the marked lattice map in the actual abelianization

Admissibility gives integral Bézout coefficients for `γ(v)` and `m`.
The explicit primitive-relation quotient therefore identifies the actual
affine-group abelianization with a free rank-two lattice. Both translation
and affine-generator coordinates are computed. The source's main twists
are also given a marking in which the affine generator is `(1,0)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- An explicit rank-two coordinate system for any chosen Bézout identity. -/
def deckAbelianizationEquivOfBezout (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (u t : ℤ) (hbez : u * γ v + t * (j.order : ℤ) = 1) :
    DeckAbelianization j v ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (deckAbelianizationQuotientEquiv j v hv).trans
    (PrimitiveRelation.quotientEquiv (γ v) (psi j v) (j.order : ℤ) u t hbez)

@[simp] theorem deckAbelianizationEquivOfBezout_translation
    (j : Kind) (v w : Lattice) (hv : AdmissibleTwist j v)
    (u t : ℤ) (hbez : u * γ v + t * (j.order : ℤ) = 1) :
    deckAbelianizationEquivOfBezout j v hv u t hbez (deckAbelianTranslation j v w) =
      ![(j.order : ℤ) * γ w, psi j w - psi j v * (u * γ w)] := by
  change PrimitiveRelation.quotientEquiv _ _ _ _ _ hbez
    (deckAbelianizationQuotientEquiv j v hv (deckAbelianTranslation j v w)) = _
  rw [deckAbelianizationQuotientEquiv_translation]
  change PrimitiveRelation.quotientEquiv _ _ _ _ _ hbez
    (Submodule.Quotient.mk ![γ w, psi j w, 0]) = _
  rw [PrimitiveRelation.quotientEquiv_mk]
  simp [PrimitiveRelation.projection]

@[simp] theorem deckAbelianizationEquivOfBezout_generator
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (u t : ℤ) (hbez : u * γ v + t * (j.order : ℤ) = 1) :
    deckAbelianizationEquivOfBezout j v hv u t hbez (deckAbelianGenerator j v) =
      ![γ v, psi j v * t] := by
  change PrimitiveRelation.quotientEquiv _ _ _ _ _ hbez
    (deckAbelianizationQuotientEquiv j v hv (deckAbelianGenerator j v)) = _
  rw [deckAbelianizationQuotientEquiv_generator]
  change PrimitiveRelation.quotientEquiv _ _ _ _ _ hbez
    (Submodule.Quotient.mk ![0, 0, 1]) = _
  rw [PrimitiveRelation.quotientEquiv_mk]
  simp [PrimitiveRelation.projection]

def twistBezoutLeft (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) : ℤ :=
  Classical.choose (admissible_gamma_bezout j v hv)

def twistBezoutRight (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) : ℤ :=
  Classical.choose (Classical.choose_spec (admissible_gamma_bezout j v hv))

theorem twistBezout_spec (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    twistBezoutLeft j v hv * γ v + twistBezoutRight j v hv * (j.order : ℤ) = 1 :=
  Classical.choose_spec (Classical.choose_spec (admissible_gamma_bezout j v hv))

/-- Every admissible twist has actual abelianization isomorphic to `ℤ²`. -/
def deckAbelianizationRankTwoEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    DeckAbelianization j v ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  deckAbelianizationEquivOfBezout j v hv (twistBezoutLeft j v hv)
    (twistBezoutRight j v hv) (twistBezout_spec j v hv)

theorem deckAbelianization_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.Free ℤ (DeckAbelianization j v) :=
  Module.Free.of_equiv (deckAbelianizationRankTwoEquiv j v hv).symm

theorem deckAbelianization_finrank (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.finrank ℤ (DeckAbelianization j v) = 2 := by
  rw [(deckAbelianizationRankTwoEquiv j v hv).finrank_eq]
  simp

theorem deckAbelianization_torsionFree (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.IsTorsionFree ℤ (DeckAbelianization j v) := by
  let := deckAbelianization_free j v hv
  infer_instance

/-- The exact translation image in any of these rank-two coordinates:
the first coordinate is divisible by the elliptic order. -/
theorem deckAbelianization_translation_image (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (u t : ℤ)
    (hbez : u * γ v + t * (j.order : ℤ) = 1) (z : Fin 2 → ℤ) :
    (∃ w : Lattice, deckAbelianizationEquivOfBezout j v hv u t hbez
        (deckAbelianTranslation j v w) = z) ↔ (j.order : ℤ) ∣ z 0 := by
  constructor
  · rintro ⟨w, hw⟩
    rw [deckAbelianizationEquivOfBezout_translation] at hw
    exact ⟨γ w, (congrFun hw 0).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨coinvariantSection j ![k, z 1 + psi j v * (u * k)], ?_⟩
    rw [deckAbelianizationEquivOfBezout_translation]
    have hsec := coinvariantMap_section j ![k, z 1 + psi j v * (u * k)]
    have hγ : γ (coinvariantSection j ![k, z 1 + psi j v * (u * k)]) = k :=
      congrFun hsec 0
    have hψ : psi j (coinvariantSection j ![k, z 1 + psi j v * (u * k)]) =
        z 1 + psi j v * (u * k) := congrFun hsec 1
    rw [hγ, hψ]
    ext i
    fin_cases i <;> simp [hk]

/-- In particular no new kernel is introduced when the coinvariant
lattice embeds in the actual abelianization. -/
theorem deckAbelianTranslation_ker (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    LinearMap.ker (deckAbelianTranslation j v) = LinearMap.range (coinvariantDifference j) := by
  rw [← coinvariantMap_ker_eq_range]
  ext w
  change deckAbelianTranslation j v w = 0 ↔ coinvariantMap j w = 0
  constructor
  · intro hw
    have he := congrArg (deckAbelianizationRankTwoEquiv j v hv) hw
    change deckAbelianizationEquivOfBezout j v hv _ _ _ (deckAbelianTranslation j v w) = _ at he
    rw [deckAbelianizationEquivOfBezout_translation, map_zero] at he
    have h0 : (j.order : ℤ) * γ w = 0 := congrFun he 0
    have hm : (j.order : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt j.order_pos)
    have hγ : γ w = 0 := (mul_eq_zero.mp h0).resolve_left hm
    have h1 : psi j w - psi j v * (twistBezoutLeft j v hv * γ w) = 0 := congrFun he 1
    have hψ : psi j w = 0 := by simpa [hγ] using h1
    ext i
    fin_cases i <;> simp [coinvariantMap, hγ, hψ]
  · intro hw
    rw [← deckAbelianTranslation_section j v w, hw, map_zero, map_zero]

/-- The integral coinvariant lattice embedded in the genuine abelianization. -/
def deckCoinvariantInclusion (j : Kind) (v : Lattice) :
    (Fin 2 → ℤ) →ₗ[ℤ] DeckAbelianization j v :=
  (deckAbelianTranslation j v).comp (coinvariantSection j)

theorem deckCoinvariantInclusion_coordinate (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (deckAbelianizationQuotientEquiv j v hv).toLinearMap.comp (deckCoinvariantInclusion j v) =
      PrimitiveRelation.translationMap (γ v) (psi j v) (j.order : ℤ) := by
  apply LinearMap.ext
  intro c
  change deckAbelianizationQuotientEquiv j v hv
    (deckAbelianTranslation j v (coinvariantSection j c)) = _
  rw [deckAbelianizationQuotientEquiv_translation]
  change Submodule.Quotient.mk (abelianCoordinateInclusion
    (coinvariantMap j (coinvariantSection j c))) = _
  rw [coinvariantMap_section]
  rfl

theorem deckCoinvariantInclusion_injective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Injective (deckCoinvariantInclusion j v) := by
  have hm : (j.order : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt j.order_pos)
  have hi := PrimitiveRelation.translationMap_injective (γ v) (psi j v) (j.order : ℤ)
    (twistBezoutLeft j v hv) (twistBezoutRight j v hv) (twistBezout_spec j v hv) hm
  intro c d hcd
  apply hi
  rw [← deckCoinvariantInclusion_coordinate j v hv]
  exact congrArg (deckAbelianizationQuotientEquiv j v hv) hcd

theorem deckAbelianTranslation_range (j : Kind) (v : Lattice) :
    LinearMap.range (deckAbelianTranslation j v) =
      LinearMap.range (deckCoinvariantInclusion j v) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨coinvariantMap j w, deckAbelianTranslation_section j v w⟩
  · rintro ⟨c, rfl⟩
    exact ⟨coinvariantSection j c, rfl⟩

/-- The translation image has exactly `m` cosets in the actual abelianization. -/
theorem deckAbelianTranslation_range_index (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (LinearMap.range (deckAbelianTranslation j v)).toAddSubgroup.index = j.order := by
  rw [deckAbelianTranslation_range]
  calc
    _ = (LinearMap.range
        (PrimitiveRelation.translationMap (γ v) (psi j v) (j.order : ℤ))).toAddSubgroup.index := by
      have hi : (LinearMap.range ((deckAbelianizationQuotientEquiv j v hv).toLinearMap.comp
          (deckCoinvariantInclusion j v))).toAddSubgroup.index =
          (LinearMap.range (deckCoinvariantInclusion j v)).toAddSubgroup.index := by
        rw [LinearMap.range_comp, Submodule.map_toAddSubgroup]
        exact AddSubgroup.index_map_equiv _ (deckAbelianizationQuotientEquiv j v hv).toAddEquiv
      exact hi.symm.trans (congrArg
        (fun f : (Fin 2 → ℤ) →ₗ[ℤ] AbelianCoordinateQuotient j v => f.range.toAddSubgroup.index)
        (deckCoinvariantInclusion_coordinate j v hv))
    _ = (j.order : ℤ).natAbs := PrimitiveRelation.translationMap_range_index
      (γ v) (psi j v) (j.order : ℤ) (twistBezoutLeft j v hv) (twistBezoutRight j v hv)
        (twistBezout_spec j v hv)
    _ = j.order := Int.natAbs_natCast j.order

/-- The sign in the source's main twist: `1` for order three, `-1` for order four. -/
def mainAbelianSign : Kind → ℤ
  | .three => 1
  | .four => -1

theorem mainAbelianSign_sq (j : Kind) : mainAbelianSign j * mainAbelianSign j = 1 := by
  cases j <;> rfl

theorem mainAbelianSign_gamma (j : Kind) : γ j.twist = mainAbelianSign j := by
  cases j <;> rfl

@[simp] theorem psi_mainTwist (j : Kind) : psi j j.twist = 0 := by
  cases j <;> decide

private theorem mainAbelianBezout (j : Kind) :
    mainAbelianSign j * γ j.twist + 0 * (j.order : ℤ) = 1 := by
  rw [mainAbelianSign_gamma, zero_mul, add_zero, mainAbelianSign_sq]

/-- Change the sign of the first coordinate when the main twist has negative sign. -/
def mainAbelianCoordinateSign (j : Kind) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![mainAbelianSign j * z 0, z 1]
  invFun z := ![mainAbelianSign j * z 0, z 1]
  left_inv z := by ext i; fin_cases i <;> simp [← mul_assoc, mainAbelianSign_sq]
  right_inv z := by ext i; fin_cases i <;> simp [← mul_assoc, mainAbelianSign_sq]
  map_add' z w := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' a z := by ext i; fin_cases i <;> simp [mul_left_comm]

/-- Main-twist coordinates in which the affine generator is the first
standard basis vector. The lattice's `γ̂` maps to `3σ` or `-4σ`. -/
def mainDeckAbelianizationEquiv (j : Kind) :
    DeckAbelianization j j.twist ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (deckAbelianizationEquivOfBezout j j.twist (mainTwist_admissible j)
    (mainAbelianSign j) 0 (mainAbelianBezout j)).trans (mainAbelianCoordinateSign j)

@[simp] theorem mainDeckAbelianizationEquiv_translation (j : Kind) (w : Lattice) :
    mainDeckAbelianizationEquiv j (deckAbelianTranslation j j.twist w) =
      ![mainAbelianSign j * (j.order : ℤ) * γ w, psi j w] := by
  change mainAbelianCoordinateSign j
    (deckAbelianizationEquivOfBezout j j.twist (mainTwist_admissible j)
      (mainAbelianSign j) 0 (mainAbelianBezout j) (deckAbelianTranslation j j.twist w)) = _
  rw [deckAbelianizationEquivOfBezout_translation]
  ext i
  fin_cases i <;> simp [mainAbelianCoordinateSign, psi_mainTwist, mul_assoc]

@[simp] theorem mainDeckAbelianizationEquiv_generator (j : Kind) :
    mainDeckAbelianizationEquiv j (deckAbelianGenerator j j.twist) = ![1, 0] := by
  change mainAbelianCoordinateSign j
    (deckAbelianizationEquivOfBezout j j.twist (mainTwist_admissible j)
      (mainAbelianSign j) 0 (mainAbelianBezout j) (deckAbelianGenerator j j.twist)) = _
  rw [deckAbelianizationEquivOfBezout_generator]
  ext i
  fin_cases i <;>
    simp [mainAbelianCoordinateSign, mainAbelianSign_gamma, mainAbelianSign_sq]

end Wikipedia.HopfProblem.Elliptic
