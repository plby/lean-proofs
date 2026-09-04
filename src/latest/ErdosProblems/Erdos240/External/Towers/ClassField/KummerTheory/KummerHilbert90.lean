import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerRadicalExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Hilbert 90 and generation by Kummer radicals

The converse half of Theorem VII.A.3 starts from a finite abelian Galois
extension of exponent dividing `n`.  Every character of its Galois group is
realized by a Hilbert-90 eigenvector.  The `n`th power of this eigenvector is
in the base field, and finite-abelian character separation shows that all of
these radical eigenvectors generate the extension.
-/

namespace Towers.CField.KTheory

noncomputable section

open groupCohomology

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable (n : ℕ) (hn : 0 < n)

/-- A base-field-valued character, embedded in the units of the extension. -/
def galoisCharacterUnits
    (χ : Gal(L/K) →* rootsOfUnity n K) (sigma : Gal(L/K)) : Lˣ :=
  Units.map (algebraMap K L).toMonoidHom (χ sigma : Kˣ)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A base-valued character is a multiplicative `1`-cocycle because the
Galois action fixes all of its values. -/
theorem galois_character_cocycle
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    IsMulCocycle₁ (galoisCharacterUnits K L n χ) := by
  intro sigma tau
  change Units.map (algebraMap K L).toMonoidHom (χ (sigma * tau) : Kˣ) =
    Units.map sigma
        (Units.map (algebraMap K L).toMonoidHom (χ tau : Kˣ)) *
      Units.map (algebraMap K L).toMonoidHom (χ sigma : Kˣ)
  apply Units.ext
  change algebraMap K L ((((χ (sigma * tau) : rootsOfUnity n K) : Kˣ) : K)) =
    sigma (algebraMap K L ((((χ tau : rootsOfUnity n K) : Kˣ) : K))) *
      algebraMap K L ((((χ sigma : rootsOfUnity n K) : Kˣ) : K))
  rw [χ.map_mul]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, sigma.commutes]
  exact mul_comm _ _

/-- A Hilbert-90 eigenvector realizing a Galois character. -/
def hilbert90Radical (χ : Gal(L/K) →* rootsOfUnity n K) : Lˣ :=
  Classical.choose
    (isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (galoisCharacterUnits K L n χ)
      (galois_character_cocycle K L n χ))

omit [IsGalois K L] in
/-- The defining eigenvector equation `sigma(beta)/beta = chi(sigma)`. -/
theorem hilbert_90_ratio
    (χ : Gal(L/K) →* rootsOfUnity n K) (sigma : Gal(L/K)) :
    Units.map sigma (hilbert90Radical K L n χ) /
        hilbert90Radical K L n χ =
      galoisCharacterUnits K L n χ sigma :=
  Classical.choose_spec
    (isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (galoisCharacterUnits K L n χ)
      (galois_character_cocycle K L n χ)) sigma

omit [IsGalois K L] in
/-- The Hilbert-90 eigenvector transforms by the prescribed character. -/
theorem aut_hilbert_90
    (χ : Gal(L/K) →* rootsOfUnity n K) (sigma : Gal(L/K)) :
    Units.map sigma (hilbert90Radical K L n χ) =
      galoisCharacterUnits K L n χ sigma *
        hilbert90Radical K L n χ := by
  have h := hilbert_90_ratio K L n χ sigma
  calc
    Units.map sigma (hilbert90Radical K L n χ) =
        (Units.map sigma (hilbert90Radical K L n χ) /
          hilbert90Radical K L n χ) * hilbert90Radical K L n χ := by
      rw [div_eq_mul_inv]
      group
    _ = galoisCharacterUnits K L n χ sigma *
          hilbert90Radical K L n χ := by rw [h]

/-- The `n`th power of a Hilbert-90 character eigenvector belongs to the
base field. -/
theorem hilbert_90_radical
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    (hilbert90Radical K L n χ : L) ^ n ∈
      Set.range (algebraMap K L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro sigma
  have hbeta := aut_hilbert_90 K L n χ sigma
  have hval :
      sigma (hilbert90Radical K L n χ : L) =
        algebraMap K L ((((χ sigma : rootsOfUnity n K) : Kˣ) : K)) *
          (hilbert90Radical K L n χ : L) := by
    simpa [galoisCharacterUnits] using congrArg Units.val hbeta
  rw [map_pow, hval, mul_pow]
  have hroot : (((χ sigma : rootsOfUnity n K) : Kˣ) : K) ^ n = 1 := by
    exact congrArg Units.val (χ sigma).property
  rw [← map_pow, hroot, map_one, one_mul]

omit [IsGalois K L] in
/-- If a character is nontrivial at an automorphism, its Hilbert-90 radical
is moved by that automorphism. -/
theorem aut_90_radical
    (χ : Gal(L/K) →* rootsOfUnity n K) (sigma : Gal(L/K))
    (hχ : χ sigma ≠ 1) :
    sigma (hilbert90Radical K L n χ : L) ≠
      (hilbert90Radical K L n χ : L) := by
  intro hfix
  have hratio := hilbert_90_ratio K L n χ sigma
  have hratioVal :
      sigma (hilbert90Radical K L n χ : L) /
          (hilbert90Radical K L n χ : L) =
        algebraMap K L ((((χ sigma : rootsOfUnity n K) : Kˣ) : K)) := by
    simpa [galoisCharacterUnits] using congrArg Units.val hratio
  rw [hfix, div_self (hilbert90Radical K L n χ).ne_zero] at hratioVal
  apply hχ
  apply Subtype.ext
  apply Units.ext
  exact (algebraMap K L).injective (by simpa using hratioVal.symm)

/-- The set of all Hilbert-90 radicals attached to base-valued characters. -/
def hilbert90Set : Set L :=
  Set.range fun χ : Gal(L/K) →* rootsOfUnity n K ↦
    (hilbert90Radical K L n χ : L)

/-- Character separation implies that all Hilbert-90 radical eigenvectors
generate a finite abelian Galois extension whose exponent divides `n`. -/
theorem adjoin_90_radical
    (hn : 0 < n)
    (hcomm : ∀ sigma tau : Gal(L/K), sigma * tau = tau * sigma)
    (hexp : ∀ sigma : Gal(L/K), sigma ^ n = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IntermediateField.adjoin K (hilbert90Set K L n) = ⊤ := by
  let : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := hcomm }
  let : NeZero n := ⟨hn.ne'⟩
  have hexponent : Monoid.exponent Gal(L/K) ∣ n := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact hexp
  let : HasEnoughRootsOfUnity K n :=
    HasEnoughRootsOfUnity.of_card_le (by rw [hζ.card_rootsOfUnity])
  let : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) :=
    HasEnoughRootsOfUnity.of_dvd K hexponent
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  rw [map_top]
  change IntermediateField.fixingSubgroup
      (IntermediateField.adjoin K (hilbert90Set K L n)) = ⊥
  apply le_antisymm
  · intro sigma hsigma
    have hfix : ∀ χ : Gal(L/K) →* rootsOfUnity n K,
        sigma (hilbert90Radical K L n χ : L) =
          (hilbert90Radical K L n χ : L) := by
      intro χ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
      exact hsigma _ (IntermediateField.subset_adjoin K _ ⟨χ, rfl⟩)
    have hsigmaOne : sigma = 1 := by
      by_contra hsigma
      obtain ⟨χ, hχ⟩ :=
        CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
          Gal(L/K) K hsigma
      let χroot : Gal(L/K) →* rootsOfUnity n K :=
        { toFun := fun tau ↦ ⟨χ tau, (mem_rootsOfUnity n (χ tau)).2 (by
              rw [← map_pow, hexp tau, map_one])⟩
          map_one' := by
            apply Subtype.ext
            exact χ.map_one
          map_mul' := fun tau rho ↦ by
            apply Subtype.ext
            exact χ.map_mul tau rho }
      have hχroot : χroot sigma ≠ 1 := by
        intro heq
        apply hχ
        exact congrArg Subtype.val heq
      exact aut_90_radical K L n χroot sigma hχroot
        (hfix χroot)
    exact (Subgroup.mem_bot).2 hsigmaOne
  · exact bot_le

end

end Towers.CField.KTheory
