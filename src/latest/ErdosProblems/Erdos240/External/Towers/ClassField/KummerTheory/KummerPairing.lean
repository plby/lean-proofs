import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerRadicalExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The Kummer character and the sharp degree upper bound

For a finite subgroup `B ≤ Kˣ / Kˣⁿ`, an automorphism of the radical field
acts on every chosen radical by an `n`th root of unity.  The ratios form a
character of `B`; the resulting map from the Galois group to the character
group is injective.  Finite abelian duality then gives the sharp inequality

`[K[B¹⁄ⁿ] : K] ≤ |B|`.

The nontrivial point is multiplicativity in the power class.  Chosen
representatives and chosen roots need not multiply on the nose.  Their defect
is an `n`th root of unity, hence lies in the ground field because the ground
field contains a primitive `n`th root.  Every ground-field automorphism fixes
that defect, so it disappears from the automorphism ratio.
-/

namespace Towers.CField.KTheory

noncomputable section

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

private theorem kummer_ne_zero
    (n : ℕ) (hn : 0 < n) (b : PowerClassGroup K n) :
    kummerRoot K Ω n hn b ≠ 0 := by
  intro hzero
  have hrep :
      algebraMap K Ω ((powerClassRepresentative K n b : Kˣ) : K) ≠ 0 :=
    (map_ne_zero (algebraMap K Ω)).2 (powerClassRepresentative K n b).ne_zero
  apply hrep
  rw [← kummerRoot_pow K Ω n hn b, hzero, zero_pow hn.ne']

/-- The chosen radical attached to `b`, bundled as a unit of the Kummer
field.  Bundling it as a unit makes the automorphism ratio and its
multiplicativity purely group-theoretic. -/
def kummerGeneratorUnit (n : ℕ) (hn : 0 < n)
    (B : PCSubgro K n) (b : B.carrier) :
    (kummerField K Ω n hn B)ˣ :=
  Units.mk0
    ⟨kummerRoot K Ω n hn b.1,
      kummer_root_field K Ω n hn B b⟩
    (by
      intro h
      exact kummer_ne_zero K Ω n hn b.1 (congrArg Subtype.val h))

@[simp]
theorem kummer_generator_val (n : ℕ) (hn : 0 < n)
    (B : PCSubgro K n) (b : B.carrier) :
    ((kummerGeneratorUnit K Ω n hn B b :
      (kummerField K Ω n hn B)ˣ) : kummerField K Ω n hn B).1 =
      kummerRoot K Ω n hn b.1 :=
  rfl

/-- The `n`th power of the bundled Kummer generator is the image of its
chosen base-field representative. -/
theorem kummer_generator_pow (n : ℕ) (hn : 0 < n)
    (B : PCSubgro K n) (b : B.carrier) :
    kummerGeneratorUnit K Ω n hn B b ^ n =
      Units.map (algebraMap K (kummerField K Ω n hn B))
        (powerClassRepresentative K n b.1) := by
  apply Units.ext
  apply Subtype.ext
  exact kummerRoot_pow K Ω n hn b.1

/-- If the base field contains all `n`th roots of unity, every such root in
an extension is fixed by every base-field automorphism.  This is the descent
fact which makes the Kummer ratio multiplicative despite arbitrary choices
of representatives and roots. -/
theorem alg_fix_unit
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (σ : L ≃ₐ[K] L) (q : Lˣ) (hq : q ^ n = 1) :
    Units.map σ q = q := by
  let : NeZero n := ⟨hn.ne'⟩
  let η : rootsOfUnity n L := ⟨q, (mem_rootsOfUnity n q).2 hq⟩
  let e : rootsOfUnity n K ≃* rootsOfUnity n L :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
  obtain ⟨ε, hε⟩ := e.surjective η
  have hqbase : Units.map (algebraMap K L) (ε : Kˣ) = q := by
    apply Units.ext
    change (algebraMap K L) ((ε : Kˣ) : K) = (q : L)
    have he := congrArg (fun z : rootsOfUnity n L ↦ ((z : Lˣ) : L)) hε
    simpa only [e, η, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe] using he
  rw [← hqbase]
  ext
  exact σ.commutes ((ε : Kˣ) : K)

/-- The raw Kummer ratio `σ(r_b)/r_b`, before transporting roots of unity
back from the Kummer field to the base field. -/
def kummerRatio (n : ℕ) (hn : 0 < n)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) (b : B.carrier) :
    (kummerField K Ω n hn B)ˣ :=
  Units.map σ (kummerGeneratorUnit K Ω n hn B b) *
    (kummerGeneratorUnit K Ω n hn B b)⁻¹

/-- Every raw Kummer ratio is an `n`th root of unity. -/
theorem kummer_ratio_pow (n : ℕ) (hn : 0 < n)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) (b : B.carrier) :
    kummerRatio K Ω n hn B σ b ^ n = 1 := by
  rw [kummerRatio, mul_pow, ← map_pow, kummer_generator_pow,
    inv_pow, kummer_generator_pow]
  have hfix :
      Units.map σ
          (Units.map (algebraMap K (kummerField K Ω n hn B)).toMonoidHom
            (powerClassRepresentative K n b.1)) =
        Units.map (algebraMap K (kummerField K Ω n hn B)).toMonoidHom
          (powerClassRepresentative K n b.1) := by
    apply Units.ext
    exact σ.commutes ((powerClassRepresentative K n b.1 : Kˣ) : K)
  calc
    _ = Units.map (algebraMap K (kummerField K Ω n hn B)).toMonoidHom
          (powerClassRepresentative K n b.1) *
        (Units.map (algebraMap K (kummerField K Ω n hn B)).toMonoidHom
          (powerClassRepresentative K n b.1))⁻¹ :=
      congrArg (fun z ↦ z *
        (Units.map (algebraMap K (kummerField K Ω n hn B)).toMonoidHom
          (powerClassRepresentative K n b.1))⁻¹) hfix
    _ = 1 := mul_inv_cancel _

private theorem representative_mul_witness
    (n : ℕ) (B : PCSubgro K n) (b c : B.carrier) :
    ∃ d : Kˣ,
      powerClassRepresentative K n (b * c).1 * d ^ n =
        powerClassRepresentative K n b.1 * powerClassRepresentative K n c.1 := by
  have hclasses :
      powerClass n (powerClassRepresentative K n (b * c).1) =
        powerClass n
          (powerClassRepresentative K n b.1 * powerClassRepresentative K n c.1) := by
    rw [map_mul, power_class_representative,
      power_class_representative, power_class_representative]
    rfl
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclasses
  obtain ⟨d, rfl⟩ := hz
  exact ⟨d, heq⟩

/-- The raw Kummer ratio is multiplicative as a function of the power class.
The proof explicitly absorbs the two choice defects (representatives and
radicals) into a root of unity and then uses that automorphisms fix it. -/
theorem kummerRatio_mul (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) (b c : B.carrier) :
    kummerRatio K Ω n hn B σ (b * c) =
      kummerRatio K Ω n hn B σ b * kummerRatio K Ω n hn B σ c := by
  let F := kummerField K Ω n hn B
  let rb : Fˣ := kummerGeneratorUnit K Ω n hn B b
  let rc : Fˣ := kummerGeneratorUnit K Ω n hn B c
  let rbc : Fˣ := kummerGeneratorUnit K Ω n hn B (b * c)
  obtain ⟨d, hd⟩ := representative_mul_witness K n B b c
  let dF : Fˣ := Units.map (algebraMap K F) d
  let q : Fˣ := rbc * dF * (rb * rc)⁻¹
  have hqpow : q ^ n = 1 := by
    change (kummerGeneratorUnit K Ω n hn B (b * c) *
      Units.map (algebraMap K F) d *
        (kummerGeneratorUnit K Ω n hn B b *
          kummerGeneratorUnit K Ω n hn B c)⁻¹) ^ n = 1
    rw [mul_pow, mul_pow, inv_pow, mul_pow,
      kummer_generator_pow, kummer_generator_pow,
      kummer_generator_pow]
    rw [← map_pow]
    rw [← map_mul, hd, map_mul]
    group
  have hqfix : Units.map σ q = q :=
    alg_fix_unit K n hn hζ σ q hqpow
  have hdfix : Units.map σ dF = dF := by
    apply Units.ext
    change σ (algebraMap K F (d : K)) = algebraMap K F (d : K)
    exact σ.commutes (d : K)
  change Units.map σ rbc * rbc⁻¹ =
    (Units.map σ rb * rb⁻¹) * (Units.map σ rc * rc⁻¹)
  have hqdef : q = rbc * dF * (rb * rc)⁻¹ := rfl
  have hrbc : rbc = q * rb * rc * dF⁻¹ := by
    rw [hqdef]
    group
  have hsrbc := congrArg (Units.map (σ : F →* F)) hrbc
  simp only [map_mul, map_inv, hqfix, hdfix] at hsrbc
  have hrbc_inv : rbc⁻¹ = dF * rc⁻¹ * rb⁻¹ * q⁻¹ := by
    rw [hrbc]
    group
  rw [hsrbc, hrbc_inv]
  calc
    q * Units.map σ rb * Units.map σ rc * dF⁻¹ *
        (dF * rc⁻¹ * rb⁻¹ * q⁻¹) =
        (dF * dF⁻¹) * (q * q⁻¹) *
          (Units.map σ rb * rb⁻¹) *
            (Units.map σ rc * rc⁻¹) := by
      ac_rfl
    _ = (Units.map σ rb * rb⁻¹) * (Units.map σ rc * rc⁻¹) := by
      rw [mul_inv_cancel, one_mul, mul_inv_cancel, one_mul]

/-- The raw Kummer ratio is trivial on the identity power class. -/
theorem kummerRatio_one (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) :
    kummerRatio K Ω n hn B σ 1 = 1 := by
  have hmul := kummerRatio_mul K Ω n hn hζ B σ 1 1
  apply mul_left_cancel (a := kummerRatio K Ω n hn B σ 1)
  simpa using hmul.symm

/-- For a fixed automorphism, the Kummer ratios form a character of `B`
with values in the `n`th roots of unity of the radical field. -/
def kummerCharacterExtension (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) :
    B.carrier →* rootsOfUnity n (kummerField K Ω n hn B) where
  toFun b := ⟨kummerRatio K Ω n hn B σ b,
    (mem_rootsOfUnity n _).2 (kummer_ratio_pow K Ω n hn B σ b)⟩
  map_one' := by
    apply Subtype.ext
    exact kummerRatio_one K Ω n hn hζ B σ
  map_mul' b c := by
    apply Subtype.ext
    exact kummerRatio_mul K Ω n hn hζ B σ b c

/-- The base-root-valued Kummer character. -/
def kummerRootCharacter (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) :
    B.carrier →* (rootsOfUnity n K) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap K (kummerField K Ω n hn B)).injective hζ).symm.toMonoidHom.comp
    (kummerCharacterExtension K Ω n hn hζ B σ)

/-- The Kummer character regarded as a character into the unit group of the
base field. Its values in fact lie in `μₙ`; this larger codomain is the one
used by finite abelian duality. -/
def kummerCharacter (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ : Gal(kummerField K Ω n hn B/K)) :
    B.carrier →* Kˣ :=
  (rootsOfUnity n K).subtype.comp
    (kummerRootCharacter K Ω n hn hζ B σ)

/-- Kummer characters multiply when automorphisms multiply. -/
theorem kummerCharacter_mul (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n)
    (σ τ : Gal(kummerField K Ω n hn B/K)) :
    kummerCharacter K Ω n hn hζ B (σ * τ) =
      kummerCharacter K Ω n hn hζ B σ *
        kummerCharacter K Ω n hn hζ B τ := by
  let : NeZero n := ⟨hn.ne'⟩
  apply MonoidHom.ext
  intro b
  apply Units.ext
  have hextF :
      kummerCharacterExtension K Ω n hn hζ B (σ * τ) b =
        kummerCharacterExtension K Ω n hn hζ B σ b *
          kummerCharacterExtension K Ω n hn hζ B τ b := by
    apply Subtype.ext
    let x := kummerGeneratorUnit K Ω n hn B b
    let qσ := kummerRatio K Ω n hn B σ b
    let qτ := kummerRatio K Ω n hn B τ b
    have hτfix : Units.map σ qτ = qτ :=
      alg_fix_unit K n hn hζ σ qτ
        (kummer_ratio_pow K Ω n hn B τ b)
    have hτdef : Units.map τ x = qτ * x := by
      dsimp [qτ, x]
      rw [kummerRatio]
      group
    have hσdef : Units.map σ x = qσ * x := by
      dsimp [qσ, x]
      rw [kummerRatio]
      group
    have hraw : kummerRatio K Ω n hn B (σ * τ) b = qσ * qτ := by
      dsimp only [kummerRatio]
      have hcomp : Units.map (σ * τ)
          (kummerGeneratorUnit K Ω n hn B b) =
          Units.map (σ : kummerField K Ω n hn B →*
            kummerField K Ω n hn B)
            (Units.map (τ : kummerField K Ω n hn B →*
              kummerField K Ω n hn B)
              (kummerGeneratorUnit K Ω n hn B b)) := by
        apply Units.ext
        exact AlgEquiv.mul_apply σ τ _
      rw [hcomp]
      change Units.map (σ : kummerField K Ω n hn B →*
        kummerField K Ω n hn B)
          (Units.map (τ : kummerField K Ω n hn B →*
            kummerField K Ω n hn B) x) * x⁻¹ = qσ * qτ
      rw [hτdef, map_mul, hτfix, hσdef]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using (mul_comm qτ qσ)
    exact hraw
  have hext :
      kummerRootCharacter K Ω n hn hζ B (σ * τ) b =
        kummerRootCharacter K Ω n hn hζ B σ b *
          kummerRootCharacter K Ω n hn hζ B τ b := by
    change
      (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K (kummerField K Ω n hn B)).injective hζ).symm
            (kummerCharacterExtension K Ω n hn hζ B (σ * τ) b) =
        (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K (kummerField K Ω n hn B)).injective hζ).symm
            (kummerCharacterExtension K Ω n hn hζ B σ b) *
        (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K (kummerField K Ω n hn B)).injective hζ).symm
            (kummerCharacterExtension K Ω n hn hζ B τ b)
    rw [hextF, map_mul]
  exact congrArg (fun z : rootsOfUnity n K ↦ ((z : Kˣ) : K)) hext

/-- The Kummer pairing as a homomorphism from the Galois group to the
character group of `B`. -/
def kummerCharacterHom (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n) :
    Gal(kummerField K Ω n hn B/K) →* (B.carrier →* Kˣ) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact
    { toFun := kummerCharacter K Ω n hn hζ B
      map_one' := by
        apply MonoidHom.ext
        intro b
        apply Units.ext
        change (((kummerRootCharacter K Ω n hn hζ B 1) b : Kˣ) : K) = 1
        have honeF : kummerCharacterExtension K Ω n hn hζ B 1 b = 1 := by
          apply Subtype.ext
          change Units.map (1 : Gal(kummerField K Ω n hn B/K))
              (kummerGeneratorUnit K Ω n hn B b) *
                (kummerGeneratorUnit K Ω n hn B b)⁻¹ = 1
          have honeMap : Units.map (1 : Gal(kummerField K Ω n hn B/K))
              (kummerGeneratorUnit K Ω n hn B b) =
                kummerGeneratorUnit K Ω n hn B b := by
            apply Units.ext
            rfl
          rw [honeMap, mul_inv_cancel]
        have hone : kummerRootCharacter K Ω n hn hζ B 1 b = 1 := by
          change
            (rootsOfUnityEquivOfPrimitiveRoots
              (algebraMap K (kummerField K Ω n hn B)).injective hζ).symm
                (kummerCharacterExtension K Ω n hn hζ B 1 b) = 1
          rw [honeF, map_one]
        exact congrArg (fun z : rootsOfUnity n K ↦ ((z : Kˣ) : K)) hone
      map_mul' := kummerCharacter_mul K Ω n hn hζ B }

/-- The Kummer character map is injective: a character determines the
automorphism on every radical generator, hence on the generated field. -/
theorem kummer_character_injective (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n) :
    Function.Injective (kummerCharacterHom K Ω n hn hζ B) := by
  let : NeZero n := ⟨hn.ne'⟩
  let : FiniteDimensional K (kummerField K Ω n hn B) :=
    dimensional_kummer_field K Ω n hn B
  intro σ τ hστ
  have hSalg : Algebra.adjoin K (kummerGeneratorSet K Ω n hn B) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
    · rw [adjoin_kummer_top K Ω n hn B]
      rfl
    · intro x hx
      exact (IsIntegral.of_finite K x).isAlgebraic
  have heq : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hSalg
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    have hchar := DFunLike.congr_fun hστ b
    have hratio : kummerRatio K Ω n hn B σ b =
        kummerRatio K Ω n hn B τ b := by
      have hroot : kummerRootCharacter K Ω n hn hζ B σ b =
          kummerRootCharacter K Ω n hn hζ B τ b := by
        change ((kummerRootCharacter K Ω n hn hζ B σ b : rootsOfUnity n K) : Kˣ) =
          ((kummerRootCharacter K Ω n hn hζ B τ b : rootsOfUnity n K) : Kˣ) at hchar
        apply Subtype.ext
        exact hchar
      have he := congrArg
        (fun z : rootsOfUnity n K ↦
          (((rootsOfUnityEquivOfPrimitiveRoots
            (algebraMap K (kummerField K Ω n hn B)).injective hζ) z :
              rootsOfUnity n (kummerField K Ω n hn B)) :
                (kummerField K Ω n hn B)ˣ)) hroot
      simpa [kummerRootCharacter, kummerCharacterExtension] using he
    have hunit : Units.map σ (kummerGeneratorUnit K Ω n hn B b) =
        Units.map (τ : kummerField K Ω n hn B →*
          kummerField K Ω n hn B) (kummerGeneratorUnit K Ω n hn B b) := by
      have h := congrArg (fun z : (kummerField K Ω n hn B)ˣ ↦
        z * kummerGeneratorUnit K Ω n hn B b) hratio
      simpa [kummerRatio, mul_assoc] using h
    exact congrArg (fun z : (kummerField K Ω n hn B)ˣ ↦
      ((z : kummerField K Ω n hn B) :
        kummerField K Ω n hn B)) hunit
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun heq x

/-- The sharp upper bound in finite Kummer theory.  Unlike the elementary
generator count `n ^ |B|`, finite character duality sees the relations in
`B` and gives `[K[B¹⁄ⁿ] : K] ≤ |B|`. -/
theorem kummer_field_card (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty)
    (B : PCSubgro K n) :
    Module.finrank K (kummerField K Ω n hn B) ≤ B.card := by
  let : NeZero n := ⟨hn.ne'⟩
  let : FiniteDimensional K (kummerField K Ω n hn B) :=
    dimensional_kummer_field K Ω n hn B
  let : IsGalois K (kummerField K Ω n hn B) :=
    kummer_galois K Ω n hn
      ((mem_primitiveRoots hn).mp hζ.choose_spec) B
  let : Fintype B.carrier := B.finite_carrier.fintype
  have hexp : Monoid.exponent B.carrier ∣ n := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro b
    exact Subtype.ext (power_class_pow n b.1)
  let : HasEnoughRootsOfUnity K n :=
    { prim := ⟨hζ.choose, (mem_primitiveRoots hn).mp hζ.choose_spec⟩
      cyc := rootsOfUnity.isCyclic K n }
  let : HasEnoughRootsOfUnity K (Monoid.exponent B.carrier) :=
    HasEnoughRootsOfUnity.of_dvd K hexp
  calc
    Module.finrank K (kummerField K Ω n hn B) =
        Nat.card Gal(kummerField K Ω n hn B/K) :=
      (IsGalois.card_aut_eq_finrank K (kummerField K Ω n hn B)).symm
    _ ≤ Nat.card (B.carrier →* Kˣ) :=
      Nat.card_le_card_of_injective
        (kummerCharacterHom K Ω n hn hζ B)
        (kummer_character_injective K Ω n hn hζ B)
    _ = Nat.card B.carrier :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        B.carrier K
    _ = B.card := by
      rw [Nat.card_eq_fintype_card]
      exact (B.finite_carrier.card_toFinset).symm

end

end Towers.CField.KTheory
