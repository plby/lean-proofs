import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerRadicalExtension
import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerHilbert90
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# The perfect Kummer pairing

For a finite abelian Galois extension `L / K` of exponent dividing `n`, the
radical power classes in `Kˣ / Kˣⁿ` are naturally dual to `Gal(L / K)`.
The pairing sends a radical class represented by `a = x ^ n` and an
automorphism `sigma` to `sigma(x) / x`.

The substantial points formalized here are independence of all chosen roots
and representatives, nondegeneracy on radical classes, and surjectivity on
characters by Noether's form of Hilbert 90.  Consequently the radical group
is finite and its order is exactly `[L : K]`.
-/

namespace Towers.CField.KTheory

noncomputable section

universe u

variable (K Omega : Type u) [Field K] [Field Omega] [Algebra K Omega]
  [IsAlgClosure K Omega]
variable (n : Nat) (hn : 0 < n)

open groupCohomology

private theorem representative_witness_general
    {a : Kˣ} {b : PowerClassGroup K n}
    (h : powerClass n a = b) :
    ∃ d : Kˣ, powerClassRepresentative K n b * d ^ n = a := by
  have hclasses :
      powerClass n (powerClassRepresentative K n b) = powerClass n a := by
    rw [power_class_representative, h]
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclasses
  obtain ⟨d, rfl⟩ := hz
  exact ⟨d, heq⟩

omit [IsAlgClosure K Omega] in
private theorem root_representative_general
    (L : IntermediateField K Omega)
    (b : PowerClassGroup K n)
    (hb : b ∈ radicalPowerClasses K Omega n L) :
    ∃ y : Lˣ, y ^ n =
      Units.map (algebraMap K L) (powerClassRepresentative K n b) := by
  obtain ⟨a, haRadical, hab⟩ := hb
  obtain ⟨x, hxpow⟩ := haRadical
  obtain ⟨d, hd⟩ := representative_witness_general K n hab
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  let dL : Lˣ := f d
  refine ⟨x * dL⁻¹, ?_⟩
  rw [mul_pow, inv_pow, hxpow, ← map_pow]
  change f a * (f (d ^ n))⁻¹ = f (powerClassRepresentative K n b)
  have hdmapped : f a =
      f (powerClassRepresentative K n b) * f d ^ n := by
    simpa using congrArg f hd.symm
  rw [hdmapped, map_pow]
  group

private theorem alg_fix_general
    {E : Type*} [Field E] [Algebra K E]
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma : E ≃ₐ[K] E) (q : Eˣ) (hq : q ^ n = 1) :
    Units.map sigma q = q := by
  let : NeZero n := ⟨hn.ne'⟩
  let eta : rootsOfUnity n E := ⟨q, (mem_rootsOfUnity n q).2 hq⟩
  let e : rootsOfUnity n K ≃* rootsOfUnity n E :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K E).injective hroots
  obtain ⟨epsilon, hepsilon⟩ := e.surjective eta
  have hqbase : Units.map (algebraMap K E) (epsilon : Kˣ) = q := by
    apply Units.ext
    change (algebraMap K E) ((epsilon : Kˣ) : K) = (q : E)
    have he := congrArg (fun z : rootsOfUnity n E ↦ ((z : Eˣ) : E)) hepsilon
    simpa only [e, eta, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe] using he
  rw [← hqbase]
  ext
  exact sigma.commutes ((epsilon : Kˣ) : K)

private theorem representative_mul_general
    (b c : PowerClassGroup K n) :
    ∃ d : Kˣ,
      powerClassRepresentative K n (b * c) * d ^ n =
        powerClassRepresentative K n b * powerClassRepresentative K n c := by
  have hclasses :
      powerClass n (powerClassRepresentative K n (b * c)) =
        powerClass n
          (powerClassRepresentative K n b * powerClassRepresentative K n c) := by
    rw [map_mul, power_class_representative,
      power_class_representative, power_class_representative]
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclasses
  obtain ⟨d, rfl⟩ := hz
  exact ⟨d, heq⟩

section

variable (L : AESubext K Omega n)

/-- A chosen root in `L` of the canonical representative of a radical
power class. -/
def radicalRootUnit
    (b : radicalPowerClasses K Omega n L.carrier) : L.carrierˣ :=
  Classical.choose
    (root_representative_general K Omega n L.carrier b.1 b.2)

omit [IsAlgClosure K Omega] in
/-- The chosen radical root has the required `n`th power. -/
theorem radical_unit_pow
    (b : radicalPowerClasses K Omega n L.carrier) :
    radicalRootUnit K Omega n L b ^ n =
      Units.map (algebraMap K L.carrier).toMonoidHom
        (powerClassRepresentative K n b.1) :=
  Classical.choose_spec
    (root_representative_general K Omega n L.carrier b.1 b.2)

/-- The raw Kummer pairing value `sigma(x) / x` in the extension. -/
def radicalKummerRatio
    (b : radicalPowerClasses K Omega n L.carrier)
    (sigma : Gal(L.carrier/K)) : L.carrierˣ :=
  Units.map sigma (radicalRootUnit K Omega n L b) *
    (radicalRootUnit K Omega n L b)⁻¹

omit [IsAlgClosure K Omega] in
/-- Every raw pairing value is an `n`th root of unity. -/
theorem radical_kummer_ratio
    (b : radicalPowerClasses K Omega n L.carrier)
    (sigma : Gal(L.carrier/K)) :
    radicalKummerRatio K Omega n L b sigma ^ n = 1 := by
  rw [radicalKummerRatio, mul_pow, ← map_pow, radical_unit_pow,
    inv_pow, radical_unit_pow]
  have hfix :
      Units.map sigma
          (Units.map (algebraMap K L.carrier).toMonoidHom
            (powerClassRepresentative K n b.1)) =
        Units.map (algebraMap K L.carrier).toMonoidHom
          (powerClassRepresentative K n b.1) := by
    apply Units.ext
    exact sigma.commutes (powerClassRepresentative K n b.1 : K)
  rw [hfix]
  exact mul_inv_cancel _

omit [IsAlgClosure K Omega] in
/-- Changing the radical class multiplicatively multiplies the raw pairing
value.  The defect between the three independently chosen roots is an
`n`th root of unity, hence is fixed by every base-field automorphism. -/
theorem radical_ratio_mul
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (b c : radicalPowerClasses K Omega n L.carrier)
    (sigma : Gal(L.carrier/K)) :
    radicalKummerRatio K Omega n L (b * c) sigma =
      radicalKummerRatio K Omega n L b sigma *
        radicalKummerRatio K Omega n L c sigma := by
  let rb : L.carrierˣ := radicalRootUnit K Omega n L b
  let rc : L.carrierˣ := radicalRootUnit K Omega n L c
  let rbc : L.carrierˣ := radicalRootUnit K Omega n L (b * c)
  obtain ⟨d, hd⟩ := representative_mul_general K n b.1 c.1
  let dL : L.carrierˣ := Units.map (algebraMap K L.carrier).toMonoidHom d
  let q : L.carrierˣ := rbc * dL * (rb * rc)⁻¹
  have hqpow : q ^ n = 1 := by
    change (radicalRootUnit K Omega n L (b * c) *
      Units.map (algebraMap K L.carrier).toMonoidHom d *
        (radicalRootUnit K Omega n L b *
          radicalRootUnit K Omega n L c)⁻¹) ^ n = 1
    rw [mul_pow, mul_pow, inv_pow, mul_pow,
      radical_unit_pow, radical_unit_pow, radical_unit_pow]
    rw [← map_pow]
    have hd' :
        powerClassRepresentative K n (b * c).1 * d ^ n =
          powerClassRepresentative K n b.1 *
            powerClassRepresentative K n c.1 := by
      simpa only [Subgroup.coe_mul] using hd
    rw [← map_mul, hd', map_mul]
    group
  have hqfix : Units.map sigma q = q :=
    alg_fix_general K n hn hroots sigma q hqpow
  have hdfix : Units.map sigma dL = dL := by
    apply Units.ext
    change sigma (algebraMap K L.carrier (d : K)) =
      algebraMap K L.carrier (d : K)
    exact sigma.commutes (d : K)
  change Units.map sigma rbc * rbc⁻¹ =
    (Units.map sigma rb * rb⁻¹) * (Units.map sigma rc * rc⁻¹)
  have hqdef : q = rbc * dL * (rb * rc)⁻¹ := rfl
  have hrbc : rbc = q * rb * rc * dL⁻¹ := by
    rw [hqdef]
    group
  have hsrbc := congrArg (Units.map (sigma : L.carrier →* L.carrier)) hrbc
  simp only [map_mul, map_inv, hqfix, hdfix] at hsrbc
  have hrbc_inv : rbc⁻¹ = dL * rc⁻¹ * rb⁻¹ * q⁻¹ := by
    rw [hrbc]
    group
  rw [hsrbc, hrbc_inv]
  calc
    q * Units.map sigma rb * Units.map sigma rc * dL⁻¹ *
        (dL * rc⁻¹ * rb⁻¹ * q⁻¹) =
        (dL * dL⁻¹) * (q * q⁻¹) *
          (Units.map sigma rb * rb⁻¹) *
            (Units.map sigma rc * rc⁻¹) := by
      ac_rfl
    _ = (Units.map sigma rb * rb⁻¹) * (Units.map sigma rc * rc⁻¹) := by
      rw [mul_inv_cancel, one_mul, mul_inv_cancel, one_mul]

omit [IsAlgClosure K Omega] in
/-- The raw pairing is trivial on the identity radical class. -/
theorem radical_ratio_one
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma : Gal(L.carrier/K)) :
    radicalKummerRatio K Omega n L 1 sigma = 1 := by
  have hmul := radical_ratio_mul K Omega n L hn hroots 1 1 sigma
  apply mul_left_cancel (a := radicalKummerRatio K Omega n L 1 sigma)
  simpa using hmul.symm

/-- For a fixed automorphism, the pairing is a character of the radical
power-class group, valued in the roots of unity of the extension. -/
def radicalKummerExtension
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma : Gal(L.carrier/K)) :
    radicalPowerClasses K Omega n L.carrier →*
      rootsOfUnity n L.carrier where
  toFun b := ⟨radicalKummerRatio K Omega n L b sigma,
    (mem_rootsOfUnity n _).2
      (radical_kummer_ratio K Omega n L b sigma)⟩
  map_one' := by
    apply Subtype.ext
    exact radical_ratio_one K Omega n L hn hroots sigma
  map_mul' b c := by
    apply Subtype.ext
    exact radical_ratio_mul K Omega n L hn hroots b c sigma

/-- The root-of-unity-valued character over the base field. -/
def radicalRootCharacter
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma : Gal(L.carrier/K)) :
    radicalPowerClasses K Omega n L.carrier →* rootsOfUnity n K :=
  by
    letI : NeZero n := ⟨hn.ne'⟩
    exact (rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap K L.carrier).injective hroots).symm.toMonoidHom.comp
        (radicalKummerExtension K Omega n L hn hroots sigma)

/-- The same character with codomain `Kˣ`, as required by finite abelian
duality. -/
def radicalKummerCharacter
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma : Gal(L.carrier/K)) :
    radicalPowerClasses K Omega n L.carrier →* Kˣ :=
  (rootsOfUnity n K).subtype.comp
    (radicalRootCharacter K Omega n L hn hroots sigma)

omit [IsAlgClosure K Omega] in
/-- Kummer characters multiply with automorphisms. -/
theorem radical_kummer_character
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty)
    (sigma tau : Gal(L.carrier/K)) :
    radicalKummerCharacter K Omega n L hn hroots (sigma * tau) =
      radicalKummerCharacter K Omega n L hn hroots sigma *
        radicalKummerCharacter K Omega n L hn hroots tau := by
  let : NeZero n := ⟨hn.ne'⟩
  apply MonoidHom.ext
  intro b
  apply Units.ext
  have hextF :
      radicalKummerExtension K Omega n L hn hroots (sigma * tau) b =
        radicalKummerExtension K Omega n L hn hroots sigma b *
          radicalKummerExtension K Omega n L hn hroots tau b := by
    apply Subtype.ext
    let r : L.carrierˣ := radicalRootUnit K Omega n L b
    let q : L.carrierˣ := Units.map tau r * r⁻¹
    have hqpow : q ^ n = 1 := by
      exact radical_kummer_ratio K Omega n L b tau
    have hqfix : Units.map sigma q = q :=
      alg_fix_general K n hn hroots sigma q hqpow
    change Units.map (sigma * tau) r * r⁻¹ =
      (Units.map sigma r * r⁻¹) * (Units.map tau r * r⁻¹)
    have hcomp : Units.map (sigma * tau) r =
        Units.map (sigma : L.carrier →* L.carrier)
          (Units.map (tau : L.carrier →* L.carrier) r) := by
      apply Units.ext
      rfl
    have hqdef : q = Units.map tau r * r⁻¹ := rfl
    have htau : Units.map tau r = q * r := by
      rw [hqdef]
      group
    rw [hcomp, htau, map_mul, hqfix]
    group
    ac_rfl
  have hext :
      radicalRootCharacter K Omega n L hn hroots (sigma * tau) b =
        radicalRootCharacter K Omega n L hn hroots sigma b *
          radicalRootCharacter K Omega n L hn hroots tau b := by
    change
      (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K L.carrier).injective hroots).symm
            (radicalKummerExtension K Omega n L hn hroots
              (sigma * tau) b) =
        (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K L.carrier).injective hroots).symm
            (radicalKummerExtension K Omega n L hn hroots sigma b) *
        (rootsOfUnityEquivOfPrimitiveRoots
          (algebraMap K L.carrier).injective hroots).symm
            (radicalKummerExtension K Omega n L hn hroots tau b)
    rw [hextF, map_mul]
  exact congrArg (fun z : rootsOfUnity n K ↦ ((z : Kˣ) : K)) hext

/-- The Kummer pairing, curried as a homomorphism from radical classes to
characters of the Galois group. -/
def radicalKummerPairing
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    radicalPowerClasses K Omega n L.carrier →*
      (Gal(L.carrier/K) →* Kˣ) where
  toFun b :=
    { toFun := fun sigma ↦ radicalKummerCharacter K Omega n L hn hroots sigma b
      map_one' := by
        let : NeZero n := ⟨hn.ne'⟩
        apply Units.ext
        change (((radicalRootCharacter K Omega n L hn hroots 1) b : Kˣ) : K) = 1
        have honeF :
            radicalKummerExtension K Omega n L hn hroots 1 b = 1 := by
          apply Subtype.ext
          change Units.map (1 : Gal(L.carrier/K))
              (radicalRootUnit K Omega n L b) *
                (radicalRootUnit K Omega n L b)⁻¹ = 1
          have hone : Units.map (1 : Gal(L.carrier/K))
              (radicalRootUnit K Omega n L b) =
                radicalRootUnit K Omega n L b := by
            apply Units.ext
            rfl
          rw [hone, mul_inv_cancel]
        have hone : radicalRootCharacter K Omega n L hn hroots 1 b = 1 := by
          change (rootsOfUnityEquivOfPrimitiveRoots
            (algebraMap K L.carrier).injective hroots).symm
              (radicalKummerExtension K Omega n L hn hroots 1 b) = 1
          rw [honeF, map_one]
        exact congrArg (fun z : rootsOfUnity n K ↦ ((z : Kˣ) : K)) hone
      map_mul' := fun sigma tau ↦ by
        exact DFunLike.congr_fun
          (radical_kummer_character K Omega n L hn hroots sigma tau) b }
  map_one' := by
    apply MonoidHom.ext
    intro sigma
    exact map_one (radicalKummerCharacter K Omega n L hn hroots sigma)
  map_mul' b c := by
    apply MonoidHom.ext
    intro sigma
    exact map_mul (radicalKummerCharacter K Omega n L hn hroots sigma) b c

omit [IsAlgClosure K Omega] in
/-- The Kummer pairing is nondegenerate on radical power classes. -/
theorem kummer_pairing_injective
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    Function.Injective (radicalKummerPairing K Omega n L hn hroots) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [injective_iff_map_eq_one]
  intro b hb
  let r : L.carrierˣ := radicalRootUnit K Omega n L b
  have hfixed : ∀ sigma : Gal(L.carrier/K), Units.map sigma r = r := by
    intro sigma
    have hchar := DFunLike.congr_fun hb sigma
    have hratio : radicalKummerRatio K Omega n L b sigma = 1 := by
      have hroot :
          radicalRootCharacter K Omega n L hn hroots sigma b = 1 := by
        apply Subtype.ext
        exact hchar
      let e := rootsOfUnityEquivOfPrimitiveRoots
        (algebraMap K L.carrier).injective hroots
      let eta : rootsOfUnity n L.carrier :=
        radicalKummerExtension K Omega n L hn hroots sigma b
      have hetaK : e.symm eta = 1 := by
        change radicalRootCharacter K Omega n L hn hroots sigma b = 1
        exact hroot
      have heta : eta = 1 := by
        apply e.symm.injective
        simpa using hetaK
      exact congrArg Subtype.val heta
    change Units.map sigma r * r⁻¹ = 1 at hratio
    exact (mul_inv_eq_one.mp hratio)
  have hrbase : (r : L.carrier) ∈ Set.range (algebraMap K L.carrier) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro sigma
    exact congrArg Units.val (hfixed sigma)
  obtain ⟨a, ha⟩ := hrbase
  have hrep :
      powerClassRepresentative K n b.1 = Units.mk0 a (by
        intro ha0
        apply r.ne_zero
        change (r : L.carrier) = 0
        simpa [ha0] using ha.symm) ^ n := by
    apply Units.map_injective (algebraMap K L.carrier).injective
    have hra : Units.map (algebraMap K L.carrier).toMonoidHom
        (Units.mk0 a (by
          intro ha0
          apply r.ne_zero
          change (r : L.carrier) = 0
          simpa [ha0] using ha.symm)) = r := by
      apply Units.ext
      exact ha
    rw [map_pow, hra, radical_unit_pow]
  apply Subtype.ext
  rw [← power_class_representative K n b.1, hrep, map_pow]
  exact power_class_pow n _

omit [IsAlgClosure K Omega] in
/-- Every base-valued character is represented by a radical power class.
This is the Hilbert-90 half of nondegeneracy. -/
theorem radical_kummer_pairing
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    Function.Surjective (radicalKummerPairing K Omega n L hn hroots) := by
  let : NeZero n := ⟨hn.ne'⟩
  intro chi
  let chiRoot : Gal(L.carrier/K) →* rootsOfUnity n K :=
    { toFun := fun sigma =>
        ⟨chi sigma, (mem_rootsOfUnity n _).2 (by
          rw [← map_pow, L.exponent_dvd sigma, map_one])⟩
      map_one' := by
        apply Subtype.ext
        exact chi.map_one
      map_mul' := fun sigma tau => by
        apply Subtype.ext
        exact chi.map_mul sigma tau }
  let beta : L.carrierˣ := hilbert90Radical K L.carrier n chiRoot
  have hbeta : ∀ sigma : Gal(L.carrier/K),
      Units.map sigma beta / beta =
        Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma) := by
    intro sigma
    simpa [beta, chiRoot, galoisCharacterUnits] using
      hilbert_90_ratio K L.carrier n chiRoot sigma
  have hbetapow : (beta : L.carrier) ^ n ∈
      Set.range (algebraMap K L.carrier) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro sigma
    have htrans : Units.map sigma beta =
        Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma) * beta := by
      calc
        Units.map sigma beta = (Units.map sigma beta / beta) * beta := by
          rw [div_eq_mul_inv]
          group
        _ = _ := by rw [hbeta sigma]
    have hchipow : chi sigma ^ n = 1 := by
      rw [← map_pow, L.exponent_dvd sigma, map_one]
    have hu : Units.map sigma (beta ^ n) = beta ^ n := by
      rw [map_pow, htrans, mul_pow, ← map_pow, hchipow, map_one, one_mul]
    exact congrArg Units.val hu
  obtain ⟨a, ha⟩ := hbetapow
  have ha0 : a ≠ 0 := by
    intro ha0
    apply beta.ne_zero
    have hz : (beta : L.carrier) ^ n = 0 := by simpa [ha0] using ha.symm
    exact eq_zero_of_pow_eq_zero hz
  let aunit : Kˣ := Units.mk0 a ha0
  let b0 : PowerClassGroup K n := powerClass n aunit
  have hb0 : b0 ∈ radicalPowerClasses K Omega n L.carrier := by
    refine ⟨aunit, ?_, rfl⟩
    refine ⟨beta, ?_⟩
    apply Units.ext
    exact ha.symm
  let b : radicalPowerClasses K Omega n L.carrier := ⟨b0, hb0⟩
  refine ⟨b, ?_⟩
  apply MonoidHom.ext
  intro sigma
  apply Units.map_injective (algebraMap K L.carrier).injective
  let r : L.carrierˣ := radicalRootUnit K Omega n L b
  have hclass : powerClass n (powerClassRepresentative K n b.1) =
      powerClass n aunit := by
    simp [b, b0]
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclass
  obtain ⟨c, rfl⟩ := hz
  let cL : L.carrierˣ := Units.map (algebraMap K L.carrier).toMonoidHom c
  let y : L.carrierˣ := beta * cL⁻¹
  have hypow : y ^ n =
      Units.map (algebraMap K L.carrier).toMonoidHom
        (powerClassRepresentative K n b.1) := by
    change (beta * cL⁻¹) ^ n =
      Units.map (algebraMap K L.carrier).toMonoidHom
        (powerClassRepresentative K n b.1)
    rw [mul_pow, inv_pow]
    have hbetaunit : beta ^ n =
        Units.map (algebraMap K L.carrier).toMonoidHom aunit := by
      apply Units.ext
      exact ha.symm
    rw [hbetaunit, ← map_pow, ← map_inv, ← map_mul]
    apply congrArg (Units.map (algebraMap K L.carrier).toMonoidHom)
    change aunit * (c ^ n)⁻¹ = powerClassRepresentative K n b.1
    rw [← heq]
    simp only [powMonoidHom_apply]
    group
  let q : L.carrierˣ := r * y⁻¹
  have hqpow : q ^ n = 1 := by
    change (r * y⁻¹) ^ n = 1
    rw [mul_pow, inv_pow, radical_unit_pow, hypow]
    group
  have hqfix : Units.map sigma q = q :=
    alg_fix_general K n hn hroots sigma q hqpow
  have hcfix : Units.map sigma cL = cL := by
    apply Units.ext
    exact sigma.commutes (c : K)
  have hpair :
      Units.map (algebraMap K L.carrier).toMonoidHom
          (radicalKummerCharacter K Omega n L hn hroots sigma b) =
        radicalKummerRatio K Omega n L b sigma := by
    have he := rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      (algebraMap K L.carrier).injective hroots
      (radicalKummerExtension K Omega n L hn hroots sigma b)
    apply Units.ext
    exact he
  change Units.map (algebraMap K L.carrier).toMonoidHom
      (radicalKummerCharacter K Omega n L hn hroots sigma b) =
    Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma)
  rw [hpair]
  change Units.map sigma r * r⁻¹ =
    Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma)
  have hqdef : q = r * y⁻¹ := rfl
  have hratio : Units.map sigma r * r⁻¹ = Units.map sigma y * y⁻¹ := by
    have hqmapped := congrArg (Units.map (sigma : L.carrier →* L.carrier)) hqdef
    simp only [map_mul, map_inv] at hqmapped
    rw [hqfix, hqdef] at hqmapped
    calc
      Units.map sigma r * r⁻¹ =
          (Units.map sigma r * (Units.map sigma y)⁻¹) *
            Units.map sigma y * r⁻¹ := by group
      _ = r * y⁻¹ * Units.map sigma y * r⁻¹ := by rw [← hqmapped]
      _ = (r * r⁻¹) * (Units.map sigma y * y⁻¹) := by ac_rfl
      _ = Units.map sigma y * y⁻¹ := by simp
  have hyratio : Units.map sigma y * y⁻¹ =
      Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma) := by
    calc
      Units.map sigma y * y⁻¹ = Units.map sigma beta * beta⁻¹ := by
        dsimp [y]
        simp only [map_mul, map_inv, hcfix]
        group
      _ = Units.map (algebraMap K L.carrier).toMonoidHom (chi sigma) := by
        simpa [div_eq_mul_inv] using hbeta sigma
  rw [hratio, hyratio]

/-- The perfect Kummer pairing as a multiplicative equivalence. -/
def radicalPairingEquiv
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    radicalPowerClasses K Omega n L.carrier ≃*
      (Gal(L.carrier/K) →* Kˣ) :=
  MulEquiv.ofBijective
    (radicalKummerPairing K Omega n L hn hroots)
    ⟨kummer_pairing_injective K Omega n L hn hroots,
      radical_kummer_pairing K Omega n L hn hroots⟩

omit [IsAlgClosure K Omega] in
/-- The radical power-class group of a finite abelian exponent-`n`
extension is finite. -/
theorem radical_classes_finite
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    Set.Finite
      ((radicalPowerClasses K Omega n L.carrier :
        Subgroup (PowerClassGroup K n)) : Set (PowerClassGroup K n)) := by
  let : Finite Gal(L.carrier/K) := inferInstance
  let : NeZero n := ⟨hn.ne'⟩
  have hexp : Monoid.exponent Gal(L.carrier/K) ∣ n := by
    exact Monoid.exponent_dvd_of_forall_pow_eq_one L.exponent_dvd
  let : HasEnoughRootsOfUnity K n := by
    have hprimitive : IsPrimitiveRoot hroots.choose n :=
      (mem_primitiveRoots hn).mp hroots.choose_spec
    exact HasEnoughRootsOfUnity.of_card_le
      (by rw [hprimitive.card_rootsOfUnity])
  let : HasEnoughRootsOfUnity K
      (Monoid.exponent Gal(L.carrier/K)) :=
    HasEnoughRootsOfUnity.of_dvd K hexp
  let : Finite (Gal(L.carrier/K) →* Kˣ) := inferInstance
  let : Finite (radicalPowerClasses K Omega n L.carrier) :=
    Finite.of_equiv _ (radicalPairingEquiv K Omega n L hn hroots).symm.toEquiv
  exact Set.finite_def.mpr ⟨Fintype.ofFinite _⟩

omit [IsAlgClosure K Omega] in
/-- The order of the radical power-class group is the extension degree. -/
theorem radical_classes_finrank
    (hn : 0 < n)
    (hroots : (primitiveRoots n K).Nonempty) :
    Nat.card (radicalPowerClasses K Omega n L.carrier) =
      Module.finrank K L.carrier := by
  have hexp : Monoid.exponent Gal(L.carrier/K) ∣ n := by
    exact Monoid.exponent_dvd_of_forall_pow_eq_one L.exponent_dvd
  let : NeZero n := ⟨hn.ne'⟩
  let : HasEnoughRootsOfUnity K n := by
    have hprimitive : IsPrimitiveRoot hroots.choose n :=
      (mem_primitiveRoots hn).mp hroots.choose_spec
    exact HasEnoughRootsOfUnity.of_card_le
      (by rw [hprimitive.card_rootsOfUnity])
  let : HasEnoughRootsOfUnity K
      (Monoid.exponent Gal(L.carrier/K)) :=
    HasEnoughRootsOfUnity.of_dvd K hexp
  let : CommGroup Gal(L.carrier/K) :=
    { (inferInstance : Group Gal(L.carrier/K)) with mul_comm := mul_comm' }
  calc
    Nat.card (radicalPowerClasses K Omega n L.carrier) =
        Nat.card (Gal(L.carrier/K) →* Kˣ) :=
      Nat.card_congr
        (radicalPairingEquiv K Omega n L hn hroots).toEquiv
    _ = Nat.card Gal(L.carrier/K) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        Gal(L.carrier/K) K
    _ = Module.finrank K L.carrier :=
      IsGalois.card_aut_eq_finrank K L.carrier

end

end

end Towers.CField.KTheory
