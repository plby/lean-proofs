import ErdosProblems.Erdos980.ElliottTail.RayPrincipalization
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Archimedean height bounds for corrected primary generators

The fundamental cone for the unit action gives a balanced generator of every
principal ideal.  This file combines that balance with the finite ray
corrections used in `RayPrincipalization`.  A finite representative of the
unit residue modulo the cyclotomic ray modulus restores the strong primary
congruence after balancing; its archimedean cost is absorbed in one constant.
-/

open scoped NumberField nonZeroDivisors

namespace Erdos980.ElliottTail.RayPrincipalizationHeight

noncomputable section

open NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone

/-- Points in the fundamental cone have every archimedean coordinate bounded
by a fixed multiple of the `d`-th root of their absolute field norm. -/
theorem exists_fundamentalCone_place_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 < B ∧
      ∀ x : mixedSpace K, x ∈ fundamentalCone K →
        ∀ w : InfinitePlace K,
          normAtPlace w x ≤
            B * mixedEmbedding.norm x ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  have hb := isBounded_normLeOne K
  have hplace : ∀ w : InfinitePlace K, ∃ C : ℝ,
      ∀ z ∈ normLeOne K, normAtPlace w z ≤ C := by
    intro w
    rcases w.isReal_or_isComplex with hw | hw
    · have hc := hb.image_fst.image_eval ⟨w, hw⟩
      rw [isBounded_iff_forall_norm_le] at hc
      obtain ⟨C, hC⟩ := hc
      refine ⟨C, fun z hz ↦ ?_⟩
      rw [normAtPlace_apply_of_isReal hw]
      exact hC (z.1 ⟨w, hw⟩) ⟨z.1, ⟨z, hz, rfl⟩, rfl⟩
    · have hc := hb.image_snd.image_eval ⟨w, hw⟩
      rw [isBounded_iff_forall_norm_le] at hc
      obtain ⟨C, hC⟩ := hc
      refine ⟨C, fun z hz ↦ ?_⟩
      rw [normAtPlace_apply_of_isComplex hw]
      exact hC (z.2 ⟨w, hw⟩) ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
  choose C hC using hplace
  let B : ℝ := 1 + ∑ w : InfinitePlace K, |C w|
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hCB (w : InfinitePlace K) : C w ≤ B := by
    calc
      C w ≤ |C w| := le_abs_self _
      _ ≤ ∑ v : InfinitePlace K, |C v| := by
        exact Finset.single_le_sum (fun v _ ↦ abs_nonneg (C v)) (Finset.mem_univ w)
      _ ≤ B := by dsimp [B]; linarith
  refine ⟨B, hBpos, ?_⟩
  intro x hx w
  let d : ℕ := Module.finrank ℚ K
  let N : ℝ := mixedEmbedding.norm x
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Module.finrank_pos.ne'
  have hN : 0 < N := by
    dsimp [N]
    exact norm_pos_of_mem hx
  let t : ℝ := N ^ ((d : ℝ)⁻¹)
  have ht : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos hN _
  let z : mixedSpace K := t⁻¹ • x
  have hzcone : z ∈ fundamentalCone K := by
    exact smul_mem_of_mem hx (inv_ne_zero ht.ne')
  have htpow : t ^ d = N := by
    dsimp [t]
    exact Real.rpow_inv_natCast_pow hN.le hd
  have hznorm : mixedEmbedding.norm z = 1 := by
    dsimp only [z]
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos ht, inv_pow, htpow]
    exact inv_mul_cancel₀ hN.ne'
  have hz : z ∈ normLeOne K :=
    mem_normLeOne.mpr ⟨hzcone, hznorm.le⟩
  have hx_tz : t • z = x := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  calc
    normAtPlace w x = normAtPlace w (t • z) := by rw [hx_tz]
    _ = |t| * normAtPlace w z := normAtPlace_smul w z t
    _ = t * normAtPlace w z := by rw [abs_of_pos ht]
    _ ≤ t * B := mul_le_mul_of_nonneg_left ((hC w z hz).trans (hCB w)) ht.le
    _ = B * mixedEmbedding.norm x ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
      dsimp [t, N, d]
      ring

/-- The mixed norm of an algebraic integer is the real cast of the absolute
norm of its principal ideal. -/
theorem mixedEmbedding_norm_ringOfIntegers
    (K : Type*) [Field K] [NumberField K] (a : RingOfIntegers K) :
    mixedEmbedding.norm (mixedEmbedding K (a : K)) =
      (Ideal.absNorm (Ideal.span ({a} : Set (RingOfIntegers K))) : ℝ) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast,
    Int.cast_abs, Algebra.coe_norm_int, ← norm_eq_norm]

section Cyclotomic

open IsCyclotomicExtension
open BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation "lam" => FLT37.zetaSubOne p K
local notation "L" => Ideal.span ({lam} : Set (RingOfIntegers K))
local notation "I" => L ^ (2 * p)

private lemma cyclotomic_lambdaIdeal_ne_bot : L ≠ ⊥ := by
  intro h
  exact FLT37.zetaSubOne_ne_zero p K
    (Ideal.span_singleton_eq_bot.mp h)

private lemma cyclotomic_modulus_ne_bot : I ≠ ⊥ :=
  pow_ne_zero _ (cyclotomic_lambdaIdeal_ne_bot p K)

noncomputable local instance : Finite (RingOfIntegers K ⧸ I) :=
  Ring.HasFiniteQuotients.finiteQuotient (cyclotomic_modulus_ne_bot p K)

noncomputable local instance : Fintype (RingOfIntegers K ⧸ I) :=
  Fintype.ofFinite _

/-- Reduction of an integral unit modulo the fixed cyclotomic ray modulus. -/
noncomputable def unitResidue (u : (RingOfIntegers K)ˣ) :
    RingOfIntegers K ⧸ I :=
  Ideal.Quotient.mk I (u : RingOfIntegers K)

/-- The finite image of the unit group in the ray residue ring. -/
def UnitResidueImage := Set.range (unitResidue p K)

noncomputable local instance : Fintype (UnitResidueImage p K) :=
  Fintype.ofFinite _

/-- A fixed unit representing a residue in the finite unit-residue image. -/
noncomputable def unitResidueRepresentative
    (r : UnitResidueImage p K) : (RingOfIntegers K)ˣ :=
  Classical.choose r.2

@[simp]
theorem unitResidue_unitResidueRepresentative
    (r : UnitResidueImage p K) :
    unitResidue p K (unitResidueRepresentative p K r) = r.1 :=
  Classical.choose_spec r.2

/-- The residue-image element represented by a given unit. -/
noncomputable def unitResidueClass (u : (RingOfIntegers K)ˣ) :
    UnitResidueImage p K :=
  ⟨unitResidue p K u, ⟨u, rfl⟩⟩

/-- Remove from a unit its fixed residue representative.  The resulting unit
is congruent to one modulo the full ray modulus. -/
noncomputable def primaryBalancingUnit (u : (RingOfIntegers K)ˣ) :
    (RingOfIntegers K)ˣ :=
  (unitResidueRepresentative p K (unitResidueClass p K u))⁻¹ * u

theorem primaryBalancingUnit_sub_one_mem
    (u : (RingOfIntegers K)ˣ) :
    (primaryBalancingUnit p K u : RingOfIntegers K) - 1 ∈ I := by
  let r := unitResidueClass p K u
  let v := unitResidueRepresentative p K r
  let q : RingOfIntegers K →+* RingOfIntegers K ⧸ I :=
    Ideal.Quotient.mk I
  have hvu : q (v : RingOfIntegers K) = q (u : RingOfIntegers K) := by
    calc
      q (v : RingOfIntegers K) = unitResidue p K v := rfl
      _ = r.1 := unitResidue_unitResidueRepresentative p K r
      _ = q (u : RingOfIntegers K) := rfl
  have hvuUnits : Units.map q.toMonoidHom v = Units.map q.toMonoidHom u := by
    apply Units.ext
    exact hvu
  have hbalanced : Units.map q.toMonoidHom (v⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, hvuUnits, inv_mul_cancel]
  have hq : q (((v⁻¹ * u : (RingOfIntegers K)ˣ)) : RingOfIntegers K) = 1 := by
    change ((Units.map q.toMonoidHom (v⁻¹ * u) :
      (RingOfIntegers K ⧸ I)ˣ) : RingOfIntegers K ⧸ I) = 1
    exact congrArg Units.val hbalanced
  rw [← Ideal.Quotient.eq]
  change q (primaryBalancingUnit p K u : RingOfIntegers K) = q 1
  change q (((v⁻¹ * u : (RingOfIntegers K)ˣ)) : RingOfIntegers K) = q 1
  rw [hq, map_one]

theorem primaryBalancingUnit_isPrimary
    (u : (RingOfIntegers K)ˣ) :
    FLT37.IsPrimary p (K := K)
      (primaryBalancingUnit p K u : RingOfIntegers K) := by
  refine ⟨1, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
  simpa using primaryBalancingUnit_sub_one_mem p K u

/-- A positive bound for the inverses of the finitely many chosen unit
residue representatives, simultaneously at every complex embedding. -/
noncomputable def unitResidueArchimedeanCost : ℝ :=
  1 + ∑ r : UnitResidueImage p K,
    ∑ φ : K →+* ℂ,
      ‖φ (((unitResidueRepresentative p K r)⁻¹ : (RingOfIntegers K)ˣ) :
        RingOfIntegers K)‖

theorem unitResidueArchimedeanCost_pos :
    0 < unitResidueArchimedeanCost p K := by
  unfold unitResidueArchimedeanCost
  positivity

theorem norm_unitResidueRepresentative_inv_le_cost
    (r : UnitResidueImage p K) (φ : K →+* ℂ) :
    ‖φ (((unitResidueRepresentative p K r)⁻¹ : (RingOfIntegers K)ˣ) :
      RingOfIntegers K)‖ ≤
      unitResidueArchimedeanCost p K := by
  let f : UnitResidueImage p K → ℝ := fun s ↦
    ∑ ψ : K →+* ℂ,
      ‖ψ (((unitResidueRepresentative p K s)⁻¹ : (RingOfIntegers K)ˣ) :
        RingOfIntegers K)‖
  calc
    ‖φ (((unitResidueRepresentative p K r)⁻¹ : (RingOfIntegers K)ˣ) :
        RingOfIntegers K)‖ ≤ f r := by
      change ‖φ (((unitResidueRepresentative p K r)⁻¹ :
          (RingOfIntegers K)ˣ) : RingOfIntegers K)‖ ≤
        ∑ ψ : K →+* ℂ,
          ‖ψ (((unitResidueRepresentative p K r)⁻¹ :
            (RingOfIntegers K)ˣ) : RingOfIntegers K)‖
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun ψ : K →+* ℂ ↦
          ‖ψ (((unitResidueRepresentative p K r)⁻¹ :
            (RingOfIntegers K)ˣ) : RingOfIntegers K)‖)
        (fun ψ _ ↦ norm_nonneg _) (Finset.mem_univ φ)
    _ ≤ ∑ s : UnitResidueImage p K, f s := by
      change (∑ ψ : K →+* ℂ,
          ‖ψ (((unitResidueRepresentative p K r)⁻¹ : (RingOfIntegers K)ˣ) :
            RingOfIntegers K)‖) ≤
        ∑ s : UnitResidueImage p K, ∑ ψ : K →+* ℂ,
          ‖ψ (((unitResidueRepresentative p K s)⁻¹ : (RingOfIntegers K)ˣ) :
            RingOfIntegers K)‖
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun s : UnitResidueImage p K ↦
          ∑ ψ : K →+* ℂ,
            ‖ψ (((unitResidueRepresentative p K s)⁻¹ :
              (RingOfIntegers K)ˣ) : RingOfIntegers K)‖)
        (fun s _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        (Finset.mem_univ r)
    _ ≤ unitResidueArchimedeanCost p K := by
      unfold unitResidueArchimedeanCost
      dsimp [f]
      linarith

/-- A positive bound for the `d`-th-root norms of the finitely many ideal
class/ray correction factors. -/
noncomputable def rayCorrectionArchimedeanCost : ℝ :=
  1 + ∑ i :
      RayPrincipalization.CyclotomicRayCorrectionIndex p K,
    (Ideal.absNorm
      (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹)

theorem rayCorrectionArchimedeanCost_pos :
    0 < rayCorrectionArchimedeanCost p K := by
  unfold rayCorrectionArchimedeanCost
  positivity

theorem rayCorrection_rpow_le_cost
    (i : RayPrincipalization.CyclotomicRayCorrectionIndex p K) :
    (Ideal.absNorm
      (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹) ≤
      rayCorrectionArchimedeanCost p K := by
  let f : RayPrincipalization.CyclotomicRayCorrectionIndex p K → ℝ :=
    fun j ↦
      (Ideal.absNorm
        (RayPrincipalization.cyclotomicRayCorrection p K j) : ℝ) ^
          ((Module.finrank ℚ K : ℝ)⁻¹)
  calc
    f i ≤ ∑ j, f j := by
      change (Ideal.absNorm
          (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
            ((Module.finrank ℚ K : ℝ)⁻¹) ≤
        ∑ j : RayPrincipalization.CyclotomicRayCorrectionIndex p K,
          (Ideal.absNorm
            (RayPrincipalization.cyclotomicRayCorrection p K j) : ℝ) ^
              ((Module.finrank ℚ K : ℝ)⁻¹)
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : RayPrincipalization.CyclotomicRayCorrectionIndex p K ↦
          (Ideal.absNorm
            (RayPrincipalization.cyclotomicRayCorrection p K j) : ℝ) ^
              ((Module.finrank ℚ K : ℝ)⁻¹))
        (fun j _ ↦ Real.rpow_nonneg
          (Nat.cast_nonneg (Ideal.absNorm
            (RayPrincipalization.cyclotomicRayCorrection p K j))) _)
        (Finset.mem_univ i)
    _ ≤ rayCorrectionArchimedeanCost p K := by
      unfold rayCorrectionArchimedeanCost
      dsimp [f]
      linarith

/-- Uniform archimedean height for the corrected strong-primary generator.

The constant depends only on the fixed cyclotomic field and ray modulus.  It
is independent of `P`, of the selected member of the finite ray-correction
family, and of the complex embedding. -/
theorem exists_primary_generator_mul_cyclotomicRayCorrection_height :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : (Ideal (RingOfIntegers K))⁰),
        L ⊔ (P : Ideal (RingOfIntegers K)) = ⊤ →
        ∃ (i : RayPrincipalization.CyclotomicRayCorrectionIndex p K)
          (a : RingOfIntegers K),
          FLT37.IsPrimary p (K := K) a ∧
          Furtwaengler.IsPrimeToP (p := p) (K := K) a ∧
          Ideal.span {a} = (P : Ideal (RingOfIntegers K)) *
            RayPrincipalization.cyclotomicRayCorrection p K i ∧
          ∀ φ : K →+* ℂ,
            ‖φ (a : K)‖ ≤
              C * (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨B, hBpos, hB⟩ := exists_fundamentalCone_place_bound K
  let U : ℝ := unitResidueArchimedeanCost p K
  let R : ℝ := rayCorrectionArchimedeanCost p K
  let C : ℝ := B * U * R
  have hUpos : 0 < U := by
    dsimp [U]
    exact unitResidueArchimedeanCost_pos p K
  have hRpos : 0 < R := by
    dsimp [R]
    exact rayCorrectionArchimedeanCost_pos p K
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro P hPL
  obtain ⟨i, a₀, ha₀primary, ha₀prime, ha₀span⟩ :=
    RayPrincipalization.exists_primary_generator_mul_cyclotomicRayCorrection
      p K P hPL
  let x : mixedSpace K := mixedEmbedding K (a₀ : K)
  have hx0 : x ≠ 0 := by
    intro hx
    have haK : (a₀ : K) = 0 := by
      apply mixedEmbedding_injective K
      simpa [x] using hx
    exact ha₀prime.1 (RingOfIntegers.coe_injective haK)
  have hxnorm : mixedEmbedding.norm x ≠ 0 :=
    (mixedEmbedding.norm_eq_zero_iff' ⟨(a₀ : K), rfl⟩).not.mpr hx0
  obtain ⟨u, hucone⟩ := exists_unit_smul_mem hxnorm
  let r : UnitResidueImage p K := unitResidueClass p K u
  let v : (RingOfIntegers K)ˣ := unitResidueRepresentative p K r
  let w : (RingOfIntegers K)ˣ := primaryBalancingUnit p K u
  let b : RingOfIntegers K := (u : RingOfIntegers K) * a₀
  let a : RingOfIntegers K := (w : RingOfIntegers K) * a₀
  have hwprimary : FLT37.IsPrimary p (K := K) (w : RingOfIntegers K) :=
    primaryBalancingUnit_isPrimary p K u
  have haprimary : FLT37.IsPrimary p (K := K) a := by
    dsimp [a]
    exact hwprimary.mul ha₀primary
  have haprime : Furtwaengler.IsPrimeToP (p := p) (K := K) a := by
    refine ⟨mul_ne_zero (Units.ne_zero w) ha₀prime.1, ?_⟩
    have ha₀cop := ha₀prime.2
    rw [Ideal.span_insert] at ha₀cop ⊢
    dsimp [a]
    rw [Ideal.span_singleton_mul_left_unit (Units.isUnit w)]
    exact ha₀cop
  have haspan : Ideal.span {a} = (P : Ideal (RingOfIntegers K)) *
      RayPrincipalization.cyclotomicRayCorrection p K i := by
    calc
      Ideal.span {a} = Ideal.span {a₀} := by
        dsimp [a]
        exact Ideal.span_singleton_mul_left_unit (Units.isUnit w) a₀
      _ = (P : Ideal (RingOfIntegers K)) *
          RayPrincipalization.cyclotomicRayCorrection p K i := ha₀span
  refine ⟨i, a, haprimary, haprime, haspan, ?_⟩
  intro φ
  have hbcone : mixedEmbedding K (b : K) ∈ fundamentalCone K := by
    simpa [x, b, unitSMul_smul] using hucone
  have hbbound := hB (mixedEmbedding K (b : K)) hbcone (InfinitePlace.mk φ)
  simp only [normAtPlace_apply, InfinitePlace.apply] at hbbound
  have hbspan : Ideal.span {b} = Ideal.span {a₀} := by
    dsimp [b]
    exact Ideal.span_singleton_mul_left_unit (Units.isUnit u) a₀
  have hnormb : mixedEmbedding.norm (mixedEmbedding K (b : K)) =
      (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) *
        (Ideal.absNorm
          (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) := by
    rw [mixedEmbedding_norm_ringOfIntegers K b, hbspan, ha₀span, map_mul,
      Nat.cast_mul]
  rw [hnormb, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hbbound
  have hvbound :
      ‖φ (((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) : K)‖ ≤ U := by
    dsimp [U, v, r]
    exact norm_unitResidueRepresentative_inv_le_cost p K
      (unitResidueClass p K u) φ
  have hQbound :
      (Ideal.absNorm
        (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
          ((Module.finrank ℚ K : ℝ)⁻¹) ≤ R := by
    dsimp [R]
    exact rayCorrection_rpow_le_cost p K i
  have hab : a =
      ((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) * b := by
    dsimp [a, w, b, v, r, primaryBalancingUnit]
    ring
  rw [hab]
  have hmap :
      φ ((((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) * b :
          RingOfIntegers K) : K) =
        φ (((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) : K) * φ (b : K) := by
    change
      φ (((((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) : K) * (b : K))) = _
    exact map_mul φ _ _
  rw [hmap]
  rw [norm_mul]
  calc
    ‖φ (((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) : K)‖ *
        ‖φ (b : K)‖ ≤
        ‖φ (((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) : K)‖ *
          (B * ((Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
              ((Module.finrank ℚ K : ℝ)⁻¹) *
            (Ideal.absNorm
              (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹))) :=
      mul_le_mul_of_nonneg_left hbbound (norm_nonneg _)
    _ ≤ U *
          (B * ((Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
              ((Module.finrank ℚ K : ℝ)⁻¹) *
            (Ideal.absNorm
              (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹))) := by
      gcongr
    _ ≤ C * (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
          ((Module.finrank ℚ K : ℝ)⁻¹) := by
      dsimp [C]
      calc
        U *
              (B * ((Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
                  ((Module.finrank ℚ K : ℝ)⁻¹) *
                (Ideal.absNorm
                    (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
                  ((Module.finrank ℚ K : ℝ)⁻¹))) =
            B * U *
                (Ideal.absNorm
                    (RayPrincipalization.cyclotomicRayCorrection p K i) : ℝ) ^
                  ((Module.finrank ℚ K : ℝ)⁻¹) *
              (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹) := by ring
        _ ≤ B * U * R *
              (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹) := by
          gcongr
        _ = B * U * R *
              (Ideal.absNorm (P : Ideal (RingOfIntegers K)) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹) := rfl

end Cyclotomic

end

end Erdos980.ElliottTail.RayPrincipalizationHeight
