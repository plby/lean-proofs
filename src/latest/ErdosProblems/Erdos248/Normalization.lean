import ErdosProblems.Erdos248.Weight
import BoundedGaps.Maynard.MaynardYDiagonalCollisionMass
import BoundedGaps.Maynard.WirsingAllEndpoints
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős Problem 248: normalization of the varying-radius sieve weight

The generic Maynard estimates use one common radius in every coordinate.
That loses an exponential in the square of the dimension and is too crude
for the Tao--Teräväinen hierarchy.  This file instead keeps the coordinate
box `r_k < R_k` throughout.  The inner box `r_k < sqrt R_k` has cutoff at
least `1/4` in every coordinate; its only loss is therefore exponential in
the dimension, which the pre-sieve cutoff absorbs.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance normalizationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The squarefree, pre-sieved scalar support at the half-logarithmic radius
in coordinate `h`. -/
def innerCoordinateSupport (K : ℕ) (h : nearShifts K) : Finset ℕ :=
  (Finset.Icc 1 (innerShiftRadius K h)).filter fun n =>
    Squarefree n ∧ Nat.Coprime n (preSieveModulus K)

/-- Cartesian product of the half-logarithmic coordinate supports. -/
def innerTupleBox (K : ℕ) : Finset (nearShifts K → ℕ) :=
  Fintype.piFinset (innerCoordinateSupport K)

/-- Tuples in the inner box whose coordinate product is not squarefree,
equivalently tuples with a prime collision between two coordinates. -/
def innerCollisionBox (K : ℕ) : Finset (nearShifts K → ℕ) :=
  (innerTupleBox K).filter fun u =>
    ¬Squarefree (divisorTupleProduct (nearShifts K) u)

theorem innerTupleBox_coordinate {K : ℕ} {u : nearShifts K → ℕ}
    (hu : u ∈ innerTupleBox K) (h : nearShifts K) :
    u h ≤ innerShiftRadius K h ∧ 0 < u h ∧ Squarefree (u h) ∧
      Nat.Coprime (u h) (preSieveModulus K) := by
  have huh := Fintype.mem_piFinset.mp hu h
  exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp huh).1).2,
    (Finset.mem_Icc.mp (Finset.mem_filter.mp huh).1).1,
    (Finset.mem_filter.mp huh).2.1,
    (Finset.mem_filter.mp huh).2.2⟩

theorem innerTupleBox_product_le_radiusProduct {K : ℕ}
    (hK : 0 < K) {u : nearShifts K → ℕ} (hu : u ∈ innerTupleBox K) :
    divisorTupleProduct (nearShifts K) u ≤ radiusProduct K := by
  unfold divisorTupleProduct radiusProduct
  rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]
  apply Finset.prod_le_prod
  · intro k hk
    exact Nat.zero_le _
  · intro k hk
    exact (innerTupleBox_coordinate hu k).1.trans
      (innerShiftRadius_le_shiftRadius hK
        (mem_nearShifts.mp k.property).2)

theorem innerTupleBox_product_lt_globalRadius {K : ℕ}
    (hK : 0 < K) {u : nearShifts K → ℕ} (hu : u ∈ innerTupleBox K) :
    divisorTupleProduct (nearShifts K) u < globalRadius K := by
  exact (innerTupleBox_product_le_radiusProduct hK hu).trans_lt
    (by simpa [globalRadius] using radiusProduct_lt_intervalStart hK)

theorem innerTupleBox_subset_preSievedSimplex {K : ℕ} (hK : 0 < K) :
    innerTupleBox K ⊆
      preSievedSimplexTupleSupport (nearShifts K) (globalRadius K)
        (preSieveModulus K) := by
  intro u hu
  rw [mem_preSievedSimplexTupleSupport_iff]
  refine ⟨?_, innerTupleBox_product_lt_globalRadius hK hu⟩
  rw [preSievedCommonTupleSupport, Fintype.mem_piFinset]
  intro h
  rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
  have hd := innerTupleBox_coordinate hu h
  have hcoordLeProd : u h ≤ divisorTupleProduct (nearShifts K) u :=
    Nat.le_of_dvd
      (by
        unfold divisorTupleProduct
        exact Finset.prod_pos fun i hi => (innerTupleBox_coordinate hu i).2.1)
      (divisorTupleCoordinate_dvd_product u h)
  exact ⟨Finset.mem_range.mpr
      (hcoordLeProd.trans_lt (innerTupleBox_product_lt_globalRadius hK hu)),
    hd.2.1, hd.2.2.1, hd.2.2.2⟩

/-- The pairwise-coprime part of the inner box is genuine Maynard support. -/
theorem innerTupleBox_mem_maynard_of_squarefree {K : ℕ} (hK : 0 < K)
    {u : nearShifts K → ℕ} (hu : u ∈ innerTupleBox K)
    (hsq : Squarefree (divisorTupleProduct (nearShifts K) u)) :
    u ∈ sieveDivisorSupport K := by
  unfold sieveDivisorSupport
  rw [maynardDivisorTupleSupport_eq_preSievedSimplex_filter,
    Finset.mem_filter]
  exact ⟨innerTupleBox_subset_preSievedSimplex hK hu, hsq⟩

theorem innerTupleBox_cutoff_argument {K : ℕ} (hK : 0 < K)
    {u : nearShifts K → ℕ} (hu : u ∈ innerTupleBox K)
    (h : nearShifts K) :
    0 ≤ ((100 ^ (h : ℕ) : ℕ) : ℝ) *
        (Real.log (u h) / Real.log (globalRadius K)) ∧
      ((100 ^ (h : ℕ) : ℕ) : ℝ) *
        (Real.log (u h) / Real.log (globalRadius K)) ≤ 1 / 2 := by
  have hglobalLog : 0 < Real.log (globalRadius K) :=
    Real.log_pos (by exact_mod_cast one_lt_globalRadius K)
  have huData := innerTupleBox_coordinate hu h
  have huReal : (0 : ℝ) < u h := by exact_mod_cast huData.2.1
  have hinnerReal : (0 : ℝ) < innerShiftRadius K h := by
    exact_mod_cast innerShiftRadius_pos K h
  have hlogNonneg : 0 ≤ Real.log (u h) :=
    Real.log_natCast_nonneg (u h)
  have hlogLe : Real.log (u h) ≤ Real.log (innerShiftRadius K h) :=
    Real.strictMonoOn_log.monotoneOn huReal hinnerReal
      (by exact_mod_cast huData.1)
  have hdivLe :
      Real.log (u h) / Real.log (globalRadius K) ≤
        Real.log (innerShiftRadius K h) / Real.log (globalRadius K) :=
    (div_le_div_iff_of_pos_right hglobalLog).2 hlogLe
  have hfactor : (0 : ℝ) < ((100 ^ (h : ℕ) : ℕ) : ℝ) := by positivity
  constructor
  · exact mul_nonneg hfactor.le (div_nonneg hlogNonneg hglobalLog.le)
  · calc
      ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (Real.log (u h) / Real.log (globalRadius K)) ≤
          ((100 ^ (h : ℕ) : ℕ) : ℝ) *
            (Real.log (innerShiftRadius K h) /
              Real.log (globalRadius K)) :=
        mul_le_mul_of_nonneg_left hdivLe hfactor.le
      _ = ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (1 / (2 * ((100 ^ (h : ℕ) : ℕ) : ℝ))) := by
        rw [log_innerShiftRadius_div_log_globalRadius hK
          (mem_nearShifts.mp h.property).2]
      _ = 1 / 2 := by field_simp

theorem quarter_pow_le_tupleCutoff_inner {K : ℕ} (hK : 0 < K)
    {u : nearShifts K → ℕ} (hu : u ∈ innerTupleBox K) :
    (1 / 4 : ℝ) ^ K ≤
      tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) := by
  unfold tupleCutoff
  calc
    (1 / 4 : ℝ) ^ K = ∏ _h : nearShifts K, (1 / 4 : ℝ) := by
      simp [Fintype.card_coe, nearShifts_card]
    _ ≤ ∏ h : nearShifts K,
        selbergCutoff (((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (Real.log (u h) / Real.log (globalRadius K))) := by
      apply Finset.prod_le_prod
      · intro h hh
        norm_num
      · intro h hh
        exact quarter_le_selbergCutoff
          (innerTupleBox_cutoff_argument hK hu h).1
          (innerTupleBox_cutoff_argument hK hu h).2

/-- Reciprocal-totient mass of the entire inner coordinate box. -/
def innerTupleMass (K : ℕ) : ℝ :=
  ∑ u ∈ innerTupleBox K,
    reciprocalTotientTupleWeight (nearShifts K) u

/-- Reciprocal-totient mass lost to shared-prime coordinate collisions. -/
def innerCollisionMass (K : ℕ) : ℝ :=
  ∑ u ∈ innerCollisionBox K,
    reciprocalTotientTupleWeight (nearShifts K) u

/-- A convenient closed majorant for one inner coordinate. -/
def innerCoordinateMajorant (K : ℕ) (h : nearShifts K) : ℝ :=
  squarefreeCoprimeInvTotientMean (preSieveModulus K)
    (innerShiftRadius K h)

theorem innerTupleMass_eq_product (K : ℕ) :
    innerTupleMass K =
      ∏ h : nearShifts K,
        ∑ n ∈ innerCoordinateSupport K h,
          (1 : ℝ) / Nat.totient n := by
  unfold innerTupleMass innerTupleBox
  exact reciprocalTotientTupleWeight_sum_pi_eq_prod _

theorem innerCoordinateMass_le_majorant (K : ℕ) (h : nearShifts K) :
    (∑ n ∈ innerCoordinateSupport K h,
        (1 : ℝ) / Nat.totient n) ≤ innerCoordinateMajorant K h := by
  unfold innerCoordinateSupport innerCoordinateMajorant
  unfold squarefreeCoprimeInvTotientMean
  rw [Finset.sum_filter]

/-- Because the inner support uses the closed endpoint `Icc 1 Q`, its scalar
mass is exactly the Wirsing mean, rather than merely bounded by it. -/
theorem innerCoordinateMass_eq_majorant (K : ℕ) (h : nearShifts K) :
    (∑ n ∈ innerCoordinateSupport K h,
        (1 : ℝ) / Nat.totient n) = innerCoordinateMajorant K h := by
  unfold innerCoordinateSupport innerCoordinateMajorant
  unfold squarefreeCoprimeInvTotientMean
  rw [Finset.sum_filter]

theorem innerTupleMass_eq_majorant_product (K : ℕ) :
    innerTupleMass K =
      ∏ h : nearShifts K, innerCoordinateMajorant K h := by
  rw [innerTupleMass_eq_product]
  apply Finset.prod_congr rfl
  intro h hh
  exact innerCoordinateMass_eq_majorant K h

/-- There are at most `K^2` ordered pairs of distinct near shifts. -/
theorem offDiagonalPairs_near_card_le (K : ℕ) :
    (offDiagonalPairs (nearShifts K)).card ≤ K ^ 2 := by
  calc
    (offDiagonalPairs (nearShifts K)).card ≤
        (Finset.univ : Finset (nearShifts K × nearShifts K)).card := by
      exact Finset.card_le_card (by simp [offDiagonalPairs])
    _ = K ^ 2 := by
      simp [nearShifts_card, pow_two]

/-- The rough cross tail retains its inverse-cutoff saving when the total
one-coordinate error over all ordered collision pairs is at most one.  This
is the quantitative replacement for the dimensionally wasteful generic
`(exp 8)^K^2` bound. -/
theorem roughCrossTupleTotientSquareTail_le_three_mul
    {H : Finset ℕ} {D Q : ℕ} (hD : 0 < D)
    (hsmall : (8 * Real.exp 8 / (D : ℝ)) *
      ((offDiagonalPairs H).card : ℝ) ≤ 1) :
    roughCrossTupleTotientSquareTail H D Q ≤
      3 * (8 * Real.exp 8 / (D : ℝ)) *
        ((offDiagonalPairs H).card : ℝ) := by
  let M : ℝ := squarefreeRoughUnitMass D Q
  let m : ℕ := (offDiagonalPairs H).card
  let ε : ℝ := 8 * Real.exp 8 / (D : ℝ)
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hMone : 1 ≤ M := one_le_squarefreeRoughUnitMass D Q
  have hMnonneg : 0 ≤ M := zero_le_one.trans hMone
  have hMtail : M - 1 ≤ ε := by
    dsimp [M, ε]
    rw [squarefreeRoughUnitMass_eq]
    simpa using squarefreeRoughTotientSquareTail_le (Q := Q) hD
  have hMexp : M ≤ Real.exp ε := by
    calc
      M ≤ 1 + ε := by linarith
      _ ≤ Real.exp ε := by
        simpa [add_comm] using Real.add_one_le_exp ε
  have harg : (((m - 1 : ℕ) : ℝ) * ε) ≤ 1 := by
    calc
      (((m - 1 : ℕ) : ℝ) * ε) ≤ (m : ℝ) * ε := by
        gcongr
        exact_mod_cast Nat.sub_le m 1
      _ = ε * (m : ℝ) := by ring
      _ ≤ 1 := by simpa [ε, m] using hsmall
  have hMpow : M ^ (m - 1) ≤ 3 := by
    calc
      M ^ (m - 1) ≤ (Real.exp ε) ^ (m - 1) :=
        pow_le_pow_left₀ hMnonneg hMexp _
      _ = Real.exp (((m - 1 : ℕ) : ℝ) * ε) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr harg
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hpow := abs_pow_sub_pow_le (a := M) (b := (1 : ℝ)) (n := m)
  have hMpowOne : 1 ≤ M ^ m := one_le_pow₀ hMone
  norm_num only [one_pow] at hpow
  rw [abs_of_nonneg (sub_nonneg.mpr hMpowOne),
    abs_of_nonneg (sub_nonneg.mpr hMone), abs_of_nonneg hMnonneg,
    max_eq_left hMone] at hpow
  calc
    roughCrossTupleTotientSquareTail H D Q = M ^ m - 1 := by
      exact roughCrossTupleTotientSquareTail_eq_pow_sub_one H D Q
    _ ≤ (M - 1) * (m : ℝ) * M ^ (m - 1) := hpow
    _ ≤ ε * (m : ℝ) * M ^ (m - 1) := by
      gcongr
    _ ≤ ε * (m : ℝ) * 3 := by
      gcongr
    _ = 3 * (8 * Real.exp 8 / (D : ℝ)) *
        ((offDiagonalPairs H).card : ℝ) := by
      dsimp [ε, m]
      ring

def innerPrimeCoordinateSupport (K : ℕ) (h : nearShifts K) (p : ℕ) :
    Finset ℕ :=
  (innerCoordinateSupport K h).filter fun n => p ∣ n

theorem innerPrimeCoordinateSupport_subset (K : ℕ)
    (h : nearShifts K) (p : ℕ) :
    innerPrimeCoordinateSupport K h p ⊆
      squarefreeCoprimePrimeDivisorSupport (preSieveModulus K)
        (innerShiftRadius K h) p := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnInner := Finset.mem_filter.mp hnData.1
  rw [squarefreeCoprimePrimeDivisorSupport, Finset.mem_filter]
  exact ⟨hnInner.1, hnInner.2.1, hnInner.2.2, hnData.2⟩

theorem innerPrimeCoordinateMass_le {K p : ℕ} (hp : p.Prime)
    (h : nearShifts K) :
    (∑ n ∈ innerPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
      (1 : ℝ) / Nat.totient p * innerCoordinateMajorant K h := by
  calc
    (∑ n ∈ innerPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
        ∑ n ∈ squarefreeCoprimePrimeDivisorSupport (preSieveModulus K)
            (innerShiftRadius K h) p,
          (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (innerPrimeCoordinateSupport_subset K h p)
      intro n hn hnot
      positivity
    _ ≤ (1 : ℝ) / Nat.totient p * innerCoordinateMajorant K h := by
      simpa [innerCoordinateMajorant] using
        (squarefreeCoprimePrimeDivisorMean_le
          (W := preSieveModulus K) (Q := innerShiftRadius K h) hp)

/-- Varying coordinate box in which a fixed prime divides two specified
coordinates. -/
def innerPairPrimeBox (K : ℕ) (a b : nearShifts K) (p : ℕ) :
    Finset (nearShifts K → ℕ) :=
  Fintype.piFinset fun h =>
    if h = a ∨ h = b then innerPrimeCoordinateSupport K h p
    else innerCoordinateSupport K h

theorem inner_filter_pair_subset_box (K : ℕ)
    (a b : nearShifts K) (p : ℕ) :
    (innerTupleBox K).filter (fun u => p ∣ u a ∧ p ∣ u b) ⊆
      innerPairPrimeBox K a b p := by
  intro u hu
  have huData := Finset.mem_filter.mp hu
  rw [innerPairPrimeBox, Fintype.mem_piFinset]
  intro h
  have huh := Fintype.mem_piFinset.mp huData.1 h
  by_cases hha : h = a
  · subst h
    simp [innerPrimeCoordinateSupport, huh, huData.2.1]
  by_cases hhb : h = b
  · subst h
    simp [innerPrimeCoordinateSupport, huh, huData.2.2]
  · simp [hha, hhb, huh]

theorem inner_pair_prime_mass_le {K p : ℕ} {a b : nearShifts K}
    (hab : a ≠ b) (hp : p.Prime) :
    (∑ u ∈ (innerTupleBox K).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight (nearShifts K) u) ≤
      ((1 : ℝ) / Nat.totient p) ^ 2 *
        ∏ h : nearShifts K, innerCoordinateMajorant K h := by
  let c : ℝ := (1 : ℝ) / Nat.totient p
  calc
    (∑ u ∈ (innerTupleBox K).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ innerPairPrimeBox K a b p,
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (inner_filter_pair_subset_box K a b p)
      intro u hu hnot
      unfold reciprocalTotientTupleWeight
      positivity
    _ = ∏ h : nearShifts K,
        ∑ n ∈ (if h = a ∨ h = b then
            innerPrimeCoordinateSupport K h p
          else innerCoordinateSupport K h),
          (1 : ℝ) / Nat.totient n := by
      unfold innerPairPrimeBox
      exact reciprocalTotientTupleWeight_sum_pi_eq_prod _
    _ ≤ ∏ h : nearShifts K,
        (if h = a ∨ h = b then c * innerCoordinateMajorant K h
          else innerCoordinateMajorant K h) := by
      apply Finset.prod_le_prod
      · intro h hh
        positivity
      · intro h hh
        by_cases hs : h = a ∨ h = b
        · rw [if_pos hs, if_pos hs]
          simpa [c] using innerPrimeCoordinateMass_le hp h
        · rw [if_neg hs, if_neg hs]
          exact innerCoordinateMass_le_majorant K h
    _ = c ^ 2 * ∏ h : nearShifts K, innerCoordinateMajorant K h := by
      have hfactor :
          (∏ h : nearShifts K, if h = a ∨ h = b then c else 1) = c ^ 2 := by
        simpa using (coordinatePrimeCollisionMass_eq
          (H := nearShifts K) hab (M := (1 : ℝ)) (P := c))
      simp_rw [show ∀ h : nearShifts K,
          (if h = a ∨ h = b then c * innerCoordinateMajorant K h
            else innerCoordinateMajorant K h) =
          (if h = a ∨ h = b then c else 1) *
            innerCoordinateMajorant K h by
        intro h
        split_ifs <;> ring]
      rw [Finset.prod_mul_distrib, hfactor]
    _ = ((1 : ℝ) / Nat.totient p) ^ 2 *
        ∏ h : nearShifts K, innerCoordinateMajorant K h := rfl

def innerCollisionPairPrimeUnion (K : ℕ) :
    Finset (nearShifts K → ℕ) :=
  (collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
      (globalRadius K)).biUnion fun x =>
    (innerTupleBox K).filter fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2

theorem innerCollisionBox_subset_pairPrimeUnion {K : ℕ} (hK : 0 < K) :
    innerCollisionBox K ⊆ innerCollisionPairPrimeUnion K := by
  classical
  intro u hu
  have huData := Finset.mem_filter.mp hu
  have huSimplex := innerTupleBox_subset_preSievedSimplex hK huData.1
  have huNot : u ∉ sieveDivisorSupport K := by
    intro huMaynard
    exact huData.2 (sieveDivisorSupport_isMaynard K u huMaynard).2.2
  obtain ⟨a, b, p, hab, hp, hpGt, hpa, hpb⟩ :=
    exists_shared_prime_gt_of_independent_not_maynard huSimplex huNot
  have hcoordPos := (innerTupleBox_coordinate huData.1 a).2.1
  have hpLeCoord : p ≤ u a := Nat.le_of_dvd hcoordPos hpa
  have hcoordLeProd : u a ≤ divisorTupleProduct (nearShifts K) u :=
    Nat.le_of_dvd
      (by
        unfold divisorTupleProduct
        exact Finset.prod_pos fun i hi =>
          (innerTupleBox_coordinate huData.1 i).2.1)
      (divisorTupleCoordinate_dvd_product u a)
  have hpLeGlobal : p ≤ globalRadius K :=
    (hpLeCoord.trans hcoordLeProd).trans
      (innerTupleBox_product_lt_globalRadius hK huData.1).le
  have habMem : (a, b) ∈ offDiagonalPairs (nearShifts K) := by
    rw [offDiagonalPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hab⟩
  have hpMem : p ∈ roughPrimeSupport (tinyCutoff K) (globalRadius K) := by
    rw [roughPrimeSupport, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeGlobal⟩, hp⟩
  rw [innerCollisionPairPrimeUnion, Finset.mem_biUnion]
  exact ⟨((a, b), p), Finset.mem_product.mpr ⟨habMem, hpMem⟩,
    Finset.mem_filter.mpr ⟨huData.1, hpa, hpb⟩⟩

theorem innerCollisionMass_le_pairPrimeSum {K : ℕ} (hK : 0 < K) :
    innerCollisionMass K ≤
      ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
          (globalRadius K),
        ∑ u ∈ (innerTupleBox K).filter
            (fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2),
          reciprocalTotientTupleWeight (nearShifts K) u := by
  unfold innerCollisionMass
  calc
    (∑ u ∈ innerCollisionBox K,
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ (collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
            (globalRadius K)).biUnion (fun x =>
              (innerTupleBox K).filter fun u =>
                x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2),
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (innerCollisionBox_subset_pairPrimeUnion hK)
      intro u hu hnot
      unfold reciprocalTotientTupleWeight
      positivity
    _ ≤ _ := sum_biUnion_le_sum _ _ _ fun u => by
      unfold reciprocalTotientTupleWeight
      positivity

/-- The varying-box collision loss has the expected `K^2 / w` factor and,
crucially, only the product of the coordinatewise scalar means. -/
theorem innerCollisionMass_le_majorant {K : ℕ} (hK : 0 < K) :
    innerCollisionMass K ≤
      ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (∏ h : nearShifts K, innerCoordinateMajorant K h) *
          (8 / (tinyCutoff K : ℝ)) := by
  let M : ℝ := ∏ h : nearShifts K, innerCoordinateMajorant K h
  calc
    innerCollisionMass K ≤
        ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
            (globalRadius K),
          ∑ u ∈ (innerTupleBox K).filter
              (fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2),
            reciprocalTotientTupleWeight (nearShifts K) u :=
      innerCollisionMass_le_pairPrimeSum hK
    _ ≤ ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
          (globalRadius K),
        primeTotientSquareWeight x.2 * M := by
      apply Finset.sum_le_sum
      intro x hx
      have hxData := Finset.mem_product.mp hx
      have hab : x.1.1 ≠ x.1.2 :=
        (Finset.mem_filter.mp hxData.1).2
      have hp : x.2.Prime := (Finset.mem_filter.mp hxData.2).2
      have hpair := inner_pair_prime_mass_le (K := K) hab hp
      simpa [primeTotientSquareWeight, M, mul_comm, mul_left_comm,
        mul_assoc] using hpair
    _ = ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (M * ∑ p ∈ roughPrimeSupport (tinyCutoff K) (globalRadius K),
          primeTotientSquareWeight p) := by
      unfold collisionPairPrimeIndex
      rw [Finset.sum_product]
      simp only [Prod.snd]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      ring
    _ ≤ ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (M * (8 / (tinyCutoff K : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
          (roughPrimeWeightSum_le (tinyCutoff_pos K))
        unfold M innerCoordinateMajorant
        apply Finset.prod_nonneg
        intro h hh
        unfold squarefreeCoprimeInvTotientMean
        apply Finset.sum_nonneg
        intro n hn
        split <;> positivity
      · positivity
    _ = ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (∏ h : nearShifts K, innerCoordinateMajorant K h) *
          (8 / (tinyCutoff K : ℝ)) := by
      unfold M
      ring

/-- Full varying coordinate support `u_h < R_h`, used for the S1 cross
correction. -/
def varyingCoordinateSupport (K : ℕ) (h : nearShifts K) : Finset ℕ :=
  preSievedCommonCoordinateSupport (preSieveModulus K) (shiftRadius K h)

def varyingTupleBox (K : ℕ) : Finset (nearShifts K → ℕ) :=
  Fintype.piFinset (varyingCoordinateSupport K)

def varyingCoordinateMajorant (K : ℕ) (h : nearShifts K) : ℝ :=
  squarefreeCoprimeInvTotientMean (preSieveModulus K) (shiftRadius K h)

/-- The local density of integers coprime to the pre-sieve modulus. -/
def sieveDensity (K : ℕ) : ℝ :=
  coprimeHarmonicDensity (preSieveModulus K)

theorem sieveDensity_pos (K : ℕ) : 0 < sieveDensity K := by
  unfold sieveDensity coprimeHarmonicDensity
  exact div_pos
    (by exact_mod_cast Nat.totient_pos.mpr (preSieveModulus_pos K))
    (by exact_mod_cast preSieveModulus_pos K)

/-- Uniform scalar error furnished by the all-endpoint Wirsing theorem. -/
def normalizationError (A : ℝ) (K : ℕ) : ℝ :=
  10 * (A + Real.log (tinyCutoff K) + Real.log 2)

/-- The only scale inequality needed to compare all reciprocal-totient means
in the inner and full varying boxes. -/
def NormalizationRegular (A : ℝ) (K : ℕ) : Prop :=
  0 < K ∧
    4 * normalizationError A K ≤ Real.log (innerShiftRadius K K)

theorem wirsing_innerCoordinateMajorant_error
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    (K : ℕ) (h : nearShifts K) :
    |innerCoordinateMajorant K h -
        sieveDensity K * Real.log (innerShiftRadius K h)| ≤
      sieveDensity K * normalizationError A K := by
  have hsq : Squarefree (primorial (tinyCutoff K) * 1) := by
    simpa using squarefree_primorial (tinyCutoff K)
  have hw := hA (D := tinyCutoff K) (P := 1)
    (Q := innerShiftRadius K h) (by norm_num) hsq
  simpa [innerCoordinateMajorant, preSieveModulus, sieveDensity,
    normalizationError, primeLogDivisorMass, mul_assoc, mul_left_comm,
    mul_comm] using hw

theorem wirsing_varyingCoordinateMajorant_error
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    (K : ℕ) (h : nearShifts K) :
    |varyingCoordinateMajorant K h -
        sieveDensity K * Real.log (shiftRadius K h)| ≤
      sieveDensity K * normalizationError A K := by
  have hsq : Squarefree (primorial (tinyCutoff K) * 1) := by
    simpa using squarefree_primorial (tinyCutoff K)
  have hw := hA (D := tinyCutoff K) (P := 1)
    (Q := shiftRadius K h) (by norm_num) hsq
  simpa [varyingCoordinateMajorant, preSieveModulus, sieveDensity,
    normalizationError, primeLogDivisorMass, mul_assoc, mul_left_comm,
    mul_comm] using hw

theorem normalizationError_le_quarter_innerLog {A : ℝ} {K : ℕ}
    (hreg : NormalizationRegular A K) (h : nearShifts K) :
    normalizationError A K ≤
      Real.log (innerShiftRadius K h) / 4 := by
  have hmonoNat := innerShiftRadius_mono_near hreg.1
    (mem_nearShifts.mp h.property).2
  have hminPos : (0 : ℝ) < innerShiftRadius K K := by
    exact_mod_cast innerShiftRadius_pos K K
  have hhPos : (0 : ℝ) < innerShiftRadius K h := by
    exact_mod_cast innerShiftRadius_pos K h
  have hlogMono : Real.log (innerShiftRadius K K) ≤
      Real.log (innerShiftRadius K h) :=
    Real.strictMonoOn_log.monotoneOn hminPos hhPos (by exact_mod_cast hmonoNat)
  linarith [hreg.2]

theorem innerCoordinateMajorant_bounds {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) (h : nearShifts K) :
    (3 / 4 : ℝ) * sieveDensity K * Real.log (innerShiftRadius K h) ≤
        innerCoordinateMajorant K h ∧
      innerCoordinateMajorant K h ≤
        (5 / 4 : ℝ) * sieveDensity K *
          Real.log (innerShiftRadius K h) := by
  have herr := wirsing_innerCoordinateMajorant_error hA K h
  have hscale := normalizationError_le_quarter_innerLog hreg h
  have hδ : 0 ≤ sieveDensity K := (sieveDensity_pos K).le
  have hmul := mul_le_mul_of_nonneg_left hscale hδ
  rw [abs_le] at herr
  constructor <;> nlinarith

theorem varyingCoordinateMajorant_le_six_inner {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) (h : nearShifts K) :
    varyingCoordinateMajorant K h ≤ 6 * innerCoordinateMajorant K h := by
  have hout := wirsing_varyingCoordinateMajorant_error hA K h
  have hin := (innerCoordinateMajorant_bounds hA hreg h).1
  have hscale := normalizationError_le_quarter_innerLog hreg h
  have hδ : 0 ≤ sieveDensity K := (sieveDensity_pos K).le
  have hmul := mul_le_mul_of_nonneg_left hscale hδ
  have hlogs := log_shiftRadius_eq_two_mul_log_inner hreg.1
    (mem_nearShifts.mp h.property).2
  rw [abs_le] at hout
  nlinarith

theorem varyingTupleBox_coordinate {K : ℕ} {u : nearShifts K → ℕ}
    (hu : u ∈ varyingTupleBox K) (h : nearShifts K) :
    u h < shiftRadius K h ∧ 0 < u h ∧ Squarefree (u h) ∧
      Nat.Coprime (u h) (preSieveModulus K) := by
  have huh := Fintype.mem_piFinset.mp hu h
  exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp huh).1,
    (Finset.mem_filter.mp huh).2.1,
    (Finset.mem_filter.mp huh).2.2.1,
    (Finset.mem_filter.mp huh).2.2.2⟩

theorem varyingTupleBox_product_le_radiusProduct {K : ℕ}
    {u : nearShifts K → ℕ} (hu : u ∈ varyingTupleBox K) :
    divisorTupleProduct (nearShifts K) u ≤ radiusProduct K := by
  unfold divisorTupleProduct radiusProduct
  rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]
  apply Finset.prod_le_prod
  · intro k hk
    exact Nat.zero_le _
  · intro k hk
    exact (varyingTupleBox_coordinate hu k).1.le

theorem varyingTupleBox_subset_preSievedCommon {K : ℕ} (hK : 0 < K) :
    varyingTupleBox K ⊆
      preSievedCommonTupleSupport (nearShifts K) (preSieveModulus K)
        (globalRadius K) := by
  intro u hu
  rw [preSievedCommonTupleSupport, Fintype.mem_piFinset]
  intro h
  rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
  have hd := varyingTupleBox_coordinate hu h
  have hcoordLeProd : u h ≤ divisorTupleProduct (nearShifts K) u :=
    Nat.le_of_dvd
      (by
        unfold divisorTupleProduct
        exact Finset.prod_pos fun i hi =>
          (varyingTupleBox_coordinate hu i).2.1)
      (divisorTupleCoordinate_dvd_product u h)
  have hprodLt : divisorTupleProduct (nearShifts K) u < globalRadius K :=
    (varyingTupleBox_product_le_radiusProduct hu).trans_lt
      (by simpa [globalRadius] using radiusProduct_lt_intervalStart hK)
  exact ⟨Finset.mem_range.mpr (hcoordLeProd.trans_lt hprodLt),
    hd.2.1, hd.2.2.1, hd.2.2.2⟩

/-- A nonzero left Y-factor forces its common tuple into the sharp varying
coordinate box. -/
theorem varyingTupleBox_of_leftCrossYFactor_ne_zero {K : ℕ}
    {u : nearShifts K → ℕ}
    {s : ∀ ab : nearShifts K × nearShifts K,
      ab ∈ offDiagonalPairs (nearShifts K) → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport (nearShifts K)
      (preSieveModulus K) (globalRadius K))
    (hl : leftCrossYFactor (nearShifts K) (sieveY K) u s ≠ 0) :
    u ∈ varyingTupleBox K := by
  rw [varyingTupleBox, Fintype.mem_piFinset]
  intro h
  rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
    Finset.mem_filter]
  have huh := Fintype.mem_piFinset.mp hu h
  have huhData := Finset.mem_filter.mp huh
  have hyne : sieveY K (leftCrossLowerTuple (nearShifts K) u s) ≠ 0 :=
    leftCrossYFactor_ne_zero_y_ne_zero hl
  have hlowerLt := sieveY_ne_zero_coordinate_lt hyne h
  have hudvd := u_dvd_leftCrossLowerTuple (nearShifts K) u s h
  have hule : u h ≤ leftCrossLowerTuple (nearShifts K) u s h :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero
        ((sieveY_supported K _ hyne).coordinate_squarefree h).ne_zero)
      hudvd
  exact ⟨Finset.mem_range.mpr (hule.trans_lt hlowerLt),
    huhData.2.1, huhData.2.2.1, huhData.2.2.2⟩

/-- Exact replacement of the generic common-radius box in the starred cross
sum by the sharp varying-radius box. -/
theorem nontrivialStarredRoughPreSievedAuxiliaryYSum_eq_varying
    {K : ℕ} (hK : 0 < K) :
    nontrivialStarredRoughPreSievedAuxiliaryYSum (nearShifts K)
        (globalRadius K) (preSieveModulus K) (tinyCutoff K) (sieveY K) =
      ∑ s ∈ roughCrossTupleSupport (nearShifts K) (tinyCutoff K)
          (globalRadius K),
        if s ≠ oneCrossMoebiusTuple (nearShifts K) then
          crossMoebiusTupleTerm (nearShifts K) s *
            ∑ u ∈ varyingTupleBox K,
              if IsStarredCrossTuple (nearShifts K) u s then
                (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                  leftCrossYFactor (nearShifts K) (sieveY K) u s *
                  rightCrossYFactor (nearShifts K) (sieveY K) u s
              else 0
        else 0 := by
  classical
  unfold nontrivialStarredRoughPreSievedAuxiliaryYSum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsNe : s ≠ oneCrossMoebiusTuple (nearShifts K)
  · rw [if_pos hsNe, if_pos hsNe]
    congr 1
    symm
    apply Finset.sum_subset (varyingTupleBox_subset_preSievedCommon hK)
    intro u huPre huNot
    by_cases hstar : IsStarredCrossTuple (nearShifts K) u s
    · rw [if_pos hstar]
      have hl : leftCrossYFactor (nearShifts K) (sieveY K) u s = 0 := by
        by_contra hlne
        exact huNot (varyingTupleBox_of_leftCrossYFactor_ne_zero huPre hlne)
      simp [hl]
    · rw [if_neg hstar]
  · rw [if_neg hsNe, if_neg hsNe]

theorem starredCrossInnerSum_eq_varying {K : ℕ} (hK : 0 < K)
    (s : ∀ ab : nearShifts K × nearShifts K,
      ab ∈ offDiagonalPairs (nearShifts K) → ℕ) :
    (∑ u ∈ preSievedCommonTupleSupport (nearShifts K)
          (preSieveModulus K) (globalRadius K),
        if IsStarredCrossTuple (nearShifts K) u s then
          (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
            leftCrossYFactor (nearShifts K) (sieveY K) u s *
            rightCrossYFactor (nearShifts K) (sieveY K) u s
        else 0) =
      ∑ u ∈ varyingTupleBox K,
        if IsStarredCrossTuple (nearShifts K) u s then
          (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
            leftCrossYFactor (nearShifts K) (sieveY K) u s *
            rightCrossYFactor (nearShifts K) (sieveY K) u s
        else 0 := by
  symm
  apply Finset.sum_subset (varyingTupleBox_subset_preSievedCommon hK)
  intro u huPre huNot
  by_cases hstar : IsStarredCrossTuple (nearShifts K) u s
  · rw [if_pos hstar]
    have hl : leftCrossYFactor (nearShifts K) (sieveY K) u s = 0 := by
      by_contra hlne
      exact huNot (varyingTupleBox_of_leftCrossYFactor_ne_zero huPre hlne)
    simp [hl]
  · rw [if_neg hstar]

theorem varyingTupleInvTotientMass_le (K : ℕ) :
    (∑ u ∈ varyingTupleBox K,
        (1 : ℝ) / commonTotientProduct (nearShifts K) u) ≤
      ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  calc
    (∑ u ∈ varyingTupleBox K,
        (1 : ℝ) / commonTotientProduct (nearShifts K) u) =
        ∏ h : nearShifts K,
          ∑ n ∈ varyingCoordinateSupport K h,
            (1 : ℝ) / Nat.totient n := by
      unfold varyingTupleBox
      calc
        (∑ u ∈ Fintype.piFinset (varyingCoordinateSupport K),
            (1 : ℝ) / commonTotientProduct (nearShifts K) u) =
            ∑ u ∈ Fintype.piFinset (varyingCoordinateSupport K),
              reciprocalTotientTupleWeight (nearShifts K) u := by
          apply Finset.sum_congr rfl
          intro u hu
          exact inv_commonTotientProduct_eq_product (nearShifts K) u
        _ = _ := reciprocalTotientTupleWeight_sum_pi_eq_prod _
    _ ≤ ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      apply Finset.prod_le_prod
      · intro h hh
        positivity
      · intro h hh
        exact preSievedCoordinateInvTotientSum_le
          (preSieveModulus K) (shiftRadius K h)

theorem abs_fixed_varying_cross_inner_le {K : ℕ} (hK : 0 < K)
    {s : ∀ ab : nearShifts K × nearShifts K,
      ab ∈ offDiagonalPairs (nearShifts K) → ℕ}
    (hs : s ∈ roughCrossTupleSupport (nearShifts K) (tinyCutoff K)
      (globalRadius K)) :
    |crossMoebiusTupleTerm (nearShifts K) s *
        ∑ u ∈ varyingTupleBox K,
          if IsStarredCrossTuple (nearShifts K) u s then
            (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor (nearShifts K) (sieveY K) u s *
              rightCrossYFactor (nearShifts K) (sieveY K) u s
          else 0| ≤
      crossTotientSquareWeight (nearShifts K) s *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  rw [Finset.mul_sum]
  calc
    |∑ u ∈ varyingTupleBox K,
        crossMoebiusTupleTerm (nearShifts K) s *
          (if IsStarredCrossTuple (nearShifts K) u s then
            (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor (nearShifts K) (sieveY K) u s *
              rightCrossYFactor (nearShifts K) (sieveY K) u s
          else 0)| ≤
        ∑ u ∈ varyingTupleBox K,
          |crossMoebiusTupleTerm (nearShifts K) s *
            (if IsStarredCrossTuple (nearShifts K) u s then
              (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor (nearShifts K) (sieveY K) u s *
                rightCrossYFactor (nearShifts K) (sieveY K) u s
            else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ varyingTupleBox K,
        crossTotientSquareWeight (nearShifts K) s *
          ((1 : ℝ) / commonTotientProduct (nearShifts K) u) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hstar : IsStarredCrossTuple (nearShifts K) u s
      · rw [if_pos hstar]
        have huPre := varyingTupleBox_subset_preSievedCommon hK hu
        simpa [commonTotientProduct, mul_assoc] using
          (abs_starredCrossYSummand_le_separated
            (H := nearShifts K) (y := sieveY K) (B := (1 : ℝ))
            (W := preSieveModulus K) (R := globalRadius K)
            (D := tinyCutoff K) (by norm_num) (abs_sieveY_le_one K)
            huPre hs hstar)
      · rw [if_neg hstar, mul_zero, abs_zero]
        apply mul_nonneg
        · unfold crossTotientSquareWeight
          positivity
        · have hc : (0 : ℝ) ≤ commonTotientProduct (nearShifts K) u := by
            exact_mod_cast Nat.zero_le (commonTotientProduct (nearShifts K) u)
          exact one_div_nonneg.mpr hc
    _ = crossTotientSquareWeight (nearShifts K) s *
        ∑ u ∈ varyingTupleBox K,
          ((1 : ℝ) / commonTotientProduct (nearShifts K) u) := by
      rw [Finset.mul_sum]
    _ ≤ crossTotientSquareWeight (nearShifts K) s *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      apply mul_le_mul_of_nonneg_left (varyingTupleInvTotientMass_le K)
      unfold crossTotientSquareWeight
      exact one_div_nonneg.mpr (sq_nonneg _)

theorem abs_nontrivialStarredRoughPreSievedAuxiliaryYSum_le_varying
    {K : ℕ} (hK : 0 < K) :
    |nontrivialStarredRoughPreSievedAuxiliaryYSum (nearShifts K)
        (globalRadius K) (preSieveModulus K) (tinyCutoff K) (sieveY K)| ≤
      roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
          (globalRadius K) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  rw [nontrivialStarredRoughPreSievedAuxiliaryYSum_eq_erase]
  calc
    |∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K)
          (globalRadius K)).erase (oneCrossMoebiusTuple (nearShifts K)),
        crossMoebiusTupleTerm (nearShifts K) s *
          ∑ u ∈ preSievedCommonTupleSupport (nearShifts K)
              (preSieveModulus K) (globalRadius K),
            if IsStarredCrossTuple (nearShifts K) u s then
              (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor (nearShifts K) (sieveY K) u s *
                rightCrossYFactor (nearShifts K) (sieveY K) u s
            else 0| ≤
        ∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K)
          (globalRadius K)).erase (oneCrossMoebiusTuple (nearShifts K)),
          |crossMoebiusTupleTerm (nearShifts K) s *
            ∑ u ∈ preSievedCommonTupleSupport (nearShifts K)
                (preSieveModulus K) (globalRadius K),
              if IsStarredCrossTuple (nearShifts K) u s then
                (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                  leftCrossYFactor (nearShifts K) (sieveY K) u s *
                  rightCrossYFactor (nearShifts K) (sieveY K) u s
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K)
          (globalRadius K)).erase (oneCrossMoebiusTuple (nearShifts K)),
        crossTotientSquareWeight (nearShifts K) s *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      apply Finset.sum_le_sum
      intro s hs
      rw [starredCrossInnerSum_eq_varying hK s]
      exact abs_fixed_varying_cross_inner_le hK (Finset.mem_of_mem_erase hs)
    _ = roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
          (globalRadius K) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      unfold roughCrossTupleTotientSquareTail
      rw [Finset.sum_mul]

theorem abs_sieve_crossCorrection_le_varying {K : ℕ} (hK : 0 < K) :
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)| ≤
      roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
          (globalRadius K) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  unfold sieveDivisorSupport sieveCoefficient
  have hcoeff :
      maynardCoefficient (nearShifts K) (globalRadius K)
          (preSieveModulus K) (tupleCutoff K) =
        maynardCoefficientFromY (nearShifts K) (globalRadius K)
          (preSieveModulus K) (sieveY K) := by
    funext d
    exact maynardCoefficient_eq_fromYValue _ _ _ _ d
  rw [hcoeff]
  simp only [preSieveModulus]
  rw [incompatibleSum_eq_neg_roughPreSievedAuxiliaryYSum
    (globalRadius_pos K) (sieveY_supported K),
    abs_neg]
  exact abs_nontrivialStarredRoughPreSievedAuxiliaryYSum_le_varying hK

/-- The explicit Y-diagonal dominates the pairwise-coprime portion of the
inner box, with the fixed cutoff loss `(1/4)^(2K)`. -/
theorem inner_mass_sub_collision_mul_le_diagonal {K : ℕ} (hK : 0 < K) :
    ((1 / 4 : ℝ) ^ K) ^ 2 *
        (innerTupleMass K - innerCollisionMass K) ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
        (preSieveModulus K) (sieveY K) := by
  classical
  rw [sieveY, maynardYDiagonalSum_maynardYValue_eq_explicit]
  let goodInner := (innerTupleBox K).filter fun u =>
    Squarefree (divisorTupleProduct (nearShifts K) u)
  have hsplit : innerTupleMass K =
      (∑ u ∈ goodInner,
        reciprocalTotientTupleWeight (nearShifts K) u) +
        innerCollisionMass K := by
    unfold innerTupleMass innerCollisionMass innerCollisionBox goodInner
    exact (Finset.sum_filter_add_sum_filter_not
      (innerTupleBox K)
      (fun u => Squarefree (divisorTupleProduct (nearShifts K) u))
      (reciprocalTotientTupleWeight (nearShifts K))).symm
  rw [hsplit]
  rw [add_sub_cancel_right]
  calc
    ((1 / 4 : ℝ) ^ K) ^ 2 *
        ∑ u ∈ goodInner,
          reciprocalTotientTupleWeight (nearShifts K) u =
        ∑ u ∈ goodInner,
          ((1 / 4 : ℝ) ^ K) ^ 2 *
            reciprocalTotientTupleWeight (nearShifts K) u := by
      rw [Finset.mul_sum]
    _ ≤ ∑ u ∈ goodInner,
        tupleCutoff K
            (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 /
          ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      have huData := Finset.mem_filter.mp hu
      have hcut := quarter_pow_le_tupleCutoff_inner hK huData.1
      have hcutNonneg := tupleCutoff_nonneg K
        (fun h => Real.log (u h) / Real.log (globalRadius K))
      have hsq : ((1 / 4 : ℝ) ^ K) ^ 2 ≤
          tupleCutoff K
              (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) K]
      have hden : 0 < ∏ h : nearShifts K,
          (Nat.totient (u h) : ℝ) := by
        apply Finset.prod_pos
        intro h hh
        exact_mod_cast Nat.totient_pos.mpr
          (innerTupleBox_coordinate huData.1 h).2.1
      rw [reciprocalTotientTupleWeight,
        ← inv_commonTotientProduct_eq_product]
      have hcommon :
          (commonTotientProduct (nearShifts K) u : ℝ) =
            ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) := by
        unfold commonTotientProduct
        push_cast
        simp
      rw [hcommon]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hden.le)
    _ ≤ ∑ u ∈ sieveDivisorSupport K,
        tupleCutoff K
            (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 /
          ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have huData := Finset.mem_filter.mp hu
        exact innerTupleBox_mem_maynard_of_squarefree hK huData.1 huData.2
      · intro u hu hnot
        positivity

end Erdos248
