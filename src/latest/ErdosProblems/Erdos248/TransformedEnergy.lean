import ErdosProblems.Erdos248.CrossBounds

/-!
# Erdős Problem 248: quadratic control of transformed `Y`-variables

Fixed-prime correlations repeatedly replace the original Selberg `Y`-variable
by `erasePrimeY` or `differencePrimeY`.  This file puts those transforms in
the weighted finite-dimensional `L²` space carried by the sharp varying box.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance transformedEnergyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Weighted quadratic energy on the sharp product box. -/
def varyingYEnergy (K : ℕ) (y : (nearShifts K → ℕ) → ℝ) : ℝ :=
  ∑ u ∈ varyingTupleBox K,
    y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u

theorem varyingYEnergy_nonneg (K : ℕ)
    (y : (nearShifts K → ℕ) → ℝ) :
    0 ≤ varyingYEnergy K y := by
  unfold varyingYEnergy reciprocalTotientTupleWeight
  positivity

/-- For a supported sharply localized `Y`, the library diagonal is exactly
its sharp-box quadratic energy. -/
theorem maynardYDiagonalSum_eq_varyingYEnergy
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y) :
    maynardYDiagonalSum (nearShifts K) R W y = varyingYEnergy K y := by
  let D := maynardDivisorTupleSupport (nearShifts K) R W
  let A := D.filter fun u => y u ≠ 0
  let V := (varyingTupleBox K).filter fun u => y u ≠ 0
  let G : (nearShifts K → ℕ) → ℝ := fun u =>
    y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u
  have hAeqV : A = V := by
    ext u
    simp only [A, V, Finset.mem_filter]
    constructor
    · rintro ⟨huD, hyu⟩
      rw [varyingTupleBox, Fintype.mem_piFinset]
      refine ⟨?_, hyu⟩
      intro h
      rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
        Finset.mem_filter]
      have huMaynard := isMaynardDivisorTuple_of_mem_support huD
      have hpos : 0 < u h :=
        Nat.pos_of_ne_zero (huMaynard.coordinate_squarefree h).ne_zero
      exact ⟨Finset.mem_range.mpr (hySharp hyu h), hpos,
        huMaynard.coordinate_squarefree h,
        (huMaynard.coordinate_coprime_W h).coprime_dvd_right hmod⟩
    · rintro ⟨huVary, hyu⟩
      have huMaynard := hy u hyu
      exact ⟨mem_maynardDivisorTupleSupport_iff.mpr
        ⟨huMaynard.mem_maynardDivisorTupleBox, huMaynard⟩, hyu⟩
  calc
    maynardYDiagonalSum (nearShifts K) R W y = ∑ u ∈ D, G u := by
      unfold maynardYDiagonalSum G reciprocalTotientTupleWeight D
      apply Finset.sum_congr rfl
      intro u hu
      rw [show (∏ h : nearShifts K, (1 : ℝ) / Nat.totient (u h)) =
          1 / ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) by
        simp only [one_div, Finset.prod_inv_distrib]]
      ring
    _ = ∑ u ∈ A, G u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u huD huNot
      have hyzero : y u = 0 := by
        by_contra hyu
        exact huNot (Finset.mem_filter.mpr ⟨huD, hyu⟩)
      simp [G, hyzero]
    _ = ∑ u ∈ V, G u := by rw [hAeqV]
    _ = ∑ u ∈ varyingTupleBox K, G u := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u huV huNot
      have hyzero : y u = 0 := by
        by_contra hyu
        exact huNot (Finset.mem_filter.mpr ⟨huV, hyu⟩)
      simp [G, hyzero]
    _ = varyingYEnergy K y := rfl

theorem varyingYEnergy_sieveY_le (K : ℕ) :
    varyingYEnergy K (sieveY K) ≤ productCoordinateEnergy K := by
  calc
    varyingYEnergy K (sieveY K) ≤ varyingCutoffEnergy K := by
      unfold varyingYEnergy varyingCutoffEnergy
      apply Finset.sum_le_sum
      intro u hu
      have hbound := abs_sieveY_le_coordinateProduct K u
      have hprod0 :
          0 ≤ ∏ h : nearShifts K, coordinateCutoff K h (u h) :=
        Finset.prod_nonneg fun h _ => coordinateCutoff_nonneg K h (u h)
      have hsq :
          sieveY K u ^ 2 ≤
            (∏ h : nearShifts K, coordinateCutoff K h (u h)) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hprod0).mpr hbound
      exact mul_le_mul_of_nonneg_right hsq (by
        unfold reciprocalTotientTupleWeight
        positivity)
    _ = productCoordinateEnergy K := varyingCutoffEnergy_eq_product K

theorem varyingTupleReciprocalWeightSum_le (K : ℕ) :
    (∑ u ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
      ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  calc
    (∑ u ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) u) =
        ∑ u ∈ varyingTupleBox K,
          (1 : ℝ) / commonTotientProduct (nearShifts K) u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (inv_commonTotientProduct_eq_product (nearShifts K) u).symm
    _ ≤ ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      varyingTupleInvTotientMass_le K

theorem varyingPrimeCoordinateMass_le {K p : ℕ} (hp : p.Prime)
    (h : nearShifts K) :
    (∑ n ∈ varyingPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
      (1 : ℝ) / Nat.totient p * varyingCoordinateMajorant K h := by
  calc
    (∑ n ∈ varyingPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
        ∑ n ∈ squarefreeCoprimePrimeDivisorSupport (preSieveModulus K)
            (shiftRadius K h) p,
          (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (varyingPrimeCoordinateSupport_subset K h p)
      intro n hn hnot
      positivity
    _ ≤ (1 : ℝ) / Nat.totient p * varyingCoordinateMajorant K h := by
      simpa [varyingCoordinateMajorant] using
        (squarefreeCoprimePrimeDivisorMean_le
          (W := preSieveModulus K) (Q := shiftRadius K h) hp)

def varyingPrimeCoordinateTupleBox (K : ℕ) (h : nearShifts K) (p : ℕ) :
    Finset (nearShifts K → ℕ) :=
  Fintype.piFinset fun i =>
    if i = h then varyingPrimeCoordinateSupport K i p
    else varyingCoordinateSupport K i

theorem varyingTuple_filter_prime_coordinate_subset
    (K : ℕ) (h : nearShifts K) (p : ℕ) :
    (varyingTupleBox K).filter (fun u => p ∣ u h) ⊆
      varyingPrimeCoordinateTupleBox K h p := by
  intro u hu
  have huData := Finset.mem_filter.mp hu
  rw [varyingPrimeCoordinateTupleBox, Fintype.mem_piFinset]
  intro i
  by_cases hi : i = h
  · subst i
    rw [if_pos rfl, varyingPrimeCoordinateSupport, Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.mp huData.1 h, huData.2⟩
  · rw [if_neg hi]
    exact Fintype.mem_piFinset.mp huData.1 i

theorem fixedCoordinatePrimeMass_le {K p : ℕ} (hp : p.Prime)
    (h : nearShifts K) :
    (∑ u ∈ (varyingTupleBox K).filter (fun u => p ∣ u h),
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
      (1 : ℝ) / Nat.totient p *
        ∏ i : nearShifts K, varyingCoordinateMajorant K i := by
  let S : nearShifts K → Finset ℕ := fun i =>
    if i = h then varyingPrimeCoordinateSupport K i p
    else varyingCoordinateSupport K i
  let M : nearShifts K → ℝ := fun i => varyingCoordinateMajorant K i
  calc
    (∑ u ∈ (varyingTupleBox K).filter (fun u => p ∣ u h),
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ varyingPrimeCoordinateTupleBox K h p,
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (varyingTuple_filter_prime_coordinate_subset K h p)
      intro u hu hnot
      unfold reciprocalTotientTupleWeight
      positivity
    _ = ∏ i : nearShifts K,
        ∑ n ∈ S i, (1 : ℝ) / Nat.totient n := by
      exact reciprocalTotientTupleWeight_sum_pi_eq_prod S
    _ ≤ ∏ i : nearShifts K,
        if i = h then (1 : ℝ) / Nat.totient p * M i else M i := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        by_cases hih : i = h
        · subst i
          simpa [S, M] using varyingPrimeCoordinateMass_le hp h
        · simpa [S, M, hih, varyingCoordinateSupport,
            varyingCoordinateMajorant] using
            preSievedCoordinateInvTotientSum_le
              (preSieveModulus K) (shiftRadius K i)
    _ = (1 : ℝ) / Nat.totient p *
        ∏ i : nearShifts K, varyingCoordinateMajorant K i := by
      classical
      let f : nearShifts K → ℝ := fun i => M i
      have hfun :
          (fun i : nearShifts K =>
            if i = h then (1 : ℝ) / Nat.totient p * M i else M i) =
            Function.update f h ((1 : ℝ) / Nat.totient p * M h) := by
        funext i
        by_cases hi : i = h
        · subst i
          simp [f]
        · simp [f, hi]
      rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ h)]
      simp only [Finset.sdiff_singleton_eq_erase]
      rw [show ∏ i : nearShifts K, varyingCoordinateMajorant K i =
          M h * ∏ i ∈ (Finset.univ : Finset (nearShifts K)).erase h,
            M i by
        symm
        exact Finset.mul_prod_erase Finset.univ M (Finset.mem_univ h)]
      dsimp [f]
      ring

/-- Reciprocal-totient mass of tuples on which a prime occurs in at least
one coordinate. -/
theorem varyingPrimeTupleMass_le {K p : ℕ} (hp : p.Prime) :
    (∑ u ∈ (varyingTupleBox K).filter
          (fun u => p ∣ divisorTupleProduct (nearShifts K) u),
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
      (K : ℝ) / Nat.totient p *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  calc
    (∑ u ∈ (varyingTupleBox K).filter
          (fun u => p ∣ divisorTupleProduct (nearShifts K) u),
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ varyingTupleBox K,
          ∑ h : nearShifts K,
            if p ∣ u h then reciprocalTotientTupleWeight (nearShifts K) u
            else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro u hu
      have hw : 0 ≤ reciprocalTotientTupleWeight (nearShifts K) u := by
        unfold reciprocalTotientTupleWeight
        positivity
      by_cases hdiv : p ∣ divisorTupleProduct (nearShifts K) u
      · rw [if_pos hdiv]
        obtain ⟨h, _hh, hph⟩ :=
          (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp)
            (fun i : nearShifts K => u i)).mp hdiv
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset (nearShifts K)))
          (f := fun i => if p ∣ u i then
              reciprocalTotientTupleWeight (nearShifts K) u else 0)
          (fun i hi => by split_ifs <;> first | exact hw | norm_num)
          (Finset.mem_univ h)
        simpa [hph] using hsingle
      · rw [if_neg hdiv]
        apply Finset.sum_nonneg
        intro i hi
        split_ifs <;> first | exact hw | norm_num
    _ = ∑ h : nearShifts K,
        ∑ u ∈ (varyingTupleBox K).filter (fun u => p ∣ u h),
          reciprocalTotientTupleWeight (nearShifts K) u := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_filter]
    _ ≤ ∑ _h : nearShifts K,
        ((1 : ℝ) / Nat.totient p) *
          ∏ i : nearShifts K, varyingCoordinateMajorant K i := by
      apply Finset.sum_le_sum
      intro h hh
      exact fixedCoordinatePrimeMass_le hp h
    _ = (K : ℝ) / Nat.totient p *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nearShifts_card]
      simp only [nsmul_eq_mul]
      ring

theorem abs_sq_sub_sq_le {x y X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x ^ 2 - y ^ 2| ≤ X ^ 2 + Y ^ 2 := by
  have hx2 : x ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg x) hX).mpr hx
  have hy2 : y ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg y) hY).mpr hy
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

/-- Away from tuples containing `p`, forbidding `p` changes `Y` only by
the insertion average. -/
theorem abs_erasePrimeY_sub_le_of_not_dvd
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {r : nearShifts K → ℕ}
    (hpr : ¬p ∣ divisorTupleProduct (nearShifts K) r) :
    |erasePrimeY R W p y r - y r| ≤
      B * (K : ℝ) / Nat.totient p := by
  have htot : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  unfold erasePrimeY
  split_ifs with hr
  · rw [show y r +
        (∑ h : nearShifts K,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ)) - y r =
        ∑ h : nearShifts K,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ) by ring]
    calc
      |∑ h : nearShifts K,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| ≤
          ∑ h : nearShifts K,
            |y (insertTuplePrime p h r) / (Nat.totient p : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h : nearShifts K, B / Nat.totient p := by
        apply Finset.sum_le_sum
        intro h hh
        rw [abs_div, abs_of_pos htot]
        exact div_le_div_of_nonneg_right (hyBound _) htot.le
      _ = B * (K : ℝ) / Nat.totient p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  · have hyr : y r = 0 := by
      by_contra hyr
      have hOld := hy r hyr
      have hpCop : Nat.Coprime
          (divisorTupleProduct (nearShifts K) r) p :=
        (hp.coprime_iff_not_dvd.mpr hpr).symm
      have hNew : IsMaynardDivisorTuple (nearShifts K) R (W * p) r := by
        refine ⟨hOld.1, ?_, hOld.2.2⟩
        rw [Nat.coprime_mul_iff_right]
        exact ⟨hOld.2.1, hpCop⟩
      exact hr hNew
    rw [hyr, sub_zero, abs_zero]
    exact div_nonneg (mul_nonneg hB (by positivity)) htot.le

/-- One prime-forbidding transform changes the sharp quadratic energy by
`O(K/φ(p))`, with an entirely explicit finite-dimensional bound. -/
theorem abs_varyingYEnergy_erasePrimeY_sub_le
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    |varyingYEnergy K (erasePrimeY R W p y) - varyingYEnergy K y| ≤
      ((B * (1 + (K : ℝ) / (p - 1 : ℕ))) ^ 2 + B ^ 2) *
          ((K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (B * (K : ℝ) / Nat.totient p) *
          (2 * B + B * (K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
  let Z : ℝ := B * (1 + (K : ℝ) / (p - 1 : ℕ))
  let ε : ℝ := B * (K : ℝ) / Nat.totient p
  let M : ℝ := ∏ h : nearShifts K, varyingCoordinateMajorant K h
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    positivity
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.prod_nonneg
    intro h hh
    unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
    positivity
  have hgood : 0 ≤ ε * (2 * B + ε) :=
    mul_nonneg hε (add_nonneg (mul_nonneg (by norm_num) hB) hε)
  have hzBound : ∀ r, |erasePrimeY R W p y r| ≤ Z := by
    intro r
    simpa [Z, Fintype.card_coe, nearShifts_card] using
      abs_erasePrimeY_le hB hyBound hp r
  have hpoint : ∀ u : nearShifts K → ℕ,
      |(erasePrimeY R W p y u) ^ 2 - y u ^ 2| ≤
        (if p ∣ divisorTupleProduct (nearShifts K) u then Z ^ 2 + B ^ 2
          else ε * (2 * B + ε)) := by
    intro u
    by_cases hpu : p ∣ divisorTupleProduct (nearShifts K) u
    · rw [if_pos hpu]
      exact abs_sq_sub_sq_le hZ hB (hzBound u) (hyBound u)
    · rw [if_neg hpu]
      have hdiff : |erasePrimeY R W p y u - y u| ≤ ε := by
        simpa [ε] using
          abs_erasePrimeY_sub_le_of_not_dvd hp hy hB hyBound hpu
      have hz : |erasePrimeY R W p y u| ≤ B + ε := by
        calc
          |erasePrimeY R W p y u| =
              |(erasePrimeY R W p y u - y u) + y u| := by ring_nf
          _ ≤ |erasePrimeY R W p y u - y u| + |y u| := abs_add_le _ _
          _ ≤ ε + B := add_le_add hdiff (hyBound u)
          _ = B + ε := by ring
      rw [show (erasePrimeY R W p y u) ^ 2 - y u ^ 2 =
          (erasePrimeY R W p y u - y u) *
            (erasePrimeY R W p y u + y u) by ring, abs_mul]
      have hsum : |erasePrimeY R W p y u + y u| ≤ 2 * B + ε := by
        calc
          |erasePrimeY R W p y u + y u| ≤
              |erasePrimeY R W p y u| + |y u| := abs_add_le _ _
          _ ≤ (B + ε) + B := add_le_add hz (hyBound u)
          _ = 2 * B + ε := by ring
      exact mul_le_mul hdiff hsum (abs_nonneg _) hε
  unfold varyingYEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ u ∈ varyingTupleBox K,
        ((erasePrimeY R W p y u) ^ 2 *
            reciprocalTotientTupleWeight (nearShifts K) u -
          y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u)| ≤
        ∑ u ∈ varyingTupleBox K,
          |(erasePrimeY R W p y u) ^ 2 - y u ^ 2| *
            reciprocalTotientTupleWeight (nearShifts K) u := by
      calc
        _ ≤ ∑ u ∈ varyingTupleBox K,
            |(erasePrimeY R W p y u) ^ 2 *
                reciprocalTotientTupleWeight (nearShifts K) u -
              y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          have hw : 0 ≤ reciprocalTotientTupleWeight (nearShifts K) u := by
            unfold reciprocalTotientTupleWeight
            positivity
          rw [← sub_mul, abs_mul, abs_of_nonneg hw]
    _ ≤ ∑ u ∈ varyingTupleBox K,
        ((if p ∣ divisorTupleProduct (nearShifts K) u then Z ^ 2 + B ^ 2
          else 0) + ε * (2 * B + ε)) *
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum
      intro u hu
      have hw : 0 ≤ reciprocalTotientTupleWeight (nearShifts K) u := by
        unfold reciprocalTotientTupleWeight
        positivity
      apply mul_le_mul_of_nonneg_right _ hw
      by_cases hpu : p ∣ divisorTupleProduct (nearShifts K) u
      · rw [if_pos hpu]
        calc
          |(erasePrimeY R W p y u) ^ 2 - y u ^ 2| ≤ Z ^ 2 + B ^ 2 := by
            simpa [hpu] using hpoint u
          _ ≤ Z ^ 2 + B ^ 2 + ε * (2 * B + ε) :=
            le_add_of_nonneg_right hgood
      · rw [if_neg hpu, zero_add]
        simpa [hpu] using hpoint u
    _ = (Z ^ 2 + B ^ 2) *
          (∑ u ∈ (varyingTupleBox K).filter
            (fun u => p ∣ divisorTupleProduct (nearShifts K) u),
              reciprocalTotientTupleWeight (nearShifts K) u) +
        (ε * (2 * B + ε)) *
          (∑ u ∈ varyingTupleBox K,
          reciprocalTotientTupleWeight (nearShifts K) u) := by
      calc
        _ = ∑ u ∈ varyingTupleBox K,
            ((if p ∣ divisorTupleProduct (nearShifts K) u then
                (Z ^ 2 + B ^ 2) *
                  reciprocalTotientTupleWeight (nearShifts K) u else 0) +
              (ε * (2 * B + ε)) *
                reciprocalTotientTupleWeight (nearShifts K) u) := by
          apply Finset.sum_congr rfl
          intro u hu
          by_cases hpu : p ∣ divisorTupleProduct (nearShifts K) u
          · simp [hpu]
            ring
          · simp [hpu]
        _ = (∑ u ∈ varyingTupleBox K,
              if p ∣ divisorTupleProduct (nearShifts K) u then
                (Z ^ 2 + B ^ 2) *
                  reciprocalTotientTupleWeight (nearShifts K) u else 0) +
            ∑ u ∈ varyingTupleBox K,
              (ε * (2 * B + ε)) *
                reciprocalTotientTupleWeight (nearShifts K) u := by
          rw [Finset.sum_add_distrib]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (Z ^ 2 + B ^ 2) * ((K : ℝ) / Nat.totient p * M) +
        (ε * (2 * B + ε)) * M := by
      gcongr
      · exact varyingPrimeTupleMass_le hp
      · exact varyingTupleReciprocalWeightSum_le K
    _ = ((B * (1 + (K : ℝ) / (p - 1 : ℕ))) ^ 2 + B ^ 2) *
          ((K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (B * (K : ℝ) / Nat.totient p) *
          (2 * B + B * (K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
      dsimp [Z, ε, M]
      ring

/-- Sharp support kills insertion at a coordinate once the inserted prime is
at least that coordinate's radius. -/
theorem insertTuplePrime_y_eq_zero_of_radius_le
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (m : nearShifts K) (hpm : shiftRadius K m ≤ p)
    (r : nearShifts K → ℕ) :
    y (insertTuplePrime p m r) = 0 := by
  by_contra hyne
  have hlt := hySharp hyne m
  have hMaynard := hy (insertTuplePrime p m r) hyne
  have hpne : p * r m ≠ 0 := by
    simpa only [insertTuplePrime_apply_same] using
      (hMaynard.coordinate_squarefree m).ne_zero
  have hpos : 0 < p * r m := Nat.pos_of_ne_zero hpne
  have hrpos : 0 < r m := by
    by_contra hr
    have hrzero : r m = 0 := Nat.eq_zero_of_not_pos hr
    simp [hrzero] at hpos
  have hple : p ≤ p * r m := Nat.le_mul_of_pos_right p hrpos
  simp only [insertTuplePrime_apply_same] at hlt
  omega

theorem differencePrimeY_eq_erasePrimeY_of_radius_le
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (m : nearShifts K) (hpm : shiftRadius K m ≤ p) :
    differencePrimeY R W p m y = erasePrimeY R W p y := by
  funext r
  have hz := insertTuplePrime_y_eq_zero_of_radius_le hy hySharp m hpm r
  unfold differencePrimeY erasePrimeY
  split_ifs
  · rw [hz]
    ring
  · rfl

/-- For a prime above the distinguished coordinate radius, the forced-prime
transform has the same perturbation estimate as the separated transform. -/
theorem abs_varyingYEnergy_largeDifference_sub_le
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    (m : nearShifts K) (hpm : shiftRadius K m ≤ p) :
    |varyingYEnergy K (differencePrimeY R W p m y) - varyingYEnergy K y| ≤
      ((B * (1 + (K : ℝ) / (p - 1 : ℕ))) ^ 2 + B ^ 2) *
          ((K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (B * (K : ℝ) / Nat.totient p) *
          (2 * B + B * (K : ℝ) / Nat.totient p) *
          (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
  rw [differencePrimeY_eq_erasePrimeY_of_radius_le hy hySharp m hpm]
  exact abs_varyingYEnergy_erasePrimeY_sub_le hp hy hB hyBound

/-- A uniform pointwise perturbation gives a uniform perturbation of the
sharp quadratic energy. -/
theorem abs_varyingYEnergy_sub_le
    {K : ℕ} {y z : (nearShifts K → ℕ) → ℝ} {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hy : ∀ u, |y u| ≤ B)
    (hzy : ∀ u, |z u - y u| ≤ ε) :
    |varyingYEnergy K z - varyingYEnergy K y| ≤
      ε * (2 * B + ε) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  have hpoint : ∀ u : nearShifts K → ℕ,
      |z u ^ 2 - y u ^ 2| ≤ ε * (2 * B + ε) := by
    intro u
    have hz : |z u| ≤ B + ε := by
      calc
        |z u| = |(z u - y u) + y u| := by ring_nf
        _ ≤ |z u - y u| + |y u| := abs_add_le _ _
        _ ≤ ε + B := add_le_add (hzy u) (hy u)
        _ = B + ε := by ring
    rw [show z u ^ 2 - y u ^ 2 = (z u - y u) * (z u + y u) by ring,
      abs_mul]
    have hsum : |z u + y u| ≤ 2 * B + ε := by
      calc
        |z u + y u| ≤ |z u| + |y u| := abs_add_le _ _
        _ ≤ (B + ε) + B := add_le_add hz (hy u)
        _ = 2 * B + ε := by ring
    exact (mul_le_mul (hzy u) hsum (abs_nonneg _) hε).trans_eq
      (by ring)
  unfold varyingYEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ u ∈ varyingTupleBox K,
        (z u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u -
          y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u)| ≤
        ∑ u ∈ varyingTupleBox K,
          |z u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u -
            y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ varyingTupleBox K,
        (ε * (2 * B + ε)) *
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum
      intro u hu
      have hw : 0 ≤ reciprocalTotientTupleWeight (nearShifts K) u := by
        unfold reciprocalTotientTupleWeight
        positivity
      calc
        |z u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u -
            y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u| =
            |z u ^ 2 - y u ^ 2| *
              reciprocalTotientTupleWeight (nearShifts K) u := by
          rw [← sub_mul, abs_mul, abs_of_nonneg hw]
        _ ≤ (ε * (2 * B + ε)) *
              reciprocalTotientTupleWeight (nearShifts K) u :=
          mul_le_mul_of_nonneg_right (hpoint u) hw
    _ = (ε * (2 * B + ε)) *
        (∑ u ∈ varyingTupleBox K,
          reciprocalTotientTupleWeight (nearShifts K) u) := by
      rw [Finset.mul_sum]
    _ ≤ (ε * (2 * B + ε)) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      apply mul_le_mul_of_nonneg_left (varyingTupleReciprocalWeightSum_le K)
      positivity
    _ = ε * (2 * B + ε) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by ring

end Erdos248
