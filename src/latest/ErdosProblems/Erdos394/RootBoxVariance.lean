import ErdosProblems.Erdos394.RootBoxSecondMoment

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Variance and no-hit bounds for actual CRT root boxes
-/

open Nat Finset

namespace Erdos394

/-- First-moment double counting for a finite incidence relation. -/
theorem sum_hitCount_eq_singleCount [DecidableEq α] [DecidableEq β]
    (H : Finset α) (T : Finset β) (hit : α → β → Prop)
    [DecidableRel hit] :
    (∑ h ∈ H, (T.filter (hit h)).card) =
      ∑ j ∈ T, (H.filter (fun h ↦ hit h j)).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

/-- The global one-time hit set lies in the full multiplier universe. -/
theorem rootBoxGlobalHitSet_subset_universe
    (P : Finset ℕ) (K j : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    rootBoxGlobalHitSet P K j hprime ⊆
      rootBoxMultiplierUniverse P hprime := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  intro h hh
  unfold rootBoxMultiplierUniverse
  apply Fintype.mem_piFinset.mpr
  intro p
  exact Finset.mem_univ _

/-- Filtering the universe by one global hit recovers the global hit set. -/
theorem filter_rootBoxMultiplierUniverse_hit_eq
    (P : Finset ℕ) (K j : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (rootBoxMultiplierUniverse P hprime).filter (fun h ↦
      h ∈ rootBoxGlobalHitSet P K j hprime) =
      rootBoxGlobalHitSet P K j hprime := by
  classical
  ext h
  simp only [Finset.mem_filter]
  constructor
  · exact fun hh ↦ hh.2
  · intro hh
    exact ⟨rootBoxGlobalHitSet_subset_universe P K j hprime hh, hh⟩

/-- The actual global one-time hit set has the arithmetic local weight. -/
theorem card_rootBoxGlobalHitSet_eq_weight
    (P : Finset ℕ) (K j : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hK : 1 ≤ K) (hKp : ∀ p ∈ P, K < p) :
    (rootBoxGlobalHitSet P K j hprime).card =
      rootBoxLocalWeight P K j := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  unfold rootBoxGlobalHitSet
  rw [Fintype.card_piFinset]
  calc
    (∏ p : ↥P, (localBlockHitSet p.val K j).card) =
        ∏ p : ↥P,
          (if p.val ∣ j then p.val - 1 else K - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact card_localBlockHitSet (hprime p.val p.property) hK
        (hKp p.val p.property)
    _ = rootBoxLocalWeight P K j := by
      unfold rootBoxLocalWeight
      rw [← Finset.attach_eq_univ]
      simpa using Finset.prod_attach P
        (fun p ↦ if p ∣ j then p - 1 else K - 1)

/-- Summing the actual hit number over multiplier tuples gives exactly the
arithmetic first moment. -/
theorem sum_rootBoxTupleHitNumber_eq_firstMoment
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hK : 1 ≤ K) (hKp : ∀ p ∈ P, K < p) :
    (∑ h ∈ rootBoxMultiplierUniverse P hprime,
      rootBoxTupleHitNumber P K Y hprime h) =
      rootBoxFirstMoment P K Y := by
  unfold rootBoxTupleHitNumber rootBoxFirstMoment
  calc
    (∑ h ∈ rootBoxMultiplierUniverse P hprime,
      ((Icc 1 Y).filter (fun j ↦
        h ∈ rootBoxGlobalHitSet P K j hprime)).card) =
      ∑ j ∈ Icc 1 Y,
        ((rootBoxMultiplierUniverse P hprime).filter (fun h ↦
          h ∈ rootBoxGlobalHitSet P K j hprime)).card :=
      sum_hitCount_eq_singleCount
        (rootBoxMultiplierUniverse P hprime) (Icc 1 Y)
        (fun h j ↦ h ∈ rootBoxGlobalHitSet P K j hprime)
    _ = ∑ j ∈ Icc 1 Y,
        (rootBoxGlobalHitSet P K j hprime).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [filter_rootBoxMultiplierUniverse_hit_eq]
    _ = ∑ j ∈ Icc 1 Y, rootBoxLocalWeight P K j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact card_rootBoxGlobalHitSet_eq_weight P K j hprime hK hKp

/-- Main continuous first-moment parameter `K^|P| Y / ∏P`. -/
noncomputable def rootBoxMainParameter
    (P : Finset ℕ) (K Y : ℕ) : ℝ :=
  (K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ)

/-- Corrected-area Euler factor from the origin-ignored pair count. -/
noncomputable def rootBoxAreaCorrection
    (P : Finset ℕ) (K : ℕ) : ℝ :=
  ∏ p ∈ P,
    (1 + ((K * K - 1 : ℕ) : ℝ) /
      (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))

/-- Rational-boundary Euler correction. -/
noncomputable def rootBoxRationalCorrection
    (P : Finset ℕ) (K : ℕ) : ℝ :=
  ∏ p ∈ P,
    (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
      ((K : ℝ) * ((p : ℝ) - 1)))

/-- Non-rational-boundary Euler correction at root scale `Z`. -/
noncomputable def rootBoxNonrationalCorrection
    (P : Finset ℕ) (K Z : ℕ) : ℝ :=
  ∏ _p ∈ P,
    (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))

/-- Additive-constant Euler correction at root scale `Z`. -/
noncomputable def rootBoxConstantCorrection
    (P : Finset ℕ) (K Z : ℕ) : ℝ :=
  ∏ _p ∈ P,
    (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
      ((Z * Z : ℕ) : ℝ))

/-- F-065 rewritten in terms of the four named correction factors. -/
theorem normalized_rootBoxTupleSecondMoment_le_corrections
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p) :
    (rootBoxTupleSecondMoment P K Y hprime : ℝ) /
        (primeUnitCount P : ℝ) ≤
      (rootBoxMainParameter P K Y) ^ 2 *
        rootBoxAreaCorrection P K +
      40 * (K * K - 1 : ℕ) * rootBoxMainParameter P K Y *
        rootBoxRationalCorrection P K +
      80 * (K : ℝ) * ((Y : ℝ) / (primeProduct P : ℝ)) *
        rootBoxNonrationalCorrection P K Z +
      44 * rootBoxConstantCorrection P K Z := by
  have h := normalized_rootBoxTupleSecondMoment_le P K Y Z hK hZ
    hprime hKp hK2p hlarge hZp hZ2p
  unfold rootBoxMainParameter rootBoxAreaCorrection
    rootBoxRationalCorrection rootBoxNonrationalCorrection
    rootBoxConstantCorrection
  convert h using 1 <;> push_cast <;> ring

/-- If the area correction is within `1/R` and all three boundary corrections
are at most two, the normalized second moment has a simple variance-ready
bound. -/
theorem normalized_rootBoxTupleSecondMoment_le_simple
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (harea : rootBoxAreaCorrection P K ≤
      1 + 1 / ((K ^ P.card : ℕ) : ℝ))
    (hrat : rootBoxRationalCorrection P K ≤ 2)
    (hnon : rootBoxNonrationalCorrection P K Z ≤ 2)
    (hconst : rootBoxConstantCorrection P K Z ≤ 2) :
    (rootBoxTupleSecondMoment P K Y hprime : ℝ) /
        (primeUnitCount P : ℝ) ≤
      (rootBoxMainParameter P K Y) ^ 2 *
        (1 + 1 / ((K ^ P.card : ℕ) : ℝ)) +
      ((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)) *
        rootBoxMainParameter P K Y + 88 := by
  have hraw := normalized_rootBoxTupleSecondMoment_le_corrections
    P K Y Z hK hZ hprime hKp hK2p hlarge hZp hZ2p
  have hq : (0 : ℝ) < primeProduct P := by
    exact_mod_cast (show 0 < primeProduct P by
      unfold primeProduct
      exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos)
  have hRnat : 1 ≤ K ^ P.card := by
    have : 0 < K ^ P.card := pow_pos (by omega) _
    omega
  have hR : (1 : ℝ) ≤ ((K ^ P.card : ℕ) : ℝ) := by
    exact_mod_cast hRnat
  have hyq : (Y : ℝ) / (primeProduct P : ℝ) ≤
      rootBoxMainParameter P K Y := by
    unfold rootBoxMainParameter
    have hyq0 : (0 : ℝ) ≤ (Y : ℝ) / (primeProduct P : ℝ) := by positivity
    rw [show (K : ℝ) ^ P.card * (Y : ℝ) / (primeProduct P : ℝ) =
        ((K ^ P.card : ℕ) : ℝ) *
          ((Y : ℝ) / (primeProduct P : ℝ)) by
      push_cast
      ring]
    nlinarith
  have hmu0 : 0 ≤ rootBoxMainParameter P K Y := by
    unfold rootBoxMainParameter
    positivity
  have hnon0 : 0 ≤ rootBoxNonrationalCorrection P K Z := by
    unfold rootBoxNonrationalCorrection
    apply Finset.prod_nonneg
    intro p hp
    have hZR : (0 : ℝ) < Z := by exact_mod_cast (Nat.zero_lt_of_lt hZ)
    positivity
  calc
    (rootBoxTupleSecondMoment P K Y hprime : ℝ) /
        (primeUnitCount P : ℝ) ≤
      (rootBoxMainParameter P K Y) ^ 2 *
        rootBoxAreaCorrection P K +
      40 * (K * K - 1 : ℕ) * rootBoxMainParameter P K Y *
        rootBoxRationalCorrection P K +
      80 * (K : ℝ) * ((Y : ℝ) / (primeProduct P : ℝ)) *
        rootBoxNonrationalCorrection P K Z +
      44 * rootBoxConstantCorrection P K Z := hraw
    _ ≤ (rootBoxMainParameter P K Y) ^ 2 *
        (1 + 1 / ((K ^ P.card : ℕ) : ℝ)) +
      40 * (K * K - 1 : ℕ) * rootBoxMainParameter P K Y * 2 +
      80 * (K : ℝ) * rootBoxMainParameter P K Y * 2 +
      44 * 2 := by
      gcongr
    _ = (rootBoxMainParameter P K Y) ^ 2 *
        (1 + 1 / ((K ^ P.card : ℕ) : ℝ)) +
      ((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)) *
        rootBoxMainParameter P K Y + 88 := by
      push_cast
      ring

/-- Multiplier tuples with no hit through time `Y`. -/
noncomputable def rootBoxTupleNoHitSet
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  exact (rootBoxMultiplierUniverse P hprime).filter (fun h ↦
    rootBoxTupleHitNumber P K Y hprime h = 0)

/-- A generic finite Chebyshev estimate centered at an external main term.
The first moment may lie one unit below `mu`. -/
theorem finite_zero_fraction_le_of_moments
    [DecidableEq α] (H : Finset α) (N : α → ℕ)
    (mu delta A B : ℝ)
    (hH : 0 < H.card) (hmu : 0 < mu)
    (hfirst : mu - 1 ≤
      (∑ h ∈ H, (N h : ℝ)) / (H.card : ℝ))
    (hsecond :
      (∑ h ∈ H, ((N h : ℝ) ^ 2)) / (H.card : ℝ) ≤
        mu ^ 2 * (1 + delta) + A * mu + B) :
    (((H.filter (fun h ↦ N h = 0)).card : ℝ) / (H.card : ℝ)) ≤
      delta + (A + 2) / mu + B / mu ^ 2 := by
  classical
  let Z := H.filter (fun h ↦ N h = 0)
  have hZsub : Z ⊆ H := Finset.filter_subset _ _
  have hzeroSquare : (Z.card : ℝ) * mu ^ 2 ≤
      ∑ h ∈ H, ((N h : ℝ) - mu) ^ 2 := by
    calc
      (Z.card : ℝ) * mu ^ 2 =
          ∑ _h ∈ Z, mu ^ 2 := by simp
      _ = ∑ h ∈ Z, ((N h : ℝ) - mu) ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        have hNh : N h = 0 := (Finset.mem_filter.mp hh).2
        rw [hNh]
        norm_num
      _ ≤ ∑ h ∈ H, ((N h : ℝ) - mu) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hZsub
        intro h hh hnot
        positivity
  have hcardR : (0 : ℝ) < H.card := by exact_mod_cast hH
  have hcenterEq :
      (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) / (H.card : ℝ) =
        (∑ h ∈ H, ((N h : ℝ) ^ 2)) / (H.card : ℝ) -
          2 * mu * ((∑ h ∈ H, (N h : ℝ)) / (H.card : ℝ)) +
          mu ^ 2 := by
    rw [show (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) =
        (∑ h ∈ H, ((N h : ℝ) ^ 2)) -
          2 * mu * (∑ h ∈ H, (N h : ℝ)) +
          H.card * mu ^ 2 by
      calc
        (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) =
            ∑ h ∈ H,
              (((N h : ℝ) ^ 2 - 2 * mu * (N h : ℝ)) + mu ^ 2) := by
          apply Finset.sum_congr rfl
          intro h hh
          ring
        _ = (∑ h ∈ H, ((N h : ℝ) ^ 2)) -
            2 * mu * (∑ h ∈ H, (N h : ℝ)) +
            H.card * mu ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul]]
    field_simp
  have hcenter :
      (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) / (H.card : ℝ) ≤
        mu ^ 2 * delta + (A + 2) * mu + B := by
    rw [hcenterEq]
    have hmupos : 0 ≤ mu := hmu.le
    nlinarith
  have hzeroNorm :
      ((Z.card : ℝ) / (H.card : ℝ)) * mu ^ 2 ≤
        (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) / (H.card : ℝ) := by
    calc
      ((Z.card : ℝ) / (H.card : ℝ)) * mu ^ 2 =
          ((Z.card : ℝ) * mu ^ 2) / (H.card : ℝ) := by ring
      _ ≤ (∑ h ∈ H, ((N h : ℝ) - mu) ^ 2) / (H.card : ℝ) :=
        (div_le_div_iff_of_pos_right hcardR).mpr hzeroSquare
  have hmain : ((Z.card : ℝ) / (H.card : ℝ)) * mu ^ 2 ≤
      mu ^ 2 * delta + (A + 2) * mu + B := hzeroNorm.trans hcenter
  have hmu0 : mu ≠ 0 := ne_of_gt hmu
  have hid :
      (delta + (A + 2) / mu + B / mu ^ 2) * mu ^ 2 =
        mu ^ 2 * delta + (A + 2) * mu + B := by
    field_simp [hmu0]
  dsimp [Z] at hmain ⊢
  nlinarith [sq_pos_of_pos hmu]

/-- Quantitative no-hit tail obtained from the first and second moments, under
explicit bounds on the four Euler corrections. -/
theorem normalized_rootBoxTupleNoHitSet_le
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hY : 0 < Y)
    (hZ : 1 ≤ Z) (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (harea : rootBoxAreaCorrection P K ≤
      1 + 1 / ((K ^ P.card : ℕ) : ℝ))
    (hrat : rootBoxRationalCorrection P K ≤ 2)
    (hnon : rootBoxNonrationalCorrection P K Z ≤ 2)
    (hconst : rootBoxConstantCorrection P K Z ≤ 2) :
    ((rootBoxTupleNoHitSet P K Y hprime).card : ℝ) /
        (primeUnitCount P : ℝ) ≤
      1 / ((K ^ P.card : ℕ) : ℝ) +
      (((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)) + 2) /
        rootBoxMainParameter P K Y +
      88 / (rootBoxMainParameter P K Y) ^ 2 := by
  let H := rootBoxMultiplierUniverse P hprime
  let N : RootBoxMultiplierTuple P → ℕ :=
    rootBoxTupleHitNumber P K Y hprime
  let mu := rootBoxMainParameter P K Y
  let delta : ℝ := 1 / ((K ^ P.card : ℕ) : ℝ)
  let A : ℝ := (80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)
  have hphiNat : 0 < primeUnitCount P := by
    unfold primeUnitCount
    exact Finset.prod_pos fun p hp ↦ by
      have hp2 := (hprime p hp).two_le
      omega
  have hHcard : H.card = primeUnitCount P :=
    card_rootBoxMultiplierUniverse P hprime
  have hH : 0 < H.card := by rw [hHcard]; exact hphiNat
  have hq : (0 : ℝ) < primeProduct P := by
    exact_mod_cast (show 0 < primeProduct P by
      unfold primeProduct
      exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos)
  have hmu : 0 < mu := by
    dsimp [mu, rootBoxMainParameter]
    positivity
  have hsumFirst : (∑ h ∈ H, N h) = rootBoxFirstMoment P K Y := by
    exact sum_rootBoxTupleHitNumber_eq_firstMoment P K Y hprime
      (by omega) hKp
  have hfirst : mu - 1 ≤
      (∑ h ∈ H, (N h : ℝ)) / (H.card : ℝ) := by
    have hfirstRaw := (normalized_rootBoxFirstMoment_bounds P K Y
      (by omega) hprime (fun p hp ↦ (hKp p hp).le)).1
    have hsumFirstR : (∑ h ∈ H, (N h : ℝ)) =
        (rootBoxFirstMoment P K Y : ℝ) := by
      exact_mod_cast hsumFirst
    rw [hHcard, hsumFirstR]
    dsimp [mu, rootBoxMainParameter]
    simpa using hfirstRaw
  have hsumSecond : (∑ h ∈ H, ((N h : ℝ) ^ 2)) =
      (rootBoxTupleSecondMoment P K Y hprime : ℝ) := by
    unfold H N rootBoxTupleSecondMoment
    push_cast
    rfl
  have hsecond :
      (∑ h ∈ H, ((N h : ℝ) ^ 2)) / (H.card : ℝ) ≤
        mu ^ 2 * (1 + delta) + A * mu + 88 := by
    rw [hsumSecond, hHcard]
    exact normalized_rootBoxTupleSecondMoment_le_simple
      P K Y Z hK hZ hprime hKp hK2p hlarge hZp hZ2p
      harea hrat hnon hconst
  have htail := finite_zero_fraction_le_of_moments H N mu delta A 88
    hH hmu hfirst hsecond
  dsimp [rootBoxTupleNoHitSet, H, N, mu, delta, A] at htail ⊢
  rw [hHcard] at htail
  exact htail

end Erdos394
