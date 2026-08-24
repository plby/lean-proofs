import ErdosProblems.Erdos360.Core

open scoped BigOperators Pointwise

namespace Erdos360

/-!
This file isolates the finite sieve connector needed in the
unsaturated branch of CFP Lemma 5.9.  A long progression cover by itself
does not record the arithmetic fact that every progression step is coprime
to the missing-prime product, so the definition below adds exactly that
piece of data.
-/

lemma missingPrimesUpTo_mul_subset_left (n b y : ℕ) :
    missingPrimesUpTo (n * b) y ⊆ missingPrimesUpTo n y := by
  intro p hp
  obtain ⟨hp2, hpy, hpprime, hpnot⟩ := mem_missingPrimesUpTo.mp hp
  apply mem_missingPrimesUpTo.mpr
  refine ⟨hp2, hpy, hpprime, ?_⟩
  intro hpn
  exact hpnot (dvd_mul_of_dvd_left hpn b)

lemma missingPrimeProduct_mul_dvd_left (n b y : ℕ) :
    missingPrimeProduct (n * b) y ∣ missingPrimeProduct n y := by
  unfold missingPrimeProduct
  exact Finset.prod_dvd_prod_of_subset _ _ id
    (missingPrimesUpTo_mul_subset_left n b y)

lemma progressionCoprimeIndices_mono_missing_mul
    (n a b L y : ℕ) :
    progressionCoprimeIndices a b L (missingPrimeProduct n y) ⊆
      progressionCoprimeIndices a b L (missingPrimeProduct (n * b) y) := by
  intro i hi
  rw [progressionCoprimeIndices, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, Nat.Coprime.of_dvd_left
    (missingPrimeProduct_mul_dvd_left n b y) hi.2⟩

lemma coprimePart_eq_self_of_all_coprime
    {X : Finset ℕ} {M : ℕ}
    (hcop : ∀ x ∈ X, Nat.Coprime M x) :
    coprimePart X M = X := by
  ext x
  simp only [coprimePart, Finset.mem_filter]
  exact and_iff_left_of_imp (hcop x)

/-- Dividing by a common factor cannot introduce a prime divisor which was
absent from the original integer.  This is the arithmetic bridge from the
common-divisor extraction output to the progression sieve. -/
lemma coprime_of_divisorExtraction_scale
    {Y Z : Finset ℕ} {d M : ℕ}
    (hscale : ∀ z ∈ Z, d * z ∈ Y)
    (hYcop : ∀ y ∈ Y, Nat.Coprime M y) :
    ∀ z ∈ Z, Nat.Coprime M z := by
  intro z hz
  exact Nat.Coprime.of_dvd_right (dvd_mul_left z d)
    (hYcop (d * z) (hscale z hz))

/-- Common-divisor extraction with the sieve invariant retained explicitly.
In applications `M` is `missingPrimeProduct n y`; hence the terminal diverse
set can be fed directly to the sharp long-progression-cover sieve below. -/
theorem exists_divisorExtraction_coprime
    (B L K M : ℕ) (hB : 0 < B) (Y : Finset ℕ)
    (hYcop : ∀ y ∈ Y, Nat.Coprime M y) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      (∀ z ∈ Z, Nat.Coprime M z) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card := by
  obtain ⟨d, Z, hd, hdB, hscale, hloss, hdiverse⟩ :=
    exists_divisorExtraction B L K hB Y
  exact ⟨d, Z, hd, hdB, hscale,
    coprime_of_divisorExtraction_scale hscale hYcop, hloss, hdiverse⟩

lemma number_progressions_le_total_length
    {X : Finset ℕ} (hX : X.Nonempty)
    {m : ℕ} (P : Fin m → NatProgressionSpec)
    (hlong : ∀ i, X.card ≤ (P i).length ^ 3) :
    m ≤ ∑ i, (P i).length := by
  have hXpos : 0 < X.card := Finset.card_pos.mpr hX
  calc
    m = ∑ _i : Fin m, 1 := by simp
    _ ≤ ∑ i, (P i).length := by
      apply Finset.sum_le_sum
      intro i _hi
      have hpow : 0 < (P i).length ^ 3 := hXpos.trans_le (hlong i)
      exact Nat.one_le_iff_ne_zero.mpr (fun hzero ↦ by simp [hzero] at hpow)

/-- A long progression cover retaining the quantitative upper bound on the
common differences.  CFP's lifted progressions all have step at most the
ambient modulus; recording that fact avoids the unusable requirement of a
single totient-ratio bound for every natural number. -/
def HasStepBoundedLongProgressionCover
    (X : Finset ℕ) (mass stepBound : ℕ) : Prop :=
  ∃ m : ℕ, ∃ P : Fin m → NatProgressionSpec,
    (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) ∧
    (∑ i, (P i).length) ≤ mass ∧
    (∀ i, X.card ≤ (P i).length ^ 3) ∧
    ∀ i, (P i).step ≤ stepBound

lemma HasStepBoundedLongProgressionCover.toHasLongProgressionCover
    {X : Finset ℕ} {mass stepBound : ℕ}
    (h : HasStepBoundedLongProgressionCover X mass stepBound) :
    HasLongProgressionCover X mass := by
  obtain ⟨m, P, hcover, hmass, hlong, _hstep⟩ := h
  exact ⟨m, P, hcover, hmass, hlong⟩

lemma HasStepBoundedLongProgressionCover.mono_set
    {X Y : Finset ℕ} {mass stepBound : ℕ} (hXY : X ⊆ Y)
    (h : HasStepBoundedLongProgressionCover Y mass stepBound) :
    HasStepBoundedLongProgressionCover X mass stepBound := by
  obtain ⟨m, P, hcover, hmass, hlong, hstep⟩ := h
  exact ⟨m, P, (fun x hx ↦ hcover x (hXY hx)), hmass,
    (fun i ↦ (Finset.card_le_card hXY).trans (hlong i)), hstep⟩

/-- First index at which a positive-step natural progression reaches a
given lower endpoint. -/
noncomputable def NatProgressionSpec.firstIndexAtLeast
    (P : NatProgressionSpec) (c : ℕ) : ℕ :=
  Nat.find (show ∃ i : ℕ, c ≤ P.start + P.step * i by
    refine ⟨c, ?_⟩
    have hstep : 1 ≤ P.step := P.step_pos
    exact (Nat.le_mul_of_pos_left c P.step_pos).trans
      (Nat.le_add_left (P.step * c) P.start))

lemma NatProgressionSpec.le_firstIndexAtLeast
    (P : NatProgressionSpec) (c : ℕ) :
    c ≤ P.start + P.step * P.firstIndexAtLeast c := by
  exact Nat.find_spec (show ∃ i : ℕ, c ≤ P.start + P.step * i by
    refine ⟨c, ?_⟩
    exact (Nat.le_mul_of_pos_left c P.step_pos).trans
      (Nat.le_add_left (P.step * c) P.start))

lemma NatProgressionSpec.firstIndexAtLeast_le
    (P : NatProgressionSpec) {c i : ℕ}
    (hi : c ≤ P.start + P.step * i) :
    P.firstIndexAtLeast c ≤ i := by
  exact Nat.find_min' (show ∃ j : ℕ, c ≤ P.start + P.step * j by
    exact ⟨i, hi⟩) hi

/-- Shift a progression down by `c`, discarding its initial terms below
`c` and extending at the upper end so that its parameter length is
unchanged. -/
noncomputable def NatProgressionSpec.shiftDown
    (P : NatProgressionSpec) (c : ℕ) : NatProgressionSpec where
  start := P.start + P.step * P.firstIndexAtLeast c - c
  step := P.step
  length := P.length
  step_pos := P.step_pos

@[simp] lemma NatProgressionSpec.shiftDown_step
    (P : NatProgressionSpec) (c : ℕ) : (P.shiftDown c).step = P.step := rfl

@[simp] lemma NatProgressionSpec.shiftDown_length
    (P : NatProgressionSpec) (c : ℕ) : (P.shiftDown c).length = P.length := rfl

lemma NatProgressionSpec.sub_mem_shiftDown
    (P : NatProgressionSpec) {c x : ℕ}
    (hx : x ∈ P.carrier) (hcx : c ≤ x) :
    x - c ∈ (P.shiftDown c).carrier := by
  obtain ⟨i, hi, rfl⟩ := mem_natProgression_iff.mp hx
  let j := P.firstIndexAtLeast c
  have hj : j ≤ i := P.firstIndexAtLeast_le hcx
  have hjc : c ≤ P.start + P.step * j :=
    P.le_firstIndexAtLeast c
  have hdecomp :
      P.start + P.step * i =
        (P.start + P.step * j) + P.step * (i - j) := by
    have hij : i = (i - j) + j := by omega
    conv_lhs => rw [hij]
    ring
  apply mem_natProgression_iff.mpr
  refine ⟨i - j, ?_, ?_⟩
  · change i - j < P.length
    omega
  change P.start + P.step * i - c =
    (P.start + P.step * P.firstIndexAtLeast c - c) +
      P.step * (i - P.firstIndexAtLeast c)
  change P.start + P.step * i - c =
    (P.start + P.step * j - c) + P.step * (i - j)
  omega

/-- Shift every member of a long progression cover down by the same amount.
The steps, lengths, number of pieces, and total mass are unchanged. -/
lemma HasLongProgressionCover.shiftDown
    {X : Finset ℕ} {mass c : ℕ}
    (h : HasLongProgressionCover X mass)
    (hc : ∀ x ∈ X, c ≤ x) :
    HasLongProgressionCover (X.image fun x ↦ x - c) mass := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  let Q : Fin m → NatProgressionSpec := fun i ↦ (P i).shiftDown c
  refine ⟨m, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hxi⟩ := hcover x hx
    exact ⟨i, (P i).sub_mem_shiftDown hxi (hc x hx)⟩
  · simpa [Q] using hmass
  · intro i
    have hinj : Set.InjOn (fun x : ℕ ↦ x - c) X := by
      intro x hx y hy hxy
      exact (tsub_left_inj (hc x hx) (hc y hy)).mp hxy
    rw [Finset.card_image_iff.mpr hinj]
    simpa [Q] using hlong i

/-- The interval-recentering operation preserves an explicit step bound. -/
lemma HasStepBoundedLongProgressionCover.shiftDown
    {X : Finset ℕ} {mass stepBound c : ℕ}
    (h : HasStepBoundedLongProgressionCover X mass stepBound)
    (hc : ∀ x ∈ X, c ≤ x) :
    HasStepBoundedLongProgressionCover (X.image fun x ↦ x - c)
      mass stepBound := by
  obtain ⟨m, P, hcover, hmass, hlong, hstep⟩ := h
  let Q : Fin m → NatProgressionSpec := fun i ↦ (P i).shiftDown c
  refine ⟨m, Q, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hxi⟩ := hcover x hx
    exact ⟨i, (P i).sub_mem_shiftDown hxi (hc x hx)⟩
  · simpa [Q] using hmass
  · intro i
    have hinj : Set.InjOn (fun x : ℕ ↦ x - c) X := by
      intro x hx y hy hxy
      exact (tsub_left_inj (hc x hx) (hc y hy)).mp hxy
    rw [Finset.card_image_iff.mpr hinj]
    simpa [Q] using hlong i
  · intro i
    simpa [Q] using hstep i

/-- Recenter residues so that `base` becomes the left endpoint of the
chosen ordinary interval of representatives. -/
def recenteredZmodValues {b : ℕ} [NeZero b]
    (base : ℕ) (R : Finset (ZMod b)) : Finset (ZMod b) :=
  R.image fun r ↦ r - (base : ZMod b)

/-- Representatives of `R` in the half-open interval
`[base, base + b)`. -/
def intervalZmodValues {b : ℕ} [NeZero b]
    (base : ℕ) (R : Finset (ZMod b)) : Finset ℕ :=
  R.image fun r ↦ base + (r - (base : ZMod b)).val

@[simp] lemma card_intervalZmodValues {b : ℕ} [NeZero b]
    (base : ℕ) (R : Finset (ZMod b)) :
    (intervalZmodValues base R).card = R.card := by
  rw [intervalZmodValues, Finset.card_image_iff.mpr]
  intro x _hx y _hy hxy
  apply_fun fun n ↦ n - base at hxy
  have hval : (x - (base : ZMod b)).val =
      (y - (base : ZMod b)).val := by simpa using hxy
  have hsub : x - (base : ZMod b) = y - (base : ZMod b) :=
    ZMod.val_injective b hval
  calc
    x = (x - (base : ZMod b)) + (base : ZMod b) := by abel
    _ = (y - (base : ZMod b)) + (base : ZMod b) := by rw [hsub]
    _ = y := by abel

lemma recenteredZmodValues_mono
    {b : ℕ} [NeZero b] {base : ℕ}
    {R T : Finset (ZMod b)} (hRT : R ⊆ T) :
    recenteredZmodValues base R ⊆ recenteredZmodValues base T := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨r, hRT hr, rfl⟩

lemma shifted_recentered_shiftDown_eq_interval
    {b : ℕ} [NeZero b] {base : ℕ} (hbase : base ≤ b)
    (R : Finset (ZMod b)) :
    (shiftedZmodValues (recenteredZmodValues base R)).image
        (fun x ↦ x - (b - base)) =
      intervalZmodValues base R := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s, hs, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
    obtain ⟨r, hr, hrs⟩ := Finset.mem_image.mp hs
    subst s
    apply Finset.mem_image.mpr
    refine ⟨r, hr, ?_⟩
    omega
  · intro hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨b + (r - (base : ZMod b)).val, ?_, ?_⟩
    · apply mem_shiftedZmodValues_iff.mpr
      refine ⟨r - (base : ZMod b), ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    · omega

/-- CFP's interval-flexibility clause for a long progression cover.  It is
enough to prove a cover for shifted standard representatives of the
recentered residue set; shifting the progressions down gives a cover in any
interval `[base,base+b)` whose left endpoint is at most the modulus. -/
lemma longProgressionCover_interval_of_shifted_recentered
    {b : ℕ} [NeZero b] {base mass : ℕ} (hbase : base ≤ b)
    (R : Finset (ZMod b))
    (h : HasLongProgressionCover
      (shiftedZmodValues (recenteredZmodValues base R)) mass) :
    HasLongProgressionCover (intervalZmodValues base R) mass := by
  have hlower : ∀ x ∈ shiftedZmodValues (recenteredZmodValues base R),
      b - base ≤ x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
    omega
  have hdown := h.shiftDown hlower
  rwa [shifted_recentered_shiftDown_eq_interval hbase R] at hdown

lemma stepBoundedLongProgressionCover_interval_of_shifted_recentered
    {b : ℕ} [NeZero b] {base mass stepBound : ℕ}
    (hbase : base ≤ b) (R : Finset (ZMod b))
    (h : HasStepBoundedLongProgressionCover
      (shiftedZmodValues (recenteredZmodValues base R)) mass stepBound) :
    HasStepBoundedLongProgressionCover
      (intervalZmodValues base R) mass stepBound := by
  have hlower : ∀ x ∈ shiftedZmodValues (recenteredZmodValues base R),
      b - base ≤ x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
    omega
  have hdown := h.shiftDown hlower
  rwa [shifted_recentered_shiftDown_eq_interval hbase R] at hdown

lemma subset_intervalZmodValues_occupiedResidues
    {b : ℕ} [NeZero b] {base : ℕ} {X : Finset ℕ}
    (hXlo : ∀ x ∈ X, base ≤ x)
    (hXhi : ∀ x ∈ X, x < base + b) :
    X ⊆ intervalZmodValues base (occupiedResidues X b) := by
  intro x hx
  apply Finset.mem_image.mpr
  refine ⟨(x : ZMod b), Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  have hbaseX : base ≤ x := hXlo x hx
  have hdiff : x - base < b := by
    have := hXhi x hx
    omega
  have hz : (x : ZMod b) - (base : ZMod b) = ((x - base : ℕ) : ZMod b) := by
    rw [Nat.cast_sub hbaseX]
  rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hdiff]
  omega

/-- Turn a cyclic cover into a cover of the original integer set when the
set lies in an interval shorter than the modulus.  This supplies the
arbitrary-interval version of CFP Lemma 5.10 needed before the AP sieve. -/
lemma longProgressionCover_of_occupiedResidues
    {b : ℕ} [NeZero b] {base mass : ℕ} {X : Finset ℕ}
    (hbase : base ≤ b)
    (hXlo : ∀ x ∈ X, base ≤ x)
    (hXhi : ∀ x ∈ X, x < base + b)
    (h : HasLongProgressionCover
      (shiftedZmodValues
        (recenteredZmodValues base (occupiedResidues X b))) mass) :
    HasLongProgressionCover X mass := by
  exact (longProgressionCover_interval_of_shifted_recentered
    hbase (occupiedResidues X b) h).mono_set
      (subset_intervalZmodValues_occupiedResidues hXlo hXhi)

/-- If every admissible integer translation is an almost period and the
inverse theorem supplies a long cover of the recentered almost-period set,
then the original integer translations have the same long cover mass. -/
lemma longProgressionCover_of_almostPeriods
    {b : ℕ} [NeZero b] {base mass growth : ℕ}
    {X : Finset ℕ} (U : Finset (ZMod b))
    (hbase : base ≤ b)
    (hXlo : ∀ x ∈ X, base ≤ x)
    (hXhi : ∀ x ∈ X, x < base + b)
    (hperiod : ∀ x ∈ X, (x : ZMod b) ∈ almostPeriods U growth)
    (hcover : HasLongProgressionCover
      (shiftedZmodValues
        (recenteredZmodValues base (almostPeriods U growth))) mass) :
    HasLongProgressionCover X mass := by
  have hres : occupiedResidues X b ⊆ almostPeriods U growth := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact hperiod x hx
  have hrec : recenteredZmodValues base (occupiedResidues X b) ⊆
      recenteredZmodValues base (almostPeriods U growth) :=
    recenteredZmodValues_mono hres
  have hshift :
      shiftedZmodValues (recenteredZmodValues base (occupiedResidues X b)) ⊆
        shiftedZmodValues
          (recenteredZmodValues base (almostPeriods U growth)) :=
    shiftedZmodValues_mono hrec
  exact longProgressionCover_of_occupiedResidues hbase hXlo hXhi
    (hcover.mono_set hshift)

/-- Bounded-step counterpart of `longProgressionCover_of_almostPeriods`.
It is the exact interface between a step-controlled inverse theorem and the
arbitrary-interval progression sieve. -/
lemma stepBoundedLongProgressionCover_of_almostPeriods
    {b : ℕ} [NeZero b] {base mass stepBound growth : ℕ}
    {X : Finset ℕ} (U : Finset (ZMod b))
    (hbase : base ≤ b)
    (hXlo : ∀ x ∈ X, base ≤ x)
    (hXhi : ∀ x ∈ X, x < base + b)
    (hperiod : ∀ x ∈ X, (x : ZMod b) ∈ almostPeriods U growth)
    (hcover : HasStepBoundedLongProgressionCover
      (shiftedZmodValues
        (recenteredZmodValues base (almostPeriods U growth)))
      mass stepBound) :
    HasStepBoundedLongProgressionCover X mass stepBound := by
  have hres : occupiedResidues X b ⊆ almostPeriods U growth := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact hperiod x hx
  have hrec : recenteredZmodValues base (occupiedResidues X b) ⊆
      recenteredZmodValues base (almostPeriods U growth) :=
    recenteredZmodValues_mono hres
  have hshift :
      shiftedZmodValues (recenteredZmodValues base (occupiedResidues X b)) ⊆
        shiftedZmodValues
          (recenteredZmodValues base (almostPeriods U growth)) :=
    shiftedZmodValues_mono hrec
  have hinterval :=
    stepBoundedLongProgressionCover_interval_of_shifted_recentered
      hbase (occupiedResidues X b) (hcover.mono_set hshift)
  exact hinterval.mono_set
    (subset_intervalZmodValues_occupiedResidues hXlo hXhi)

/-- The progression sieve with no coprimality hypothesis on the common
difference.  Multiplying the target by the common difference removes its
prime divisors from the sifting product.  This is the exact finite version
of CFP's instruction to discard sieve primes dividing the step. -/
theorem exists_progressionCoprimeIndices_card_bound_any_step :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n a b L y S : ℕ, 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct (n * b) y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((progressionCoprimeIndices a b L
          (missingPrimeProduct n y)).card : ℝ) ≤
          (L : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  obtain ⟨A, hA, hsieve⟩ := exists_progressionCoprimeIndices_card_bound
  refine ⟨A, hA, ?_⟩
  intro n a b L y S hy hS hlog
  dsimp only
  have hcard :
      (progressionCoprimeIndices a b L (missingPrimeProduct n y)).card ≤
        (progressionCoprimeIndices a b L
          (missingPrimeProduct (n * b) y)).card :=
    Finset.card_le_card (progressionCoprimeIndices_mono_missing_mul n a b L y)
  have hcardR :
      ((progressionCoprimeIndices a b L
        (missingPrimeProduct n y)).card : ℝ) ≤
      ((progressionCoprimeIndices a b L
        (missingPrimeProduct (n * b) y)).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (hsieve (n * b) a b L y S hy hS hlog
    (progression_step_coprime_missingPrimeProduct_mul n b y))

/-- Mertens bound after adjoining an arbitrary progression step to the
target.  Totient supermultiplicativity cleanly isolates the sole loss as
the step's ratio `step / φ(step)`. -/
theorem exists_missingEulerProduct_mul_step_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n step y : ℕ,
      0 < n → 0 < step → 2 ≤ y →
      missingEulerProduct (n * step) y ≤
        C * ((n : ℝ) / Nat.totient n) *
          ((step : ℝ) / Nat.totient step) / Real.log (y : ℝ) := by
  obtain ⟨C, hC, hMertens⟩ := exists_missingEulerProduct_upper
  refine ⟨C, hC, ?_⟩
  intro n step y hn hstep hy
  have hnstep : 0 < n * step := Nat.mul_pos hn hstep
  have hphin : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have hphistep : 0 < Nat.totient step := Nat.totient_pos.mpr hstep
  have hphiprod : (0 : ℝ) < Nat.totient n * Nat.totient step := by
    positivity
  have hphiMul : (Nat.totient n : ℝ) * Nat.totient step ≤
      Nat.totient (n * step) := by
    exact_mod_cast Nat.totient_super_multiplicative n step
  have hratio : ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤
      ((n : ℝ) / Nat.totient n) *
        ((step : ℝ) / Nat.totient step) := by
    calc
      ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤
          ((n * step : ℕ) : ℝ) /
            ((Nat.totient n : ℝ) * Nat.totient step) := by
        exact div_le_div_of_nonneg_left (by positivity) hphiprod hphiMul
      _ = ((n : ℝ) / Nat.totient n) *
          ((step : ℝ) / Nat.totient step) := by
        push_cast
        field_simp
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  calc
    missingEulerProduct (n * step) y ≤
        C * (((n * step : ℕ) : ℝ) / Nat.totient (n * step)) /
          Real.log (y : ℝ) := hMertens (n * step) y hnstep hy
    _ ≤ C * (((n : ℝ) / Nat.totient n) *
          ((step : ℝ) / Nat.totient step)) /
          Real.log (y : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hC.le) hlog.le
    _ = C * ((n : ℝ) / Nat.totient n) *
          ((step : ℝ) / Nat.totient step) / Real.log (y : ℝ) := by
      ring

/-- The arbitrary-step progression sieve summed over a long cover.  The
single analytic input `Vbound` is precisely where the standard bound
`(n b)/φ(n b) \ll (n/φ(n)) log log b` is used in the paper. -/
theorem exists_progressionCover_card_bound_any_step :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass m : ℕ, ∀ P : Fin m → NatProgressionSpec,
        ∀ X : Finset ℕ, ∀ V : ℝ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) →
        (∑ i, (P i).length) ≤ mass →
        (∀ i, X.card ≤ (P i).length ^ 3) →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (∀ i, missingEulerProduct (n * (P i).step) y ≤ V) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X.card : ℝ) ≤
          (mass : ℝ) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hsieve⟩ :=
    exists_progressionCoprimeIndices_card_bound_any_step
  refine ⟨A, hA, ?_⟩
  intro n y S mass m P X V hy hS hlog hX hcover hmass hlong hXcop hV
  dsimp only
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℕ := y ^ S
  have heta : 0 ≤ 1 + eta := by
    dsimp [eta]
    positivity
  have hpiece (i : Fin m) :
      ((progressionCoprimeIndices (P i).start (P i).step (P i).length
        (missingPrimeProduct n y)).card : ℝ) ≤
        ((P i).length : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
    have hi := hsieve n (P i).start (P i).step (P i).length y S
      hy hS hlog
    dsimp only at hi
    calc
      ((progressionCoprimeIndices (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) ≤
          ((P i).length : ℝ) *
              ((1 + eta) * missingEulerProduct (n * (P i).step) y) +
            (D : ℝ) ^ 2 := by simpa [eta, D] using hi
      _ ≤ ((P i).length : ℝ) * ((1 + eta) * V) +
          (D : ℝ) ^ 2 := by
        have hv' : (1 + eta) * missingEulerProduct (n * (P i).step) y ≤
            (1 + eta) * V := mul_le_mul_of_nonneg_left (hV i) heta
        exact add_le_add
          (mul_le_mul_of_nonneg_left hv' (Nat.cast_nonneg _)) le_rfl
  have hcount := card_coprimePart_le_sum_cover P hcover
    (missingPrimeProduct n y)
  rw [coprimePart_eq_self_of_all_coprime hXcop] at hcount
  have hcountR : (X.card : ℝ) ≤
      ∑ i, ((progressionCoprimeIndices
        (P i).start (P i).step (P i).length
        (missingPrimeProduct n y)).card : ℝ) := by
    exact_mod_cast hcount
  have hmassR : ((∑ i, (P i).length : ℕ) : ℝ) ≤ mass := by
    exact_mod_cast hmass
  have hm : m ≤ mass :=
    (number_progressions_le_total_length hX P hlong).trans hmass
  have hmR : (m : ℝ) ≤ mass := by exact_mod_cast hm
  have hmainNonneg : 0 ≤ (1 + eta) * V := by
    obtain ⟨x, hx⟩ := hX
    obtain ⟨i, _hi⟩ := hcover x hx
    have hVpos : 0 < V :=
      (missingEulerProduct_pos (n * (P i).step) y).trans_le (hV i)
    positivity
  calc
    (X.card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) := hcountR
    _ ≤ ∑ i, (((P i).length : ℝ) * ((1 + eta) * V) +
          (D : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun i _ ↦ hpiece i
    _ = ((∑ i, (P i).length : ℕ) : ℝ) * ((1 + eta) * V) +
          (m : ℝ) * (D : ℝ) ^ 2 := by
      push_cast
      simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (mass : ℝ) * ((1 + eta) * V) +
          (mass : ℝ) * (D : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hmassR hmainNonneg)
        (mul_le_mul_of_nonneg_right hmR (sq_nonneg (D : ℝ)))
    _ = (mass : ℝ) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by ring

/-- Sharp error-absorbing form of the cover sieve.  Instead of paying one
raw square-level error per progression, an estimate
`D² ≤ lengthᵢ * E` charges that error to the length of its piece.  The
whole cover then costs only its total mass times the density `main + E`.
This is the form compatible with CFP's long-progression hypothesis. -/
theorem exists_progressionCover_card_bound_any_step_absorbed :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass m : ℕ, ∀ P : Fin m → NatProgressionSpec,
        ∀ X : Finset ℕ, ∀ V E : ℝ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) →
        (∑ i, (P i).length) ≤ mass →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (∀ i, missingEulerProduct (n * (P i).step) y ≤ V) →
        0 ≤ E →
        (∀ i, (((y ^ S : ℕ) : ℝ) ^ 2) ≤ ((P i).length : ℝ) * E) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (X.card : ℝ) ≤
          (mass : ℝ) *
            (((1 + eta) * V) + E) := by
  obtain ⟨A, hA, hsieve⟩ :=
    exists_progressionCoprimeIndices_card_bound_any_step
  refine ⟨A, hA, ?_⟩
  intro n y S mass m P X V E hy hS hlog hX hcover hmass hXcop hV hE herror
  dsimp only
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have heta : 0 ≤ 1 + eta := by
    dsimp [eta]
    positivity
  have hpiece (i : Fin m) :
      ((progressionCoprimeIndices (P i).start (P i).step (P i).length
        (missingPrimeProduct n y)).card : ℝ) ≤
        ((P i).length : ℝ) * (((1 + eta) * V) + E) := by
    have hi := hsieve n (P i).start (P i).step (P i).length y S
      hy hS hlog
    dsimp only at hi
    calc
      ((progressionCoprimeIndices (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) ≤
          ((P i).length : ℝ) *
              ((1 + eta) * missingEulerProduct (n * (P i).step) y) +
            (((y ^ S : ℕ) : ℝ) ^ 2) := by simpa [eta] using hi
      _ ≤ ((P i).length : ℝ) * ((1 + eta) * V) +
          ((P i).length : ℝ) * E := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hV i) heta) (Nat.cast_nonneg _)
        · exact herror i
      _ = ((P i).length : ℝ) * (((1 + eta) * V) + E) := by ring
  have hcount := card_coprimePart_le_sum_cover P hcover
    (missingPrimeProduct n y)
  rw [coprimePart_eq_self_of_all_coprime hXcop] at hcount
  have hcountR : (X.card : ℝ) ≤
      ∑ i, ((progressionCoprimeIndices
        (P i).start (P i).step (P i).length
        (missingPrimeProduct n y)).card : ℝ) := by
    exact_mod_cast hcount
  have hmassR : (((∑ i, (P i).length : ℕ) : ℝ)) ≤ mass := by
    exact_mod_cast hmass
  have hfactor : 0 ≤ ((1 + eta) * V) + E := by
    obtain ⟨x, hx⟩ := hX
    obtain ⟨i, _hi⟩ := hcover x hx
    have hVpos : 0 < V :=
      (missingEulerProduct_pos (n * (P i).step) y).trans_le (hV i)
    positivity
  calc
    (X.card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) := hcountR
    _ ≤ ∑ i, ((P i).length : ℝ) * (((1 + eta) * V) + E) := by
      exact Finset.sum_le_sum fun i _ ↦ hpiece i
    _ = (((∑ i, (P i).length : ℕ) : ℝ)) *
          (((1 + eta) * V) + E) := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (mass : ℝ) * (((1 + eta) * V) + E) :=
      mul_le_mul_of_nonneg_right hmassR hfactor

/-- Sharp modular-growth connector in the form used by the phase argument:
if an inverse theorem covers all remaining admissible translations by long
progressions of mass at most `K * growth`, then the number of translations
is at most `K * growth` times the sieve density (including its finite
square-level error).  Thus any independent strict reverse inequality forces
the desired lower bound on `growth`. -/
theorem exists_progressionCover_growth_bound_any_step :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S K growth mass m : ℕ,
        ∀ P : Fin m → NatProgressionSpec,
        ∀ X : Finset ℕ, ∀ V : ℝ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) →
        (∑ i, (P i).length) ≤ mass →
        (∀ i, X.card ≤ (P i).length ^ 3) →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (∀ i, missingEulerProduct (n * (P i).step) y ≤ V) →
        mass ≤ K * growth →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X.card : ℝ) ≤
          ((K : ℝ) * growth) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hcover⟩ := exists_progressionCover_card_bound_any_step
  refine ⟨A, hA, ?_⟩
  intro n y S K growth mass m P X V hy hS hlog hX hPX hmass hlong
    hXcop hV hmassGrowth
  dsimp only
  have hmain := hcover n y S mass m P X V hy hS hlog hX hPX hmass
    hlong hXcop hV
  dsimp only at hmain
  have hmassR : (mass : ℝ) ≤ (K : ℝ) * growth := by
    exact_mod_cast hmassGrowth
  have hfactor : 0 ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V) +
        ((y ^ S : ℕ) : ℝ) ^ 2 := by
    obtain ⟨x, hx⟩ := hX
    obtain ⟨i, _hi⟩ := hPX x hx
    have hVpos : 0 < V :=
      (missingEulerProduct_pos (n * (P i).step) y).trans_le (hV i)
    positivity
  exact hmain.trans (mul_le_mul_of_nonneg_right hmassR hfactor)

/-- Existential-cover interface for the phase proof.  A uniform bound for
the Euler product after adjoining an arbitrary progression step is the only
remaining analytic hypothesis. -/
theorem exists_longProgressionCover_growth_bound_any_step :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S K growth : ℕ, ∀ X : Finset ℕ, ∀ V : ℝ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasLongProgressionCover X (K * growth) →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (∀ step : ℕ, missingEulerProduct (n * step) y ≤ V) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X.card : ℝ) ≤
          ((K : ℝ) * growth) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := exists_progressionCover_growth_bound_any_step
  refine ⟨A, hA, ?_⟩
  intro n y S K growth X V hy hS hlog hX hcover hXcop hV
  dsimp only
  obtain ⟨m, P, hPX, hmass, hlong⟩ := hcover
  exact hbound n y S K growth (K * growth) m P X V hy hS hlog hX
    hPX hmass hlong hXcop (fun i ↦ hV (P i).step) (by rfl)

/-- Usable bounded-step version of the sharp connector.  Only totient
ratios of steps up to `stepBound` are required; this is the form to combine
with the lifted-cover construction, whose differences are bounded by the
ambient modulus. -/
theorem exists_stepBoundedLongProgressionCover_growth_bound_totient_ratio :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ n y S K growth stepBound : ℕ,
        ∀ X : Finset ℕ, ∀ R : ℝ,
        0 < n → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          (step : ℝ) / Nat.totient step ≤ R) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        let V := C * ((n : ℝ) / Nat.totient n) * R /
          Real.log (y : ℝ)
        (X.card : ℝ) ≤
          ((K : ℝ) * growth) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := exists_progressionCover_growth_bound_any_step
  obtain ⟨C, hC, hMertens⟩ := exists_missingEulerProduct_mul_step_upper
  refine ⟨A, C, hA, hC, ?_⟩
  intro n y S K growth stepBound X R hn hy hS hlog hX hcover hXcop hratio
  dsimp only
  obtain ⟨m, P, hPX, hmass, hlong, hstep⟩ := hcover
  have hV (i : Fin m) :
      missingEulerProduct (n * (P i).step) y ≤
        C * ((n : ℝ) / Nat.totient n) * R / Real.log (y : ℝ) := by
    have hmain := hMertens n (P i).step y hn (P i).step_pos hy
    have hfactor : 0 ≤
        C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ) := by
      positivity
    calc
      missingEulerProduct (n * (P i).step) y ≤
          C * ((n : ℝ) / Nat.totient n) *
            (((P i).step : ℝ) / Nat.totient (P i).step) /
              Real.log (y : ℝ) := hmain
      _ = (C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ)) *
          (((P i).step : ℝ) / Nat.totient (P i).step) := by ring
      _ ≤ (C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ)) * R :=
        mul_le_mul_of_nonneg_left
          (hratio (P i).step (P i).step_pos (hstep i)) hfactor
      _ = C * ((n : ℝ) / Nat.totient n) * R /
          Real.log (y : ℝ) := by ring
  exact hbound n y S K growth (K * growth) m P X
    (C * ((n : ℝ) / Nat.totient n) * R / Real.log (y : ℝ))
    hy hS hlog hX hPX hmass hlong hXcop hV (by rfl)

/-- Direct `target < growth` consequence for a bounded-step long cover.
Taking `target = y / z` is the sharp unsaturated-phase increment. -/
theorem exists_growth_gt_of_stepBoundedLongProgressionCover :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ n y S K growth target stepBound : ℕ,
        ∀ X : Finset ℕ, ∀ R : ℝ,
        0 < n → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        0 ≤ R →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          (step : ℝ) / Nat.totient step ≤ R) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        let V := C * ((n : ℝ) / Nat.totient n) * R /
          Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + (D : ℝ) ^ 2) <
          (X.card : ℝ) →
        target < growth := by
  obtain ⟨A, C, hA, hC, hupper⟩ :=
    exists_stepBoundedLongProgressionCover_growth_bound_totient_ratio
  refine ⟨A, C, hA, hC, ?_⟩
  intro n y S K growth target stepBound X R hn hy hS hlog hX hcover hXcop
    hR hratio
  dsimp only
  intro hstrict
  have hmain := hupper n y S K growth stepBound X R hn hy hS hlog hX
    hcover hXcop hratio
  dsimp only at hmain
  have hfactor : 0 ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C * ((n : ℝ) / Nat.totient n) * R / Real.log (y : ℝ))) +
        (((y ^ S : ℕ) : ℝ) ^ 2) := by
    have hphi : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  by_contra hnot
  have hgrowth : growth ≤ target := Nat.le_of_not_gt hnot
  have hcoeff : (K : ℝ) * growth ≤ (K : ℝ) * target := by
    gcongr
  have hcontra := hmain.trans
    (mul_le_mul_of_nonneg_right hcoeff hfactor)
  exact (not_lt_of_ge hcontra) hstrict

/-- Fully error-absorbed bounded-step connector.  If every cover piece is
long and `Q * D²` cubed is at most `|X|`, then `D² ≤ lengthᵢ / Q`; hence
the beta-sieve square-level error contributes only `1 / Q` to the density.
Choosing the sieve cutoff so that `Q` is of logarithmic size is the finite
substitute for CFP's negligible Selberg-sieve remainder. -/
theorem exists_stepBoundedLongProgressionCover_growth_bound_absorbed :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ n y S K growth stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ R : ℝ,
        0 < n → 2 ≤ y → 101 ≤ S → 0 < Q →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ S) ^ 2) ^ 3 ≤ X.card →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ R) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let V := C * R / Real.log (y : ℝ)
        (X.card : ℝ) ≤
          ((K : ℝ) * growth) *
            (((1 + eta) * V) + 1 / (Q : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_progressionCover_card_bound_any_step_absorbed
  obtain ⟨C, hC, hMertens⟩ := exists_missingEulerProduct_upper
  refine ⟨A, C, hA, hC, ?_⟩
  intro n y S K growth stepBound Q X R hn hy hS hQ hlog hX hcover hXcop
    hscale hratio
  dsimp only
  obtain ⟨m, P, hPX, hmass, hlong, hstep⟩ := hcover
  have hV (i : Fin m) :
      missingEulerProduct (n * (P i).step) y ≤
        C * R / Real.log (y : ℝ) := by
    have hmain := hMertens (n * (P i).step) y
      (Nat.mul_pos hn (P i).step_pos) hy
    have hfactor : 0 ≤
        C / Real.log (y : ℝ) := by
      positivity
    calc
      missingEulerProduct (n * (P i).step) y ≤
          C * (((n * (P i).step : ℕ) : ℝ) /
            Nat.totient (n * (P i).step)) / Real.log (y : ℝ) := hmain
      _ = (C / Real.log (y : ℝ)) *
          (((n * (P i).step : ℕ) : ℝ) /
            Nat.totient (n * (P i).step)) := by ring
      _ ≤ (C / Real.log (y : ℝ)) * R :=
        mul_le_mul_of_nonneg_left
          (hratio (P i).step (P i).step_pos (hstep i)) hfactor
      _ = C * R / Real.log (y : ℝ) := by ring
  have herror (i : Fin m) :
      (((y ^ S : ℕ) : ℝ) ^ 2) ≤
        ((P i).length : ℝ) * (1 / (Q : ℝ)) := by
    have hcube : (Q * (y ^ S) ^ 2) ^ 3 ≤ (P i).length ^ 3 :=
      hscale.trans (hlong i)
    have hroot : Q * (y ^ S) ^ 2 ≤ (P i).length :=
      (Nat.pow_le_pow_iff_left (by omega : 3 ≠ 0)).mp hcube
    have hrootR : (Q : ℝ) * (((y ^ S : ℕ) : ℝ) ^ 2) ≤
        ((P i).length : ℝ) := by
      exact_mod_cast hroot
    rw [show ((P i).length : ℝ) * (1 / (Q : ℝ)) =
        ((P i).length : ℝ) / Q by ring]
    rw [le_div_iff₀ (by exact_mod_cast hQ)]
    simpa [mul_comm] using hrootR
  have hmain := hbound n y S (K * growth) m P X
    (C * R / Real.log (y : ℝ))
    (1 / (Q : ℝ)) hy hS hlog hX hPX hmass hXcop hV (by positivity) herror
  simpa using hmain

/-- Sharp unsaturated-growth conclusion with the square-level error already
absorbed by longness.  Set `target := scale / z`; a strict reverse bound at
that target forces `scale / z < growth`. -/
theorem exists_growth_gt_of_stepBoundedLongProgressionCover_absorbed :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ n y S K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ R : ℝ,
        0 < n → 2 ≤ y → 101 ≤ S → 0 < Q →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ S) ^ 2) ^ 3 ≤ X.card →
        0 ≤ R →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ R) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let V := C * R / Real.log (y : ℝ)
        ((K : ℝ) * target) *
            (((1 + eta) * V) + 1 / (Q : ℝ)) < (X.card : ℝ) →
        target < growth := by
  obtain ⟨A, C, hA, hC, hupper⟩ :=
    exists_stepBoundedLongProgressionCover_growth_bound_absorbed
  refine ⟨A, C, hA, hC, ?_⟩
  intro n y S K growth target stepBound Q X R hn hy hS hQ hlog hX hcover
    hXcop hscale hR hratio
  dsimp only
  intro hstrict
  have hmain := hupper n y S K growth stepBound Q X R hn hy hS hQ hlog hX
    hcover hXcop hscale hratio
  dsimp only at hmain
  have hfactor : 0 ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C * R / Real.log (y : ℝ))) +
        1 / (Q : ℝ) := by
    have hphi : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  by_contra hnot
  have hgrowth : growth ≤ target := Nat.le_of_not_gt hnot
  have hcoeff : (K : ℝ) * growth ≤ (K : ℝ) * target := by
    gcongr
  have hcontra := hmain.trans
    (mul_le_mul_of_nonneg_right hcoeff hfactor)
  exact (not_lt_of_ge hcontra) hstrict

/-- A long progression cover all of whose steps are coprime to `M`. -/
def HasCoprimeLongProgressionCover
    (X : Finset ℕ) (mass M : ℕ) : Prop :=
  ∃ m : ℕ, ∃ P : Fin m → NatProgressionSpec,
    (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) ∧
    (∑ i, (P i).length) ≤ mass ∧
    (∀ i, X.card ≤ (P i).length ^ 3) ∧
    ∀ i, Nat.Coprime (P i).step M

/-- The number of pieces in a nonempty coprime long cover is at most its
mass.  This removes the per-progression square-level error from the final
interface. -/
lemma HasCoprimeLongProgressionCover.piece_count_le_mass
    {X : Finset ℕ} {mass M : ℕ}
    (hX : X.Nonempty) (h : HasCoprimeLongProgressionCover X mass M) :
    ∃ m : ℕ, ∃ P : Fin m → NatProgressionSpec,
      (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) ∧
      (∑ i, (P i).length) ≤ mass ∧
      (∀ i, X.card ≤ (P i).length ^ 3) ∧
      (∀ i, Nat.Coprime (P i).step M) ∧
      m ≤ mass := by
  obtain ⟨m, P, hcover, hmass, hlong, hcop⟩ := h
  exact ⟨m, P, hcover, hmass, hlong, hcop,
    (number_progressions_le_total_length hX P hlong).trans hmass⟩

/-- Sieve obstruction for a coprime long-progression cover.  It is the
formal finite connector used after the inverse theorem in an unsaturated
phase.  The error has been absorbed into the cover mass, so the right hand
side is linear in `mass` rather than in the number of pieces. -/
theorem exists_coprimeLongProgressionCover_card_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass : ℕ, ∀ X : Finset ℕ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasCoprimeLongProgressionCover X mass
          (missingPrimeProduct n y) →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X.card : ℝ) ≤
          (mass : ℝ) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hsieve⟩ := exists_progressionCover_coprimePart_bound
  refine ⟨A, hA, ?_⟩
  intro n y S mass X hy hS hlog hX hcover hXcop
  dsimp only
  obtain ⟨m, P, hPX, hmass, hlong, hPcop, hm⟩ :=
    hcover.piece_count_le_mass hX
  have hs := hsieve n y S mass m P hy hS hlog
    hPcop hmass X hPX
  dsimp only at hs
  rw [coprimePart_eq_self_of_all_coprime hXcop] at hs
  have hmR : (m : ℝ) ≤ mass := by exact_mod_cast hm
  have hD : (0 : ℝ) ≤ (y ^ S : ℕ) := by positivity
  calc
    (X.card : ℝ) ≤
        (mass : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              missingEulerProduct n y) +
          (m : ℝ) * ((y ^ S : ℕ) : ℝ) ^ 2 := hs
    _ ≤ (mass : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            missingEulerProduct n y) +
          (mass : ℝ) * ((y ^ S : ℕ) : ℝ) ^ 2 := by
      gcongr
    _ = (mass : ℝ) *
          (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            missingEulerProduct n y) +
            ((y ^ S : ℕ) : ℝ) ^ 2) := by ring

/-- A form convenient for an inverse theorem whose cover mass is bounded by
`K * growth`.  It turns the progression-sieve estimate directly into the
linear lower bound on the translation growth used in the CFP modular
iteration. -/
theorem exists_coprimeLongProgressionCover_growth_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S K growth mass : ℕ, ∀ X : Finset ℕ,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        X.Nonempty →
        HasCoprimeLongProgressionCover X mass
          (missingPrimeProduct n y) →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        mass ≤ K * growth →
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X.card : ℝ) ≤
          ((K : ℝ) * growth) * (((1 + eta) * V) + (D : ℝ) ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := exists_coprimeLongProgressionCover_card_bound
  refine ⟨A, hA, ?_⟩
  intro n y S K growth mass X hy hS hlog hX hcover hXcop hmass
  dsimp only
  have hmain := hbound n y S mass X hy hS hlog hX hcover hXcop
  dsimp only at hmain
  have hmassR : (mass : ℝ) ≤ (K : ℝ) * growth := by
    exact_mod_cast hmass
  have hfactor : 0 ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        missingEulerProduct n y) + (((y ^ S : ℕ) : ℝ) ^ 2) := by
    have hV := (missingEulerProduct_pos n y).le
    positivity
  exact hmain.trans (mul_le_mul_of_nonneg_right hmassR hfactor)

end Erdos360
