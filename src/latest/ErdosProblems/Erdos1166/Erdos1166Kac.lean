import Mathlib

open scoped BigOperators

namespace KacMoment

abbrev TimeTuple (n r : ℕ) := Fin r → Fin (n + 1)

noncomputable def sortedTuples (n r : ℕ) : Finset (TimeTuple n r) :=
  Finset.univ.filter Monotone

noncomputable def encode (n r : ℕ) (t : TimeTuple n r) :
    Equiv.Perm (Fin r) × TimeTuple n r :=
  (Tuple.sort t, t ∘ Tuple.sort t)

def decode (n r : ℕ) (p : Equiv.Perm (Fin r) × TimeTuple n r) : TimeTuple n r :=
  p.2 ∘ p.1.symm

lemma decode_encode (n r : ℕ) (t : TimeTuple n r) :
    decode n r (encode n r t) = t := by
  ext i
  simp [decode, encode, Function.comp_def]

lemma encode_injective (n r : ℕ) : Function.Injective (encode n r) :=
  (Function.LeftInverse.injective (decode_encode n r))

lemma encode_mem_product (n r : ℕ) (t : TimeTuple n r) :
    encode n r t ∈
      (Finset.univ : Finset (Equiv.Perm (Fin r))) ×ˢ sortedTuples n r := by
  simp [encode, sortedTuples, Tuple.monotone_sort]

/-- Every nonnegative permutation-invariant weight on ordered time tuples is at most
`r!` times its mass on weakly increasing tuples. This is the combinatorial core
of Kac's moment argument. -/
theorem sum_weight_le_factorial_mul_sorted
    (n r : ℕ) (w : TimeTuple n r → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_perm : ∀ (t : TimeTuple n r) (σ : Equiv.Perm (Fin r)), w (t ∘ σ) = w t) :
    ∑ t, w t ≤ (r.factorial : ℝ) * ∑ t ∈ sortedTuples n r, w t := by
  classical
  calc
    ∑ t, w t = ∑ t, w (encode n r t).2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hw_perm t (Tuple.sort t)).symm
    _ = ∑ p ∈ Finset.univ.image (encode n r), w p.2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h ↦ encode_injective n r h
    _ ≤ ∑ p ∈
        (Finset.univ : Finset (Equiv.Perm (Fin r))) ×ˢ sortedTuples n r, w p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_image] at hp
        obtain ⟨t, -, rfl⟩ := hp
        exact encode_mem_product n r t
      · intro p _ _
        exact hw_nonneg p.2
    _ = (r.factorial : ℝ) * ∑ t ∈ sortedTuples n r, w t := by
      rw [Finset.sum_product]
      simp [Fintype.card_perm]

section LocalTime

variable {Site : Type*} [DecidableEq Site]

def finiteLocalTime (n : ℕ) (p : Fin (n + 1) → Site) (x : Site) : ℕ :=
  (Finset.univ.filter fun i ↦ p i = x).card

def allEqualAlong (n r : ℕ) (p : Fin (n + 1) → Site) (t : TimeTuple n r) : Prop :=
  ∀ i j, p (t i) = p (t j)

noncomputable def hitIndicator (n r : ℕ) (p : Fin (n + 1) → Site)
    (x : Site) (t : TimeTuple n r) : ℕ :=
  if ∀ j, p (t j) = x then 1 else 0

noncomputable def collisionIndicator (n r : ℕ) (p : Fin (n + 1) → Site)
    (t : TimeTuple n r) : ℕ :=
  @ite ℕ (allEqualAlong n r p t) (Classical.propDecidable _) 1 0

lemma localTime_pow_eq_tuple_sum (n r : ℕ) (p : Fin (n + 1) → Site) (x : Site) :
    finiteLocalTime n p x ^ r =
      ∑ t : TimeTuple n r, hitIndicator n r p x t := by
  classical
  change (Finset.univ.filter fun i ↦ p i = x).card ^ r = _
  rw [← Fintype.card_piFinset_const]
  rw [Finset.card_eq_sum_ones]
  change (∑ t ∈ Fintype.piFinset (fun _ : Fin r ↦ {i | p i = x}), 1) = _
  simp only [hitIndicator]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext t
    simp [Fintype.mem_piFinset]
  · simp

lemma sum_localTime_pow_eq_collision_sum [Fintype Site] (n r : ℕ) (hr : 0 < r)
    (p : Fin (n + 1) → Site) :
    ∑ x : Site, finiteLocalTime n p x ^ r =
      ∑ t : TimeTuple n r, collisionIndicator n r p t := by
  classical
  simp_rw [localTime_pow_eq_tuple_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  let i0 : Fin r := ⟨0, hr⟩
  by_cases h : allEqualAlong n r p t
  · rw [collisionIndicator, if_pos h]
    have hchar : (∀ j, p (t j) = p (t i0)) := fun j ↦ h j i0
    rw [Finset.sum_eq_single (p (t i0))]
    · simp [hitIndicator, hchar]
    · intro x _ hx
      simp only [hitIndicator, ite_eq_right_iff]
      intro hall
      exact (hx (hall i0).symm).elim
    · simp
  · rw [collisionIndicator, if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    simp only [hitIndicator, ite_eq_right_iff]
    intro hall
    exfalso
    apply h
    intro i j
    exact (hall i).trans (hall j).symm

end LocalTime

section VisitedLocalTime

variable {Site : Type*} [DecidableEq Site]

def visitedSites (n : ℕ) (p : Fin (n + 1) → Site) : Finset Site :=
  Finset.univ.image p

def finiteMaxLocalTime (n : ℕ) (p : Fin (n + 1) → Site) : ℕ :=
  Finset.univ.sup fun i : Fin (n + 1) ↦ finiteLocalTime n p (p i)

lemma finiteMaxLocalTime_pow_le_visited_moment (n r : ℕ)
    (p : Fin (n + 1) → Site) :
    finiteMaxLocalTime n p ^ r ≤
      ∑ x ∈ visitedSites n p, finiteLocalTime n p x ^ r := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset (Fin (n + 1)))) Finset.univ_nonempty
    (fun i : Fin (n + 1) ↦ finiteLocalTime n p (p i))
  rw [finiteMaxLocalTime, hi]
  apply Finset.single_le_sum (fun x _ ↦ Nat.zero_le (finiteLocalTime n p x ^ r))
  simp [visitedSites]

lemma sum_visited_localTime_pow_eq_collision_sum (n r : ℕ) (hr : 0 < r)
    (p : Fin (n + 1) → Site) :
    ∑ x ∈ visitedSites n p, finiteLocalTime n p x ^ r =
      ∑ t : TimeTuple n r, collisionIndicator n r p t := by
  classical
  simp_rw [localTime_pow_eq_tuple_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  let i0 : Fin r := ⟨0, hr⟩
  by_cases h : allEqualAlong n r p t
  · rw [collisionIndicator, if_pos h]
    have hchar : (∀ j, p (t j) = p (t i0)) := fun j ↦ h j i0
    rw [Finset.sum_eq_single (p (t i0))]
    · simp [hitIndicator, hchar]
    · intro x _ hx
      simp only [hitIndicator, ite_eq_right_iff]
      intro hall
      exact (hx (hall i0).symm).elim
    · simp [visitedSites]
  · rw [collisionIndicator, if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    simp only [hitIndicator, ite_eq_right_iff]
    intro hall
    exfalso
    apply h
    intro i j
    exact (hall i).trans (hall j).symm

end VisitedLocalTime

section GreenKernel

def timeGaps (n k : ℕ) (t : TimeTuple n (k + 1)) : Fin k → Fin (n + 1) :=
  fun i ↦ ⟨(t i.succ).val - (t i.castSucc).val, by omega⟩

def gapEncode (n k : ℕ) (t : TimeTuple n (k + 1)) :
    Fin (n + 1) × (Fin k → Fin (n + 1)) :=
  (t 0, timeGaps n k t)

lemma gapEncode_injOn_sorted (n k : ℕ) :
    Set.InjOn (gapEncode n k) (sortedTuples n (k + 1)) := by
  classical
  intro t ht u hu henc
  have htmono : Monotone t := by simpa [sortedTuples] using ht
  have humono : Monotone u := by simpa [sortedTuples] using hu
  have hzero : t 0 = u 0 := congrArg Prod.fst henc
  have hgaps : timeGaps n k t = timeGaps n k u := congrArg Prod.snd henc
  funext i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i ih =>
      apply Fin.ext
      have htl : (t i.castSucc).val ≤ (t i.succ).val :=
        Fin.val_le_of_le (htmono (Fin.castSucc_le_succ i))
      have hul : (u i.castSucc).val ≤ (u i.succ).val :=
        Fin.val_le_of_le (humono (Fin.castSucc_le_succ i))
      have hprev := congrArg Fin.val ih
      have hgap := congrArg (fun g ↦ (g i).val) hgaps
      simp only [timeGaps] at hgap
      omega

def gapWeight (n k : ℕ) (q : Fin (n + 1) → ℝ) (t : TimeTuple n (k + 1)) : ℝ :=
  ∏ i : Fin k, q (timeGaps n k t i)

/-- The increasing-time Green-kernel sum is bounded by one free starting time
and one Green sum for each of the `k` gaps. -/
theorem sum_sorted_gapWeight_le (n k : ℕ) (q : Fin (n + 1) → ℝ)
    (hq : ∀ d, 0 ≤ q d) :
    ∑ t ∈ sortedTuples n (k + 1), gapWeight n k q t ≤
      (n + 1 : ℝ) * (∑ d : Fin (n + 1), q d) ^ k := by
  classical
  let target : Finset (Fin (n + 1) × (Fin k → Fin (n + 1))) := Finset.univ
  let W : (Fin (n + 1) × (Fin k → Fin (n + 1))) → ℝ :=
    fun p ↦ ∏ i : Fin k, q (p.2 i)
  calc
    ∑ t ∈ sortedTuples n (k + 1), gapWeight n k q t =
        ∑ p ∈ (sortedTuples n (k + 1)).image (gapEncode n k), W p := by
      rw [Finset.sum_image (gapEncode_injOn_sorted n k)]
      apply Finset.sum_congr rfl
      intro t _
      rfl
    _ ≤ ∑ p ∈ target, W p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro p _ _
        exact Finset.prod_nonneg fun i _ ↦ hq (p.2 i)
    _ = (n + 1 : ℝ) * (∑ d : Fin (n + 1), q d) ^ k := by
      simp only [target, W]
      rw [Fintype.sum_prod_type]
      simp only [Prod.snd]
      rw [← Fintype.sum_pow]
      simp

end GreenKernel

section Probability

open MeasureTheory

variable {Site Ω : Type*} [DecidableEq Site] [MeasurableSpace Ω]

def collisionSet (n r : ℕ) (X : Ω → Fin (n + 1) → Site) (t : TimeTuple n r) : Set Ω :=
  {ω | allEqualAlong n r (X ω) t}

noncomputable def collisionRealIndicator
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site) (t : TimeTuple n r) : Ω → ℝ :=
  (collisionSet n r X t).indicator 1

noncomputable def collisionMoment
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site) : Ω → ℝ :=
  fun ω ↦ ∑ t : TimeTuple n r, collisionRealIndicator n r X t ω

noncomputable def localMoment
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site) : Ω → ℝ :=
  fun ω ↦ ∑ x ∈ visitedSites n (X ω), (finiteLocalTime n (X ω) x ^ r : ℕ)

lemma collisionRealIndicator_eq_cast
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site) (t : TimeTuple n r) (ω : Ω) :
    collisionRealIndicator n r X t ω = (collisionIndicator n r (X ω) t : ℝ) := by
  classical
  by_cases h : allEqualAlong n r (X ω) t
  · simp [collisionRealIndicator, collisionSet, collisionIndicator, h]
  · simp [collisionRealIndicator, collisionSet, collisionIndicator, h]

lemma localMoment_eq_collisionMoment (n r : ℕ) (hr : 0 < r)
    (X : Ω → Fin (n + 1) → Site) :
    localMoment n r X = collisionMoment n r X := by
  funext ω
  simp only [localMoment, collisionMoment, collisionRealIndicator_eq_cast]
  exact_mod_cast sum_visited_localTime_pow_eq_collision_sum n r hr (X ω)

lemma localMoment_nonneg (n r : ℕ) (X : Ω → Fin (n + 1) → Site) (ω : Ω) :
    0 ≤ localMoment n r X ω := by
  exact Finset.sum_nonneg fun x _ ↦ Nat.cast_nonneg _

lemma localMoment_eq_cast_nat_sum (n r : ℕ)
    (X : Ω → Fin (n + 1) → Site) (ω : Ω) :
    localMoment n r X ω =
      ((∑ x ∈ visitedSites n (X ω), finiteLocalTime n (X ω) x ^ r : ℕ) : ℝ) := by
  simp [localMoment]

lemma integrable_localMoment (n r : ℕ) (hr : 0 < r)
    (X : Ω → Fin (n + 1) → Site) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple n r, MeasurableSet (collisionSet n r X t)) :
    Integrable (localMoment n r X) μ := by
  rw [localMoment_eq_collisionMoment n r hr X]
  apply MeasureTheory.integrable_finsetSum Finset.univ
  intro t _
  exact (MeasureTheory.integrable_const (1 : ℝ)).indicator (hMeas t)

/-- Markov's inequality turns a spatial local-time moment estimate into a
tail estimate for the maximum local time. -/
theorem measureReal_finiteMaxLocalTime_ge_le_moment_div
    (n r m : ℕ) (hm : 0 < m) (X : Ω → Fin (n + 1) → Site)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hInt : Integrable (localMoment n r X) μ) (B : ℝ)
    (hMoment : ∫ ω, localMoment n r X ω ∂μ ≤ B) :
    μ.real {ω | m ≤ finiteMaxLocalTime n (X ω)} ≤ B / (m : ℝ) ^ r := by
  have hmr : (0 : ℝ) < (m : ℝ) ^ r := pow_pos (Nat.cast_pos.mpr hm) _
  have hsubset : {ω | m ≤ finiteMaxLocalTime n (X ω)} ⊆
      {ω | (m : ℝ) ^ r ≤ localMoment n r X ω} := by
    intro ω hω
    have hpow : m ^ r ≤ finiteMaxLocalTime n (X ω) ^ r := Nat.pow_le_pow_left hω r
    have hdet := finiteMaxLocalTime_pow_le_visited_moment n r (X ω)
    change (m : ℝ) ^ r ≤ localMoment n r X ω
    have hcast : (m ^ r : ℕ) ≤
        ∑ x ∈ visitedSites n (X ω), finiteLocalTime n (X ω) x ^ r := hpow.trans hdet
    rw [localMoment_eq_cast_nat_sum]
    exact_mod_cast hcast
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (localMoment_nonneg n r X)) hInt ((m : ℝ) ^ r)
  apply (le_div_iff₀ hmr).2
  have hchain :
    (m : ℝ) ^ r * μ.real {ω | m ≤ finiteMaxLocalTime n (X ω)} ≤
        B := by
    calc
      (m : ℝ) ^ r * μ.real {ω | m ≤ finiteMaxLocalTime n (X ω)} ≤
          (m : ℝ) ^ r * μ.real {ω | (m : ℝ) ^ r ≤ localMoment n r X ω} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hmr.le
      _ ≤ ∫ ω, localMoment n r X ω ∂μ := hmarkov
      _ ≤ B := hMoment
  simpa [mul_comm] using hchain

lemma collisionSet_comp_perm (n r : ℕ) (X : Ω → Fin (n + 1) → Site)
    (t : TimeTuple n r) (σ : Equiv.Perm (Fin r)) :
    collisionSet n r X (t ∘ σ) = collisionSet n r X t := by
  ext ω
  simp only [collisionSet, Set.mem_setOf_eq, allEqualAlong, Function.comp_apply]
  constructor
  · intro h i j
    simpa using h (σ.symm i) (σ.symm j)
  · intro h i j
    exact h (σ i) (σ j)

lemma integral_collisionMoment_eq_sum_probability
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple n r, MeasurableSet (collisionSet n r X t)) :
    ∫ ω, collisionMoment n r X ω ∂μ =
      ∑ t : TimeTuple n r, μ.real (collisionSet n r X t) := by
  change (∫ ω, ∑ t : TimeTuple n r, collisionRealIndicator n r X t ω ∂μ) = _
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro t _
    exact MeasureTheory.integral_indicator_one (hMeas t)
  · intro t _
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator (hMeas t)

/-- Factorial symmetrization of Kac's moment formula. No Markov property is used here. -/
theorem integral_localMoment_le_factorial_mul_sorted_probabilities
    (n r : ℕ) (hr : 0 < r) (X : Ω → Fin (n + 1) → Site)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple n r, MeasurableSet (collisionSet n r X t)) :
    ∫ ω, localMoment n r X ω ∂μ ≤
      (r.factorial : ℝ) *
        ∑ t ∈ sortedTuples n r, μ.real (collisionSet n r X t) := by
  rw [localMoment_eq_collisionMoment n r hr X,
    integral_collisionMoment_eq_sum_probability n r X μ hMeas]
  apply sum_weight_le_factorial_mul_sorted
  · intro t
    exact measureReal_nonneg
  · intro t σ
    rw [collisionSet_comp_perm]

/-- Kac's moment bound after the Markov/Green-kernel estimate for increasing tuples
has been supplied. The latter estimate is the sole process-specific input. -/
theorem integral_localMoment_le_factorial_mul_green
    (n r : ℕ) (hr : 0 < r) (X : Ω → Fin (n + 1) → Site)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple n r, MeasurableSet (collisionSet n r X t))
    (G : ℝ) (hSorted :
      ∑ t ∈ sortedTuples n r, μ.real (collisionSet n r X t) ≤
        (n + 1 : ℝ) * G ^ (r - 1)) :
    ∫ ω, localMoment n r X ω ∂μ ≤
      (r.factorial : ℝ) * (n + 1) * G ^ (r - 1) := by
  calc
    ∫ ω, localMoment n r X ω ∂μ ≤
        (r.factorial : ℝ) *
          ∑ t ∈ sortedTuples n r, μ.real (collisionSet n r X t) :=
      integral_localMoment_le_factorial_mul_sorted_probabilities n r hr X μ hMeas
    _ ≤ (r.factorial : ℝ) * ((n + 1 : ℝ) * G ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hSorted (Nat.cast_nonneg _)
    _ = (r.factorial : ℝ) * (n + 1) * G ^ (r - 1) := by ring

/-- Full finite-horizon Kac moment bound from the collision-kernel factorization.
For a random walk, `q d` is the `d`-step return probability and `hKernel` follows
from stationary independent increments. -/
theorem kac_moment_bound_of_collision_kernel
    (n k : ℕ) (X : Ω → Fin (n + 1) → Site)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple n (k + 1), MeasurableSet (collisionSet n (k + 1) X t))
    (q : Fin (n + 1) → ℝ) (hq : ∀ d, 0 ≤ q d)
    (hKernel : ∀ t ∈ sortedTuples n (k + 1),
      μ.real (collisionSet n (k + 1) X t) ≤ gapWeight n k q t) :
    ∫ ω, localMoment n (k + 1) X ω ∂μ ≤
      ((k + 1).factorial : ℝ) * (n + 1) * (∑ d : Fin (n + 1), q d) ^ k := by
  have hSorted :
      ∑ t ∈ sortedTuples n (k + 1), μ.real (collisionSet n (k + 1) X t) ≤
        (n + 1 : ℝ) * (∑ d : Fin (n + 1), q d) ^ k := by
    exact (Finset.sum_le_sum fun t ht ↦ hKernel t ht).trans
      (sum_sorted_gapWeight_le n k q hq)
  calc
    ∫ ω, localMoment n (k + 1) X ω ∂μ ≤
        ((k + 1).factorial : ℝ) *
          ∑ t ∈ sortedTuples n (k + 1), μ.real (collisionSet n (k + 1) X t) :=
      integral_localMoment_le_factorial_mul_sorted_probabilities
        n (k + 1) (by omega) X μ hMeas
    _ ≤ ((k + 1).factorial : ℝ) *
        ((n + 1 : ℝ) * (∑ d : Fin (n + 1), q d) ^ k) :=
      mul_le_mul_of_nonneg_left hSorted (Nat.cast_nonneg _)
    _ = ((k + 1).factorial : ℝ) * (n + 1) *
        (∑ d : Fin (n + 1), q d) ^ k := by ring

lemma dyadic_factorial_ratio_bound (k : ℕ) (hk : 1 ≤ k) :
    ((k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k) /
        (48 * k ^ 2 : ℝ) ^ k ≤
      2 * ((4 : ℝ)⁻¹) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hpow2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have htwo : (2 : ℝ) ^ k + 1 ≤ 2 * 2 ^ k := by linarith
  have hnum :
      (k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k ≤
        (k : ℝ) ^ k * (2 * 2 ^ k) * (6 * k : ℝ) ^ k := by
    gcongr <;> positivity
  calc
    ((k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k) /
          (48 * k ^ 2 : ℝ) ^ k ≤
        ((k : ℝ) ^ k * (2 * 2 ^ k) * (6 * k : ℝ) ^ k) /
          (48 * k ^ 2 : ℝ) ^ k := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 * ((4 : ℝ)⁻¹) ^ k := by
      rw [show (6 * k : ℝ) = 6 * (k : ℝ) by norm_num,
        show (48 * k ^ 2 : ℝ) = 48 * (k : ℝ) ^ 2 by norm_num]
      field_simp
      simp only [mul_pow, pow_two]
      have hconst : (2 : ℝ) ^ k * 6 ^ k = ((1 : ℝ) / 4) ^ k * 48 ^ k := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      calc
        (k : ℝ) ^ k * 2 ^ k * (6 ^ k * (k : ℝ) ^ k) =
            (k : ℝ) ^ k * (k : ℝ) ^ k * (2 ^ k * 6 ^ k) := by ring
        _ = (k : ℝ) ^ k * (k : ℝ) ^ k * (((1 : ℝ) / 4) ^ k * 48 ^ k) := by
          rw [hconst]
        _ = (k : ℝ) ^ k * (k : ℝ) ^ k * 48 ^ k * ((1 : ℝ) / 4) ^ k := by
          ring

/-- Explicit dyadic tail estimate with `A = 48`.  The deliberately loose
replacement `G^(k-1) ≤ (6k)^k` makes the final arithmetic exact. -/
theorem dyadic_maxLocalTime_tail
    (k : ℕ) (hk : 1 ≤ k)
    (X : Ω → Fin ((2 : ℕ) ^ k + 1) → Site)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : TimeTuple ((2 : ℕ) ^ k) k,
      MeasurableSet (collisionSet ((2 : ℕ) ^ k) k X t))
    (G : ℝ) (hG0 : 0 ≤ G) (hG : G ≤ 6 * k)
    (hKac :
      ∫ ω, localMoment ((2 : ℕ) ^ k) k X ω ∂μ ≤
        (k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * G ^ (k - 1)) :
    μ.real {ω | 48 * k ^ 2 ≤ finiteMaxLocalTime ((2 : ℕ) ^ k) (X ω)} ≤
      2 * ((4 : ℝ)⁻¹) ^ k := by
  have hkreal : (1 : ℝ) ≤ 6 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hGpow : G ^ (k - 1) ≤ (6 * k : ℝ) ^ k := by
    exact (pow_le_pow_left₀ hG0 hG (k - 1)).trans
      (pow_le_pow_right₀ hkreal (Nat.sub_le k 1))
  have hMoment :
      ∫ ω, localMoment ((2 : ℕ) ^ k) k X ω ∂μ ≤
        (k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k := by
    exact hKac.trans (mul_le_mul_of_nonneg_left hGpow (by positivity))
  have htail := measureReal_finiteMaxLocalTime_ge_le_moment_div
    ((2 : ℕ) ^ k) k (48 * k ^ 2) (by positivity) X μ
    (integrable_localMoment ((2 : ℕ) ^ k) k (by omega) X μ hMeas)
    ((k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k) hMoment
  calc
    μ.real {ω | 48 * k ^ 2 ≤ finiteMaxLocalTime ((2 : ℕ) ^ k) (X ω)} ≤
        ((k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k) /
          ((48 * k ^ 2 : ℕ) : ℝ) ^ k := htail
    _ = ((k.factorial : ℝ) * ((2 : ℝ) ^ k + 1) * (6 * k : ℝ) ^ k) /
          (48 * (k : ℝ) ^ 2) ^ k := by norm_num
    _ ≤ 2 * ((4 : ℝ)⁻¹) ^ k := dyadic_factorial_ratio_bound k hk

def restrictedPath (N : ℕ) (S : Ω → ℕ → Site) : Ω → Fin (N + 1) → Site :=
  fun ω i ↦ S ω i.val

def shiftedDyadicBad (S : Ω → ℕ → Site) (k : ℕ) : Set Ω :=
  {ω | 48 * (k + 1) ^ 2 ≤
    finiteMaxLocalTime ((2 : ℕ) ^ (k + 1))
      (restrictedPath ((2 : ℕ) ^ (k + 1)) S ω)}

/-- First Borel--Cantelli applied to the explicit dyadic tail. -/
theorem ae_eventually_dyadic_maxLocalTime_lt
    (S : Ω → ℕ → Site) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hTail : ∀ k : ℕ,
      μ.real (shiftedDyadicBad S k) ≤ 2 * ((4 : ℝ)⁻¹) ^ (k + 1)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in Filter.atTop,
      finiteMaxLocalTime ((2 : ℕ) ^ (k + 1))
        (restrictedPath ((2 : ℕ) ^ (k + 1)) S ω) < 48 * (k + 1) ^ 2 := by
  have hgeom : Summable (fun k : ℕ ↦ 2 * ((4 : ℝ)⁻¹) ^ (k + 1)) := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one (r := (4 : ℝ)⁻¹) (by positivity) (by norm_num)).mul_left
        (2 * (4 : ℝ)⁻¹)
  have hpoint : ∀ k : ℕ,
      μ (shiftedDyadicBad S k) ≤
        ENNReal.ofReal (2 * ((4 : ℝ)⁻¹) ^ (k + 1)) := by
    intro k
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (shiftedDyadicBad S k))]
    exact ENNReal.ofReal_le_ofReal (hTail k)
  have hbound_ne :
      (∑' k : ℕ, ENNReal.ofReal (2 * ((4 : ℝ)⁻¹) ^ (k + 1))) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hgeom]
    exact ENNReal.ofReal_ne_top
  have hsum_ne : (∑' k : ℕ, μ (shiftedDyadicBad S k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbound_ne (ENNReal.tsum_le_tsum hpoint)
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum_ne] with ω hω
  filter_upwards [hω] with k hk
  simpa [shiftedDyadicBad] using hk

end Probability


section CentralBinomialBound

/-- A convenient elementary upper bound for the square of the central
binomial coefficient.  It yields the `O(1/n)` planar return-probability
estimate after diagonalizing the walk into two independent sign sums. -/
theorem succ_mul_centralBinom_sq_le_sixteen_pow : ∀ j : ℕ,
    (j + 1) * Nat.centralBinom j ^ 2 ≤ 16 ^ j := by
  intro j
  induction j with
  | zero => norm_num [Nat.centralBinom]
  | succ j ih =>
      have hrec := Nat.succ_mul_centralBinom_succ j
      have hsq := congrArg (fun x : ℕ ↦ x ^ 2) hrec
      have hpoly : (j + 2) * (2 * j + 1) ^ 2 ≤ 4 * (j + 1) ^ 3 := by nlinarith
      have hmul : (j + 1) ^ 2 *
            ((j + 2) * Nat.centralBinom (j + 1) ^ 2) ≤
          (j + 1) ^ 2 * 16 ^ (j + 1) := by
        calc
          (j + 1) ^ 2 * ((j + 2) * Nat.centralBinom (j + 1) ^ 2) =
              (j + 2) * ((j + 1) * Nat.centralBinom (j + 1)) ^ 2 := by ring
          _ = (j + 2) * (2 * (2 * j + 1) * Nat.centralBinom j) ^ 2 := by rw [hsq]
          _ = 4 * ((j + 2) * (2 * j + 1) ^ 2) * Nat.centralBinom j ^ 2 := by ring
          _ ≤ 4 * (4 * (j + 1) ^ 3) * Nat.centralBinom j ^ 2 := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hpoly) le_rfl
          _ = 16 * (j + 1) ^ 2 * ((j + 1) * Nat.centralBinom j ^ 2) := by ring
          _ ≤ 16 * (j + 1) ^ 2 * 16 ^ j := Nat.mul_le_mul_left _ ih
          _ = (j + 1) ^ 2 * 16 ^ (j + 1) := by rw [pow_succ]; ring
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        Nat.le_of_mul_le_mul_left hmul (by positivity)

theorem succ_mul_choose_sq_le_sixteen_pow (j : ℕ) :
    (j + 1) * ((2 * j).choose j) ^ 2 ≤ 16 ^ j := by
  simpa [Nat.centralBinom_eq_two_mul_choose] using
    succ_mul_centralBinom_sq_le_sixteen_pow j

/-- Cast-and-cancel form of a natural-number ratio bound in `ENNReal`. -/
theorem ennreal_div_le_inv_of_nat {a b c : ℕ} (hc : 0 < c) (hb : 0 < b)
    (h : c * a ≤ b) :
    (a : ENNReal) / (b : ENNReal) ≤ (c : ENNReal)⁻¹ := by
  rw [ENNReal.div_le_iff (by exact_mod_cast hb.ne') (by simp)]
  have hcast : (c : ENNReal) * a ≤ b := by exact_mod_cast h
  calc
    (a : ENNReal) = (c : ENNReal)⁻¹ * ((c : ENNReal) * a) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel] <;> simp [hc.ne']
    _ ≤ (c : ENNReal)⁻¹ * b := by gcongr
    _ = (c : ENNReal)⁻¹ * (b : ENNReal) := rfl

end CentralBinomialBound

end KacMoment
