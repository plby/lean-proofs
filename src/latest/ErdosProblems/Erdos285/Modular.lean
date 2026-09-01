import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.Data.ZMod.ValMinAbs
import UnitFractions.Fourier

/-!
# The modular subset-sum core of Martin's construction

This file isolates the finite cyclic-group argument used when eliminating a
prime-power factor from the denominator of a residual rational number.  The
objects being added are the inverses of the auxiliary denominators modulo the
prime power.

The first result below is the Cauchy--Davenport--Chowla branch of Martin's
subset-sum lemma: at least `n - 1` invertible residues modulo `n`, with the
choices indexed separately even when residues repeat, represent every residue
as a subset sum.  Keeping the indices separate is essential in the application
to distinct Egyptian-fraction denominators.
-/

namespace Erdos285.Modular

open scoped BigOperators
open Finset

noncomputable section

/-- The least-absolute-value representative of `h / m (mod n)`. -/
def centeredInverse (n h m : ℕ) : ℤ :=
  ((h : ZMod n) * (m : ZMod n)⁻¹).valMinAbs

/-- A finite fiber-counting lemma used in the pigeonhole part of Martin's
inverse-dispersion argument. -/
theorem card_le_card_mul_of_fiber_bound {α β : Type*}
    [Fintype β] [DecidableEq β] (S : Finset α) (bucket : α → β) (D : ℕ)
    (hfiber : ∀ b : β, (S.filter fun x ↦ bucket x = b).card ≤ D) :
    S.card ≤ Fintype.card β * D := by
  classical
  rw [card_eq_sum_card_fiberwise (t := univ) (f := bucket) (by simp)]
  calc
    ∑ b ∈ (univ : Finset β), (S.filter fun x ↦ bucket x = b).card
        ≤ ∑ _b ∈ (univ : Finset β), D := by
          exact sum_le_sum fun b _ ↦ hfiber b
    _ = Fintype.card β * D := by simp

/-- Exact finite form of the pigeonhole conclusion in Martin's modular
inverse-dispersion lemma.  The `bucket` is the integer
`(m * r_m - h) / n`; its source-specific fiber bound comes from counting
divisors with exactly `k` distinct prime factors. -/
theorem centeredInverse_dispersion_of_fiber_bound
    (n h R L D : ℕ) (M : Finset ℕ) (bucket : ℕ → Fin L)
    (hfiber : ∀ b : Fin L,
      ((M.filter fun m ↦ (centeredInverse n h m).natAbs ≤ R).filter
        fun m ↦ bucket m = b).card ≤ D)
    (hhalf : 2 * (L * D) ≤ M.card) :
    M.card ≤ 2 * (M.filter fun m ↦ R < (centeredInverse n h m).natAbs).card := by
  let bad := M.filter fun m ↦ (centeredInverse n h m).natAbs ≤ R
  have hbad : bad.card ≤ L * D := by
    have h := card_le_card_mul_of_fiber_bound bad bucket D hfiber
    simpa using h
  have hpartition := card_filter_add_card_filter_not
    (s := M) (p := fun m ↦ (centeredInverse n h m).natAbs ≤ R)
  change bad.card + (M.filter fun m ↦ ¬ (centeredInverse n h m).natAbs ≤ R).card =
    M.card at hpartition
  have hgood :
      (M.filter fun m ↦ ¬ (centeredInverse n h m).natAbs ≤ R).card =
        (M.filter fun m ↦ R < (centeredInverse n h m).natAbs).card := by
    congr 1
    ext m
    simp
  rw [hgood] at hpartition
  omega

/-- Multiplicity of a residue among all indexed inverse subset sums, embedded
in `ℂ` for Fourier inversion. -/
def inverseSubsetMass (n : ℕ) (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ K ∈ M.powerset,
    if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a then 1 else 0

theorem inverseSubsetMass_eq_card (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      ((M.powerset.filter fun K ↦
        K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a).card : ℂ) := by
  rw [inverseSubsetMass, ← sum_filter]
  simp

theorem inverseSubsetMass_ne_zero_iff (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a ≠ 0 ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  rw [inverseSubsetMass_eq_card]
  simp

/-- The Fourier transform of the inverse-subset multiplicity is Martin's
product `∏ (1 + e_n(-h / m))`. -/
theorem dft_inverseSubsetMass {n : ℕ} [NeZero n] (M : Finset ℕ) (h : ZMod n) :
    ZMod.dft (inverseSubsetMass n M) h =
      M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, inverseSubsetMass]
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  simp only [mul_ite, mul_one, mul_zero]
  have hinner (K : Finset ℕ) :
      (∑ j : ZMod n, if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = j then
        ZMod.stdAddChar (-(j * h)) else 0) =
          ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) := by
    let s := K.sum (fun m ↦ ((m : ZMod n)⁻¹))
    change (∑ j : ZMod n, if s = j then ZMod.stdAddChar (-(j * h)) else 0) = _
    have hfun :
        (fun j : ZMod n ↦ if s = j then ZMod.stdAddChar (-(j * h)) else 0) =
          fun j ↦ if j = s then ZMod.stdAddChar (-(j * h)) else 0 := by
      funext j
      by_cases heq : s = j
      · rw [if_pos heq, if_pos heq.symm]
      · rw [if_neg heq, if_neg (fun hjs ↦ heq hjs.symm)]
    rw [hfun]
    simp [s]
  have hchar (K : Finset ℕ) :
      ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) =
        K.prod fun m ↦ ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
    induction K using Finset.induction with
    | empty => simp
    | @insert m K hm ih =>
        rw [sum_insert hm, prod_insert hm, ← ih, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  simp_rw [hinner, hchar]
  exact UnitFractions.sum_powerset_prod M _

/-- Fourier inversion formula for the exact subset count. -/
theorem inverseSubsetMass_fourier {n : ℕ} [NeZero n] (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      (n : ℂ)⁻¹ * ∑ h : ZMod n,
        ZMod.stdAddChar (h * a) *
          (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))) := by
  have hinv := congr_fun (ZMod.dft.symm_apply_apply (inverseSubsetMass n M)) a
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, dft_inverseSubsetMass] at hinv
  exact hinv.symm

/-- Contribution of all nonzero frequencies in the inverse-subset Fourier
formula. -/
def inverseSubsetFourierError (n : ℕ) [NeZero n] (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
    ZMod.stdAddChar (h * a) *
      (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))

/-- If the nonzero Fourier modes have total norm smaller than the zero mode,
then every prescribed residue has an inverse subset-sum representation. -/
theorem inverse_subset_sum_surjective_of_fourier_error {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n)
    (herror : ‖inverseSubsetFourierError n M a‖ < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply (inverseSubsetMass_ne_zero_iff n M a).mp
  rw [inverseSubsetMass_fourier]
  apply mul_ne_zero
  · exact inv_ne_zero (by exact_mod_cast NeZero.ne n)
  · have hsplit :
        (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card + inverseSubsetFourierError n M a := by
        change (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card +
            ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
              ZMod.stdAddChar (h * a) *
                (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
        rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))]
        rw [add_comm]
        congr 1
        simp
        norm_num
    rw [hsplit]
    intro hzero
    have herr_eq : inverseSubsetFourierError n M a = -((2 : ℂ) ^ M.card) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hzero
    have hnorm : ‖inverseSubsetFourierError n M a‖ = (2 : ℝ) ^ M.card := by
      rw [herr_eq, norm_neg, norm_pow]
      norm_num
    linarith

/-- Pointwise Fourier coefficient control implies the total-error hypothesis.
This is the exact analytic interface used after Martin's inverse-dispersion
estimate bounds each nonzero product. -/
theorem inverse_subset_sum_surjective_of_fourier_bound {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n) (E : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ E)
    (hdom : ((n - 1 : ℕ) : ℝ) * E < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective_of_fourier_error M a
  calc
    ‖inverseSubsetFourierError n M a‖
        ≤ ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
            ‖ZMod.stdAddChar (h * a) *
              (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))‖ :=
          by
            simpa only [inverseSubsetFourierError] using
              norm_sum_le (univ.erase 0 : Finset (ZMod n)) (fun h ↦
                ZMod.stdAddChar (h * a) *
                  (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))))
    _ ≤ ∑ _h ∈ (univ.erase 0 : Finset (ZMod n)), E := by
          apply sum_le_sum
          intro h hh
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hcoeff h (ne_of_mem_erase hh)
    _ = ((n - 1 : ℕ) : ℝ) * E := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ (0 : ZMod n)), card_univ,
            ZMod.card]
    _ < (2 : ℝ) ^ M.card := hdom

/-- Residues obtained by summing inverses of a subset of the indexed integers. -/
def inverseSubsetSums (n : ℕ) (M : Finset ℕ) : Finset (ZMod n) :=
  M.powerset.image fun K : Finset ℕ ↦ K.sum fun m ↦ ((m : ZMod n)⁻¹)

@[simp] theorem inverseSubsetSums_empty (n : ℕ) : inverseSubsetSums n ∅ = {0} := by
  simp [inverseSubsetSums]

theorem mem_inverseSubsetSums_iff {n : ℕ} {M : Finset ℕ} {a : ZMod n} :
    a ∈ inverseSubsetSums n M ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  simp [inverseSubsetSums]

theorem inverseSubsetSums_insert {n m : ℕ} {M : Finset ℕ} (hm : m ∉ M) :
    inverseSubsetSums n (insert m M) =
      inverseSubsetSums n M ∪
        (inverseSubsetSums n M).image (fun x ↦ ((m : ZMod n)⁻¹) + x) := by
  ext a
  constructor
  · intro ha
    obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
    by_cases hmem : m ∈ K
    · rw [mem_union]
      right
      refine mem_image.mpr ⟨(K.erase m).sum (fun x ↦ ((x : ZMod n)⁻¹)), ?_, ?_⟩
      · apply mem_inverseSubsetSums_iff.mpr
        refine ⟨K.erase m, ?_, rfl⟩
        intro x hx
        have hxK : x ∈ K := mem_of_mem_erase hx
        have hxInsert := hK hxK
        rcases mem_insert.mp hxInsert with hxm | hxM
        · exact False.elim ((ne_of_mem_erase hx) hxm)
        · exact hxM
      · simpa [add_comm] using sum_erase_add K (fun x ↦ ((x : ZMod n)⁻¹)) hmem
    · rw [mem_union]
      left
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨K, ?_, rfl⟩
      intro x hx
      rcases mem_insert.mp (hK hx) with hxm | hxM
      · exact False.elim (hmem (hxm ▸ hx))
      · exact hxM
  · intro ha
    rw [mem_union] at ha
    rcases ha with ha | ha
    · obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
      apply mem_inverseSubsetSums_iff.mpr
      exact ⟨K, hK.trans (subset_insert m M), rfl⟩
    · obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
      obtain ⟨K, hK, hxK⟩ := mem_inverseSubsetSums_iff.mp hx
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨insert m K, ?_, ?_⟩
      · exact insert_subset_insert m hK
      · rw [sum_insert]
        · rw [hxK, hxa]
        · exact fun h ↦ hm (hK h)

/-- An invertible residue additively generates the cyclic group `ZMod n`. -/
theorem nsmul_unit_hits {n : ℕ} [NeZero n] {u y : ZMod n} (hu : IsUnit u) :
    ∃ k : ℕ, k • u = y := by
  let k : ℕ := (y * u⁻¹).val
  refine ⟨k, ?_⟩
  simp only [nsmul_eq_mul]
  rw [show (k : ZMod n) = y * u⁻¹ by simp [k]]
  rw [mul_assoc, ZMod.inv_mul_of_unit u hu, mul_one]

/-- A nonempty proper subset cannot be stable under translation by a unit. -/
theorem unit_translate_not_subset {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A) (hproper : A ≠ univ) :
    ¬ A.image (fun x ↦ u + x) ⊆ A := by
  intro hstable
  have hnsmul : ∀ k : ℕ, k • u ∈ A := by
    intro k
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
        apply hstable
        exact mem_image.mpr ⟨k • u, ih, by
          simp only [nsmul_eq_mul, Nat.cast_succ]
          ring⟩
  apply hproper
  apply eq_univ_of_forall
  intro y
  obtain ⟨k, hk⟩ := nsmul_unit_hits (y := y) hu
  rw [← hk]
  exact hnsmul k

theorem card_lt_card_union_unit_translate {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A)
    (hcard : A.card < n) :
    A.card < (A ∪ A.image (fun x ↦ u + x)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, ?_⟩
  intro heq
  have hproper : A ≠ univ := by
    intro hA
    have : A.card = n := by simp [hA]
    omega
  exact unit_translate_not_subset hu hzero hproper (by
    intro x hx
    have hx' : x ∈ A ∪ A.image (fun z ↦ u + z) := mem_union_right A hx
    rw [← heq] at hx'
    exact hx')

/-- Quantitative Chowla growth for the indexed inverse subset sums. -/
theorem min_card_succ_le_card_inverseSubsetSums (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n) :
    min (M.card + 1) n ≤ (inverseSubsetSums n M).card := by
  induction M using Finset.induction with
  | empty => simp
  | @insert m M hm ih =>
      have hcoprimeM : ∀ x ∈ M, Nat.Coprime x n :=
        fun x hx ↦ hcoprime x (mem_insert_of_mem hx)
      have hcm := ih hcoprimeM
      rw [inverseSubsetSums_insert hm]
      have hunit0 : IsUnit (m : ZMod n) :=
        (ZMod.isUnit_iff_coprime m n).mpr (hcoprime m (mem_insert_self m M))
      have hunit : IsUnit ((m : ZMod n)⁻¹) :=
        isUnit_of_dvd_one ⟨(m : ZMod n), (ZMod.inv_mul_of_unit (m : ZMod n) hunit0).symm⟩
      have hzero : 0 ∈ inverseSubsetSums n M := by
        apply mem_inverseSubsetSums_iff.mpr
        exact ⟨∅, empty_subset _, by simp⟩
      by_cases hfull : n ≤ (inverseSubsetSums n M).card
      · have heq : (inverseSubsetSums n M).card = n := by
          apply le_antisymm
          · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
          · exact hfull
        have hset : inverseSubsetSums n M = univ := by
          apply eq_univ_of_card
          simpa [ZMod.card] using heq
        rw [hset, Finset.union_eq_left.mpr (subset_univ _), card_univ, ZMod.card]
        simp only [card_insert_of_notMem hm]
        omega
      · have hlt : (inverseSubsetSums n M).card < n := Nat.lt_of_not_ge hfull
        have hgrowth := card_lt_card_union_unit_translate hunit hzero hlt
        simp only [card_insert_of_notMem hm]
        omega

/-- If the indexed set has at least `n - 1` elements, every residue modulo
`n` is a sum of inverses of a subset.  Martin invokes the slightly weaker
hypothesis `n ≤ M.card` in this branch. -/
theorem inverse_subset_sum_surjective (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card + 1) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  have hle := min_card_succ_le_card_inverseSubsetSums n M hcoprime
  have hcount : n ≤ (inverseSubsetSums n M).card := by
    simpa [min_eq_right hcard] using hle
  have hall : inverseSubsetSums n M = univ := by
    apply eq_univ_of_card
    apply le_antisymm
    · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
    · rw [ZMod.card]
      exact hcount
  apply mem_inverseSubsetSums_iff.mp
  simp [hall]

/-- Martin's stated large-cardinality branch, with the paper's hypothesis
`n ≤ |M|` rather than the slightly sharper cutoff proved above. -/
theorem inverse_subset_sum_surjective_of_card (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective n M hcoprime (a := a)
  omega

/-- Prime-power specialization of the modular elimination step.  It is enough
to check that the underlying prime divides none of the auxiliary factors. -/
theorem primePower_inverse_subset_sum_surjective {p ν : ℕ} (hp : p.Prime)
    (M : Finset ℕ) (hnotdvd : ∀ m ∈ M, ¬ p ∣ m)
    (hcard : p ^ ν ≤ M.card + 1) (a : ZMod (p ^ ν)) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = a := by
  let _ : NeZero (p ^ ν) := ⟨pow_ne_zero ν hp.ne_zero⟩
  apply inverse_subset_sum_surjective (p ^ ν) M (a := a) ?_ hcard
  intro m hm
  exact hp.coprime_pow_of_not_dvd (hnotdvd m hm)

/-- The exact hypothesis used when Martin dismisses the `|M| ≥ q` case of
the large-prime-power elimination lemma. -/
theorem primePower_inverse_subset_sum_surjective_of_card {p ν : ℕ} (hp : p.Prime)
    (M : Finset ℕ) (hnotdvd : ∀ m ∈ M, ¬ p ∣ m)
    (hcard : p ^ ν ≤ M.card) (a : ZMod (p ^ ν)) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = a := by
  apply primePower_inverse_subset_sum_surjective hp M hnotdvd (a := a)
  omega

end

end Erdos285.Modular
