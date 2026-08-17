import ErdosProblems.Erdos49.PrimaryPacking
import ErdosProblems.Erdos49.Smooth
import ErdosProblems.Erdos49.Analytic

/-!
# Canonical primary representations

For the primary part every integer is `d * p` with `d ≤ D` and `p > D`.
This representation is unique.  We use that uniqueness to attach functions
`primaryD` and `primaryP` to the finite primary set and then prove the
ratio-labelled interval hulls are pairwise disjoint.
-/

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def PrimaryRep (N L D n d p : ℕ) : Prop :=
  1 ≤ d ∧ d ≤ D ∧ Smooth L d ∧ p.Prime ∧ D < p ∧
    8 * D ^ 2 ≤ p ∧ n = d * p ∧ n ≤ N

def primarySet (N L D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ ∃ d p, PrimaryRep N L D n d p

@[simp] lemma mem_primarySet {N L D n : ℕ} :
    n ∈ primarySet N L D ↔
      1 ≤ n ∧ n ≤ N ∧ ∃ d p, PrimaryRep N L D n d p := by
  simp [primarySet, and_assoc]

private def primaryWitness (N L D n : ℕ) : ℕ × ℕ :=
  if h : ∃ z : ℕ × ℕ, PrimaryRep N L D n z.1 z.2 then
    Classical.choose h
  else (1, 2)

def primaryD (N L D n : ℕ) : ℕ := (primaryWitness N L D n).1
def primaryP (N L D n : ℕ) : ℕ := (primaryWitness N L D n).2

lemma primaryWitness_spec {N L D n : ℕ} (hn : n ∈ primarySet N L D) :
    PrimaryRep N L D n (primaryD N L D n) (primaryP N L D n) := by
  have hex : ∃ z : ℕ × ℕ, PrimaryRep N L D n z.1 z.2 := by
    obtain ⟨d, p, hrep⟩ := (mem_primarySet.mp hn).2.2
    exact ⟨(d, p), hrep⟩
  simpa [primaryD, primaryP, primaryWitness, hex] using
    (Classical.choose_spec hex)

lemma primaryRep_unique {N L D n d p e q : ℕ}
    (hdp : PrimaryRep N L D n d p) (heq : PrimaryRep N L D n e q) :
    d = e ∧ p = q := by
  rcases hdp with ⟨hd1, hdD, hds, hp, hDp, hpLarge, hnDP, hnN⟩
  rcases heq with ⟨he1, heD, hes, hq, hDq, hqLarge, hnEQ, hnN'⟩
  have hpne : ¬p ∣ e := by
    intro hpe
    have hp_le_e := Nat.le_of_dvd (by omega) hpe
    omega
  have hpq : p ∣ q := by
    have hp_prod : p ∣ e * q := by
      rw [← hnEQ, hnDP]
      exact dvd_mul_left p d
    exact (hp.dvd_mul.mp hp_prod).resolve_left hpne
  have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  subst q
  have hmul : d * p = e * p := by
    rw [← hnDP, ← hnEQ]
  exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos hmul, rfl⟩

lemma primaryD_eq_of_rep {N L D n d p : ℕ}
    (hn : n ∈ primarySet N L D) (hrep : PrimaryRep N L D n d p) :
    primaryD N L D n = d :=
  (primaryRep_unique (primaryWitness_spec hn) hrep).1

lemma primaryP_eq_of_rep {N L D n d p : ℕ}
    (hn : n ∈ primarySet N L D) (hrep : PrimaryRep N L D n d p) :
    primaryP N L D n = p :=
  (primaryRep_unique (primaryWitness_spec hn) hrep).2

def quotientBucket (W n : ℕ) : ℕ := n / W

lemma quotientBucket_bounds {W n : ℕ} (hW : 0 < W) :
    quotientBucket W n * W ≤ n ∧
      n < quotientBucket W n * W + W := by
  constructor
  · exact Nat.div_mul_le_self n W
  · dsimp only [quotientBucket]
    calc
      n = W * (n / W) + n % W := (Nat.div_add_mod n W).symm
      _ = n / W * W + n % W := by rw [Nat.mul_comm W]
      _ < n / W * W + W := Nat.add_lt_add_left (Nat.mod_lt n hW) _

lemma primary_not_dvd_D {N L D n : ℕ} (hn : n ∈ primarySet N L D) :
    ¬ primaryP N L D n ∣ primaryD N L D n := by
  rcases primaryWitness_spec hn with
    ⟨hd1, hdD, hds, hp, hDp, hpLarge, hnfac, hnN⟩
  intro hdiv
  have := Nat.le_of_dvd (by omega) hdiv
  omega

/-- Monotonicity plus the arithmetic ratio separation orders any two
different ratio cells inside the same sufficiently short bucket. -/
lemma primary_cell_order
    {N L D W : ℕ} {A : Finset ℕ}
    (hAprim : A ⊆ primarySet N L D)
    (hmono : TotientMonotoneOn A)
    (hD : 1 ≤ D) (hW : 0 < W)
    (hshort : ∀ n ∈ A,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2))
    {n m : ℕ} (hn : n ∈ A) (hm : m ∈ A)
    (hsame : quotientBucket W n = quotientBucket W m)
    (hratio : totientRatio (primaryD N L D n) <
      totientRatio (primaryD N L D m)) : n < m := by
  have hnP := hAprim hn
  have hmP := hAprim hm
  rcases primaryWitness_spec hnP with
    ⟨hnd1, hndD, hnds, hnp, hDnp, hnpLarge, hnfac, hnN⟩
  rcases primaryWitness_spec hmP with
    ⟨hmd1, hmdD, hmds, hmp, hDmp, hmpLarge, hmfac, hmN⟩
  have hnb := quotientBucket_bounds (n := n) hW
  have hmb := quotientBucket_bounds (n := m) hW
  let B : ℝ := (quotientBucket W n * W : ℕ)
  have hB : 0 < B := by
    have hs := hshort n hn
    have hden : 0 < 4 * (D : ℝ) ^ 2 := by positivity
    have hWreal : 0 < (W : ℝ) := by exact_mod_cast hW
    dsimp only [B]
    by_contra hnot
    have : ((quotientBucket W n * W : ℕ) : ℝ) ≤ 0 := le_of_not_gt hnot
    have : ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hden.le
    linarith
  have hnlow : B ≤ (primaryD N L D n * primaryP N L D n : ℕ) := by
    rw [← hnfac]
    change (((quotientBucket W n * W : ℕ) : ℝ)) ≤ (n : ℝ)
    exact_mod_cast hnb.1
  have hnhigh : (primaryD N L D n * primaryP N L D n : ℕ) ≤ B + W := by
    rw [← hnfac]
    change (n : ℝ) ≤ (((quotientBucket W n * W : ℕ) : ℝ)) + (W : ℝ)
    exact_mod_cast hnb.2.le
  have hmlow : B ≤ (primaryD N L D m * primaryP N L D m : ℕ) := by
    rw [← hmfac]
    rw [← hsame] at hmb
    change (((quotientBucket W n * W : ℕ) : ℝ)) ≤ (m : ℝ)
    exact_mod_cast hmb.1
  have hmhigh : (primaryD N L D m * primaryP N L D m : ℕ) ≤ B + W := by
    rw [← hmfac]
    rw [← hsame] at hmb
    change (m : ℝ) ≤ (((quotientBucket W n * W : ℕ) : ℝ)) + (W : ℝ)
    exact_mod_cast hmb.2.le
  have hphi := primary_totient_lt_of_ratio_lt
    hD (by omega) (by omega) hndD hmdD
    hnp hmp
    (primary_not_dvd_D hnP) (primary_not_dvd_D hmP)
    hratio hB (by positivity : (0 : ℝ) ≤ W) (hshort n hn)
    hnlow hnhigh hmlow hmhigh
    hnpLarge hmpLarge
  by_contra hnot
  have hmn : m ≤ n := Nat.le_of_not_gt hnot
  have hmon := hmono hm hn hmn
  rw [hnfac, hmfac] at hmon
  exact (not_lt_of_ge hmon) hphi

/-- The occupied primary hulls are pairwise disjoint. -/
theorem primary_hulls_pairwiseDisjoint
    {N L D W : ℕ} {A : Finset ℕ}
    (hAprim : A ⊆ primarySet N L D)
    (hmono : TotientMonotoneOn A)
    (hD : 1 ≤ D) (hW : 0 < W)
    (hshort : ∀ n ∈ A,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2)) :
    ((primaryKeys A (quotientBucket W) (primaryD N L D) :
        Finset (ℕ × ℚ)) : Set (ℕ × ℚ)).PairwiseDisjoint
      (fun k ↦ intervalHull
        (primaryCell A (quotientBucket W) (primaryD N L D) k)) := by
  intro k hk l hl hkl
  let cell := primaryCell A (quotientBucket W) (primaryD N L D)
  by_cases hb : k.1 = l.1
  · have hq : k.2 ≠ l.2 := by
      intro heq
      exact hkl (Prod.ext hb heq)
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact intervalHull_disjoint_of_lt fun n hn m hm ↦ by
        have hnk := (Finset.mem_filter.mp hn).2
        have hml := (Finset.mem_filter.mp hm).2
        have hbn : quotientBucket W n = k.1 := by
          simpa [primaryKey] using congrArg Prod.fst hnk
        have hbm : quotientBucket W m = l.1 := by
          simpa [primaryKey] using congrArg Prod.fst hml
        have hqn : totientRatio (primaryD N L D n) = k.2 := by
          simpa [primaryKey] using congrArg Prod.snd hnk
        have hqm : totientRatio (primaryD N L D m) = l.2 := by
          simpa [primaryKey] using congrArg Prod.snd hml
        apply primary_cell_order hAprim hmono hD hW hshort
          (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hm).1
        · exact hbn.trans (hb.trans hbm.symm)
        · rw [hqn, hqm]
          exact hq
    · exact (intervalHull_disjoint_of_lt fun m hm n hn ↦ by
        have hnk := (Finset.mem_filter.mp hn).2
        have hml := (Finset.mem_filter.mp hm).2
        have hbn : quotientBucket W n = k.1 := by
          simpa [primaryKey] using congrArg Prod.fst hnk
        have hbm : quotientBucket W m = l.1 := by
          simpa [primaryKey] using congrArg Prod.fst hml
        have hqn : totientRatio (primaryD N L D n) = k.2 := by
          simpa [primaryKey] using congrArg Prod.snd hnk
        have hqm : totientRatio (primaryD N L D m) = l.2 := by
          simpa [primaryKey] using congrArg Prod.snd hml
        apply primary_cell_order hAprim hmono hD hW hshort
          (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hn).1
        · exact hbm.trans (hb.symm.trans hbn.symm)
        · rw [hqm, hqn]
          exact hq).symm
  · rcases lt_or_gt_of_ne hb with hb | hb
    · exact intervalHull_disjoint_of_lt fun n hn m hm ↦ by
        have hnk := (Finset.mem_filter.mp hn).2
        have hml := (Finset.mem_filter.mp hm).2
        have hbn : quotientBucket W n = k.1 := by
          simpa [primaryKey] using congrArg Prod.fst hnk
        have hbm : quotientBucket W m = l.1 := by
          simpa [primaryKey] using congrArg Prod.fst hml
        have hnb := quotientBucket_bounds (n := n) hW
        have hmb := quotientBucket_bounds (n := m) hW
        rw [hbn] at hnb
        rw [hbm] at hmb
        calc
          n < k.1 * W + W := hnb.2
          _ = (k.1 + 1) * W := by simp [add_mul]
          _ ≤ l.1 * W := Nat.mul_le_mul_right W (by omega)
          _ ≤ m := hmb.1
    · exact (intervalHull_disjoint_of_lt fun m hm n hn ↦ by
        have hnk := (Finset.mem_filter.mp hn).2
        have hml := (Finset.mem_filter.mp hm).2
        have hbn : quotientBucket W n = k.1 := by
          simpa [primaryKey] using congrArg Prod.fst hnk
        have hbm : quotientBucket W m = l.1 := by
          simpa [primaryKey] using congrArg Prod.fst hml
        have hnb := quotientBucket_bounds (n := n) hW
        have hmb := quotientBucket_bounds (n := m) hW
        rw [hbn] at hnb
        rw [hbm] at hmb
        calc
          m < l.1 * W + W := hmb.2
          _ = (l.1 + 1) * W := by simp [add_mul]
          _ ≤ k.1 * W := Nat.mul_le_mul_right W (by omega)
          _ ≤ n := hnb.1).symm

/-- A fixed-denominator slice of one primary cell injects into the primes in
the quotient of its integer hull. -/
lemma primary_slice_card_le_primeInterval
    {N L D W : ℕ} {A : Finset ℕ}
    (hAprim : A ⊆ primarySet N L D)
    (k : ℕ × ℚ) {d₀ : ℕ} (hd₀ : 1 ≤ d₀) :
    let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
    let slice := cell.filter fun n ↦ primaryD N L D n = d₀
    slice.card ≤ if hcell : cell.Nonempty then
      (Analytic.primeInterval (cell.min' hcell / d₀) (cell.max' hcell / d₀)).card
    else 0 := by
  dsimp only
  let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
  let slice := cell.filter fun n ↦ primaryD N L D n = d₀
  by_cases hs : slice.Nonempty
  · have hc : cell.Nonempty := by
      obtain ⟨n, hn⟩ := hs
      exact ⟨n, (Finset.mem_filter.mp hn).1⟩
    rw [dif_pos hc]
    let f : ℕ → ℕ := primaryP N L D
    have hinj : Set.InjOn f (slice : Set ℕ) := by
      intro n hn m hm hpm
      have hns := Finset.mem_filter.mp hn
      have hms := Finset.mem_filter.mp hm
      have hnP := hAprim (Finset.mem_filter.mp hns.1).1
      have hmP := hAprim (Finset.mem_filter.mp hms.1).1
      rcases primaryWitness_spec hnP with
        ⟨hnd1, hndD, hnds, hnp, hDnp, hnpL, hnfac, hnN⟩
      rcases primaryWitness_spec hmP with
        ⟨hmd1, hmdD, hmds, hmp, hDmp, hmpL, hmfac, hmN⟩
      rw [hns.2] at hnfac
      change primaryP N L D n = primaryP N L D m at hpm
      rw [hms.2] at hmfac
      rw [← hpm] at hmfac
      exact hnfac.trans hmfac.symm
    have hcard : slice.card = (slice.image f).card := by
      symm
      exact Finset.card_image_iff.mpr fun n hn m hm hnm ↦ hinj hn hm hnm
    rw [hcard]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    have hns := Finset.mem_filter.mp hn
    have hnc := hns.1
    have hnP := hAprim (Finset.mem_filter.mp hnc).1
    rcases primaryWitness_spec hnP with
      ⟨hnd1, hndD, hnds, hnp, hDnp, hnpL, hnfac, hnN⟩
    have hdeq := hns.2
    have hmin : cell.min' hc ≤ d₀ * primaryP N L D n := by
      rw [← hdeq, ← hnfac]
      exact cell.min'_le n hnc
    have hmax : d₀ * primaryP N L D n ≤ cell.max' hc := by
      rw [← hdeq, ← hnfac]
      exact cell.le_max' n hnc
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · apply Nat.div_le_of_le_mul
        simpa [mul_comm] using hmin
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < d₀)).2
          (by simpa [mul_comm] using hmax)
    · exact hnp
  · have hs0 : slice = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change slice.card ≤ _
    rw [hs0]
    exact Nat.zero_le _

/-- Primary packing with the only remaining input stated as an interval-prime
bound for each fixed-denominator cell. -/
theorem primary_packing_from_interval_bound
    {N L D W : ℕ} {A : Finset ℕ} {K E : ℝ}
    (hAprim : A ⊆ primarySet N L D)
    (hmono : TotientMonotoneOn A)
    (hD : 1 ≤ D) (hW : 0 < W)
    (hshort : ∀ n ∈ A,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2))
    (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hinterval : ∀ k ∈ primaryKeys A (quotientBucket W) (primaryD N L D),
      ∀ d₀ ∈ ratioFibre D k.2,
      let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
      ((if hcell : cell.Nonempty then
          (Analytic.primeInterval (cell.min' hcell / d₀)
            (cell.max' hcell / d₀)).card else 0 : ℕ) : ℝ) ≤
        K * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) + E) :
    (A.card : ℝ) ≤ K * N +
      ((primaryKeys A (quotientBucket W) (primaryD N L D)).card : ℝ) * D * E := by
  apply primary_packing_bound
    (A := A) (bucket := quotientBucket W) (d := primaryD N L D)
    (K := K) (E := E)
  · intro n hn
    have hmem := mem_primarySet.mp (hAprim hn)
    exact Finset.mem_Icc.mpr ⟨hmem.1, hmem.2.1⟩
  · intro n hn
    have hrep := primaryWitness_spec (hAprim hn)
    exact ⟨hrep.1, hrep.2.1⟩
  · exact hK
  · exact hE
  · exact primary_hulls_pairwiseDisjoint hAprim hmono hD hW hshort
  · intro k hk d₀ hd₀
    have hs := primary_slice_card_le_primeInterval (W := W) hAprim k
      (mem_ratioFibre.mp hd₀).1
    have hsR :
        (((primaryCell A (quotientBucket W) (primaryD N L D) k).filter
          fun n ↦ primaryD N L D n = d₀).card : ℝ) ≤
        ((if hcell :
            (primaryCell A (quotientBucket W) (primaryD N L D) k).Nonempty then
          (Analytic.primeInterval
            ((primaryCell A (quotientBucket W) (primaryD N L D) k).min' hcell / d₀)
            ((primaryCell A (quotientBucket W) (primaryD N L D) k).max' hcell / d₀)).card
          else 0 : ℕ) : ℝ) := by
      exact_mod_cast hs
    exact hsR.trans (hinterval k hk d₀ hd₀)

/-- Every occupied primary cell lies inside one additive bucket, so its
integer hull has at most the bucket width. -/
lemma primaryCell_intervalHull_card_le
    {N L D W : ℕ} {A : Finset ℕ} (hW : 0 < W) (k : ℕ × ℚ) :
    (intervalHull
      (primaryCell A (quotientBucket W) (primaryD N L D) k)).card ≤ W := by
  let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
  change (intervalHull cell).card ≤ W
  by_cases hc : cell.Nonempty
  · have hminMem := cell.min'_mem hc
    have hmaxMem := cell.max'_mem hc
    have hminKey := (Finset.mem_filter.mp hminMem).2
    have hmaxKey := (Finset.mem_filter.mp hmaxMem).2
    have hminBucket : quotientBucket W (cell.min' hc) = k.1 := by
      simpa [primaryKey] using congrArg Prod.fst hminKey
    have hmaxBucket : quotientBucket W (cell.max' hc) = k.1 := by
      simpa [primaryKey] using congrArg Prod.fst hmaxKey
    have hminBounds := quotientBucket_bounds (n := cell.min' hc) hW
    have hmaxBounds := quotientBucket_bounds (n := cell.max' hc) hW
    rw [hminBucket] at hminBounds
    rw [hmaxBucket] at hmaxBounds
    rw [intervalHull, dif_pos hc]
    simp only [Nat.card_Icc]
    omega
  · simp [intervalHull, hc]

/-- Dividing the endpoints of an integer hull by a positive denominator
enlarges its inclusive length by at most two beyond the expected scaled
length. -/
lemma div_hull_width_le {a b d H : ℕ} (hab : a ≤ b) (hd : 0 < d)
    (hH : b + 1 - a ≤ H) :
    b / d - (a / d - 1) ≤ H / d + 2 := by
  have hab' : b = a + (b - a) := by omega
  have hadd := Nat.add_div_le_div_add_div_add_one a (b - a) d
  have hdelta : b - a ≤ H := by omega
  have hdiv : (b - a) / d ≤ H / d := Nat.div_le_div_right hdelta
  have hv : b / d ≤ a / d + H / d + 1 := by
    rw [hab']
    exact hadd.trans (by omega)
  rw [Nat.sub_le_iff_le_add]
  exact hv.trans (by omega)

/-- The quotient interval occurring in a fixed-denominator primary slice has
length controlled by the hull length divided by that denominator. -/
lemma primary_quotient_width_le
    {N L D W : ℕ} {A : Finset ℕ} (k : ℕ × ℚ)
    {d₀ : ℕ} (hd₀ : 0 < d₀)
    (hc : (primaryCell A (quotientBucket W) (primaryD N L D) k).Nonempty) :
    let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
    cell.max' hc / d₀ - (cell.min' hc / d₀ - 1) ≤
      (intervalHull cell).card / d₀ + 2 := by
  dsimp only
  apply div_hull_width_le
    ((primaryCell A (quotientBucket W) (primaryD N L D) k).min'_le_max' hc) hd₀
  simp [intervalHull, hc]

/-- There are at most `N / W + 1` additive buckets and at most `D`
denominator-ratio labels. -/
lemma primaryKeys_card_le
    {N L D W : ℕ} {A : Finset ℕ}
    (hAprim : A ⊆ primarySet N L D) (_hW : 0 < W) :
    (primaryKeys A (quotientBucket W) (primaryD N L D)).card ≤
      (N / W + 1) * D := by
  let buckets := Finset.range (N / W + 1)
  let ratios := (Finset.Icc 1 D).image totientRatio
  have hsub : primaryKeys A (quotientBucket W) (primaryD N L D) ⊆
      buckets.product ratios := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hnP := hAprim hn
    have hnN := (mem_primarySet.mp hnP).2.1
    have hd := primaryWitness_spec hnP
    apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.div_le_div_right hnN
    · apply Finset.mem_image.mpr
      exact ⟨primaryD N L D n, Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩, rfl⟩
  apply (Finset.card_le_card hsub).trans
  calc
    (buckets.product ratios).card = buckets.card * ratios.card :=
      Finset.card_product buckets ratios
    _ ≤ buckets.card * D := Nat.mul_le_mul_left _
      (Finset.card_image_le.trans_eq (card_Icc_one D))
    _ = (N / W + 1) * D := by simp [buckets]

/-- A uniform theta error and a common lower bound for the logarithm turn the
prime interval attached to one primary slice into the exact affine estimate
needed by `primary_packing_from_interval_bound`. -/
lemma primary_primeInterval_bound
    {N L D W : ℕ} {A : Finset ℕ} (k : ℕ × ℚ) {d₀ : ℕ}
    (hd₀ : 0 < d₀) {ell Err : ℝ} (hell : 0 < ell) (hErr : 0 ≤ Err)
    (hdata : ∀ hc :
      (primaryCell A (quotientBucket W) (primaryD N L D) k).Nonempty,
      let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
      let u := cell.min' hc / d₀
      let v := cell.max' hc / d₀
      1 < u ∧ ell ≤ Real.log u ∧
        |Chebyshev.theta ((u - 1 : ℕ) : ℝ) - (u - 1 : ℕ)| ≤ Err ∧
        |Chebyshev.theta v - v| ≤ Err) :
    let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
    ((if hc : cell.Nonempty then
        (Analytic.primeInterval (cell.min' hc / d₀)
          (cell.max' hc / d₀)).card else 0 : ℕ) : ℝ) ≤
      (1 / ell) * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) +
        (2 + 2 * Err) / ell := by
  dsimp only
  let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
  change ((if hc : cell.Nonempty then
      (Analytic.primeInterval (cell.min' hc / d₀)
        (cell.max' hc / d₀)).card else 0 : ℕ) : ℝ) ≤
    (1 / ell) * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) +
      (2 + 2 * Err) / ell
  by_cases hc : cell.Nonempty
  · rw [dif_pos hc]
    let u := cell.min' hc / d₀
    let v := cell.max' hc / d₀
    rcases hdata hc with ⟨hu, hellu, hthetaU, hthetaV⟩
    have huv : u ≤ v := Nat.div_le_div_right (cell.min'_le_max' hc)
    have hpnt := Analytic.primeInterval_card_real_upper hu huv hthetaU hthetaV
    have hwidthNat : v - (u - 1) ≤ (intervalHull cell).card / d₀ + 2 := by
      exact primary_quotient_width_le k hd₀ hc
    have hwidthReal : (v : ℝ) - (u - 1 : ℕ) ≤
        (((intervalHull cell).card / d₀ : ℕ) : ℝ) + 2 := by
      have hu1v : u - 1 ≤ v := (Nat.sub_le u 1).trans huv
      rw [← Nat.cast_sub hu1v]
      exact_mod_cast hwidthNat
    have hnum : (v : ℝ) - (u - 1 : ℕ) + Err + Err ≤
        (((intervalHull cell).card / d₀ : ℕ) : ℝ) + 2 + 2 * Err := by
      linarith
    have hlogu : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
    have hdiv :
        ((v : ℝ) - (u - 1 : ℕ) + Err + Err) / Real.log u ≤
          ((((intervalHull cell).card / d₀ : ℕ) : ℝ) + 2 + 2 * Err) /
            ell := by
      exact div_le_div₀ (by positivity) hnum hell hellu
    apply hpnt.trans (hdiv.trans ?_)
    have hcastDiv :
        (((intervalHull cell).card / d₀ : ℕ) : ℝ) ≤
          ((intervalHull cell).card : ℝ) / (d₀ : ℝ) :=
      Nat.cast_div_le
    have hInv : 0 ≤ 1 / ell := by positivity
    calc
      ((((intervalHull cell).card / d₀ : ℕ) : ℝ) + 2 + 2 * Err) / ell =
          (1 / ell) * (((intervalHull cell).card / d₀ : ℕ) : ℝ) +
            (2 + 2 * Err) / ell := by field_simp; ring
      _ ≤ (1 / ell) * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) +
            (2 + 2 * Err) / ell := by
        have hmul :
            (1 / ell) * (((intervalHull cell).card / d₀ : ℕ) : ℝ) ≤
              (1 / ell) * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) := by
          calc
            (1 / ell) * (((intervalHull cell).card / d₀ : ℕ) : ℝ) ≤
                (1 / ell) * (((intervalHull cell).card : ℝ) / (d₀ : ℝ)) :=
              mul_le_mul_of_nonneg_left hcastDiv hInv
            _ = (1 / ell) * ((intervalHull cell).card : ℝ) / (d₀ : ℝ) := by
              ring
        exact add_le_add hmul le_rfl
  · rw [dif_neg hc]
    norm_num only [Nat.cast_zero]
    apply add_nonneg
    · positivity
    · exact div_nonneg (by linarith) hell.le

/-- Complete primary estimate with all scale-dependent analytic facts exposed
as hypotheses.  This is the finite statement used when the eventual choices
of `L`, `D`, and `W` are substituted. -/
theorem primary_global_bound
    {N L D W : ℕ} {A : Finset ℕ} {ell Err : ℝ}
    (hAprim : A ⊆ primarySet N L D)
    (hmono : TotientMonotoneOn A)
    (hD : 1 ≤ D) (hW : 0 < W)
    (hshort : ∀ n ∈ A,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2))
    (hell : 0 < ell) (hErr : 0 ≤ Err)
    (hdata : ∀ k ∈ primaryKeys A (quotientBucket W) (primaryD N L D),
      ∀ d₀ ∈ ratioFibre D k.2,
      ∀ hc : (primaryCell A (quotientBucket W) (primaryD N L D) k).Nonempty,
        let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
        let u := cell.min' hc / d₀
        let v := cell.max' hc / d₀
        1 < u ∧ ell ≤ Real.log u ∧
          |Chebyshev.theta ((u - 1 : ℕ) : ℝ) - (u - 1 : ℕ)| ≤ Err ∧
          |Chebyshev.theta v - v| ≤ Err) :
    (A.card : ℝ) ≤ (N : ℝ) / ell +
      (((N / W + 1) * D : ℕ) : ℝ) * D * ((2 + 2 * Err) / ell) := by
  have hpack := primary_packing_from_interval_bound
    hAprim hmono hD hW hshort
    (K := 1 / ell) (E := (2 + 2 * Err) / ell)
    (by positivity)
    (div_nonneg (by linarith) hell.le)
    (by
      intro k hk d₀ hd₀
      exact primary_primeInterval_bound k (mem_ratioFibre.mp hd₀).1
        hell hErr (hdata k hk d₀ hd₀))
  have hkeys := primaryKeys_card_le hAprim hW
  have hkeysReal :
      ((primaryKeys A (quotientBucket W) (primaryD N L D)).card : ℝ) ≤
        (((N / W + 1) * D : ℕ) : ℝ) := by
    exact_mod_cast hkeys
  calc
    (A.card : ℝ) ≤ (1 / ell) * N +
        ((primaryKeys A (quotientBucket W) (primaryD N L D)).card : ℝ) * D *
          ((2 + 2 * Err) / ell) := hpack
    _ ≤ (1 / ell) * N + (((N / W + 1) * D : ℕ) : ℝ) * D *
          ((2 + 2 * Err) / ell) := by
      gcongr
    _ = (N : ℝ) / ell + (((N / W + 1) * D : ℕ) : ℝ) * D *
          ((2 + 2 * Err) / ell) := by ring

#print axioms primary_hulls_pairwiseDisjoint
#print axioms primary_packing_from_interval_bound
#print axioms primaryKeys_card_le
#print axioms primary_primeInterval_bound
#print axioms primary_global_bound

end

end Erdos49
