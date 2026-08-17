import ErdosProblems.Erdos49.PrimaryStructure

/-!
# Finite secondary packing

This file isolates the counting argument for Tao's secondary set.  On one
fixed denominator and one dyadic prime band, elements have a chosen
factorisation `n = d * p * s`.  We partition both `n` and `p` into additive
buckets.  The arithmetic ordering argument used later supplies overlap at
most two for the occupied integer hulls; everything here is finite elementary
bookkeeping.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def secondaryKey (U V : ℕ) (p : ℕ → ℕ) (n : ℕ) : ℕ × ℕ :=
  (n / U, p n / V)

def secondaryKeys (A : Finset ℕ) (U V : ℕ) (p : ℕ → ℕ) :
    Finset (ℕ × ℕ) :=
  A.image (secondaryKey U V p)

def secondaryCell (A : Finset ℕ) (U V : ℕ) (p : ℕ → ℕ)
    (k : ℕ × ℕ) : Finset ℕ :=
  A.filter fun n ↦ secondaryKey U V p n = k

/-- Once separated prime buckets are known to respect the ambient order,
the corresponding secondary hulls are disjoint. -/
lemma secondary_hulls_disjoint_of_separated
    {A : Finset ℕ} {U V : ℕ} {p : ℕ → ℕ} (hU : 0 < U)
    (horder : ∀ n ∈ A, ∀ m ∈ A, n / U = m / U →
      p n / V + 1 < p m / V → n < m)
    {k l : ℕ × ℕ}
    (hsep : k.1 < l.1 ∨ (k.1 = l.1 ∧ k.2 + 1 < l.2)) :
    Disjoint (intervalHull (secondaryCell A U V p k))
      (intervalHull (secondaryCell A U V p l)) := by
  apply intervalHull_disjoint_of_lt
  intro n hn m hm
  have hnData := Finset.mem_filter.mp hn
  have hmData := Finset.mem_filter.mp hm
  have hnKey := hnData.2
  have hmKey := hmData.2
  have hbn : n / U = k.1 := by
    simpa [secondaryKey] using congrArg Prod.fst hnKey
  have hbm : m / U = l.1 := by
    simpa [secondaryKey] using congrArg Prod.fst hmKey
  rcases hsep with hsep | hsep
  · have hnBounds := quotientBucket_bounds (W := U) (n := n) hU
    have hmBounds := quotientBucket_bounds (W := U) (n := m) hU
    change n / U * U ≤ n ∧ n < n / U * U + U at hnBounds
    change m / U * U ≤ m ∧ m < m / U * U + U at hmBounds
    rw [hbn] at hnBounds
    rw [hbm] at hmBounds
    calc
      n < k.1 * U + U := hnBounds.2
      _ = (k.1 + 1) * U := by simp [add_mul]
      _ ≤ l.1 * U := Nat.mul_le_mul_right U (by omega)
      _ ≤ m := hmBounds.1
  · apply horder n hnData.1 m hmData.1
    · exact hbn.trans (hsep.1.trans hbm.symm)
    · have hpn : p n / V = k.2 := by
        simpa [secondaryKey] using congrArg Prod.snd hnKey
      have hpm : p m / V = l.2 := by
        simpa [secondaryKey] using congrArg Prod.snd hmKey
      simpa [hpn, hpm] using hsep.2

/-- The separated-bucket ordering statement implies overlap at most two for
all occupied secondary hulls. -/
theorem secondary_hulls_overlap_two
    {A : Finset ℕ} {U V : ℕ} {p : ℕ → ℕ} (hU : 0 < U)
    (horder : ∀ n ∈ A, ∀ m ∈ A, n / U = m / U →
      p n / V + 1 < p m / V → n < m) :
    ∀ x : ℕ, ((secondaryKeys A U V p).filter fun k ↦
      x ∈ intervalHull (secondaryCell A U V p k)).card ≤ 2 := by
  intro x
  let keys := secondaryKeys A U V p
  let hull := fun k ↦ intervalHull (secondaryCell A U V p k)
  let hit := keys.filter fun k ↦ x ∈ hull k
  change hit.card ≤ 2
  by_cases hhit : hit.Nonempty
  · have hfirst (k : ℕ × ℕ) (hk : k ∈ hit)
        (l : ℕ × ℕ) (hl : l ∈ hit) : k.1 = l.1 := by
      have hkData := Finset.mem_filter.mp hk
      have hlData := Finset.mem_filter.mp hl
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hd := secondary_hulls_disjoint_of_separated hU horder (Or.inl hlt)
        exact (Finset.disjoint_left.mp hd) hkData.2 hlData.2
      · have hd := secondary_hulls_disjoint_of_separated hU horder (Or.inl hlt)
        exact (Finset.disjoint_left.mp hd) hlData.2 hkData.2
    have hclose (k : ℕ × ℕ) (hk : k ∈ hit)
        (l : ℕ × ℕ) (hl : l ∈ hit) : k.2 ≤ l.2 + 1 := by
      have hkData := Finset.mem_filter.mp hk
      have hlData := Finset.mem_filter.mp hl
      by_contra hnot
      have hsep : l.2 + 1 < k.2 := by omega
      have hd := secondary_hulls_disjoint_of_separated hU horder
        (Or.inr ⟨(hfirst l hl k hk), hsep⟩)
      exact (Finset.disjoint_left.mp hd) hlData.2 hkData.2
    let vals := hit.image Prod.snd
    have hvals : vals.Nonempty := hhit.image _
    have hsndInj : Set.InjOn Prod.snd (hit : Set (ℕ × ℕ)) := by
      intro k hk l hl hsnd
      exact Prod.ext (hfirst k hk l hl) hsnd
    have hcard : hit.card = vals.card := by
      symm
      exact Finset.card_image_iff.mpr fun k hk l hl heq ↦ hsndInj hk hl heq
    rw [hcard]
    apply (Finset.card_le_card (t := Finset.Icc (vals.min' hvals) (vals.min' hvals + 1)) ?_).trans
    · simp only [Nat.card_Icc]
      omega
    · intro r hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      have hminMem := vals.min'_mem hvals
      obtain ⟨l, hl, hleq⟩ := Finset.mem_image.mp hminMem
      have hminEq : vals.min' hvals = l.2 := hleq.symm
      apply Finset.mem_Icc.mpr
      constructor
      · exact vals.min'_le k.2 (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      · rw [hminEq]
        exact hclose k hk l hl
  · have : hit = ∅ := Finset.not_nonempty_iff_eq_empty.mp hhit
    simp [this]

lemma secondaryKeys_card_le {N P U V : ℕ} {A : Finset ℕ} {p : ℕ → ℕ}
    (hN : ∀ n ∈ A, n ≤ N) (hp : ∀ n ∈ A, p n ≤ 2 * P) :
    (secondaryKeys A U V p).card ≤
      (N / U + 1) * (2 * P / V + 1) := by
  let left := Finset.range (N / U + 1)
  let right := Finset.range (2 * P / V + 1)
  have hsub : secondaryKeys A U V p ⊆ left.product right := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_product.mpr
    constructor <;> rw [Finset.mem_range, Nat.lt_succ_iff]
    · exact Nat.div_le_div_right (hN n hn)
    · exact Nat.div_le_div_right (hp n hn)
  apply (Finset.card_le_card hsub).trans
  simp [left, right]

/-- For fixed `p₀`, the chosen cofactor `s` injects the corresponding cell
slice into the quotient of the cell hull by `d₀ p₀`. -/
lemma secondary_slice_card_le
    {A : Finset ℕ} {U V d₀ : ℕ} {p s : ℕ → ℕ} (k : ℕ × ℕ)
    (hd₀ : 0 < d₀) (hfac : ∀ n ∈ A, n = d₀ * p n * s n)
    {p₀ : ℕ} (hp₀ : 0 < p₀) :
    let cell := secondaryCell A U V p k
    let slice := cell.filter fun n ↦ p n = p₀
    slice.card ≤ (intervalHull cell).card / (d₀ * p₀) + 3 := by
  dsimp only
  let cell := secondaryCell A U V p k
  let slice := cell.filter fun n ↦ p n = p₀
  change slice.card ≤ (intervalHull cell).card / (d₀ * p₀) + 3
  by_cases hs : slice.Nonempty
  · have hc : cell.Nonempty := by
      obtain ⟨n, hn⟩ := hs
      exact ⟨n, (Finset.mem_filter.mp hn).1⟩
    have hden : 0 < d₀ * p₀ := Nat.mul_pos hd₀ hp₀
    have hinj : Set.InjOn s (slice : Set ℕ) := by
      intro n hn m hm hsm
      have hnData := Finset.mem_filter.mp hn
      have hmData := Finset.mem_filter.mp hm
      have hnA := (Finset.mem_filter.mp hnData.1).1
      have hmA := (Finset.mem_filter.mp hmData.1).1
      have hnfac := hfac n hnA
      have hmfac := hfac m hmA
      rw [hnData.2] at hnfac
      rw [hmData.2] at hmfac
      rw [hsm] at hnfac
      exact hnfac.trans hmfac.symm
    have hcard : slice.card = (slice.image s).card := by
      symm
      exact Finset.card_image_iff.mpr fun n hn m hm hnm ↦ hinj hn hm hnm
    rw [hcard]
    have hsub : slice.image s ⊆
        Finset.Icc (cell.min' hc / (d₀ * p₀))
          (cell.max' hc / (d₀ * p₀)) := by
      intro z hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      have hnData := Finset.mem_filter.mp hn
      have hnc := hnData.1
      have hnA := (Finset.mem_filter.mp hnc).1
      have hnfac := hfac n hnA
      rw [hnData.2] at hnfac
      apply Finset.mem_Icc.mpr
      constructor
      · apply Nat.div_le_of_le_mul
        exact (cell.min'_le n hnc).trans_eq hnfac
      · apply (Nat.le_div_iff_mul_le hden).2
        rw [show s n * (d₀ * p₀) = d₀ * p₀ * s n by ac_rfl]
        exact hnfac.symm.trans_le (cell.le_max' n hnc)
    apply (Finset.card_le_card hsub).trans
    have hw := div_hull_width_le (cell.min'_le_max' hc) hden
      (show cell.max' hc + 1 - cell.min' hc ≤ (intervalHull cell).card by
        simp [intervalHull, hc])
    have huv : cell.min' hc / (d₀ * p₀) ≤
        cell.max' hc / (d₀ * p₀) :=
      Nat.div_le_div_right (cell.min'_le_max' hc)
    rw [Nat.card_Icc]
    let u := cell.min' hc / (d₀ * p₀)
    let v := cell.max' hc / (d₀ * p₀)
    change v + 1 - u ≤ (intervalHull cell).card / (d₀ * p₀) + 3
    have huv' : u ≤ v := huv
    have hfirst : v + 1 - u ≤ (v - (u - 1)) + 1 := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · have huPos : 0 < u := Nat.pos_of_ne_zero hu0
        omega
    exact hfirst.trans (by omega)
  · have hs0 : slice = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs0]
    exact Nat.zero_le _

/-- A cell is the disjoint union of its fixed-prime slices. -/
lemma secondaryCell_card_eq_sum_slices
    {A : Finset ℕ} {U V P : ℕ} {p : ℕ → ℕ} (k : ℕ × ℕ)
    (hpBand : ∀ n ∈ A, P ≤ p n ∧ p n ≤ 2 * P) :
    (secondaryCell A U V p k).card =
      ∑ p₀ ∈ Finset.Icc P (2 * P),
        ((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro n hn
  exact Finset.mem_Icc.mpr (hpBand n (Finset.mem_filter.mp hn).1)

/-- Inside one secondary cell the chosen primes occupy one additive bucket.
This sharper fibre decomposition is what recovers the factor `V / P` in
Tao's secondary estimate. -/
lemma secondaryCell_card_eq_sum_bucket_slices
    {A : Finset ℕ} {U V : ℕ} {p : ℕ → ℕ} (k : ℕ × ℕ)
    (hV : 0 < V) :
    (secondaryCell A U V p k).card =
      ∑ p₀ ∈ Finset.Icc (k.2 * V) (k.2 * V + V - 1),
        ((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro n hn
  have hkey := (Finset.mem_filter.mp hn).2
  have hpBucket : p n / V = k.2 := by
    simpa [secondaryKey] using congrArg Prod.snd hkey
  have hb := quotientBucket_bounds (W := V) (n := p n) hV
  change p n / V * V ≤ p n ∧ p n < p n / V * V + V at hb
  rw [hpBucket] at hb
  exact Finset.mem_Icc.mpr ⟨hb.1, by omega⟩

/-- A secondary cell has at most `V` possible chosen primes, rather than all
`P+1` integers in the ambient dyadic band. -/
lemma secondaryCell_card_real_le_bucket
    {A : Finset ℕ} {U V d₀ P : ℕ} {p s : ℕ → ℕ} (k : ℕ × ℕ)
    (hV : 0 < V) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hfac : ∀ n ∈ A, n = d₀ * p n * s n)
    (hpBand : ∀ n ∈ A, P ≤ p n ∧ p n ≤ 2 * P) :
    ((secondaryCell A U V p k).card : ℝ) ≤
      (V : ℝ) *
        (((intervalHull (secondaryCell A U V p k)).card : ℝ) /
          ((d₀ * P : ℕ) : ℝ) + 3) := by
  rw [secondaryCell_card_eq_sum_bucket_slices k hV, Nat.cast_sum]
  let J := Finset.Icc (k.2 * V) (k.2 * V + V - 1)
  let B : ℝ :=
    ((intervalHull (secondaryCell A U V p k)).card : ℝ) /
      ((d₀ * P : ℕ) : ℝ) + 3
  have hs : ∀ p₀ ∈ J,
      (((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card : ℝ) ≤ B := by
    intro p₀ hp₀
    by_cases hslice :
        ((secondaryCell A U V p k).filter fun n ↦ p n = p₀).Nonempty
    · obtain ⟨n, hn⟩ := hslice
      have hnCell := (Finset.mem_filter.mp hn).1
      have hnA := (Finset.mem_filter.mp hnCell).1
      have hp₀Pos : 0 < p₀ := by
        rw [← (Finset.mem_filter.mp hn).2]
        exact hP.trans_le (hpBand n hnA).1
      have hsliceNat := secondary_slice_card_le (U := U) (V := V) k hd₀ hfac hp₀Pos
      have hsliceReal :
          (((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card : ℝ) ≤
            (((intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) : ℕ) : ℝ) + 3 := by
        exact_mod_cast hsliceNat
      apply hsliceReal.trans
      have hp₀Low : P ≤ p₀ := by
        rw [← (Finset.mem_filter.mp hn).2]
        exact (hpBand n hnA).1
      have hden : d₀ * P ≤ d₀ * p₀ := Nat.mul_le_mul_left d₀ hp₀Low
      have hdivNat :
          (intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) ≤
            (intervalHull (secondaryCell A U V p k)).card / (d₀ * P) :=
        Nat.div_le_div_left hden (Nat.mul_pos hd₀ hP)
      calc
        (((intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) : ℕ) : ℝ) + 3 ≤
            (((intervalHull (secondaryCell A U V p k)).card / (d₀ * P) : ℕ) : ℝ) + 3 := by
          have hdivReal :
              (((intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) : ℕ) : ℝ) ≤
                (((intervalHull (secondaryCell A U V p k)).card / (d₀ * P) : ℕ) : ℝ) := by
            exact_mod_cast hdivNat
          linarith
        _ ≤ B := by
          dsimp only [B]
          gcongr
          exact Nat.cast_div_le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hslice]
      simp only [Finset.card_empty, Nat.cast_zero]
      dsimp only [B]
      positivity
  calc
    (∑ p₀ ∈ J,
        (((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card : ℝ)) ≤
        ∑ _p₀ ∈ J, B := Finset.sum_le_sum fun p₀ hp₀ ↦ hs p₀ hp₀
    _ = (J.card : ℝ) * B := by simp
    _ ≤ (V : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : J.card = V := by
          dsimp only [J]
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcard.le
      · dsimp only [B]
        positivity

/-- Uniform cardinality bound for one occupied secondary cell. -/
lemma secondaryCell_card_real_le
    {A : Finset ℕ} {U V d₀ P : ℕ} {p s : ℕ → ℕ} (k : ℕ × ℕ)
    (hd₀ : 0 < d₀) (hP : 0 < P)
    (hfac : ∀ n ∈ A, n = d₀ * p n * s n)
    (hpBand : ∀ n ∈ A, P ≤ p n ∧ p n ≤ 2 * P) :
    ((secondaryCell A U V p k).card : ℝ) ≤
      (P + 1 : ℕ) *
        (((intervalHull (secondaryCell A U V p k)).card : ℝ) /
          ((d₀ * P : ℕ) : ℝ) + 3) := by
  rw [secondaryCell_card_eq_sum_slices k hpBand, Nat.cast_sum]
  calc
    (∑ p₀ ∈ Finset.Icc P (2 * P),
        (((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card : ℝ)) ≤
      ∑ _p₀ ∈ Finset.Icc P (2 * P),
        (((intervalHull (secondaryCell A U V p k)).card : ℝ) /
          ((d₀ * P : ℕ) : ℝ) + 3) := by
      apply Finset.sum_le_sum
      intro p₀ hp₀
      have hp₀Data := Finset.mem_Icc.mp hp₀
      have hslice := secondary_slice_card_le (U := U) (V := V) k hd₀ hfac
        (p₀ := p₀) (hP.trans_le hp₀Data.1)
      have hsliceReal :
          (((secondaryCell A U V p k).filter fun n ↦ p n = p₀).card : ℝ) ≤
            (((intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) : ℕ) : ℝ) + 3 := by
        exact_mod_cast hslice
      apply hsliceReal.trans
      have hden : d₀ * P ≤ d₀ * p₀ :=
        Nat.mul_le_mul_left d₀ hp₀Data.1
      have hdivNat :
          (intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) ≤
            (intervalHull (secondaryCell A U V p k)).card / (d₀ * P) :=
        Nat.div_le_div_left hden (Nat.mul_pos hd₀ hP)
      calc
        (((intervalHull (secondaryCell A U V p k)).card / (d₀ * p₀) : ℕ) : ℝ) + 3 ≤
            (((intervalHull (secondaryCell A U V p k)).card / (d₀ * P) : ℕ) : ℝ) + 3 := by
          gcongr
        _ ≤ ((intervalHull (secondaryCell A U V p k)).card : ℝ) /
              ((d₀ * P : ℕ) : ℝ) + 3 := by
          gcongr
          exact Nat.cast_div_le
    _ = (P + 1 : ℕ) *
        (((intervalHull (secondaryCell A U V p k)).card : ℝ) /
          ((d₀ * P : ℕ) : ℝ) + 3) := by
      have hcard : (Finset.Icc P (2 * P)).card = P + 1 := by
        simp only [Nat.card_Icc]
        omega
      simp [hcard]
      ring

/-- The complete two-scale secondary packing bound for one denominator and
one dyadic prime band. -/
theorem secondary_band_bound
    {N P U V d₀ : ℕ} {A : Finset ℕ} {p s : ℕ → ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hfac : ∀ n ∈ A, n = d₀ * p n * s n)
    (hpBand : ∀ n ∈ A, P ≤ p n ∧ p n ≤ 2 * P)
    (hoverlap : ∀ x ∈ Finset.Icc 1 N,
      ((secondaryKeys A U V p).filter fun k ↦
        x ∈ intervalHull (secondaryCell A U V p k)).card ≤ 2) :
    (A.card : ℝ) ≤
      (P + 1 : ℕ) * (2 * N : ℕ) / (d₀ * P : ℕ) +
        (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) *
          (3 * (P + 1 : ℕ)) := by
  let keys := secondaryKeys A U V p
  let cell := secondaryCell A U V p
  let hull := fun k ↦ intervalHull (cell k)
  have hcellSub (k : ℕ × ℕ) : cell k ⊆ A := fun _ hn ↦
    (Finset.mem_filter.mp hn).1
  have hcardA : (A.card : ℝ) = ∑ k ∈ keys, ((cell k).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    exact Finset.card_eq_sum_card_image (secondaryKey U V p) A
  have hhullSub (k : ℕ × ℕ) (hk : k ∈ keys) :
      hull k ⊆ Finset.Icc 1 N :=
    intervalHull_subset_Icc ((hcellSub k).trans hA)
  have hhullSum : ∑ k ∈ keys, (hull k).card ≤ 2 * N :=
    sum_card_Icc_le_of_boundedOverlap keys hull N 2 hhullSub hoverlap
  have hhullSumReal : ∑ k ∈ keys, ((hull k).card : ℝ) ≤ (2 * N : ℕ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hhullSum
  have hkeys := secondaryKeys_card_le (U := U) (V := V)
    (fun n hn ↦ (Finset.mem_Icc.mp (hA hn)).2)
    (fun n hn ↦ (hpBand n hn).2)
  have hkeysReal : (keys.card : ℝ) ≤
      (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) := by
    exact_mod_cast hkeys
  rw [hcardA]
  calc
    (∑ k ∈ keys, ((cell k).card : ℝ)) ≤
        ∑ k ∈ keys, (P + 1 : ℕ) *
          (((hull k).card : ℝ) / ((d₀ * P : ℕ) : ℝ) + 3) := by
      exact Finset.sum_le_sum fun k hk ↦
        secondaryCell_card_real_le k hd₀ hP hfac hpBand
    _ = (P + 1 : ℕ) * (∑ k ∈ keys, ((hull k).card : ℝ)) /
          (d₀ * P : ℕ) + (keys.card : ℝ) * (3 * (P + 1 : ℕ)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      simp
      ring
    _ ≤ (P + 1 : ℕ) * (2 * N : ℕ) / (d₀ * P : ℕ) +
          (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) *
            (3 * (P + 1 : ℕ)) := by
      apply add_le_add
      · gcongr
      · gcongr

/-- Sharpened two-scale packing bound.  The factor multiplying the total hull
length is `V / (d₀ P)`, because each cell sees only one prime bucket. -/
theorem secondary_band_bucket_bound
    {N P U V d₀ : ℕ} {A : Finset ℕ} {p s : ℕ → ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hV : 0 < V) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hfac : ∀ n ∈ A, n = d₀ * p n * s n)
    (hpBand : ∀ n ∈ A, P ≤ p n ∧ p n ≤ 2 * P)
    (hoverlap : ∀ x ∈ Finset.Icc 1 N,
      ((secondaryKeys A U V p).filter fun k ↦
        x ∈ intervalHull (secondaryCell A U V p k)).card ≤ 2) :
    (A.card : ℝ) ≤
      (V : ℝ) * (2 * N : ℕ) / (d₀ * P : ℕ) +
        (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) * (3 * V) := by
  let keys := secondaryKeys A U V p
  let cell := secondaryCell A U V p
  let hull := fun k ↦ intervalHull (cell k)
  have hcellSub (k : ℕ × ℕ) : cell k ⊆ A := fun _ hn ↦
    (Finset.mem_filter.mp hn).1
  have hcardA : (A.card : ℝ) = ∑ k ∈ keys, ((cell k).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    exact Finset.card_eq_sum_card_image (secondaryKey U V p) A
  have hhullSub (k : ℕ × ℕ) (hk : k ∈ keys) :
      hull k ⊆ Finset.Icc 1 N :=
    intervalHull_subset_Icc ((hcellSub k).trans hA)
  have hhullSum : ∑ k ∈ keys, (hull k).card ≤ 2 * N :=
    sum_card_Icc_le_of_boundedOverlap keys hull N 2 hhullSub hoverlap
  have hhullSumReal : ∑ k ∈ keys, ((hull k).card : ℝ) ≤ (2 * N : ℕ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hhullSum
  have hkeys := secondaryKeys_card_le (U := U) (V := V)
    (fun n hn ↦ (Finset.mem_Icc.mp (hA hn)).2)
    (fun n hn ↦ (hpBand n hn).2)
  have hkeysReal : (keys.card : ℝ) ≤
      (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) := by
    exact_mod_cast hkeys
  rw [hcardA]
  calc
    (∑ k ∈ keys, ((cell k).card : ℝ)) ≤
        ∑ k ∈ keys, (V : ℝ) *
          (((hull k).card : ℝ) / ((d₀ * P : ℕ) : ℝ) + 3) := by
      exact Finset.sum_le_sum fun k hk ↦
        secondaryCell_card_real_le_bucket k hV hd₀ hP hfac hpBand
    _ = (V : ℝ) * (∑ k ∈ keys, ((hull k).card : ℝ)) /
          (d₀ * P : ℕ) + (keys.card : ℝ) * (3 * V) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      simp
      ring
    _ ≤ (V : ℝ) * (2 * N : ℕ) / (d₀ * P : ℕ) +
          (((N / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) * (3 * V) := by
      apply add_le_add <;> gcongr

#print axioms secondary_band_bound
#print axioms secondary_band_bucket_bound

end

end Erdos49
