/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos874.LocalDensity
import ErdosProblems.Erdos874.ExactUpper

/-!
# The density endgame for Erdős Problem 874

This file connects the local-density theorem to the exact integral endgame.
It keeps the two pigeonhole comparisons separate, in particular recording the
different error terms `(2 * R + 1) * q` and `(2 * R - 1) * q`.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Translation of progression blocks -/

/-- Translate a finite set of integers by `c`. -/
def translateFinset (c : ℤ) (S : Finset ℤ) : Finset ℤ :=
  S.image fun x => c + x

@[simp] theorem mem_translateFinset {c x : ℤ} {S : Finset ℤ} :
    x ∈ translateFinset c S ↔ x - c ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x - c, hx, by ring⟩

theorem progressionBlock_translate (c z q : ℤ) (n : ℕ) :
    progressionBlock (c + z) q n =
      translateFinset c (progressionBlock z q n) := by
  ext x
  simp only [mem_progressionBlock, mem_translateFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by ring⟩
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi, by omega⟩

theorem translateFinset_inter (c : ℤ) (S T : Finset ℤ) :
    translateFinset c (S ∩ T) =
      translateFinset c S ∩ translateFinset c T := by
  ext x
  simp

theorem card_translateFinset (c : ℤ) (S : Finset ℤ) :
    (translateFinset c S).card = S.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact add_left_cancel hxy

theorem card_progressionBlock_inter_translate
    (c z q : ℤ) (n : ℕ) (S : Finset ℤ) :
    (progressionBlock (c + z) q n ∩ translateFinset c S).card =
      (progressionBlock z q n ∩ S).card := by
  rw [progressionBlock_translate, ← translateFinset_inter,
    card_translateFinset]

/-- Two translated restricted-sum layers obtained by adjoining fixed disjoint
supports are disjoint when their total numbers of summands differ. -/
theorem translated_restrictedSumsets_disjoint_of_admissible
    {A V B C : Finset ℤ} {r s : ℕ}
    (hA : IsAdmissible A)
    (hVA : V ⊆ A) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hBV : Disjoint B V) (hCV : Disjoint C V)
    (hr : 0 < B.card + r) (hs : 0 < C.card + s)
    (hne : B.card + r ≠ C.card + s) :
    Disjoint
      (translateFinset (∑ x ∈ B, x) (restrictedSumset r V))
      (translateFinset (∑ x ∈ C, x) (restrictedSumset s V)) := by
  rw [Finset.disjoint_left]
  intro z hzB hzC
  have hzB' : z ∈ restrictedSumset (B.card + r) A := by
    have hz : z - (∑ x ∈ B, x) ∈ restrictedSumset r V :=
      mem_translateFinset.mp hzB
    have hmem := fixed_subset_sum_add_mem_restrictedSumset
      hVA hBA hBV hz
    convert hmem using 1 <;> ring
  have hzC' : z ∈ restrictedSumset (C.card + s) A := by
    have hz : z - (∑ x ∈ C, x) ∈ restrictedSumset s V :=
      mem_translateFinset.mp hzC
    have hmem := fixed_subset_sum_add_mem_restrictedSumset
      hVA hCA hCV hz
    convert hmem using 1 <;> ring
  exact (Finset.disjoint_left.mp (hA hr hs hne)) hzB' hzC'

/-! ## The two corrected pigeonhole comparisons -/

/-- The first DF99 comparison.  If a translate by `alpha` came too far to the
left, a block of `2R+1` progression terms would have strict-majority
intersection with both the original layer and its translate. -/
theorem first_pigeonhole_bound_of_localDensity
    {X : Finset ℤ} {m M residue alpha q : ℤ} {R : ℕ}
    (hq : 0 < q)
    (hdensity : HasLocalDensity X m M residue q R)
    (hmres : m % q = residue % q)
    (halpha : 0 ≤ alpha)
    (halphaDiv : q ∣ alpha)
    (hdisjoint : Disjoint X (translateFinset alpha X)) :
    FirstPigeonholeBound alpha (M - m) R q := by
  dsimp [FirstPigeonholeBound]
  by_contra hbound
  have hq0 : q ≠ 0 := ne_of_gt hq
  have halphaMod : alpha % q = 0 := Int.emod_eq_zero_of_dvd halphaDiv
  have hstartRes : (alpha + m) % q = residue % q := by
    rw [Int.add_emod, halphaMod, zero_add, Int.emod_emod, hmres]
  have hend : alpha + m + q * (2 * R : ℕ) ≤ M := by
    push_cast at hbound ⊢
    nlinarith
  have horigEnd : m + q * (2 * R : ℕ) ≤ M := by
    push_cast at hend ⊢
    nlinarith
  have hX := hdensity (alpha + m) hstartRes (by omega) hend
  have hbase := hdensity m hmres (by rfl) horigEnd
  have hY : R + 1 ≤
      ((progressionBlock (alpha + m) q (2 * R + 1)) ∩
        translateFinset alpha X).card := by
    rw [card_progressionBlock_inter_translate]
    exact hbase
  have hnot := not_disjoint_of_majorities_on_block
    (B := progressionBlock (alpha + m) q (2 * R + 1))
    (X := X) (Y := translateFinset alpha X) (R := R)
    (by rw [progressionBlock_card hq0]) hX hY
  exact hnot hdisjoint

/-- The second DF99 comparison.  The gap is `(2R-1)q`: failure of this
inequality, together with congruence modulo `q`, gives an overlap of at least
`2Rq`, hence an actual block of `2R+1` eligible progression terms. -/
theorem second_pigeonhole_bound_of_localDensity
    {X Y : Finset ℤ}
    {mX MX mY MY residueX residueY shiftX shiftY q : ℤ} {R : ℕ}
    (hq : 0 < q)
    (hdensityX : HasLocalDensity X mX MX residueX q R)
    (hdensityY : HasLocalDensity Y mY MY residueY q R)
    (hresX : (shiftY + mY - shiftX) % q = residueX % q)
    (hresY : mY % q = residueY % q)
    (hleft : shiftX + mX ≤ shiftY + mY)
    (hYwidth : mY + q * (2 * R : ℕ) ≤ MY)
    (halign : q ∣ (shiftX + MX) - (shiftY + mY))
    (hdisjoint : Disjoint (translateFinset shiftX X)
      (translateFinset shiftY Y)) :
    SecondPigeonholeBound (shiftX + MX) (shiftY + mY) R q := by
  dsimp [SecondPigeonholeBound]
  by_contra hbound
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hmultiple : 2 * (R : ℤ) * q ≤
      (shiftX + MX) - (shiftY + mY) := by
    obtain ⟨d, hd⟩ := halign
    have hdpos : (2 * (R : ℤ) - 1) * q < q * d := by
      nlinarith [hbound]
    have : 2 * (R : ℤ) ≤ d := by
      by_contra hdlt
      have hdle : d ≤ 2 * (R : ℤ) - 1 := by omega
      nlinarith
    rw [hd]
    nlinarith
  let z : ℤ := shiftY + mY
  have hXlo : mX ≤ z - shiftX := by
    dsimp [z]
    linarith
  have hXhi : z - shiftX + q * (2 * R : ℕ) ≤ MX := by
    dsimp [z]
    nlinarith
  have hXres : (z - shiftX) % q = residueX % q := by
    simpa [z] using hresX
  have hXbase := hdensityX (z - shiftX) hXres hXlo hXhi
  have hX : R + 1 ≤
      ((progressionBlock z q (2 * R + 1)) ∩
        translateFinset shiftX X).card := by
    have hz : z = shiftX + (z - shiftX) := by ring
    rw [hz, card_progressionBlock_inter_translate]
    exact hXbase
  have hYbase := hdensityY mY hresY (by rfl) hYwidth
  have hY : R + 1 ≤
      ((progressionBlock z q (2 * R + 1)) ∩
        translateFinset shiftY Y).card := by
    change R + 1 ≤
      ((progressionBlock (shiftY + mY) q (2 * R + 1)) ∩
        translateFinset shiftY Y).card
    rw [card_progressionBlock_inter_translate]
    exact hYbase
  exact (not_disjoint_of_majorities_on_block
    (B := progressionBlock z q (2 * R + 1))
    (X := translateFinset shiftX X) (Y := translateFinset shiftY Y) (R := R)
    (by rw [progressionBlock_card hq0]) hX hY) hdisjoint

/-- The orientation-free form of the second pigeonhole comparison.  Local
density alone does not determine which translated layer starts first.  If the
`X`-layer starts first, the usual DF99 bound holds from the right endpoint of
`X` to the left endpoint of `Y`; if the `Y`-layer starts first, the symmetric
bound holds in the opposite direction. -/
theorem second_pigeonhole_bound_dichotomy_of_localDensity
    {X Y : Finset ℤ}
    {mX MX mY MY residueX residueY shiftX shiftY q : ℤ} {R : ℕ}
    (hq : 0 < q)
    (hdensityX : HasLocalDensity X mX MX residueX q R)
    (hdensityY : HasLocalDensity Y mY MY residueY q R)
    (hcrossX : (shiftY + mY - shiftX) % q = residueX % q)
    (hcrossY : (shiftX + mX - shiftY) % q = residueY % q)
    (hleastX : mX % q = residueX % q)
    (hleastY : mY % q = residueY % q)
    (hXwidth : mX + q * (2 * R : ℕ) ≤ MX)
    (hYwidth : mY + q * (2 * R : ℕ) ≤ MY)
    (halignXY : q ∣ (shiftX + MX) - (shiftY + mY))
    (halignYX : q ∣ (shiftY + MY) - (shiftX + mX))
    (hdisjoint : Disjoint (translateFinset shiftX X)
      (translateFinset shiftY Y)) :
    SecondPigeonholeBound (shiftX + MX) (shiftY + mY) R q ∨
      SecondPigeonholeBound (shiftY + MY) (shiftX + mX) R q := by
  rcases le_total (shiftX + mX) (shiftY + mY) with hXY | hYX
  · exact Or.inl (second_pigeonhole_bound_of_localDensity hq
      hdensityX hdensityY hcrossX hleastY hXY hYwidth halignXY hdisjoint)
  · exact Or.inr (second_pigeonhole_bound_of_localDensity hq
      hdensityY hdensityX hcrossY hleastX hYX hXwidth halignYX hdisjoint.symm)

/-! ## Ordered endpoint bookkeeping -/

private theorem two_mul_sum_range_cast (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i : ℤ)) =
      (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith

private theorem sum_symmetric_gaps (K L : ℕ) :
    ∑ i ∈ Finset.range L, ((K : ℤ) - 2 * (i : ℤ) - 1) =
      (L : ℤ) * ((K : ℤ) - (L : ℤ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- `QSeparated` also supplies the weak endpoint estimate when the indices
coincide. -/
theorem QSeparated.le_gap {a : ℕ → ℤ} {K q i j : ℕ}
    (hsep : QSeparated a K q) (hij : i ≤ j) (hjK : j < K) :
    a i + (q : ℤ) * ((j : ℤ) - (i : ℤ)) ≤ a j := by
  rcases hij.eq_or_lt with rfl | hij
  · simp
  · exact hsep hij hjK

theorem qSeparated_of_strictMono_of_dvd_adjacent
    {a : ℕ → ℤ} {K q : ℕ} (hq : 0 < q)
    (hmono : ∀ i : ℕ, i + 1 < K → a i < a (i + 1))
    (hdiv : ∀ i : ℕ, i + 1 < K → (q : ℤ) ∣ a (i + 1) - a i) :
    QSeparated a K q := by
  apply qSeparated_of_adjacent
  intro i hi
  obtain ⟨d, hd⟩ := hdiv i hi
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hdpos : (0 : ℤ) < d := by
    nlinarith [hmono i hi]
  nlinarith

theorem QSeparated.eq_of_eq {a : ℕ → ℤ} {K q i j : ℕ}
    (hsep : QSeparated a K q) (hq : 0 < q)
    (hiK : i < K) (hjK : j < K) (hij : a i = a j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have h := hsep hijlt hjK
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    have hgap : (0 : ℤ) < (j : ℤ) - (i : ℤ) := by omega
    rw [hij] at h
    nlinarith
  · have h := hsep hjilt hiK
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    have hgap : (0 : ℤ) < (i : ℤ) - (j : ℤ) := by omega
    rw [hij] at h
    nlinarith

/-- Sum of the first `L` entries of an ordered sequence. -/
def orderedInitialSum (a : ℕ → ℤ) (L : ℕ) : ℤ :=
  ∑ i ∈ Finset.range L, a i

/-- Sum of the last `L` entries among the first `K` entries. -/
def orderedTerminalSum (a : ℕ → ℤ) (K L : ℕ) : ℤ :=
  ∑ i ∈ Finset.range L, a (K - 1 - i)

/-- The unpaired block of `q` entries beginning at position `L`. -/
def orderedMiddleSum (a : ℕ → ℤ) (L q : ℕ) : ℤ :=
  ∑ j ∈ Finset.range q, a (L + j)

theorem pairedEndpointSpread_eq_terminal_sub_initial
    (a : ℕ → ℤ) (K L : ℕ) :
    pairedEndpointSpread a K L =
      orderedTerminalSum a K L - orderedInitialSum a L := by
  simp only [pairedEndpointSpread, orderedTerminalSum, orderedInitialSum,
    Finset.sum_sub_distrib]

theorem orderedInitialSum_add (a : ℕ → ℤ) (L q : ℕ) :
    orderedInitialSum a (L + q) =
      orderedInitialSum a L + orderedMiddleSum a L q := by
  simp only [orderedInitialSum, orderedMiddleSum, Finset.sum_range_add]

theorem orderedTerminalSum_add (a : ℕ → ℤ) {K u s : ℕ}
    (hus : u + s ≤ K) :
    orderedTerminalSum a K (u + s) =
      orderedTerminalSum a K u +
        ∑ j ∈ Finset.range s, a (K - u - 1 - j) := by
  simp only [orderedTerminalSum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  congr 1
  omega

/-- Cancellation of the common initial `L` terms in the raw second
pigeonhole comparison. -/
theorem secondPigeonholeBound_cancel_initial
    {a : ℕ → ℤ} {K L q R : ℕ}
    (hsecond : SecondPigeonholeBound
      (orderedTerminalSum a K L) (orderedInitialSum a (L + q)) R (q : ℤ)) :
    SecondPigeonholeBound (pairedEndpointSpread a K L)
      (orderedMiddleSum a L q) R (q : ℤ) := by
  dsimp [SecondPigeonholeBound] at hsecond ⊢
  rw [pairedEndpointSpread_eq_terminal_sub_initial]
  rw [orderedInitialSum_add] at hsecond
  linarith

/-- The central interval contains `R` additional progression gaps.  Every one
of the first `u` outer pairs crosses this interval, so the ordinary
`q L (K-L)` endpoint estimate gains `u R q`. -/
theorem outerPairBound_of_central_span
    {a : ℕ → ℤ} {K L q u R : ℕ}
    (h2L : 2 * L ≤ K) (huL : u ≤ L) (hcentral : 2 * u + 1 < K)
    (hsep : QSeparated a K q)
    (hspan : a (K - u - 1) - a u =
      (q : ℤ) * ((K : ℤ) - 2 * (u : ℤ) - 1 + (R : ℤ))) :
    OuterPairBound (K : ℤ) (L : ℤ) (q : ℤ)
      (pairedEndpointSpread a K L) u R := by
  let gap : ℕ → ℤ := fun i => a (K - 1 - i) - a i
  let base : ℕ → ℤ := fun i =>
    (q : ℤ) * ((K : ℤ) - 2 * (i : ℤ) - 1)
  have hbase : ∀ i, i < L → base i ≤ gap i := by
    intro i hi
    have hij : i < K - 1 - i := by omega
    have hjK : K - 1 - i < K := by omega
    have h := hsep hij hjK
    have hcast : ((K - 1 - i : ℕ) : ℤ) =
        (K : ℤ) - 1 - (i : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    dsimp [base, gap]
    rw [hcast] at h
    linarith
  have hextra : ∀ i, i < u →
      base i + (R : ℤ) * q ≤ gap i := by
    intro i hi
    have hiu : i < u := hi
    have huK : u < K := by omega
    have hcK : K - u - 1 < K := by omega
    have hleft := hsep (i := i) (j := u) hiu huK
    have hright : a (K - u - 1) +
        (q : ℤ) * (((K - 1 - i : ℕ) : ℤ) - ((K - u - 1 : ℕ) : ℤ)) ≤
        a (K - 1 - i) := by
      apply hsep
      · omega
      · omega
    have hiCast : ((K - 1 - i : ℕ) : ℤ) =
        (K : ℤ) - 1 - (i : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have hcCast : ((K - u - 1 : ℕ) : ℤ) =
        (K : ℤ) - (u : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hiCast, hcCast] at hright
    dsimp [base, gap]
    nlinarith
  have hfirst :
      ∑ i ∈ Finset.range u, (base i + (R : ℤ) * q) ≤
        ∑ i ∈ Finset.range u, gap i := by
    exact Finset.sum_le_sum fun i hi => hextra i (Finset.mem_range.mp hi)
  have hrest :
      ∑ i ∈ Finset.range (L - u), base (u + i) ≤
        ∑ i ∈ Finset.range (L - u), gap (u + i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply hbase
    have hi' := Finset.mem_range.mp hi
    omega
  have hL : L = u + (L - u) := by omega
  have htotal :
      (∑ i ∈ Finset.range L, base i) + (u : ℤ) * (R : ℤ) * q ≤
        ∑ i ∈ Finset.range L, gap i := by
    rw [hL, Finset.sum_range_add, Finset.sum_range_add]
    have hfirst' :
        (∑ i ∈ Finset.range u, base i) + (u : ℤ) * (R : ℤ) * q ≤
          ∑ i ∈ Finset.range u, gap i := by
      calc
        (∑ i ∈ Finset.range u, base i) + (u : ℤ) * (R : ℤ) * q =
            ∑ i ∈ Finset.range u, (base i + (R : ℤ) * q) := by
              simp [Finset.sum_add_distrib]
              ring
        _ ≤ ∑ i ∈ Finset.range u, gap i := hfirst
    linarith
  dsimp [OuterPairBound, pairedEndpointSpread]
  change (q : ℤ) * (L : ℤ) * ((K : ℤ) - (L : ℤ)) +
      (u : ℤ) * (R : ℤ) * (q : ℤ) ≤
    ∑ i ∈ Finset.range L, gap i
  calc
    _ = (∑ i ∈ Finset.range L, base i) +
        (u : ℤ) * (R : ℤ) * (q : ℤ) := by
      dsimp [base]
      rw [← Finset.mul_sum, sum_symmetric_gaps]
      ring
    _ ≤ _ := htotal

/-- The `q` middle elements are bounded by walking backwards from the ambient
endpoint `a (K-1) ≤ N`.  The factor two clears the triangular sum. -/
theorem middleEndpointBound_of_qSeparated
    {a : ℕ → ℤ} {N K L q : ℕ}
    (hK : 0 < K) (hLq : L + q ≤ K)
    (hsep : QSeparated a K q) (hN : a (K - 1) ≤ (N : ℤ)) :
    MiddleEndpointBound (N : ℤ) (K : ℤ) (L : ℤ) (q : ℤ)
      (∑ j ∈ Finset.range q, a (L + j)) := by
  have hterm : ∀ j ∈ Finset.range q,
      a (L + j) ≤ (N : ℤ) -
        (q : ℤ) * ((K : ℤ) - 1 - (L : ℤ) - (j : ℤ)) := by
    intro j hj
    have hjq := Finset.mem_range.mp hj
    have hindex : L + j ≤ K - 1 := by omega
    have hwalk := hsep.le_gap hindex (by omega)
    have htopCast : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [htopCast] at hwalk
    push_cast at hwalk
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  dsimp [MiddleEndpointBound]
  have htwice := mul_le_mul_of_nonneg_left hsum (show (0 : ℤ) ≤ 2 by omega)
  have hsumj := two_mul_sum_range_cast q
  have hrhs :
      (∑ i ∈ Finset.range q,
          ((N : ℤ) - (q : ℤ) *
            ((K : ℤ) - 1 - (L : ℤ) - (i : ℤ)))) =
        (q : ℤ) * (N : ℤ) - (q : ℤ) *
          ((q : ℤ) * ((K : ℤ) - 1 - (L : ℤ)) -
            ∑ i ∈ Finset.range q, (i : ℤ)) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrhs] at htwice
  nlinarith

/-- The sharp middle bookkeeping bound in the density endgame.  It is the
ambient endpoint estimate before the additional `-2q` supplied by the central
span and corrected second pigeonhole comparison. -/
def SharpMiddleBookkeepingBound (N K L q U : ℤ) : Prop :=
  MiddleEndpointBound N K L q U

theorem sharpMiddleBookkeepingBound_of_qSeparated
    {a : ℕ → ℤ} {N K L q : ℕ}
    (hK : 0 < K) (hLq : L + q ≤ K)
    (hsep : QSeparated a K q) (hN : a (K - 1) ≤ (N : ℤ)) :
    SharpMiddleBookkeepingBound (N : ℤ) (K : ℤ) (L : ℤ) (q : ℤ)
      (∑ j ∈ Finset.range q, a (L + j)) :=
  middleEndpointBound_of_qSeparated hK hLq hsep hN

/-! ## Concrete finite certificates -/

/-- All concrete hypotheses used in the first local-density comparison.  The
predicate contains the sumset, its actual translate, and the verified density
and congruence facts; it does not contain the desired inequality. -/
structure FirstDensityComparison (q : ℤ) (R : ℕ) : Type where
  X : Finset ℤ
  m : ℤ
  M : ℤ
  residue : ℤ
  alpha : ℤ
  density : HasLocalDensity X m M residue q R
  least_residue : m % q = residue % q
  alpha_nonneg : 0 ≤ alpha
  alpha_divisible : q ∣ alpha
  disjoint_translate : Disjoint X (translateFinset alpha X)

theorem FirstDensityComparison.bound {q : ℤ} {R : ℕ}
    (D : FirstDensityComparison q R) (hq : 0 < q) :
    FirstPigeonholeBound D.alpha (D.M - D.m) R q :=
  first_pigeonhole_bound_of_localDensity hq D.density D.least_residue
    D.alpha_nonneg D.alpha_divisible D.disjoint_translate

/-- All concrete hypotheses used in the second local-density comparison.
Again, the corrected `(2R-1)q` inequality is a theorem, not a field. -/
structure SecondDensityComparison (q : ℤ) (R : ℕ) : Type where
  X : Finset ℤ
  Y : Finset ℤ
  mX : ℤ
  MX : ℤ
  mY : ℤ
  MY : ℤ
  residueX : ℤ
  residueY : ℤ
  shiftX : ℤ
  shiftY : ℤ
  densityX : HasLocalDensity X mX MX residueX q R
  densityY : HasLocalDensity Y mY MY residueY q R
  start_residueX : (shiftY + mY - shiftX) % q = residueX % q
  least_residueY : mY % q = residueY % q
  left_endpoints_ordered : shiftX + mX ≤ shiftY + mY
  Y_has_full_block : mY + q * (2 * R : ℕ) ≤ MY
  endpoint_difference_divisible : q ∣ (shiftX + MX) - (shiftY + mY)
  translated_layers_disjoint :
    Disjoint (translateFinset shiftX X) (translateFinset shiftY Y)

theorem SecondDensityComparison.bound {q : ℤ} {R : ℕ}
    (D : SecondDensityComparison q R) (hq : 0 < q) :
    SecondPigeonholeBound (D.shiftX + D.MX) (D.shiftY + D.mY) R q :=
  second_pigeonhole_bound_of_localDensity hq D.densityX D.densityY
    D.start_residueX D.least_residueY D.left_endpoints_ordered
    D.Y_has_full_block D.endpoint_difference_divisible
    D.translated_layers_disjoint

/-- Orientation-free concrete input for the second local-density argument.
Unlike `SecondDensityComparison`, this structure makes no unsupported choice
of which translated layer has the smaller left endpoint.  Consequently its
conclusion is the mathematically forced two-branch bound. -/
structure SymmetricSecondDensityComparison (q : ℤ) (R : ℕ) : Type where
  X : Finset ℤ
  Y : Finset ℤ
  mX : ℤ
  MX : ℤ
  mY : ℤ
  MY : ℤ
  residueX : ℤ
  residueY : ℤ
  shiftX : ℤ
  shiftY : ℤ
  densityX : HasLocalDensity X mX MX residueX q R
  densityY : HasLocalDensity Y mY MY residueY q R
  cross_residueX : (shiftY + mY - shiftX) % q = residueX % q
  cross_residueY : (shiftX + mX - shiftY) % q = residueY % q
  least_residueX : mX % q = residueX % q
  least_residueY : mY % q = residueY % q
  X_has_full_block : mX + q * (2 * R : ℕ) ≤ MX
  Y_has_full_block : mY + q * (2 * R : ℕ) ≤ MY
  forward_endpoint_difference_divisible :
    q ∣ (shiftX + MX) - (shiftY + mY)
  reverse_endpoint_difference_divisible :
    q ∣ (shiftY + MY) - (shiftX + mX)
  translated_layers_disjoint :
    Disjoint (translateFinset shiftX X) (translateFinset shiftY Y)

theorem SymmetricSecondDensityComparison.bounds {q : ℤ} {R : ℕ}
    (D : SymmetricSecondDensityComparison q R) (hq : 0 < q) :
    SecondPigeonholeBound (D.shiftX + D.MX) (D.shiftY + D.mY) R q ∨
      SecondPigeonholeBound (D.shiftY + D.MY) (D.shiftX + D.mX) R q :=
  second_pigeonhole_bound_dichotomy_of_localDensity hq D.densityX D.densityY
    D.cross_residueX D.cross_residueY D.least_residueX D.least_residueY
    D.X_has_full_block D.Y_has_full_block
    D.forward_endpoint_difference_divisible
    D.reverse_endpoint_difference_divisible D.translated_layers_disjoint

/-- Selecting the forward branch requires exactly the missing endpoint
orientation, rather than hiding it in a local-density claim. -/
def SymmetricSecondDensityComparison.forward {q : ℤ} {R : ℕ}
    (D : SymmetricSecondDensityComparison q R)
    (hleft : D.shiftX + D.mX ≤ D.shiftY + D.mY) :
    SecondDensityComparison q R where
  X := D.X
  Y := D.Y
  mX := D.mX
  MX := D.MX
  mY := D.mY
  MY := D.MY
  residueX := D.residueX
  residueY := D.residueY
  shiftX := D.shiftX
  shiftY := D.shiftY
  densityX := D.densityX
  densityY := D.densityY
  start_residueX := D.cross_residueX
  least_residueY := D.least_residueY
  left_endpoints_ordered := hleft
  Y_has_full_block := D.Y_has_full_block
  endpoint_difference_divisible := D.forward_endpoint_difference_divisible
  translated_layers_disjoint := D.translated_layers_disjoint

/-- An ordered central block and the exact quantitative facts supplied by the
central-span theorem.  The sequence `a` enumerates all of `A`; its central
subsequence has `R` missing `q`-steps. -/
structure OrderedCentralBlock (N : ℕ) (A : Finset ℤ) : Type where
  a : ℕ → ℤ
  q : ℕ
  u : ℕ
  R : ℕ
  L : ℕ
  θ : ℕ
  enumerates : A = Finset.image a (Finset.range A.card)
  q_pos : 1 ≤ q
  u_ge_two : 2 ≤ u
  u_le_L : u ≤ L
  central_nonempty : 2 * u + 1 < A.card
  size_condition : q + 3 ≤ 2 * A.card
  theta_cases : θ = 0 ∨ θ = 1
  card_decomposition : A.card = 2 * L + q + θ
  separated : QSeparated a A.card q
  central_span : a (A.card - u - 1) - a u =
    (q : ℤ) * ((A.card : ℤ) - 2 * (u : ℤ) - 1 + (R : ℤ))
  last_le : a (A.card - 1) ≤ (N : ℤ)

/-- The actual ordered central subfinset, after deleting `u` entries from
each end of the ordered enumeration. -/
def OrderedCentralBlock.centralFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : Finset ℤ :=
  Finset.image (fun i : ℕ => D.a (D.u + i))
    (Finset.range (A.card - 2 * D.u))

theorem OrderedCentralBlock.centralFinset_card {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    D.centralFinset.card = A.card - 2 * D.u := by
  unfold OrderedCentralBlock.centralFinset
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_range _
  · intro i hi j hj hij
    have hi' : i < A.card - 2 * D.u := by simpa using hi
    have hj' : j < A.card - 2 * D.u := by simpa using hj
    have hcentral := D.central_nonempty
    have hq := D.q_pos
    have heq : D.u + i = D.u + j :=
      D.separated.eq_of_eq (by omega : 0 < D.q) (by omega) (by omega) hij
    omega

theorem OrderedCentralBlock.centralFinset_subset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) : D.centralFinset ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hmem : D.a (D.u + i) ∈
      Finset.image D.a (Finset.range A.card) := by
    apply Finset.mem_image.mpr
    refine ⟨D.u + i, ?_, rfl⟩
    simp only [Finset.mem_range] at hi ⊢
    have hcentral := D.central_nonempty
    omega
  exact (le_of_eq D.enumerates.symm) hmem

theorem OrderedCentralBlock.outerPairBound {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    OuterPairBound (A.card : ℤ) (D.L : ℤ) (D.q : ℤ)
      (pairedEndpointSpread D.a A.card D.L) D.u D.R := by
  have hcard := D.card_decomposition
  apply outerPairBound_of_central_span
  · omega
  · exact D.u_le_L
  · exact D.central_nonempty
  · exact D.separated
  · exact D.central_span

theorem OrderedCentralBlock.middleEndpointBound {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) :
    MiddleEndpointBound (N : ℤ) (A.card : ℤ) (D.L : ℤ) (D.q : ℤ)
      (∑ j ∈ Finset.range D.q, D.a (D.L + j)) := by
  have hcard := D.card_decomposition
  have hq := D.q_pos
  apply middleEndpointBound_of_qSeparated
  · omega
  · omega
  · exact D.separated
  · exact D.last_le

/-- A complete finite input to the density endgame.  The only remaining data
beyond the ordered central block are the two actual dense layers and the
identities obtained by cancelling their explicit endpoint sums. -/
structure DensityEndgameData (N : ℕ) (A : Finset ℤ) : Type
    extends OrderedCentralBlock N A where
  second : SecondDensityComparison (q : ℤ) R
  second_left_eq : second.shiftX + second.MX =
    orderedTerminalSum a A.card L
  second_right_eq : second.shiftY + second.mY =
    orderedInitialSum a (L + q)

/-- Once the correctly oriented raw second comparison is known, the endpoint
cancellation and central-span bookkeeping give the exact density endgame. -/
theorem OrderedCentralBlock.hasDensityEndgame_of_raw_second_bound
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hsecondRaw : SecondPigeonholeBound
      (orderedTerminalSum D.a A.card D.L)
      (orderedInitialSum D.a (D.L + D.q)) D.R (D.q : ℤ)) :
    HasDensityEndgame N A := by
  let P := pairedEndpointSpread D.a A.card D.L
  let U := orderedMiddleSum D.a D.L D.q
  have hsecond : SecondPigeonholeBound P U D.R (D.q : ℤ) := by
    simpa [P, U] using secondPigeonholeBound_cancel_initial hsecondRaw
  have houter : OuterPairBound (A.card : ℤ) (D.L : ℤ) (D.q : ℤ)
      P D.u D.R := by
    simpa [P] using D.outerPairBound
  have hmiddle : MiddleEndpointBound (N : ℤ) (A.card : ℤ)
      (D.L : ℤ) (D.q : ℤ) U := by
    simpa [U, orderedMiddleSum] using D.middleEndpointBound
  have hcleared : ClearedDensityEstimate (N : ℤ) (A.card : ℤ)
      (D.L : ℤ) (D.q : ℤ) :=
    cleared_density_estimate_of_pigeonhole_bounds
      (by positivity) D.u_ge_two houter hsecond hmiddle
  exact ⟨D.L, D.q, D.θ, D.q_pos, D.size_condition, D.theta_cases,
    by exact_mod_cast D.card_decomposition, hcleared⟩

/-- The ordered central block and the two genuinely oriented local-density
outputs imply the concrete `HasDensityEndgame` witness consumed by
`ExactUpper`. -/
theorem DensityEndgameData.hasDensityEndgame {N : ℕ} {A : Finset ℤ}
    (D : DensityEndgameData N A) : HasDensityEndgame N A := by
  apply D.toOrderedCentralBlock.hasDensityEndgame_of_raw_second_bound
  have hsecond0 := D.second.bound (show (0 : ℤ) < (D.q : ℕ) by
    exact_mod_cast D.q_pos)
  simpa [D.second_left_eq, D.second_right_eq] using hsecond0

/-- The unconditional finite certificate supplied by the two local-density
layers.  It records the same endpoint identities as `DensityEndgameData`, but
uses the orientation-free second comparison. -/
structure SymmetricDensityEndgameData (N : ℕ) (A : Finset ℤ) : Type
    extends OrderedCentralBlock N A where
  second : SymmetricSecondDensityComparison (q : ℤ) R
  second_left_eq : second.shiftX + second.MX =
    orderedTerminalSum a A.card L
  second_right_eq : second.shiftY + second.mY =
    orderedInitialSum a (L + q)

/-- The exact conclusion available without an endpoint-orientation theorem:
either the desired density endgame follows, or the symmetric second
pigeonhole bound holds in the reverse direction. -/
theorem SymmetricDensityEndgameData.hasDensityEndgame_or_reverse_bound
    {N : ℕ} {A : Finset ℤ} (D : SymmetricDensityEndgameData N A) :
    HasDensityEndgame N A ∨
      SecondPigeonholeBound
        (D.second.shiftY + D.second.MY)
        (D.second.shiftX + D.second.mX) D.R (D.q : ℤ) := by
  rcases D.second.bounds (show (0 : ℤ) < (D.q : ℕ) by
      exact_mod_cast D.q_pos) with hforward | hreverse
  · left
    apply D.toOrderedCentralBlock.hasDensityEndgame_of_raw_second_bound
    simpa [D.second_left_eq, D.second_right_eq] using hforward
  · exact Or.inr hreverse

/-- Eventual extraction of the concrete ordered/density data for maximizing
admissible sets is exactly the upstream-to-endgame bridge.  It deliberately
quantifies only over maximizers: empty bounded admissible sets cannot satisfy
the positive-`q` conclusion. -/
theorem eventually_density_endgame_of_eventually_data
    (hdata : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℤ, IsBoundedAdmissible N A → A.card = k N →
        Nonempty (DensityEndgameData N A)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℤ, IsBoundedAdmissible N A → A.card = k N →
        HasDensityEndgame N A := by
  filter_upwards [hdata] with N hN
  intro A hA hcard
  exact (hN A hA hcard).some.hasDensityEndgame

/-- Consequently, an eventual extractor for the concrete central/density data
immediately yields the sharp square bound for the extremal function. -/
theorem eventually_k_sq_le_of_eventually_data
    (hdata : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℤ, IsBoundedAdmissible N A → A.card = k N →
        Nonempty (DensityEndgameData N A)) :
    ∀ᶠ N : ℕ in Filter.atTop, (k N + 1) ^ 2 ≤ 4 * N + 1 := by
  have hendgame := eventually_density_endgame_of_eventually_data hdata
  filter_upwards [hendgame] with N hN
  exact k_sq_le_of_maximizers_density_endgame hN

end

end Erdos874
