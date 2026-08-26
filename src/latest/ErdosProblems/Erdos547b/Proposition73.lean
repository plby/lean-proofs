/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos547b.EC2

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoProp73

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of neighbors of `v` in `S`. -/
abbrev degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : ℕ :=
  Erdos547EC2.degreeInto G v S

theorem degreeInto_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v Finset.univ = G.degree v := by
  unfold degreeInto Erdos547EC2.degreeInto
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G.mem_neighborFinset]

/-- Passing to a smaller target set cannot increase the number of missed
vertices. -/
theorem missing_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {A B : Finset V} (hAB : A ⊆ B) :
    (A.card : ℝ) - degreeInto G v A ≤
      (B.card : ℝ) - degreeInto G v B := by
  let NA : Finset V := A.filter fun w ↦ ¬G.Adj v w
  let NB : Finset V := B.filter fun w ↦ ¬G.Adj v w
  have hN : NA ⊆ NB := by
    intro w hw
    simp only [NA, NB, Finset.mem_filter] at hw ⊢
    exact ⟨hAB hw.1, hw.2⟩
  have hcardN : NA.card ≤ NB.card := Finset.card_le_card hN
  have hpartA := Finset.card_filter_add_card_filter_not (s := A) (G.Adj v)
  have hpartB := Finset.card_filter_add_card_filter_not (s := B) (G.Adj v)
  change (A.card : ℝ) - ((A.filter fun w ↦ G.Adj v w).card : ℝ) ≤
    (B.card : ℝ) - ((B.filter fun w ↦ G.Adj v w).card : ℝ)
  have hpartAR :
      ((A.filter fun w ↦ G.Adj v w).card : ℝ) + NA.card = A.card := by
    exact_mod_cast hpartA
  have hpartBR :
      ((B.filter fun w ↦ G.Adj v w).card : ℝ) + NB.card = B.card := by
    exact_mod_cast hpartB
  have hcardNR : (NA.card : ℝ) ≤ NB.card := by exact_mod_cast hcardN
  linarith

theorem sum_missing_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (∑ b ∈ B, ((A.card : ℝ) - degreeInto G b A)) =
      ∑ a ∈ A, ((B.card : ℝ) - degreeInto G a B) := by
  have hBA : (∑ b ∈ B, (degreeInto G b A : ℝ)) =
      ((G.interedges B A).card : ℝ) := by
    exact_mod_cast Erdos547EC2.sum_degreeInto_eq_card_interedges G B A
  have hAB : (∑ a ∈ A, (degreeInto G a B : ℝ)) =
      ((G.interedges A B).card : ℝ) := by
    exact_mod_cast Erdos547EC2.sum_degreeInto_eq_card_interedges G A B
  have hedge : (G.interedges B A).card = (G.interedges A B).card := by
    have := G.symm
    exact Rel.card_interedges_comm B A
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hBA, hAB, hedge]
  ring

/-- The density-pruning engine in Proposition 7.3.  If every vertex of `A`
misses at most `q` vertices of `B`, discard from `B` the vertices which miss
more than an `eps` proportion of `A`.  The discarded set has size at most
`q / eps`; the division-free last inequality is the form used below. -/
theorem density_prune_by_missing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps)
    (hmiss : ∀ a ∈ A,
      (B.card : ℝ) - degreeInto G a B ≤ q) :
    ∃ B' : Finset V,
      B' ⊆ B ∧
      (∀ b ∈ B', (1 - eps) * (A.card : ℝ) ≤ degreeInto G b A) ∧
      (((B \ B').card : ℝ) * eps ≤ q) := by
  classical
  let B' : Finset V := B.filter fun b ↦
    (1 - eps) * (A.card : ℝ) ≤ degreeInto G b A
  let C : Finset V := B \ B'
  have hB'B : B' ⊆ B := Finset.filter_subset _ _
  have hCB : C ⊆ B := Finset.sdiff_subset
  have hgood : ∀ b ∈ B',
      (1 - eps) * (A.card : ℝ) ≤ degreeInto G b A := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  refine ⟨B', hB'B, hgood, ?_⟩
  by_cases hC : C.Nonempty
  · have hbad : ∀ b ∈ C,
        eps * (A.card : ℝ) < (A.card : ℝ) - degreeInto G b A := by
      intro b hb
      have hbB : b ∈ B := hCB hb
      have hbnot : b ∉ B' := (Finset.mem_sdiff.mp hb).2
      have hlt : (degreeInto G b A : ℝ) < (1 - eps) * (A.card : ℝ) := by
        simpa only [B', Finset.mem_filter, hbB, true_and, not_le] using hbnot
      linarith
    have hstrict :
        (C.card : ℝ) * (eps * (A.card : ℝ)) <
          ∑ b ∈ C, ((A.card : ℝ) - degreeInto G b A) := by
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using
        (Finset.sum_lt_sum_of_nonempty hC hbad)
    have hnonneg : ∀ b ∈ B,
        0 ≤ (A.card : ℝ) - degreeInto G b A := by
      intro b hb
      have hdegR : (degreeInto G b A : ℝ) ≤ (A.card : ℝ) := by
        exact_mod_cast Erdos547EC2.degreeInto_le_card G b A
      exact sub_nonneg.mpr hdegR
    have hsubset :
        (∑ b ∈ C, ((A.card : ℝ) - degreeInto G b A)) ≤
          ∑ b ∈ B, ((A.card : ℝ) - degreeInto G b A) :=
      Finset.sum_le_sum_of_subset_of_nonneg hCB (fun b hbB _ ↦ hnonneg b hbB)
    have htotal :
        (∑ b ∈ B, ((A.card : ℝ) - degreeInto G b A)) ≤
          (A.card : ℝ) * q := by
      rw [sum_missing_comm G A B]
      calc
        (∑ a ∈ A, ((B.card : ℝ) - degreeInto G a B))
            ≤ ∑ _a ∈ A, q := Finset.sum_le_sum fun a ha ↦ hmiss a ha
        _ = (A.card : ℝ) * q := by simp [mul_comm]
    have hApos : 0 < (A.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hA
    have hchain :
        (C.card : ℝ) * (eps * (A.card : ℝ)) < (A.card : ℝ) * q :=
      hstrict.trans_le (hsubset.trans htotal)
    have : (C.card : ℝ) * eps < q := by
      nlinarith
    simpa only [C] using this.le
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    have hq : 0 ≤ q := by
      obtain ⟨a, ha⟩ := hA
      have hm := hmiss a ha
      have hdeg := Erdos547EC2.degreeInto_le_card G a B
      have hdegR : (degreeInto G a B : ℝ) ≤ (B.card : ℝ) := by
        exact_mod_cast hdeg
      exact (sub_nonneg.mpr hdegR).trans hm
    simpa only [C, hCempty, Finset.card_empty, Nat.cast_zero, zero_mul] using hq

/-- `⌈n/2⌉`, represented as a natural number. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

theorem ceilHalf_cast_le (n : ℕ) :
    (ceilHalf n : ℝ) ≤ (n : ℝ) / 2 + 1 / 2 := by
  have h : 2 * ceilHalf n ≤ n + 1 := by
    simp only [ceilHalf]
    omega
  have hR : (2 : ℝ) * ceilHalf n ≤ (n : ℝ) + 1 := by
    exact_mod_cast h
  linarith

/-- Zhao's Proposition 7.3, with every cardinal inequality interpreted in
the reals exactly as in the paper.  The host has order `n`; `ceilHalf n` is
`⌈n/2⌉`. -/
theorem proposition_7_3
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (theta : ℝ) (X : Finset V)
    (hcard : Fintype.card V = n)
    (htheta0 : 0 < theta) (htheta : theta ≤ 1 / 100)
    (hn : 100 ≤ n)
    (hX : |(X.card : ℝ) - (n : ℝ) / 2| ≤ theta * n)
    (hdegree : ∀ x ∈ X, (n : ℝ) - theta * n ≤ G.degree x) :
    ∃ Y : Finset V,
      Y ⊆ Finset.univ \ X ∧
      (∀ x ∈ X, (Y.card : ℝ) - theta * n ≤ degreeInto G x Y) ∧
      (∀ y ∈ Y, (X.card : ℝ) - Real.sqrt theta * n ≤ degreeInto G y X) ∧
      (∀ x ∈ X,
        (ceilHalf n : ℝ) - Real.sqrt theta * n ≤ degreeInto G x Y) ∧
      (∀ y ∈ Y,
        (ceilHalf n : ℝ) - Real.sqrt theta * n ≤ degreeInto G y X) := by
  classical
  let t : ℝ := Real.sqrt theta
  let s : ℝ := Real.sqrt (3 * theta)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = theta := by
    dsimp only [t]
    exact Real.sq_sqrt htheta0.le
  have hs_sq : s ^ 2 = 3 * theta := by
    dsimp only [s]
    exact Real.sq_sqrt (mul_nonneg (by norm_num) htheta0.le)
  have ht_le : t ≤ 1 / 10 := by
    nlinarith
  have hs_pos : 0 < s := by
    have : 0 < 3 * theta := mul_pos (by norm_num) htheta0
    exact Real.sqrt_pos.2 this
  have hs_lower : (5 / 3 : ℝ) * t ≤ s := by
    nlinarith
  have hs_upper : s ≤ (26 / 15 : ℝ) * t := by
    nlinarith
  have hone_sub_s : 0 ≤ 1 - s := by
    have hs_le : s ≤ 1 := by
      nlinarith
    linarith
  have hnreal : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hXlower : (n : ℝ) / 2 - theta * n ≤ X.card := by
    have := (abs_le.mp hX).1
    linarith
  have hXupper : (X.card : ℝ) ≤ (n : ℝ) / 2 + theta * n := by
    have := (abs_le.mp hX).2
    linarith
  have hXposR : 0 < (X.card : ℝ) := by
    have htheta_nonneg : 0 ≤ theta := htheta0.le
    nlinarith
  have hXcardPos : 0 < X.card := by exact_mod_cast hXposR
  have hXnonempty : X.Nonempty := Finset.card_pos.mp hXcardPos
  obtain ⟨x0, hx0⟩ := hXnonempty
  have htheta_n_one : (1 : ℝ) ≤ theta * n := by
    have hdeg0 := hdegree x0 hx0
    have hlt := G.degree_lt_card_verts x0
    rw [hcard] at hlt
    have hdegUpper : (G.degree x0 : ℝ) ≤ (n : ℝ) - 1 := by
      have hnat : G.degree x0 ≤ n - 1 := Nat.le_sub_one_of_lt hlt
      have hcast : (G.degree x0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sub (by omega : 1 ≤ n)] at hcast
      norm_num at hcast
      exact hcast
    linarith
  let Y' : Finset V := Finset.univ \ X
  have hXY'disj : Disjoint X Y' := by
    exact Finset.disjoint_sdiff
  have hXY'cover : X ∪ Y' = Finset.univ := by
    exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
  have hY'cardNat : X.card + Y'.card = n := by
    rw [← Finset.card_union_of_disjoint hXY'disj, hXY'cover,
      Finset.card_univ, hcard]
  have hY'card : (Y'.card : ℝ) = n - X.card := by
    have hR : (X.card : ℝ) + (Y'.card : ℝ) = n := by
      exact_mod_cast hY'cardNat
    linarith
  have hmiss : ∀ x ∈ X,
      (Y'.card : ℝ) - degreeInto G x Y' ≤ theta * n := by
    intro x hx
    have hpartition := Erdos547EC2.degreeInto_partition G x hXY'disj hXY'cover
    rw [show Erdos547EC2.degreeInto G x Finset.univ = G.degree x from
      degreeInto_univ G x] at hpartition
    have hpartR :
        (degreeInto G x X : ℝ) + degreeInto G x Y' = G.degree x := by
      exact_mod_cast hpartition
    have hintoX : (degreeInto G x X : ℝ) ≤ X.card := by
      exact_mod_cast Erdos547EC2.degreeInto_le_card G x X
    have hdeg := hdegree x hx
    rw [hY'card]
    linarith
  obtain ⟨Y, hYY', hgood, hdiscard⟩ :=
    density_prune_by_missing G X Y' (theta * n) s ⟨x0, hx0⟩ hs_pos hmiss
  have hbadBound : (((Y' \ Y).card : ℝ) ≤ (3 / 5 : ℝ) * t * n) := by
    have hmul : ((Y' \ Y).card : ℝ) * ((5 / 3 : ℝ) * t) ≤ theta * n := by
      calc
        ((Y' \ Y).card : ℝ) * ((5 / 3 : ℝ) * t)
            ≤ ((Y' \ Y).card : ℝ) * s := by
              exact mul_le_mul_of_nonneg_left hs_lower (Nat.cast_nonneg _)
        _ ≤ theta * n := hdiscard
    have htpos : 0 < t := Real.sqrt_pos.2 htheta0
    nlinarith
  have hYcardNat : Y.card + (Y' \ Y).card = Y'.card := by
    have hcardle := Finset.card_le_card hYY'
    rw [Finset.card_sdiff_of_subset hYY']
    omega
  have hYcard : (Y.card : ℝ) + ((Y' \ Y).card : ℝ) = Y'.card := by
    exact_mod_cast hYcardNat
  have hYlower :
      (n : ℝ) / 2 - theta * n - (3 / 5 : ℝ) * t * n ≤ Y.card := by
    rw [hY'card] at hYcard
    linarith
  have hcommonX :
      (ceilHalf n : ℝ) - t * n ≤ (Y.card : ℝ) - theta * n := by
    have hceil := ceilHalf_cast_le n
    have hmargin : (1 / 2 : ℝ) ≤
        ((2 / 5 : ℝ) * t - 2 * theta) * n := by
      have ht_bound : 10 * theta ≤ t := by
        have hfac : 0 ≤ t * (1 - 10 * t) :=
          mul_nonneg ht0 (sub_nonneg.mpr (by linarith only [ht_le]))
        nlinarith only [hfac, ht_sq]
      have hcoeff : 2 * theta ≤ (2 / 5 : ℝ) * t - 2 * theta := by
        linarith only [ht_bound]
      have hmul := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have htwo : (2 : ℝ) ≤ 2 * theta * n := by
        nlinarith only [htheta_n_one]
      linarith only [hmul, htwo]
    calc
      (ceilHalf n : ℝ) - t * n
          ≤ (n : ℝ) / 2 + 1 / 2 - t * n := by linarith only [hceil]
      _ ≤ (n : ℝ) / 2 - 2 * theta * n - (3 / 5 : ℝ) * t * n := by
        linarith only [hmargin]
      _ ≤ (Y.card : ℝ) - theta * n := by linarith only [hYlower]
  have hcommonYBase :
      (ceilHalf n : ℝ) - t * n ≤
        (1 - s) * (X.card : ℝ) := by
    have hceil := ceilHalf_cast_le n
    have hcoef : theta / 2 ≤ t - s / 2 - theta + s * theta := by
      have hpoly : 0 ≤ (1 - 10 * t) * (4 - 5 * t) := by
        exact mul_nonneg
          (sub_nonneg.mpr (by linarith only [ht_le]))
          (sub_nonneg.mpr (by linarith only [ht_le]))
      have hs_half : s / 2 ≤ (13 / 15 : ℝ) * t := by
        linarith only [hs_upper]
      have hs_theta : (5 / 3 : ℝ) * t * theta ≤ s * theta := by
        exact mul_le_mul_of_nonneg_right hs_lower htheta0.le
      nlinarith only [hpoly, hs_half, hs_theta, ht_sq, ht0]
    have hmargin : (1 / 2 : ℝ) ≤
        (t - s / 2 - theta + s * theta) * n := by
      have hmul := mul_le_mul_of_nonneg_right hcoef
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have hhalf : (1 / 2 : ℝ) ≤ theta / 2 * n := by
        nlinarith only [htheta_n_one]
      linarith only [hmul, hhalf]
    have hmono := mul_le_mul_of_nonneg_left hXlower hone_sub_s
    calc
      (ceilHalf n : ℝ) - t * n
          ≤ (n : ℝ) / 2 + 1 / 2 - t * n := by linarith only [hceil]
      _ ≤ (1 - s) * ((n : ℝ) / 2 - theta * n) := by
        calc
          (n : ℝ) / 2 + 1 / 2 - t * n
              ≤ (n : ℝ) / 2 - t * n +
                  (t - s / 2 - theta + s * theta) * n := by
                linarith only [hmargin]
          _ = (1 - s) * ((n : ℝ) / 2 - theta * n) := by ring
      _ ≤ (1 - s) * (X.card : ℝ) := hmono
  have hsX : s * (X.card : ℝ) ≤ t * n := by
    have hprod := mul_le_mul hs_upper hXupper (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26 / 15) ht0)
    have hcoef : (26 / 15 : ℝ) * (1 / 2 + theta) ≤ 1 := by
      nlinarith only [htheta]
    have htnonneg : 0 ≤ t * (n : ℝ) :=
      mul_nonneg ht0 (Nat.cast_nonneg n)
    calc
      s * (X.card : ℝ)
          ≤ ((26 / 15 : ℝ) * t) * ((n : ℝ) / 2 + theta * n) := hprod
      _ = ((26 / 15 : ℝ) * (1 / 2 + theta)) * (t * n) := by ring
      _ ≤ 1 * (t * n) := mul_le_mul_of_nonneg_right hcoef htnonneg
      _ = t * n := one_mul _
  have hfirst : ∀ x ∈ X,
      (Y.card : ℝ) - theta * n ≤ degreeInto G x Y := by
    intro x hx
    have hm := (missing_mono G x hYY').trans (hmiss x hx)
    linarith
  refine ⟨Y, hYY', ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hfirst x hx
  · intro y hy
    have := hgood y hy
    nlinarith
  · intro x hx
    exact hcommonX.trans (hfirst x hx)
  · intro y hy
    have := hgood y hy
    exact hcommonYBase.trans this

end Erdos547b.ZhaoProp73

#print axioms Erdos547b.ZhaoProp73.density_prune_by_missing
#print axioms Erdos547b.ZhaoProp73.proposition_7_3
