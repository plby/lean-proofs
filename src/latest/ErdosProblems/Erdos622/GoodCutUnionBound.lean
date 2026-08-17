/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.GoodCutHamiltonicity

/-!
# A sharp two-sided low-cross-degree bound

The deterministic absorber protects the low-cross-degree vertices on both
sides of a cut.  Bounding the two sides separately loses the useful fact that
the two side sizes have fixed sum.  Here we add the two *incidence deficiency*
inequalities first and only then use
`4 * |X| * |Y| <= (|X| + |Y|)^2`.  This gives a direct estimate for the union
of the two low sets.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622.GoodCutHamiltonicity

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

open SimpleGraph
open Trichotomy

/-- The elementary product estimate for the two sides of a finite cut. -/
theorem four_mul_cut_cards_le_card_sq {X Y : Finset V}
    (hcut : IsCut X Y) :
    4 * (X.card : ℝ) * Y.card <= (Fintype.card V : ℝ) ^ 2 := by
  have haddNat := hcut.card_add_card
  have hadd : (X.card : ℝ) + Y.card = Fintype.card V := by
    exact_mod_cast haddNat
  nlinarith [sq_nonneg ((X.card : ℝ) - Y.card)]

/-- Direct two-sided deficiency estimate.  Each absent crossing edge is
charged at most once from each endpoint, which accounts for the factor `2`.
The cardinality on the left is the cardinality of the union, not the sum of
two independently estimated upper bounds. -/
theorem card_lowCrossSet_union_mul_gap_le_two_deficiency
    (G : SimpleGraph V) (X Y : Finset V) (d m : ℝ)
    (hcut : IsCut X Y)
    (hmX : m <= (X.card : ℝ)) (hmY : m <= (Y.card : ℝ)) :
    ((lowCrossSet G X Y d ∪ lowCrossSet G Y X d).card : ℝ) * (m - d) <=
      2 * ((X.card : ℝ) * Y.card - edgeCount G X Y) := by
  let LX := lowCrossSet G X Y d
  let LY := lowCrossSet G Y X d
  have hLX := card_lowCrossSet_mul_gap_le_deficiency G X Y d
  have hLY := card_lowCrossSet_mul_gap_le_deficiency G Y X d
  rw [edgeCount_comm G Y X] at hLY
  have hdisj : Disjoint LX LY := by
    exact hcut.1.mono
      (lowCrossSet_subset G X Y d) (lowCrossSet_subset G Y X d)
  have hcardNat : (LX ∪ LY).card = LX.card + LY.card :=
    Finset.card_union_of_disjoint hdisj
  have hcard : ((LX ∪ LY).card : ℝ) = (LX.card : ℝ) + LY.card := by
    exact_mod_cast hcardNat
  have hLXnonneg : (0 : ℝ) <= LX.card := by positivity
  have hLYnonneg : (0 : ℝ) <= LY.card := by positivity
  dsimp only [LX, LY] at hLX hLY hcard ⊢
  rw [hcard]
  nlinarith

/-- If the crossing graph misses at most `eps * N^2` edges from the balanced
extremal value, the union of the low sets has the stated strict bound.  The
equation `N = |V|` lets the proof use `4|X||Y| <= N^2` exactly. -/
theorem card_lowCrossSet_union_lt_of_dense_cut
    (G : SimpleGraph V) (X Y : Finset V) {N delta eps q K : ℝ}
    (hcut : IsCut X Y)
    (hNcard : (Fintype.card V : ℝ) = N)
    (hXlower : N / 2 - delta <= (X.card : ℝ))
    (hYlower : N / 2 - delta <= (Y.card : ℝ))
    (hdense : N ^ 2 / 4 - eps * N ^ 2 <= edgeCount G X Y)
    (hgap : 0 < N / 2 - delta - q)
    (hnumeric : 2 * eps * N ^ 2 < K * (N / 2 - delta - q)) :
    ((lowCrossSet G X Y q ∪ lowCrossSet G Y X q).card : ℝ) < K := by
  have hprod4 := four_mul_cut_cards_le_card_sq (V := V) hcut
  rw [hNcard] at hprod4
  have hdef : (X.card : ℝ) * Y.card - edgeCount G X Y <= eps * N ^ 2 := by
    nlinarith
  have hinc := card_lowCrossSet_union_mul_gap_le_two_deficiency
    G X Y q (N / 2 - delta) hcut hXlower hYlower
  nlinarith

/-- Natural-number form of `card_lowCrossSet_union_lt_of_dense_cut`, suited
to the protected-set budget in the absorber. -/
theorem card_lowCrossSet_union_le_of_dense_cut
    (G : SimpleGraph V) (X Y : Finset V) {N delta eps q : ℝ} {ell : ℕ}
    (hcut : IsCut X Y)
    (hNcard : (Fintype.card V : ℝ) = N)
    (hXlower : N / 2 - delta <= (X.card : ℝ))
    (hYlower : N / 2 - delta <= (Y.card : ℝ))
    (hdense : N ^ 2 / 4 - eps * N ^ 2 <= edgeCount G X Y)
    (hgap : 0 < N / 2 - delta - q)
    (hnumeric : 2 * eps * N ^ 2 <
      (((ell + 1 : ℕ) : ℝ) * (N / 2 - delta - q))) :
    (lowCrossSet G X Y q ∪ lowCrossSet G Y X q).card <= ell := by
  have hreal :
      ((lowCrossSet G X Y q ∪ lowCrossSet G Y X q).card : ℝ) <
        (((ell + 1 : ℕ) : ℝ)) :=
    card_lowCrossSet_union_lt_of_dense_cut G X Y hcut hNcard
      hXlower hYlower hdense hgap hnumeric
  have hnat :
      (lowCrossSet G X Y q ∪ lowCrossSet G Y X q).card < ell + 1 := by
    exact_mod_cast hreal
  omega

/-- Sharp-union version of the high-level deterministic DKM lemma.  Compared
with `IsKGoodCut.isHamiltonian_of_dense_crossing`, its protected-set budget
contains `ell` rather than `2 * ell`. -/
theorem IsKGoodCut.isHamiltonian_of_dense_crossing_union {X Y : Finset V}
    {k ell t d : ℕ} (hgood : IsKGoodCut G X Y k) (anchor : V)
    {N delta eps : ℝ}
    (hNcard : (Fintype.card V : ℝ) = N)
    (hXlower : N / 2 - delta <= (X.card : ℝ))
    (hYlower : N / 2 - delta <= (Y.card : ℝ))
    (hdense : N ^ 2 / 4 - eps * N ^ 2 <= edgeCount G X Y)
    (hgap : 0 < N / 5 - delta)
    (hlowNumeric : 2 * eps * N ^ 2 <
      (((ell + 1 : ℕ) : ℝ) * (N / 5 - delta)))
    (hsizeLeft : 2 * (X.card - Y.card) + ell + 1 <= t)
    (hsizeRight : 2 * (Y.card - X.card) + ell + 1 <= t)
    (hd : (d : ℝ) <= 3 * N / 10)
    (hminCross : ∀ v, 3 * t <= (crossNeighbors G X Y v).card)
    (hfirst : 10 * t < d + 1)
    (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
    (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) <=
      2 * (d + 1))
    (hV : 3 <= Fintype.card V) : G.IsHamiltonian := by
  have hLcard :
      (lowCrossSet G X Y (3 * N / 10) ∪
        lowCrossSet G Y X (3 * N / 10)).card <= ell := by
    apply card_lowCrossSet_union_le_of_dense_cut G X Y hgood.1 hNcard
      hXlower hYlower hdense
    · convert hgap using 1 <;> ring
    · convert hlowNumeric using 1 <;> ring
  exact IsKGoodCut.isHamiltonian_of_lowCrossUnion_bound hgood anchor hLcard
    hsizeLeft hsizeRight hd hminCross hfirst hcommon hclose hV

/-- The scalar inequality behind the concrete hierarchy used in the final
almost-bipartite case.  Here `x` is the ambient half-order, `N` is the sample
order, and `ell` will be `(n / 384 + 1 : ℕ)`. -/
theorem concrete_union_low_numeric {x N ell : ℝ}
    (hx : 0 < x)
    (hNwindow : |N - x| < (1 / 1048576 : ℝ) * x)
    (hell : x / 384 < ell) :
    2 * (1 / 4096 : ℝ) * N ^ 2 <
      ell * (N / 5 - x / 2048) := by
  have hw := abs_lt.mp hNwindow
  have hNlower : (1 - (1 / 1048576 : ℝ)) * x < N := by
    nlinarith
  have hNupper : N < (1 + (1 / 1048576 : ℝ)) * x := by
    nlinarith
  have hNpos : 0 < N := by
    have hc : (0 : ℝ) < 1 - 1 / 1048576 := by norm_num
    have hcx : 0 < (1 - (1 / 1048576 : ℝ)) * x := mul_pos hc hx
    linarith
  have hupperPos : 0 < (1 + (1 / 1048576 : ℝ)) * x := by positivity
  have hNsq : N ^ 2 <
      ((1 + (1 / 1048576 : ℝ)) * x) ^ 2 := by
    nlinarith
  have hgapLower :
      ((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) * x <
        N / 5 - x / 2048 := by
    nlinarith
  have hcoeffPos :
      (0 : ℝ) < (1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048 := by
    norm_num
  have hellPos : 0 < ell := (div_pos hx (by norm_num)).trans hell
  have hleft :
      2 * (1 / 4096 : ℝ) * N ^ 2 <
        (2 * (1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2) * x ^ 2 := by
    have hc : (0 : ℝ) < 2 * (1 / 4096 : ℝ) := by norm_num
    calc
      2 * (1 / 4096 : ℝ) * N ^ 2 <
          2 * (1 / 4096 : ℝ) *
            (((1 + (1 / 1048576 : ℝ)) * x) ^ 2) :=
        mul_lt_mul_of_pos_left hNsq hc
      _ = (2 * (1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2) * x ^ 2 := by ring
  have hcoefficient :
      2 * (1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2 <
        (1 / 384 : ℝ) *
          ((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) := by
    norm_num
  have hmiddle :
      (2 * (1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2) * x ^ 2 <
        (x / 384) *
          (((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) * x) := by
    have hxsq : 0 < x ^ 2 := sq_pos_of_pos hx
    calc
      _ < ((1 / 384 : ℝ) *
          ((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048)) * x ^ 2 :=
        mul_lt_mul_of_pos_right hcoefficient hxsq
      _ = _ := by ring
  have hright1 :
      (x / 384) *
          (((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) * x) <
        ell * (((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) * x) := by
    exact mul_lt_mul_of_pos_right hell (mul_pos hcoeffPos hx)
  have hright2 :
      ell * (((1 - (1 / 1048576 : ℝ)) / 5 - 1 / 2048) * x) <
        ell * (N / 5 - x / 2048) :=
    mul_lt_mul_of_pos_left hgapLower hellPos
  exact hleft.trans (hmiddle.trans (hright1.trans hright2))

/-- Arithmetic extraction of the concrete sampled-part bounds.  This lemma
is graph-free so the sampling layer can feed it just the three concentration
windows and the cardinality conclusions of the tailored cut. -/
theorem concrete_sample_part_bounds
    {n N a b x y : ℕ} (hn : 65536 ≤ n)
    (hab : a + b = 2 * n) (hna : n ≤ a)
    (haUpper : (a : ℝ) ≤
      (1 / 2 + 16 * (1 / 65536 : ℝ)) * (2 * n : ℝ))
    (hNwindow : |(N : ℝ) - n| < (1 / 1048576 : ℝ) * n)
    (hxWindow : |(x : ℝ) - (a : ℝ) / 2| <
      (1 / 1048576 : ℝ) * n)
    (hyWindow : |(y : ℝ) - (b : ℝ) / 2| <
      (1 / 1048576 : ℝ) * n) :
    (N : ℝ) / 2 - (n : ℝ) / 2048 ≤ x ∧
    (N : ℝ) / 2 - (n : ℝ) / 2048 ≤ y ∧
    max x y ≤ n / 2 + n / 1024 ∧
    x - y ≤ n / 2000 ∧ y - x ≤ n / 2000 := by
  have habReal : (a : ℝ) + b = 2 * n := by exact_mod_cast hab
  have hnaReal : (n : ℝ) ≤ a := by exact_mod_cast hna
  have haUpper' : (a : ℝ) ≤ (1 + 1 / 2048 : ℝ) * n := by
    norm_num at haUpper ⊢
    nlinarith
  have hN := abs_lt.mp hNwindow
  have hxw := abs_lt.mp hxWindow
  have hyw := abs_lt.mp hyWindow
  have hXlower : (N : ℝ) / 2 - (n : ℝ) / 2048 ≤ x := by
    norm_num at hN hxw ⊢
    nlinarith
  have hYlower : (N : ℝ) / 2 - (n : ℝ) / 2048 ≤ y := by
    norm_num at hN hyw ⊢
    nlinarith
  have hn2 : n < 2 * (n / 2 + 1) :=
    Nat.lt_mul_div_succ n (by norm_num)
  have hn1024 : n < 1024 * (n / 1024 + 1) :=
    Nat.lt_mul_div_succ n (by norm_num)
  have hn2Real : (n : ℝ) < 2 * ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hn2
  have hn1024Real : (n : ℝ) <
      1024 * ((n / 1024 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hn1024
  have hmaxX : x ≤ n / 2 + n / 1024 := by
    have hxReal : (x : ℝ) <
        (((n / 2 + n / 1024 : ℕ) : ℝ)) + 1 := by
      have hnReal : (65536 : ℝ) ≤ n := by exact_mod_cast hn
      norm_num at hxw haUpper' hn2Real hn1024Real ⊢
      nlinarith
    have hxNat : x < n / 2 + n / 1024 + 1 := by exact_mod_cast hxReal
    omega
  have hmaxY : y ≤ n / 2 + n / 1024 := by
    have hyReal : (y : ℝ) <
        (((n / 2 + n / 1024 : ℕ) : ℝ)) + 1 := by
      have hnReal : (65536 : ℝ) ≤ n := by exact_mod_cast hn
      norm_num at hyw hn2Real hn1024Real ⊢
      nlinarith
    have hyNat : y < n / 2 + n / 1024 + 1 := by exact_mod_cast hyReal
    omega
  have hdiffXY : x - y ≤ n / 2000 := by
    by_cases hyx : y ≤ x
    · have hsubReal : ((x - y : ℕ) : ℝ) = (x : ℝ) - y := by
        rw [Nat.cast_sub hyx]
      have hlt : ((x - y : ℕ) : ℝ) < (n : ℝ) / 2000 := by
        rw [hsubReal]
        have hbase : (x : ℝ) - y <
            ((a : ℝ) - n) + 2 * (1 / 1048576 : ℝ) * n := by
          linarith only [hxw.2, hyw.1, habReal]
        have hexcess : (a : ℝ) - n ≤ (n : ℝ) / 2048 := by
          linarith only [haUpper']
        have hcoeff : (1 / 2048 : ℝ) + 2 * (1 / 1048576) < 1 / 2000 := by
          norm_num
        have hnpos : (0 : ℝ) < n := by positivity
        have hcoeffn := mul_lt_mul_of_pos_right hcoeff hnpos
        linarith only [hbase, hexcess, hcoeffn]
      have hmulReal : ((2000 * (x - y) : ℕ) : ℝ) < n := by
        push_cast
        linarith only [hlt]
      have hmul : 2000 * (x - y) ≤ n := by
        exact_mod_cast hmulReal.le
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        simpa [Nat.mul_comm] using hmul)
    · have hxy : x ≤ y := Nat.le_of_lt (Nat.lt_of_not_ge hyx)
      simp only [Nat.sub_eq_zero_of_le hxy]
      exact Nat.zero_le _
  have hdiffYX : y - x ≤ n / 2000 := by
    by_cases hxy : x ≤ y
    · have hsubReal : ((y - x : ℕ) : ℝ) = (y : ℝ) - x := by
        rw [Nat.cast_sub hxy]
      have hlt : ((y - x : ℕ) : ℝ) < (n : ℝ) / 2000 := by
        rw [hsubReal]
        have hbase : (y : ℝ) - x <
            ((b : ℝ) - a) / 2 + 2 * (1 / 1048576 : ℝ) * n := by
          linarith only [hyw.2, hxw.1]
        have hba : (b : ℝ) - a ≤ 0 := by
          linarith only [habReal, hnaReal]
        have hcoeff : 2 * (1 / 1048576 : ℝ) < 1 / 2000 := by norm_num
        have hnpos : (0 : ℝ) < n := by positivity
        have hcoeffn := mul_lt_mul_of_pos_right hcoeff hnpos
        linarith only [hbase, hba, hcoeffn]
      have hmulReal : ((2000 * (y - x) : ℕ) : ℝ) < n := by
        push_cast
        linarith only [hlt]
      have hmul : 2000 * (y - x) ≤ n := by
        exact_mod_cast hmulReal.le
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        simpa [Nat.mul_comm] using hmul)
    · have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hxy)
      simp only [Nat.sub_eq_zero_of_le hyx]
      exact Nat.zero_le _
  exact ⟨hXlower, hYlower, max_le hmaxX hmaxY, hdiffXY, hdiffYX⟩

/-- The ambient crossing-density and sampled-edge concentration inequalities
imply the normalized density input used by the sharp union bound. -/
theorem concrete_sample_crossing_density
    {n N ambientEdges sampleEdges : ℝ} (hn : 0 < n)
    (hNwindow : |N - n| < (1 / 1048576 : ℝ) * n)
    (hambient :
      (1 / 4 - 14 * (1 / 65536 : ℝ)) * (2 * n) ^ 2 ≤ ambientEdges)
    (hsample : |sampleEdges - ambientEdges / 4| <
      (1 / 1048576 : ℝ) * n ^ 2) :
    N ^ 2 / 4 - (1 / 4096 : ℝ) * N ^ 2 ≤ sampleEdges := by
  have hN := abs_lt.mp hNwindow
  have hs := abs_lt.mp hsample
  have hNupper : N < (1 + (1 / 1048576 : ℝ)) * n := by
    linarith only [hN.2]
  have hNlower : (1 - (1 / 1048576 : ℝ)) * n < N := by
    linarith only [hN.1]
  have hNpos : 0 < N := by
    have hc : (0 : ℝ) < 1 - 1 / 1048576 := by norm_num
    have := mul_pos hc hn
    linarith only [this, hNlower]
  have hupperPos : 0 < (1 + (1 / 1048576 : ℝ)) * n := by positivity
  have hNsq : N ^ 2 <
      ((1 + (1 / 1048576 : ℝ)) * n) ^ 2 := by
    nlinarith only [hNupper, hNpos, hupperPos]
  have htargetUpper :
      N ^ 2 / 4 - (1 / 4096 : ℝ) * N ^ 2 <
        ((1 / 4 - 1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2) * n ^ 2 := by
    have hc : (0 : ℝ) < 1 / 4 - 1 / 4096 := by norm_num
    calc
      N ^ 2 / 4 - (1 / 4096 : ℝ) * N ^ 2 =
          (1 / 4 - 1 / 4096 : ℝ) * N ^ 2 := by ring
      _ < (1 / 4 - 1 / 4096 : ℝ) *
          (((1 + (1 / 1048576 : ℝ)) * n) ^ 2) :=
        mul_lt_mul_of_pos_left hNsq hc
      _ = _ := by ring
  have hcoeff :
      (1 / 4 - 1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2 <
        1 / 4 - 14 * (1 / 65536 : ℝ) - 1 / 1048576 := by
    norm_num
  have hcoeffn :
      ((1 / 4 - 1 / 4096 : ℝ) *
          (1 + (1 / 1048576 : ℝ)) ^ 2) * n ^ 2 <
        (1 / 4 - 14 * (1 / 65536 : ℝ) - 1 / 1048576) * n ^ 2 := by
    exact mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hn)
  have hsampleLower :
      (1 / 4 - 14 * (1 / 65536 : ℝ) - 1 / 1048576) * n ^ 2 <
        sampleEdges := by
    nlinarith only [hambient, hs.1]
  exact (htargetUpper.trans (hcoeffn.trans hsampleLower)).le

/-- A sampled crossing-neighbour count concentrated around half of an
ambient crossing degree at least `n/32` dominates `3 * floor(n/256)`. -/
theorem concrete_sample_min_cross
    {n ambientDegree sampleDegree : ℕ}
    (hambient : (n : ℝ) / 32 ≤ ambientDegree)
    (hsample : |(sampleDegree : ℝ) - (ambientDegree : ℝ) / 2| <
      (1 / 1048576 : ℝ) * n) :
    3 * (n / 256) ≤ sampleDegree := by
  have hs := (abs_lt.mp hsample).1
  have hfloorNat : 256 * (n / 256) ≤ n := by omega
  have hfloor : (256 : ℝ) * (n / 256 : ℕ) ≤ n := by
    exact_mod_cast hfloorNat
  have hlt : ((3 * (n / 256) : ℕ) : ℝ) < sampleDegree := by
    push_cast
    norm_num at hs hambient hfloor ⊢
    nlinarith only [hs, hambient, hfloor]
  exact_mod_cast hlt.le

/-- Fully instantiated deterministic certificate used downstream.  The only
inputs left to the sampling argument are its natural outputs: the sample-size
window, lower and upper part-size bounds, crossing density, imbalance bounds,
and sampled minimum crossing degree.  All hierarchy arithmetic is discharged
here with
`rho = 2^-20`, `eps = 2^-12`, `ell = n/384`, `t = n/256`, and
`d = floor (19n/64)`. -/
theorem IsKGoodCut.isHamiltonian_of_concrete_sample_bounds {X Y : Finset V}
    {n k : ℕ} (hgood : IsKGoodCut G X Y k) (anchor : V)
    (hn : 12288 ≤ n)
    (hNwindow : |(Fintype.card V : ℝ) - n| <
      (1 / 1048576 : ℝ) * n)
    (hXlower : (Fintype.card V : ℝ) / 2 - (n : ℝ) / 2048 ≤ X.card)
    (hYlower : (Fintype.card V : ℝ) / 2 - (n : ℝ) / 2048 ≤ Y.card)
    (hmax : max X.card Y.card ≤ n / 2 + n / 1024)
    (hdense : (Fintype.card V : ℝ) ^ 2 / 4 -
      (1 / 4096 : ℝ) * (Fintype.card V : ℝ) ^ 2 ≤ edgeCount G X Y)
    (himbalanceLeft : X.card - Y.card ≤ n / 2000)
    (himbalanceRight : Y.card - X.card ≤ n / 2000)
    (hminCross : ∀ v,
      3 * (n / 256) ≤ (crossNeighbors G X Y v).card) :
    G.IsHamiltonian := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hellNat : n < 384 * (n / 384 + 1) :=
    Nat.lt_mul_div_succ n (by norm_num)
  have hell : (n : ℝ) / 384 < (((n / 384 + 1 : ℕ) : ℝ)) := by
    have hellReal : (n : ℝ) < 384 * (((n / 384 + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hellNat
    linarith
  have hlowNumeric :
      2 * (1 / 4096 : ℝ) * (Fintype.card V : ℝ) ^ 2 <
        (((n / 384 + 1 : ℕ) : ℝ)) *
          ((Fintype.card V : ℝ) / 5 - (n : ℝ) / 2048) :=
    concrete_union_low_numeric hnpos hNwindow hell
  have hgap :
      0 < (Fintype.card V : ℝ) / 5 - (n : ℝ) / 2048 := by
    have hw := (abs_lt.mp hNwindow).1
    norm_num at hw ⊢
    nlinarith
  have hsizeLeft :
      2 * (X.card - Y.card) + n / 384 + 1 ≤ n / 256 := by
    omega
  have hsizeRight :
      2 * (Y.card - X.card) + n / 384 + 1 ≤ n / 256 := by
    omega
  have hd : ((19 * n / 64 : ℕ) : ℝ) ≤
      3 * (Fintype.card V : ℝ) / 10 := by
    have hfloor : 64 * (19 * n / 64) ≤ 19 * n := by omega
    have hfloorReal : (64 : ℝ) * (19 * n / 64 : ℕ) ≤ 19 * n := by
      exact_mod_cast hfloor
    have hw := (abs_lt.mp hNwindow).1
    norm_num at hw ⊢
    nlinarith
  have hfirst : 10 * (n / 256) < 19 * n / 64 + 1 := by omega
  have hcommon :
      max X.card Y.card + 9 * (n / 256) + 1 <
        2 * (19 * n / 64 + 1) := by omega
  have hclose :
      max X.card Y.card + 2 + 2 * (9 * (n / 256) + 1) ≤
        2 * (19 * n / 64 + 1) := by omega
  have hV : 3 ≤ Fintype.card V := by
    have hw := (abs_lt.mp hNwindow).1
    have hnReal : (12288 : ℝ) ≤ n := by exact_mod_cast hn
    have hcardReal : (3 : ℝ) < Fintype.card V := by
      norm_num at hw
      nlinarith
    exact_mod_cast hcardReal.le
  exact IsKGoodCut.isHamiltonian_of_dense_crossing_union hgood anchor
    (N := (Fintype.card V : ℝ)) (delta := (n : ℝ) / 2048)
    (eps := (1 / 4096 : ℝ)) (ell := n / 384) (t := n / 256)
    (d := 19 * n / 64) rfl hXlower hYlower hdense hgap hlowNumeric
    hsizeLeft hsizeRight hd hminCross hfirst hcommon hclose hV

end Erdos622.GoodCutHamiltonicity

#print axioms Erdos622.GoodCutHamiltonicity.card_lowCrossSet_union_le_of_dense_cut
#print axioms Erdos622.GoodCutHamiltonicity.IsKGoodCut.isHamiltonian_of_dense_crossing_union
#print axioms Erdos622.GoodCutHamiltonicity.IsKGoodCut.isHamiltonian_of_concrete_sample_bounds
