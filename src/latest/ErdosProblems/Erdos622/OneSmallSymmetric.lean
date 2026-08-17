import ErdosProblems.Erdos622.AlmostBipartiteRegimeCounts
import ErdosProblems.Erdos622.OneSmallGaussian

/-!
# The symmetric one-small-cover regime

This module proves the one-small-cover counting estimate when the large
minimum cover lies in the balanced part `A₀ = A \ T`.  In contrast with the
right-hand arm, transferring the resulting sampled forest back to the
original part `A` loses no edges.
-/

open Filter Finset Real
open scoped BigOperators Topology SimpleGraph

namespace Erdos622.AlmostBipartiteRegimeCounts

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Arithmetic of the positive original-cut window used when the balanced
left cover is the large one.  The lower endpoint fixes the left orientation;
the upper endpoint, together with the product arm, pays for the required
left forest. -/
lemma oneSmall_positive_window_bounds
    {n K d C x y : ℕ}
    (hK : 16 ≤ K) (hsqrt : K ≤ Nat.sqrt n)
    (hd : d ≤ sqrtCoverThreshold K n)
    (hy : y ≤ n - d)
    (hprod : n + 1 ≤ sqrtCoverThreshold K n * (C + 1))
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + ((n - d) - y)) ∈
      Set.Icc 0 ((K : ℝ) * Real.sqrt 2 / 16)) :
    y ≤ x ∧
      (((x - y : ℕ) : ℝ) ≤ (1 / 4 - 1 / 64 : ℝ) * C) := by
  let s := Nat.sqrt n
  let r := sqrtCoverThreshold K n
  have hKpos : 0 < K := by omega
  have hspos : 0 < s := lt_of_lt_of_le (by omega) hsqrt
  have hrpos : 0 < r := by
    dsimp [r, sqrtCoverThreshold]
    exact Nat.div_pos hsqrt hKpos
  have hsd : d ≤ s := hd.trans (by
    dsimp [r, sqrtCoverThreshold]
    exact Nat.div_le_self s K)
  have hsn : s * s ≤ n := by simpa [s] using Nat.sqrt_le n
  have hKr : K * r ≤ s := by
    dsimp [r, sqrtCoverThreshold]
    simpa [Nat.mul_comm] using Nat.mul_div_le s K
  have hKC : K * s ≤ C := by
    have hprod' : n + 1 ≤ r * (C + 1) := by simpa [r] using hprod
    by_contra hnot
    have hC : C + 1 ≤ K * s := by omega
    have hmul1 : r * (C + 1) ≤ r * (K * s) := Nat.mul_le_mul_left r hC
    have hmul2 : r * (K * s) ≤ s * s := by
      calc
        r * (K * s) = (K * r) * s := by ring
        _ ≤ s * s := Nat.mul_le_mul_right s hKr
    have : r * (C + 1) ≤ n := hmul1.trans (hmul2.trans hsn)
    omega
  have hnpos : 0 < n := by
    have : 0 < s * s := Nat.mul_pos hspos hspos
    omega
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdn : d ≤ n := hsd.trans (by simpa [s] using Nat.sqrt_le_self n)
  have hnum :
      (2 * (x + ((n - d) - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y - d) := by
    push_cast [Nat.cast_sub hdn, Nat.cast_sub hy]
    ring
  have hlower : (0 : ℝ) ≤ (x : ℝ) - y - d := by
    have hw := hwindow.1
    unfold BinomialCLT.standardizedBinomialPoint at hw
    norm_num at hw
    rw [Nat.cast_sub hy, Nat.cast_sub hdn, hnum] at hw
    have hden : 0 < Real.sqrt 2 * Real.sqrt n := by positivity
    have hw' := (le_div_iff₀ hden).mp hw
    nlinarith
  have hyxReal : (y : ℝ) ≤ x := by linarith
  have hyx : y ≤ x := by exact_mod_cast hyxReal
  refine ⟨hyx, ?_⟩
  have hupper :
      ((x : ℝ) - y - d) ≤ (K : ℝ) / 16 * Real.sqrt n := by
    have hw := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hw
    norm_num at hw
    rw [Nat.cast_sub hy, Nat.cast_sub hdn, hnum] at hw
    have hsqrtmul : Real.sqrt (2 * n : ℝ) = Real.sqrt 2 * Real.sqrt n := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_le_iff₀ (by positivity : 0 < Real.sqrt 2 * Real.sqrt n)] at hw
    nlinarith [hsqrt2sq]
  have hsqrtlt : Real.sqrt n < (s : ℝ) + 1 := by
    have hnlt : n < (s + 1) * (s + 1) := by
      simpa [s] using Nat.lt_succ_sqrt n
    have hnltReal : (n : ℝ) < ((s + 1) * (s + 1) : ℕ) := by
      exact_mod_cast hnlt
    have hsqrtsq : (Real.sqrt n) ^ 2 = n :=
      Real.sq_sqrt (by positivity)
    norm_num at hnltReal
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hdles : (d : ℝ) ≤ s := by exact_mod_cast hsd
  have htarget : ((x : ℝ) - y) ≤ (15 / 64 : ℝ) * (K * s) := by
    have hKreal : (16 : ℝ) ≤ K := by exact_mod_cast hK
    have hsreal : (K : ℝ) ≤ s := by exact_mod_cast hsqrt
    have hstep : ((x : ℝ) - y) ≤
        (K : ℝ) / 16 * ((s : ℝ) + 1) + s := by
      nlinarith
    calc
      ((x : ℝ) - y) ≤
          (K : ℝ) / 16 * ((s : ℝ) + 1) + s := hstep
      _ ≤ (15 / 64 : ℝ) * (K * s) := by nlinarith
  have hKCreal : ((K * s : ℕ) : ℝ) ≤ C := by exact_mod_cast hKC
  have hscale : (15 / 64 : ℝ) * ((K : ℝ) * s) ≤
      (15 / 64 : ℝ) * C :=
    mul_le_mul_of_nonneg_left (by simpa using hKCreal) (by norm_num)
  have hfinal : ((x : ℝ) - y) ≤ (15 / 64 : ℝ) * C :=
    htarget.trans hscale
  calc
    (((x - y : ℕ) : ℝ)) = (x : ℝ) - y := by
      rw [Nat.cast_sub hyx]
    _ ≤ (15 / 64 : ℝ) * C := hfinal
    _ = (1 / 4 - 1 / 64 : ℝ) * C := by ring

/-- The one-small-cover arm in which the balanced left cover is forced
large.  The sampled matching is found in `A₀ = A \ T`; since `A₀ ⊆ A`,
the resulting forest is a forest on the original sampled left part without
any transfer loss. -/
theorem eventually_oneSmallCover_left_goodSample_count
    {ε : ℝ} (hε : 0 < ε) {K : ℕ}
    (hK : 16 ≤ K)
    (hgauss : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ C : Finset (Fin (2 * n))),
        IsCut A B → n ≤ A.card →
        A.card - n ≤ sqrtCoverThreshold K n →
        A₀ = A \ T →
        IsMinimumVertexCoverOn G A₀ C →
        n + 1 ≤ sqrtCoverThreshold K n * (C.card + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hKpos : 0 < K := by omega
  have hab : (0 : ℝ) ≤ (K : ℝ) * Real.sqrt 2 / 16 := by positivity
  have hclt :=
    BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio hab hgauss
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hclt
  have hclt2 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) - ε / 2 <
        (BinomialCLT.fairBinomialWindowCount (2 * n) 0
          ((K : ℝ) * Real.sqrt 2 / 16) : ℝ) /
          (2 : ℝ) ^ (2 * n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    exact hN (2 * n) (by omega)
  have hhall := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := 1) (eps := (1 / 64 : ℝ)) (delta := ε / 2)
      (by omega) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [hclt2, hhall,
      Filter.eventually_ge_atTop (K * K)] with n hnWindow hnHall hnlarge
  intro G A B T A₀ C hcut hnA hsmall hA₀ hC hprod
  have hsqrt : K ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hnlarge)
  have hsum : A.card + B.card = 2 * n := by
    simpa using hcut.card_add_card
  let d := A.card - n
  have ha : A.card = n + d := by dsimp [d]; omega
  have hdle : d ≤ n := by omega
  have hb : B.card = n - d := by omega
  have hCsqrt : sqrtCoverThreshold 1 n ≤ C.card := by
    simp only [sqrtCoverThreshold, Nat.div_one]
    have honeK : 1 < K := by omega
    simpa using (coverProductArm_forces_sqrtCover
      (n := n) (K := K) (H := 1) (D := C.card) honeK hprod)
  let threshold : ℝ := (1 / 4 - 1 / 64 : ℝ) * C.card
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
        Set.Icc 0 ((K : ℝ) * Real.sqrt 2 / 16)
  let Failure : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S threshold
  have hfailure :
      (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        (ε / 2) * (2 : ℝ) ^ (2 * n) := by
    have h := hnHall (Fin (2 * n)) G A₀ C hC hCsqrt
    simpa [Failure, threshold, almostBipartiteCount,
      almostBipartiteEvent] using h
  have hcountEq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P =
        BinomialCLT.fairBinomialWindowCount (2 * n) 0
          ((K : ℝ) * Real.sqrt 2 / 16) := by
    simpa [P] using cut_difference_window_count hcut 0
      ((K : ℝ) * Real.sqrt 2 / 16)
  have hwindowRaw :
      ((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    rw [hcountEq]
    exact le_of_lt ((lt_div_iff₀ (by positivity)).mp hnWindow)
  have hgoodWindow : ∀ S : Finset (Fin (2 * n)), S ⊆ Finset.univ →
      P S → ¬ Failure S → IsKGoodSample G A B S 0 := by
    intro S hSuniv hSP hnotFailure
    have hy : (S ∩ B).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hbnds := oneSmall_positive_window_bounds hK hsqrt
      (d := d) (C := C.card) (x := (S ∩ A).card)
      (y := (S ∩ B).card) (by simpa [d] using hsmall)
      (by simpa [hb] using hy) hprod (by simpa [P, hb] using hSP)
    have hpartCard :
        (restrictedPart S B).card ≤ (restrictedPart S A).card := by
      simpa only [card_restrictedPart_eq_inter] using hbnds.1
    have hmatching : RandomCover.HasMatchingAtLeast
        (internalGraph G A₀) S threshold := by
      simpa [Failure] using hnotFailure
    obtain ⟨M, hMmatching, hMsupport, hMcard⟩ := hmatching
    have hmatchingTarget : RandomCover.HasMatchingAtLeast
        (internalGraph G A₀) S
          (((restrictedPart S A).card -
            (restrictedPart S B).card : ℕ) : ℝ) := by
      refine ⟨M, hMmatching, hMsupport, ?_⟩
      have hthreshold :
          (((restrictedPart S A).card -
            (restrictedPart S B).card : ℕ) : ℝ) ≤ threshold := by
        simpa only [card_restrictedPart_eq_inter] using hbnds.2
      exact hthreshold.trans hMcard
    have hforest₀ := hmatchingTarget.induce_internalGraph
    have hpartMono : restrictedPart S A₀ ⊆ restrictedPart S A := by
      intro v hv
      apply mem_restrictedPart.mpr
      have hvA₀ := mem_restrictedPart.mp hv
      rw [hA₀] at hvA₀
      exact Finset.sdiff_subset hvA₀
    have hforest : ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
        (restrictedPart S A)
        ((restrictedPart S A).card - (restrictedPart S B).card) :=
      ContainsLinearForestWith.mono_vertexSet hforest₀ hpartMono
    refine ⟨restrictedParts_isCut hcut, Or.inl ⟨hpartCard, ?_⟩⟩
    simpa using hforest
  have hgood := goodSample_count_of_window_failure G P Failure
    (((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n)) (ε / 2)
    hgoodWindow hwindowRaw (by simpa using hfailure)
  convert hgood using 1 <;> simp <;> ring

/-- Unconditional parameterized form of the symmetric one-small-cover arm.
For every positive error, a fixed integer scale `K` is chosen once and for
all.  The same `K` then works uniformly for every sufficiently large graph.

The parameter theorem is phrased for the negative one-small-cover window.
Gaussian symmetry and interval monotonicity show that the positive window
`[0,K√2/16]` contains at least as much mass: its endpoint is beyond
`M√2` because `16M < K`, and the omitted interval near zero has
nonnegative mass. -/
theorem exists_eventually_oneSmallCover_left_goodSample_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 16 ≤ K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n)))
          (A B T A₀ C : Finset (Fin (2 * n))),
          IsCut A B → n ≤ A.card →
          A.card - n ≤ sqrtCoverThreshold K n →
          A₀ = A \ T →
          IsMinimumVertexCoverOn G A₀ C →
          n + 1 ≤ sqrtCoverThreshold K n * (C.card + 1) →
          ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  obtain ⟨K, M, hM, hMK, hnegative⟩ :=
    OneSmallGaussian.exists_oneSmallCover_gaussian_parameters hε
  have hK : 16 ≤ K := by omega
  have hKpos : 0 < K := by omega
  let u : ℝ := (M : ℝ) * Real.sqrt 2
  let v : ℝ := Real.sqrt 2 / K
  let w : ℝ := (K : ℝ) * Real.sqrt 2 / 16
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvu : v ≤ u := by
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hinv : (1 : ℝ) / K ≤ M :=
      ((div_le_one hKreal).2 hKone).trans hMreal
    have hmul := mul_le_mul_of_nonneg_right hinv hsqrt2.le
    simpa [u, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have huw : u ≤ w := by
    have hMKreal : (16 : ℝ) * M ≤ K := by
      exact_mod_cast (Nat.le_of_lt hMK)
    dsimp [u, w]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    have hmul := mul_le_mul_of_nonneg_right hMKreal hsqrt2.le
    nlinarith
  have hhalfMono : gaussianHalfInterval u ≤ gaussianHalfInterval w :=
    gaussianHalfInterval_mono (by dsimp [u]; positivity) huw
  have hhalfV : 0 ≤ gaussianHalfInterval v := by
    have hmono := gaussianHalfInterval_mono (a := 0) (b := v) (by norm_num) hv
    simpa [gaussianHalfInterval] using hmono
  have hc : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  have hpositiveEq :
      BinomialCLT.gaussianWindowMass 0 w = gaussianWindow 0 w := by
    simpa using gaussianWindowMass_eq_gaussianWindow (u := 0) (v := w)
      (by norm_num) hw
  have hdominates :
      BinomialCLT.gaussianWindowMass (-u) (-v) ≤
        BinomialCLT.gaussianWindowMass 0 w := by
    calc
      BinomialCLT.gaussianWindowMass (-u) (-v) =
          (gaussianHalfInterval u - gaussianHalfInterval v) /
            Real.sqrt (2 * Real.pi) :=
        OneSmallGaussian.gaussianWindowMass_neg_neg hv hvu
      _ ≤ gaussianHalfInterval w / Real.sqrt (2 * Real.pi) := by
        rw [div_le_div_iff_of_pos_right hc]
        linarith
      _ = gaussianWindow 0 w := by
        simp [gaussianWindow, gaussianHalfInterval]
      _ = BinomialCLT.gaussianWindowMass 0 w := hpositiveEq.symm
  have hpositive : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16) := by
    dsimp [u, v, w] at hnegative hdominates ⊢
    exact hnegative.trans_le hdominates
  exact ⟨K, hK,
    eventually_oneSmallCover_left_goodSample_count hε hK hpositive⟩

end

end Erdos622.AlmostBipartiteRegimeCounts
