import Mathlib
import ErdosProblems.Erdos550.OffTuranDirectBounds
import ErdosProblems.Erdos550.OffTuranMatchingSupply
import ErdosProblems.Erdos550.OffTuranWholeEdgeSplit

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Numerical instantiation of the reduced off--Turán theorem

The theorem in this file chooses every scalar parameter used by
`offTuran_reduced_parity_embedding`.  Its assumptions are the structural
regularity/matching output, the two `78ηN` matching-supply bounds, and two
explicit largeness inequalities.  In particular it has no Erdős--Sós input.
-/

open Finset SimpleGraph Finpartition SzemerediRegularity

namespace Erdos550

open Classical

set_option maxHeartbeats 5000000 in
theorem offTuran_reduced_parity_embedding_of_large
    {A V κ : Type}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype κ] [DecidableEq κ]
    {q f m₀ : ℕ} {δ εCap : ℝ}
    (c : OffTuranConstants q f m₀ δ εCap)
    (hq : 2 ≤ q)
    (T : SimpleGraph A) [DecidableRel T.Adj] (hT : T.IsTree)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : OffTuranReducedDegreeData G c.ε c.η
      (Fintype.card A) c.η m₀)
    (X Y : {C // C ∈ D.P.parts})
    (hXY : (offTuranReducedGraph G D.P c.ε c.η).Adj X Y)
    (cL cR : κ → {C // C ∈ D.P.parts})
    (hmatch : ∀ k,
      (offTuranReducedGraph G D.P c.ε c.η).Adj (cL k) (cR k))
    (hinj : Function.Injective (Sum.elim cL cR))
    (haway : ∀ k, cL k ≠ X ∧ cL k ≠ Y ∧
      cR k ≠ X ∧ cR k ≠ Y)
    (horder : Fintype.card A ≤ Fintype.card V)
    (hellEta :
      (D.P.parts.card : ℝ) ≤ c.η * Fintype.card V)
    (hsepOrder :
      (1 : ℝ) ≤
        (c.η ^ 2 /
          (128 * (SzemerediRegularity.bound c.ε ⌈4 / c.ε⌉₊ : ℝ))) *
          Fintype.card A)
    (hfloorHuge :
      16 /
        (c.η ^ 2 /
          (128 * (SzemerediRegularity.bound c.ε
              ⌈4 / c.ε⌉₊ : ℝ))) +
          9 ≤
        c.ε *
          (↑(Fintype.card V / D.P.parts.card) : ℝ) / 4)
    (hSupplyX :
      (Fintype.card A : ℝ) + 78 * c.η * Fintype.card V ≤
        ∑ k, hpHeadMatchingWeight G
          (offTuranReducedGraph G D.P c.ε c.η)
          (fun i : {C // C ∈ D.P.parts} => i.1) X cL cR k)
    (hSupplyY :
      (Fintype.card A : ℝ) + 78 * c.η * Fintype.card V ≤
        ∑ k, hpHeadMatchingWeight G
          (offTuranReducedGraph G D.P c.ε c.η)
          (fun i : {C // C ∈ D.P.parts} => i.1) Y cL cR k) :
    T ⊑ G := by
  let N : ℝ := Fintype.card V
  let n : ℝ := Fintype.card A
  let ell : ℝ := D.P.parts.card
  let L : ℕ := SzemerediRegularity.bound c.ε ⌈4 / c.ε⌉₊
  let capNat : ℕ := Fintype.card V / D.P.parts.card
  let cap : ℝ := capNat
  let τsep : ℝ := c.η ^ 2 / (128 * (L : ℝ))
  let τ : ℝ := c.η ^ 2 * cap / 32
  let Lnat : ℕ := ⌈c.η * cap / 8⌉₊
  let retainedLoss : ℝ := c.ε * (D.scale : ℝ)
  let err : ℝ := retainedLoss
  let margin : ℝ := (Lnat : ℝ) + τ + 2 * err
  let thr : ℝ := 8 * c.ε * ell / c.η
  let edgeCap : ℝ := 2 * cap
  have hη0 : 0 < c.η := c.eta_pos
  have hη1 : c.η < 1 := c.eta_small.trans (by norm_num)
  have hη100 : c.η ≤ 1 / 100 := by
    exact c.eta_small.le.trans (by norm_num)
  have hε0 : 0 < c.ε := c.eps_pos
  have hεη : c.ε ≤ c.η := c.eps_linear.le.trans (by
    nlinarith [c.eta_pos])
  have hε1 : c.ε ≤ 1 := hεη.trans hη1.le
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr hT.1.nonempty
  have hnN : n ≤ N := by
    simpa [n, N] using! (show
      (Fintype.card A : ℝ) ≤ Fintype.card V by exact_mod_cast horder)
  have hellNat : 0 < D.P.parts.card :=
    D.parts_pos c.eps_pos
  have hell0 : 0 < ell := by
    simpa [ell] using! (show (0 : ℝ) < D.P.parts.card by
      exact_mod_cast hellNat)
  have hellN : ell < N := by
    dsimp [ell, N] at *
    have := hellEta
    nlinarith [mul_lt_mul_of_pos_right hη1 hNpos]
  have hellNatN : D.P.parts.card < Fintype.card V := by
    exact_mod_cast (show
      (D.P.parts.card : ℝ) < Fintype.card V by
        simpa [ell, N] using! hellN)
  have hcapNat : 1 ≤ capNat := by
    dsimp [capNat]
    exact Nat.one_le_div_iff hellNat |>.2 hellNatN.le
  have hcap0 : 0 < cap := by
    simpa [cap, capNat] using! (show
      (0 : ℝ) <
          (↑(Fintype.card V / D.P.parts.card) : ℝ) by
        exact_mod_cast hcapNat)
  have hscaleEq : (D.scale : ℝ) = cap + 1 := by
    simpa [cap, capNat] using! congrArg (fun z : ℕ => (z : ℝ)) D.scale_eq
  have hscaleCap : (D.scale : ℝ) ≤ 2 * cap := by
    simpa [cap, capNat] using! (show
      (D.scale : ℝ) ≤
        2 * (Fintype.card V / D.P.parts.card : ℕ) by
          exact_mod_cast D.scale_le_two_floor hcapNat)
  have hellScaleNat := D.parts_mul_scale_le
  have hellScale :
      ell * (D.scale : ℝ) ≤ N + ell := by
    simpa [ell, N] using! (show
      (D.P.parts.card : ℝ) * D.scale ≤
        Fintype.card V + D.P.parts.card by
          exact_mod_cast hellScaleNat)
  have hellScaleTwo :
      ell * (D.scale : ℝ) ≤ 2 * N := by
    have hellLeN : ell ≤ N := hellN.le
    linarith
  have hEllCap :
      ell * cap ≤ N := by
    dsimp [ell, cap, capNat, N]
    exact_mod_cast Nat.mul_div_le (Fintype.card V) D.P.parts.card
  have hNlt :
      N < ell * (D.scale : ℝ) := by
    have hnat :=
      Nat.lt_mul_div_succ (Fintype.card V) hellNat
    rw [← D.scale_eq] at hnat
    simpa [N, ell] using! (show
      (Fintype.card V : ℝ) <
        D.P.parts.card * D.scale by exact_mod_cast hnat)
  have hLpos : 0 < L := by
    dsimp [L]
    exact SzemerediRegularity.bound_pos _ _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hellLNat : D.P.parts.card ≤ L := by
    exact D.upper_parts
  have hellL : ell ≤ L := by
    simpa [ell] using! (show
      (D.P.parts.card : ℝ) ≤ (L : ℝ) by exact_mod_cast hellLNat)
  have hτsep0 : 0 < τsep := by
    dsimp [τsep]
    positivity
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    positivity
  have hsepN : (1 : ℝ) ≤ τsep * Fintype.card A := by
    simpa [τsep, L] using! hsepOrder
  obtain ⟨Q⟩ :=
    exists_offTuran_parity_tree_data T hT τsep hτsep0 hsepN
  have hcomponentRoom :
      τsep * Fintype.card A ≤ τ := by
    have hnlt : n < 2 * (L : ℝ) * cap := by
      calc
        n ≤ N := hnN
        _ < ell * (D.scale : ℝ) := hNlt
        _ ≤ (L : ℝ) * (2 * cap) := by
          exact mul_le_mul hellL hscaleCap (by positivity) (by positivity)
        _ = 2 * (L : ℝ) * cap := by ring
    dsimp [τsep, τ]
    rw [div_mul_eq_mul_div]
    have hηsq : 0 < c.η ^ 2 := sq_pos_of_pos hη0
    rw [div_le_iff₀ (mul_pos (by norm_num) hL0)]
    nlinarith [mul_lt_mul_of_pos_left hnlt hηsq]
  have hseedBound :
      (Q.S.card : ℝ) ≤ 16 / τsep + 8 :=
    Q.seed_card
  have hhuge :
      16 / τsep + 9 ≤ c.ε * cap / 4 := by
    simpa [τsep, L, cap, capNat] using! hfloorHuge
  have hround : 1 ≤ 2 * c.ε * cap := by
    have hseedNonneg : (0 : ℝ) ≤ 16 / τsep := by positivity
    nlinarith
  have hseedQuarter :
      (Q.S.card : ℝ) + 1 ≤ c.ε * cap / 4 := by
    linarith
  have hpartFloor :
      ∀ i : {C // C ∈ D.P.parts}, cap ≤ (i.1.card : ℝ) := by
    intro i
    simpa [cap, capNat] using! (show
      (↑(Fintype.card V / D.P.parts.card) : ℝ) ≤ i.1.card by
        exact_mod_cast D.floor_le_part i)
  have hpartScale :
      ∀ i : {C // C ∈ D.P.parts},
        ((i.1.card : ℝ) ≤ cap + 1) := by
    intro i
    rw [← hscaleEq]
    exact_mod_cast D.part_size_upper i
  have hTset :
      ((offTuranMatchingTargets cL cR).card : ℝ) ≤ ell := by
    have ht := matchingTargets_card_le cL cR
    simpa [ell, Fintype.card_coe] using!
      (show ((offTuranMatchingTargets cL cR).card : ℝ) ≤
          Fintype.card {C // C ∈ D.P.parts} by exact_mod_cast ht)
  have hthr0 : 0 < thr := by
    exact offTuran_bad_threshold_pos c.ε ell c.η hε0 hell0 hη0
  have hloss : ∀ b,
      hpHeadCoreLoss c.ε thr
          (offTuranMatchingTargets cL cR)
          ((offTuranBoolHead X Y b).1) ≤
        (c.ε + c.η / 8) *
          (((offTuranBoolHead X Y b).1).card : ℝ) := by
    intro b
    simpa [thr] using!
      offTuran_headCoreLoss_le c.ε c.η ell
        (offTuranMatchingTargets cL cR)
        ((offTuranBoolHead X Y b).1)
        hε0 hη0 hell0 hTset
  have hheadSeedRoom : ∀ b,
      (Q.S.card : ℝ) +
          hpHeadCoreLoss c.ε thr
            (offTuranMatchingTargets cL cR)
            ((offTuranBoolHead X Y b).1) <
        ((offTuranBoolHead X Y b).1.card : ℝ) := by
    intro b
    have hfloor := hpartFloor (offTuranBoolHead X Y b)
    have hcard0 :
        (0 : ℝ) ≤ ((offTuranBoolHead X Y b).1.card : ℝ) := by positivity
    have hepssmall : c.ε + c.η / 8 < 1 / 2 := by
      nlinarith [c.eps_linear, c.eta_small]
    have hseedHalf :
        (Q.S.card : ℝ) < cap / 2 := by
      have hepsOne : c.ε ≤ 1 := hε1
      nlinarith [hseedQuarter, hcap0]
    nlinarith [hloss b]
  have hheadCrossRoom : ∀ b,
      (Q.S.card : ℝ) + 1 +
          hpHeadCoreLoss c.ε thr
            (offTuranMatchingTargets cL cR)
            ((offTuranBoolHead X Y b).1) ≤
        (c.η - c.ε) *
          ((offTuranBoolHead X Y b).1.card : ℝ) := by
    intro b
    have hfloor := hpartFloor (offTuranBoolHead X Y b)
    have hcard0 :
        (0 : ℝ) ≤ ((offTuranBoolHead X Y b).1.card : ℝ) := by positivity
    have hseedEps :
        (Q.S.card : ℝ) + 1 ≤ c.ε / 4 *
            ((offTuranBoolHead X Y b).1.card : ℝ) := by
      calc
        _ ≤ c.ε * cap / 4 := hseedQuarter
        _ ≤ c.ε *
            ((offTuranBoolHead X Y b).1.card : ℝ) / 4 := by
              gcongr
        _ = c.ε / 4 *
            ((offTuranBoolHead X Y b).1.card : ℝ) := by ring
    nlinarith [hloss b, c.eps_linear,
      mul_nonneg c.eta_pos.le hcard0]
  have hheadFractionRoom : ∀ b,
      hpHeadCoreLoss c.ε thr
          (offTuranMatchingTargets cL cR)
          ((offTuranBoolHead X Y b).1) ≤
        (1 - c.ε) *
          ((offTuranBoolHead X Y b).1.card : ℝ) := by
    intro b
    have hcard0 :
        (0 : ℝ) ≤ ((offTuranBoolHead X Y b).1.card : ℝ) := by positivity
    nlinarith [hloss b, c.eps_linear, c.eta_small]
  have hcontactSeedRoom : ∀ b,
      (Q.S.card : ℝ) <
        c.ε * ((offTuranHeadCoreFamily G
          (offTuranReducedGraph G D.P c.ε c.η)
          (fun i : {C // C ∈ D.P.parts} => i.1)
          c.ε c.η (offTuranMatchingTargets cL cR)
          thr X Y b).card : ℝ) := by
    intro b
    let R := offTuranReducedGraph G D.P c.ε c.η
    let C : {C // C ∈ D.P.parts} → Finset V := fun i => i.1
    let head := offTuranBoolHead X Y b
    let other := offTuranBoolOtherHead X Y b
    have hheadEdge : R.Adj head other := by
      cases b
      · exact hXY
      · exact hXY.symm
    have hcoreLower :=
      hpOffTuranHeadCore_card_lower
        G R C D.part_nonempty c.ε c.η hε0 hε1
        (fun i j hij => hij.2.1)
        (offTuranMatchingTargets cL cR) thr hthr0
        head other hheadEdge.2.1 hheadEdge.2.2
    have hfloor := hpartFloor head
    have hcard0 : (0 : ℝ) ≤ ((C head).card : ℝ) := by positivity
    have hhalf :
        cap / 2 ≤
          ((offTuranHeadCoreFamily G R C c.ε c.η
            (offTuranMatchingTargets cL cR)
            thr X Y b).card : ℝ) := by
      change cap / 2 ≤
        ((hpOffTuranHeadCore G R C c.ε c.η
          (offTuranMatchingTargets cL cR) thr head other).card : ℝ)
      nlinarith [hloss b, c.eps_linear, c.eta_small]
    have hseedStrict :
        (Q.S.card : ℝ) < c.ε * cap / 2 := by
      nlinarith [hseedQuarter, mul_pos hε0 hcap0]
    have hmul := mul_le_mul_of_nonneg_left hhalf hε0.le
    apply hseedStrict.trans_le
    simpa [R, C] using! (show
      c.ε * cap / 2 ≤
        c.ε * ((offTuranHeadCoreFamily G R C c.ε c.η
          (offTuranMatchingTargets cL cR)
          thr X Y b).card : ℝ) by
      nlinarith [hmul])
  have hLlower : c.η * cap / 8 ≤ (Lnat : ℝ) := by
    dsimp [Lnat]
    exact Nat.le_ceil _
  have hLupper : (Lnat : ℝ) < c.η * cap / 8 + 1 := by
    dsimp [Lnat]
    exact Nat.ceil_lt_add_one (by positivity)
  have hLsig : c.ε * (D.scale : ℝ) ≤ (Lnat : ℝ) := by
    have hεcap : c.ε * (D.scale : ℝ) ≤
        2 * c.ε * cap := by nlinarith [hscaleCap, hε0]
    nlinarith [hLlower, c.eps_linear, mul_pos hη0 hcap0]
  have hpairRoom :
      c.ε * (D.scale : ℝ) + τ ≤
        (c.η - 2 * c.ε) * (Lnat : ℝ) := by
    have hεscale :
        c.ε * (D.scale : ℝ) ≤ 2 * c.ε * cap := by
      nlinarith [mul_le_mul_of_nonneg_left hscaleCap hε0.le]
    have hηcap : 0 < c.η * cap := mul_pos hη0 hcap0
    have hηsqcap : 0 < c.η ^ 2 * cap := mul_pos (sq_pos_of_pos hη0) hcap0
    dsimp [τ]
    nlinarith [hLlower, c.eps_cube,
      mul_nonneg c.eps_pos.le hcap0.le,
      mul_nonneg c.eta_pos.le hcap0.le]
  have hleftCap : ∀ k,
      offTuranLeftThreshold G
        (offTuranReducedGraph G D.P c.ε c.η)
        (fun i : {C // C ∈ D.P.parts} => i.1)
        (∅ : Finset κ) X Y c.ε cL k ≤ cap := by
    intro k
    apply offTuran_threshold_le_floor
    · exact hε0.le
    · exact hcap0.le
    · exact hpartFloor (cL k)
    · exact hpartScale (cL k)
    · exact hround
  have hrightCap : ∀ k,
      offTuranRightThreshold G
        (offTuranReducedGraph G D.P c.ε c.η)
        (fun i : {C // C ∈ D.P.parts} => i.1)
        (∅ : Finset κ) X Y c.ε cR k ≤ cap := by
    intro k
    apply offTuran_threshold_le_floor
    · exact hε0.le
    · exact hcap0.le
    · exact hpartFloor (cR k)
    · exact hpartScale (cR k)
    · exact hround
  -- The split is chosen below; its membership changes the assigned head in
  -- the trimmed thresholds.  The same floor bound is uniform in that head.
  let wX : κ → ℝ := fun k =>
    hpHeadMatchingWeight G
      (offTuranReducedGraph G D.P c.ε c.η)
      (fun i : {C // C ∈ D.P.parts} => i.1) X cL cR k
  let wY : κ → ℝ := fun k =>
    hpHeadMatchingWeight G
      (offTuranReducedGraph G D.P c.ε c.η)
      (fun i : {C // C ∈ D.P.parts} => i.1) Y cL cR k
  let reserve : ℝ := (Lnat : ℝ) + margin
  let common : ℝ :=
    thr * edgeCap + (Fintype.card κ : ℝ) * reserve +
      2 * c.ε * N
  let needX : ℝ :=
    parityRouteDemand T Q.S Q.D Q.col false + common
  let needY : ℝ :=
    parityRouteDemand T Q.S Q.D Q.col true + common
  let M : ℝ := 2 * (D.scale : ℝ)
  let t : ℝ := c.η * N
  have hkellNat :
      2 * Fintype.card κ ≤ D.P.parts.card := by
    simpa using! two_mul_matching_card_le cL cR hinj
  have hkell :
      2 * (Fintype.card κ : ℝ) ≤ ell := by
    dsimp [ell]
    exact_mod_cast hkellNat
  have hkell' :
      (Fintype.card κ : ℝ) ≤ ell := by
    have hk0 : (0 : ℝ) ≤ Fintype.card κ := by positivity
    nlinarith
  have hreserve0 : 0 ≤ reserve := by
    dsimp [reserve, margin, τ, err, retainedLoss]
    positivity
  have hcommon0 : 0 ≤ common := by
    dsimp [common, thr, edgeCap]
    positivity
  have hcommon :
      common ≤ 3 * c.η * N := by
    have hthrEdge :
        thr * edgeCap ≤ c.η * N / 20 := by
      have hεstrong :
          32 * c.ε ≤ c.η ^ 2 / 20 := by
        nlinarith [c.four_eps_cube, c.eta_pos, c.eta_small,
          sq_nonneg c.η]
      have hprod :
          ell * cap ≤ N := hEllCap
      dsimp [thr, edgeCap]
      rw [div_mul_eq_mul_div]
      have hηne : c.η ≠ 0 := hη0.ne'
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hprod c.eps_pos.le,
        mul_nonneg c.eta_pos.le hNpos.le]
    have htwoL :
        2 * (Lnat : ℝ) ≤ c.η * cap / 4 + 2 := by
      linarith
    have hkTwoL :
        (Fintype.card κ : ℝ) * (2 * (Lnat : ℝ)) ≤
          c.η * N / 8 + ell := by
      have hkc : (Fintype.card κ : ℝ) * cap ≤
          ell * cap / 2 := by nlinarith [hcap0]
      have hk2 : 2 * (Fintype.card κ : ℝ) ≤ ell := hkell
      nlinarith [mul_le_mul_of_nonneg_left htwoL
          (show (0 : ℝ) ≤ Fintype.card κ by positivity),
        mul_le_mul_of_nonneg_left hkc c.eta_pos.le]
    have hkτ :
        (Fintype.card κ : ℝ) * τ ≤ c.η * N / 64 := by
      have hkc : (Fintype.card κ : ℝ) * cap ≤
          ell * cap / 2 := by nlinarith [hcap0]
      dsimp [τ]
      have hηsqle : c.η ^ 2 ≤ c.η := by
        nlinarith [hη0, hη1, sq_nonneg c.η]
      nlinarith [mul_le_mul_of_nonneg_left hkc
          (show 0 ≤ c.η ^ 2 by positivity),
        hEllCap, mul_nonneg c.eta_pos.le hNpos.le]
    have hkerr :
        (Fintype.card κ : ℝ) * (2 * err) ≤ 2 * c.ε * N := by
      have hks :
          (Fintype.card κ : ℝ) * (D.scale : ℝ) ≤
            ell * (D.scale : ℝ) := by
        exact mul_le_mul_of_nonneg_right hkell'
          (by positivity)
      dsimp [err, retainedLoss]
      have hmul := mul_le_mul_of_nonneg_left hks
        (show (0 : ℝ) ≤ 2 * c.ε by positivity)
      nlinarith [hmul, hellScaleTwo]
    have hellEta' : ell ≤ c.η * N := by simpa [ell, N] using! hellEta
    have hεN : 2 * c.ε * N ≤ c.η * N / 20 := by
      nlinarith [c.eps_linear,
        mul_nonneg c.eta_pos.le hNpos.le]
    dsimp [common, reserve, margin]
    nlinarith [hthrEdge, hkTwoL, hkτ, hkerr, hellEta',
      hεN, mul_nonneg c.eta_pos.le hNpos.le]
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hwX0 : ∀ k, 0 ≤ wX k := by
    intro k
    exact hpHeadMatchingWeight_nonneg _ _ _ _ _ _ _
  have hwY0 : ∀ k, 0 ≤ wY k := by
    intro k
    exact hpHeadMatchingWeight_nonneg _ _ _ _ _ _ _
  have hwXM : ∀ k, wX k ≤ M := by
    intro k
    exact hpHeadMatchingWeight_le_two_mul
      G (offTuranReducedGraph G D.P c.ε c.η)
      (fun i : {C // C ∈ D.P.parts} => i.1)
      X cL cR (D.scale : ℝ)
      (fun i => by exact_mod_cast D.part_size_upper i) k
  have hwYM : ∀ k, wY k ≤ M := by
    intro k
    exact hpHeadMatchingWeight_le_two_mul
      G (offTuranReducedGraph G D.P c.ε c.η)
      (fun i : {C // C ∈ D.P.parts} => i.1)
      Y cL cR (D.scale : ℝ)
      (fun i => by exact_mod_cast D.part_size_upper i) k
  have ht0 : 0 < t := by
    dsimp [t]
    positivity
  have hvariance :
      (Fintype.card κ : ℝ) * M ^ 2 / 2 < t ^ 2 := by
    have hfour : (4 : ℝ) ≤ c.ε * ell := by
      have hlow := D.lower_parts
      have hceil : 4 / c.ε ≤ (⌈4 / c.ε⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcast :
          (⌈4 / c.ε⌉₊ : ℝ) ≤ ell := by
        simpa [ell] using! (show
          (⌈4 / c.ε⌉₊ : ℝ) ≤ D.P.parts.card by
            exact_mod_cast hlow)
      have := hceil.trans hcast
      rw [div_le_iff₀ hε0] at this
      nlinarith
    have htwoScale :
        2 * (D.scale : ℝ) ≤ c.ε * N := by
      have hmul :=
        mul_le_mul_of_nonneg_right hfour
          (show (0 : ℝ) ≤ D.scale by positivity)
      nlinarith [hellScaleTwo,
        mul_le_mul_of_nonneg_left hellScaleTwo c.eps_pos.le]
    have hvarWeak :
        (Fintype.card κ : ℝ) * M ^ 2 / 2 ≤
          2 * c.ε * N ^ 2 := by
      dsimp [M]
      have hkScale :
          (Fintype.card κ : ℝ) * (D.scale : ℝ) ≤
            ell * (D.scale : ℝ) := by
        exact mul_le_mul_of_nonneg_right hkell'
          (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hkScale
          (show (0 : ℝ) ≤ 2 * D.scale by positivity),
        mul_le_mul_of_nonneg_left htwoScale
          (show (0 : ℝ) ≤ ell * D.scale by positivity),
        hellScaleTwo]
    dsimp [t]
    have hepsEtaSq : 2 * c.ε < c.η ^ 2 := by
      nlinarith [c.eps_square_q_strong,
        (show (2 : ℝ) ≤ q by exact_mod_cast hq),
        sq_pos_of_pos c.eta_pos]
    nlinarith [hvarWeak, mul_pos hNpos hNpos]
  have hsumX :
      n + 78 * c.η * N ≤ ∑ k, wX k := by
    simpa [n, N, wX] using! hSupplyX
  have hsumY :
      n + 78 * c.η * N ≤ ∑ k, wY k := by
    simpa [n, N, wY] using! hSupplyY
  have hSpos : 0 < n + 78 * c.η * N := by positivity
  have hneedX0 : 0 ≤ needX + t := by
    dsimp [needX, t]
    nlinarith [parityRouteDemand_nonneg T Q.S Q.D Q.col false,
      hcommon0, ht0.le]
  have hneedY0 : 0 ≤ needY + t := by
    dsimp [needY, t]
    nlinarith [parityRouteDemand_nonneg T Q.S Q.D Q.col true,
      hcommon0, ht0.le]
  have hneedSum :
      (needX + t) + (needY + t) <
        n + 78 * c.η * N := by
    have hroute :=
      parityRouteDemand_false_add_true T Q.S Q.D Q.col
    have hrouteLe :
        parityRouteDemand T Q.S Q.D Q.col false +
            parityRouteDemand T Q.S Q.D Q.col true ≤ n := by
      dsimp [n]
      rw [hroute]
      exact_mod_cast Nat.sub_le _ _
    dsimp [needX, needY, t]
    nlinarith [hcommon, mul_pos c.eta_pos hNpos]
  have hratio :
      (needX + t) / (∑ i, wX i) +
          (needY + t) / (∑ i, wY i) < 1 := by
    apply two_ratio_lt_one_of_sum_lt
      (needX + t) (needY + t) (∑ i, wX i) (∑ i, wY i)
      (n + 78 * c.η * N)
    · exact hneedX0
    · exact hneedY0
    · exact hSpos
    · exact hsumX
    · exact hsumY
    · exact hneedSum
  obtain ⟨K₀, hKX, hKY⟩ :=
    exists_whole_matching_split_of_ratio_room
      wX wY M t needX needY
      hwX0 hwXM hwY0 hwYM ht0 hvariance
      (hSpos.trans_le hsumX) (hSpos.trans_le hsumY)
      hneedX0 hneedY0 hratio
  have hleftCap' : ∀ k,
      offTuranLeftThreshold G
        (offTuranReducedGraph G D.P c.ε c.η)
        (fun i : {C // C ∈ D.P.parts} => i.1)
        K₀ X Y c.ε cL k ≤ cap := by
    intro k
    apply offTuran_threshold_le_floor
    · exact hε0.le
    · exact hcap0.le
    · exact hpartFloor (cL k)
    · exact hpartScale (cL k)
    · exact hround
  have hrightCap' : ∀ k,
      offTuranRightThreshold G
        (offTuranReducedGraph G D.P c.ε c.η)
        (fun i : {C // C ∈ D.P.parts} => i.1)
        K₀ X Y c.ε cR k ≤ cap := by
    intro k
    apply offTuran_threshold_le_floor
    · exact hε0.le
    · exact hcap0.le
    · exact hpartFloor (cR k)
    · exact hpartScale (cR k)
    · exact hround
  have hedgeCap' : ∀ k,
      offTuranLeftThreshold G
          (offTuranReducedGraph G D.P c.ε c.η)
          (fun i : {C // C ∈ D.P.parts} => i.1)
          K₀ X Y c.ε cL k +
        offTuranRightThreshold G
          (offTuranReducedGraph G D.P c.ε c.η)
          (fun i : {C // C ∈ D.P.parts} => i.1)
          K₀ X Y c.ε cR k ≤ edgeCap := by
    intro k
    dsimp [edgeCap]
    linarith [hleftCap' k, hrightCap' k]
  have hrawAllocated : ∀ b,
      parityRouteDemand T Q.S Q.D Q.col b +
          thr * edgeCap +
          ((offTuranBoolEdges K₀ b).card : ℝ) *
            ((Lnat : ℝ) + margin) +
          2 * c.ε * Fintype.card V ≤
        ∑ k ∈ offTuranBoolEdges K₀ b,
          hpHeadMatchingWeight G
            (offTuranReducedGraph G D.P c.ε c.η)
            (fun i : {C // C ∈ D.P.parts} => i.1)
            (offTuranBoolHead X Y b) cL cR k := by
    intro b
    have hcardK :
        ((offTuranBoolEdges K₀ b).card : ℝ) ≤
          Fintype.card κ := by
      exact_mod_cast Finset.card_le_univ _
    have hresMul :
        ((offTuranBoolEdges K₀ b).card : ℝ) * reserve ≤
          (Fintype.card κ : ℝ) * reserve :=
      mul_le_mul_of_nonneg_right hcardK hreserve0
    dsimp [reserve] at hresMul
    cases b
    · simp only [offTuranBoolEdges_false] at hresMul
      simp only [offTuranBoolEdges_false, offTuranBoolHead_false]
      change
        parityRouteDemand T Q.S Q.D Q.col false +
              thr * edgeCap + (K₀.card : ℝ) *
                ((Lnat : ℝ) + margin) +
              2 * c.ε * Fintype.card V ≤
            ∑ k ∈ K₀, wX k
      calc
        _ ≤ parityRouteDemand T Q.S Q.D Q.col false + common := by
          dsimp [common, reserve, N]
          linarith [hresMul]
        _ = needX := by rfl
        _ ≤ _ := hKX
    · simp only [offTuranBoolEdges_true] at hresMul
      simp only [offTuranBoolEdges_true, offTuranBoolHead_true]
      change
        parityRouteDemand T Q.S Q.D Q.col true +
              thr * edgeCap + ((Finset.univ \ K₀).card : ℝ) *
                ((Lnat : ℝ) + margin) +
              2 * c.ε * Fintype.card V ≤
            ∑ k ∈ Finset.univ \ K₀, wY k
      calc
        _ ≤ parityRouteDemand T Q.S Q.D Q.col true + common := by
          dsimp [common, reserve, N]
          linarith [hresMul]
        _ = needY := by rfl
        _ ≤ _ := hKY
  apply offTuran_reduced_parity_embedding
    T hT G D X Y hXY cL cR hmatch hinj haway
    K₀ τsep Q thr τ margin retainedLoss err cap edgeCap Lnat
  · exact hε0
  · exact hε1
  · exact hη1.le
  · exact hthr0
  · exact hheadSeedRoom
  · exact hheadCrossRoom
  · exact hheadFractionRoom
  · exact hcontactSeedRoom
  · exact hτ0
  · exact hcomponentRoom
  · exact hLsig
  · exact hpairRoom
  · exact le_rfl
  · exact hpartFloor
  · exact hleftCap'
  · exact hrightCap'
  · dsimp [err, retainedLoss]
    positivity
  · exact le_rfl
  · dsimp [margin, err, retainedLoss]
    linarith only [hτ0]
  · dsimp [margin]
    dsimp [err, retainedLoss]
    have he : 0 ≤ c.ε * (D.scale : ℝ) :=
      mul_nonneg hε0.le (by positivity)
    linarith only [he]
  · dsimp [margin]
    dsimp [err, retainedLoss]
    have he : 0 ≤ c.ε * (D.scale : ℝ) :=
      mul_nonneg hε0.le (by positivity)
    linarith only [hτ0, he]
  · dsimp [edgeCap]
    positivity
  · exact hreserve0
  · exact hedgeCap'
  · exact hrawAllocated

end Erdos550
