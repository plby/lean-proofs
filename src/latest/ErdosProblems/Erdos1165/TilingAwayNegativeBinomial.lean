/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.NegativeBinomialLocalCLT
import Mathlib.Data.Sym.Card

/-!
# Literal tiling-away masses are negative-binomial masses

Below the coordinate cap, the capped sum defining
`tilingAwayExactTotalMass` contains every weak composition of the prescribed
total.  Stars and bars therefore identifies it with the HLOZ
negative-binomial point mass.
-/

open scoped BigOperators

namespace Erdos1165.TilingAwayNegativeBinomial

open TilingCappedMarginalization TilingSpatialInsertionFiber PathInsertion
open SmallWindow NegativeBinomialLocalCLT ScreeningInstantiation

noncomputable section

/-- If the prescribed total is at most the cap, bounded coordinate vectors
with that total are equivalent to arbitrary nonnegative coordinate vectors
with that total. -/
noncomputable def boundedTotalEquiv
    (Alpha : Type*) [Fintype Alpha] [DecidableEq Alpha]
    (cap ell : ℕ) (hell : ell ≤ cap) :
    {v : Alpha → Fin (cap + 1) // ∑ a, (v a : ℕ) = ell} ≃
      {f : Alpha → ℕ // ∑ a, f a = ell} where
  toFun v := ⟨fun a ↦ v.1 a, v.2⟩
  invFun f := ⟨fun a ↦ ⟨f.1 a, by
    apply Nat.lt_succ_of_le
    apply le_trans (Finset.single_le_sum
      (s := Finset.univ) (f := f.1) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ a))
    exact f.2.le.trans hell⟩, by simpa using f.2⟩
  left_inv v := by
    ext a
    rfl
  right_inv f := by
    ext a
    rfl

/-- The fixed-total slice of functions into `ℕ` is finite by stars and
bars. -/
noncomputable instance instFintypeFunctionNatTotal
    (Alpha : Type*) [Fintype Alpha] [DecidableEq Alpha] (ell : ℕ) :
    Fintype {f : Alpha → ℕ // ∑ a, f a = ell} :=
  Fintype.ofEquiv (Sym Alpha ell) (Sym.equivNatSumOfFintype Alpha ell)

/-- Stars and bars for bounded vectors whose total lies below the cap. -/
theorem card_boundedTotal_eq_multichoose
    (Alpha : Type*) [Fintype Alpha] [DecidableEq Alpha]
    (cap ell : ℕ) (hell : ell ≤ cap) :
    Fintype.card {v : Alpha → Fin (cap + 1) // ∑ a, (v a : ℕ) = ell} =
      (Fintype.card Alpha).multichoose ell := by
  calc
    Fintype.card {v : Alpha → Fin (cap + 1) //
        ∑ a, (v a : ℕ) = ell} =
        Fintype.card {f : Alpha → ℕ // ∑ a, f a = ell} :=
      Fintype.card_congr (boundedTotalEquiv Alpha cap ell hell)
    _ = Fintype.card (Sym Alpha ell) :=
      (Fintype.card_congr (Sym.equivNatSumOfFintype Alpha ell)).symm
    _ = (Fintype.card Alpha).multichoose ell :=
      Sym.card_sym_eq_multichoose Alpha ell

/-- A product of the HLOZ geometric gap masses depends only on the number
of coordinates and their total. -/
theorem prod_geometricGapMass_eq
    (Alpha : Type*) [Fintype Alpha] (v : Alpha → ℕ) :
    (∏ a, geometricGapMass (v a)) =
      (15 / 16 : ℝ) ^ Fintype.card Alpha *
        (1 / 16 : ℝ) ^ (∑ a, v a) := by
  simp only [geometricGapMass, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ,
    Finset.prod_pow_eq_pow_sum]

/-- The literal capped mass at a total below the cap is the corresponding
negative-binomial mass. -/
theorem cappedGeometricTotalMass_eq_negativeBinomial
    (Alpha : Type*) [Fintype Alpha] [DecidableEq Alpha] (cap ell : ℕ)
    (hell : ell ≤ cap) (hAlpha : 0 < Fintype.card Alpha) :
    (∑ v : Alpha → Fin (cap + 1),
      if (∑ a, (v a : ℕ)) = ell then
        ∏ a, geometricGapMass (v a : ℕ) else 0) =
      NegativeBinomial.mass (15 / 16 : ℝ) (Fintype.card Alpha) ell := by
  classical
  let C : ℝ := (15 / 16 : ℝ) ^ Fintype.card Alpha *
    (1 / 16 : ℝ) ^ ell
  calc
    (∑ v : Alpha → Fin (cap + 1),
        if (∑ a, (v a : ℕ)) = ell then
          ∏ a, geometricGapMass (v a : ℕ) else 0) =
        ∑ v : Alpha → Fin (cap + 1),
          if (∑ a, (v a : ℕ)) = ell then C else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · simp only [C, prod_geometricGapMass_eq Alpha]
        rw [hv]
      · rfl
    _ = (Fintype.card {v : Alpha → Fin (cap + 1) //
          ∑ a, (v a : ℕ) = ell} : ℝ) * C := by
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
      rw [Fintype.card_subtype]
      simp
    _ = ((Fintype.card Alpha).multichoose ell : ℝ) * C := by
      rw [card_boundedTotal_eq_multichoose Alpha cap ell hell]
    _ = NegativeBinomial.mass (15 / 16 : ℝ)
        (Fintype.card Alpha) ell := by
      unfold NegativeBinomial.mass
      rw [NegativeBinomial.coefficient_eq_multichoose hAlpha]
      unfold C
      rw [show 1 - (15 / 16 : ℝ) = 1 / 16 by norm_num]
      ring

/-- The concrete all-six away point mass is negative-binomial below its
coordinate cap. -/
theorem tilingAwayPointMass_eq_negativeBinomial
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (b : TilingAwayDomino t x r D) (ell : ℕ) (hell : ell ≤ cap)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1)) :
    tilingAwayPointMass (cap := cap) t x r D b ell =
      NegativeBinomial.mass (15 / 16 : ℝ)
        (Fintype.card (TilingCoordinatesAt t x r b.1)) ell := by
  unfold tilingAwayPointMass tilingAwayExactTotalMass
  exact cappedGeometricTotalMass_eq_negativeBinomial
    (TilingCoordinatesAt t x r b.1) cap ell hell hcoordinates

/-- A finite value window below both the stopped-fibre truncation and the
insertion-coordinate cap has its untruncated negative-binomial mass divided
by the literal common normalizer. -/
theorem sum_tilingAway_coordinateMass_window
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (window : Finset ℕ)
    (hwindowUpper : ∀ v ∈ window, v < upper b)
    (hwindowCap : ∀ v ∈ window, v ≤ cap)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1)) :
    (∑ v : Fin (upper b),
      if (v : ℕ) ∈ window then
        FiniteDominoProductLaw.coordinateMass
          (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0) =
      windowMass (Fintype.card (TilingCoordinatesAt t x r b.1)) window /
        ∑ j : Fin (upper b), tilingAwayPointMass (cap := cap) t x r D b j := by
  let successes := Fintype.card (TilingCoordinatesAt t x r b.1)
  let den : ℝ := ∑ j : Fin (upper b),
    tilingAwayPointMass (cap := cap) t x r D b j
  have hfilter :
      (Finset.range (upper b)).filter (fun v ↦ v ∈ window) = window := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h ↦ h.2
    · intro hv
      exact ⟨hwindowUpper v hv, hv⟩
  change (∑ v : Fin (upper b),
      (fun k : ℕ ↦ if k ∈ window then
        FiniteDominoProductLaw.coordinateMass
          (tilingAwayPointMass (cap := cap) t x r D) upper b k else 0) v) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ if k ∈ window then
      FiniteDominoProductLaw.coordinateMass
        (tilingAwayPointMass (cap := cap) t x r D) upper b k else 0)
    (upper b)]
  rw [← Finset.sum_filter, hfilter]
  calc
    (∑ v ∈ window, FiniteDominoProductLaw.coordinateMass
        (tilingAwayPointMass (cap := cap) t x r D) upper b v) =
        ∑ v ∈ window,
          NegativeBinomial.mass (15 / 16 : ℝ) successes v / den := by
      apply Finset.sum_congr rfl
      intro v hv
      unfold FiniteDominoProductLaw.coordinateMass
      rw [if_pos (hwindowUpper v hv)]
      congr 1
      exact tilingAwayPointMass_eq_negativeBinomial t x r D b v
        (hwindowCap v hv) hcoordinates
    _ = windowMass successes window / den := by
      rw [← Finset.sum_div]
      unfold windowMass NegativeBinomial.hlozMass NegativeBinomial.hlozSuccess
      rfl
    _ = windowMass (Fintype.card (TilingCoordinatesAt t x r b.1)) window /
        ∑ j : Fin (upper b),
          tilingAwayPointMass (cap := cap) t x r D b j := rfl

/-- Any checked untruncated window comparison survives the literal capped
all-six away-coordinate normalization. -/
theorem tilingAway_coordinateMass_window_ratio
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D)
    (upperWindow lowerWindow : Finset ℕ) {C : ℝ}
    (hupperUpper : ∀ v ∈ upperWindow, v < upper b)
    (hlowerUpper : ∀ v ∈ lowerWindow, v < upper b)
    (hupperCap : ∀ v ∈ upperWindow, v ≤ cap)
    (hlowerCap : ∀ v ∈ lowerWindow, v ≤ cap)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    (hratio :
      windowMass (Fintype.card (TilingCoordinatesAt t x r b.1)) upperWindow ≤
        C * windowMass
          (Fintype.card (TilingCoordinatesAt t x r b.1)) lowerWindow) :
    (∑ v : Fin (upper b),
      if (v : ℕ) ∈ upperWindow then
        FiniteDominoProductLaw.coordinateMass
          (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0) ≤
      C * ∑ v : Fin (upper b),
        if (v : ℕ) ∈ lowerWindow then
          FiniteDominoProductLaw.coordinateMass
            (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0 := by
  rw [sum_tilingAway_coordinateMass_window t x r D upper b upperWindow
      hupperUpper hupperCap hcoordinates,
    sum_tilingAway_coordinateMass_window t x r D upper b lowerWindow
      hlowerUpper hlowerCap hcoordinates]
  have hden : 0 ≤ ∑ j : Fin (upper b),
      tilingAwayPointMass (cap := cap) t x r D b j :=
    Finset.sum_nonneg fun j _ ↦ tilingAwayExactTotalMass_nonneg t x r D b j
  calc
    windowMass (Fintype.card (TilingCoordinatesAt t x r b.1)) upperWindow /
        (∑ j : Fin (upper b), tilingAwayPointMass (cap := cap) t x r D b j) ≤
      (C * windowMass (Fintype.card (TilingCoordinatesAt t x r b.1))
        lowerWindow) /
        (∑ j : Fin (upper b), tilingAwayPointMass (cap := cap) t x r D b j) :=
      div_le_div_of_nonneg_right hratio hden
    _ = C * (windowMass (Fintype.card (TilingCoordinatesAt t x r b.1))
        lowerWindow /
          ∑ j : Fin (upper b),
            tilingAwayPointMass (cap := cap) t x r D b j) := by ring

/-- Local-CLT specialization of the all-six literal capped window ratio. -/
theorem tilingAway_coordinateMass_window_ratio_of_localCLT
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D)
    (upperWindow lowerWindow : Finset ℕ)
    (hupperUpper : ∀ v ∈ upperWindow, v < upper b)
    (hlowerUpper : ∀ v ∈ lowerWindow, v < upper b)
    (hupperCap : ∀ v ∈ upperWindow, v ≤ cap)
    (hlowerCap : ∀ v ∈ lowerWindow, v ≤ cap)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    {dev windowGap : ℝ} (hdev : 0 ≤ dev) (hwindowGap : 0 ≤ windowGap)
    (hmoderate : dev ≤
      (Fintype.card (TilingCoordinatesAt t x r b.1) : ℝ) / 30)
    (hlower : lowerWindow.Nonempty)
    (hcard : upperWindow.card ≤ lowerWindow.card)
    (hupperDev : ∀ v ∈ upperWindow,
      |deviation (Fintype.card (TilingCoordinatesAt t x r b.1)) v| ≤ dev)
    (hlowerDev : ∀ v ∈ lowerWindow,
      |deviation (Fintype.card (TilingCoordinatesAt t x r b.1)) v| ≤ dev)
    (hpair : ∀ u ∈ upperWindow, ∀ l ∈ lowerWindow,
      |deviation (Fintype.card (TilingCoordinatesAt t x r b.1)) u -
        deviation (Fintype.card (TilingCoordinatesAt t x r b.1)) l| ≤ windowGap) :
    (∑ v : Fin (upper b),
      if (v : ℕ) ∈ upperWindow then
        FiniteDominoProductLaw.coordinateMass
          (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0) ≤
      adjacentLocalRatio
          (Fintype.card (TilingCoordinatesAt t x r b.1)) dev windowGap *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ lowerWindow then
            FiniteDominoProductLaw.coordinateMass
              (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0 := by
  apply tilingAway_coordinateMass_window_ratio t x r D upper b
    upperWindow lowerWindow hupperUpper hlowerUpper hupperCap hlowerCap
    hcoordinates
  exact adjacentWindowMass_le_adjacentLocalRatio hcoordinates hdev hwindowGap
    hmoderate hlower hcard hupperDev hlowerDev hpair

end

end Erdos1165.TilingAwayNegativeBinomial
