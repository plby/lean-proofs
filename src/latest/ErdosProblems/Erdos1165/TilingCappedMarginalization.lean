import ErdosProblems.Erdos1165.TilingStoppedAcceptanceFactorization

open scoped BigOperators ENNReal NNReal

/-!
# Capped distinguished/away marginalization for all six tilings

This module performs the finite coordinate reindexing behind the stopped
product law.  It splits a capped insertion vector into distinguished and
away-domino coordinates, sums arbitrary joint distinguished data out, and
retains only the actual total on every away domino.  Thus the two marginal
equalities consumed by `TilingStoppedCoordinateProductSpec` are consequences
of an explicit finite equivalence, not path-measure assumptions.
-/

namespace Erdos1165.TilingCappedMarginalization

open TilingLazyDecomposition TilingSpatialInsertionFiber
open PathInsertion SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open VariableStoppedTracePartition

abbrev DominoTiling := Tilings.Tiling

abbrev TilingDistinguishedDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point) :=
  {b : TilingExternalDomino t x r // b.1 ∈ D}

abbrev TilingAwayDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point) :=
  {b : TilingExternalDomino t x r // b.1 ∉ D}

noncomputable instance {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point) :
    Fintype (TilingDistinguishedDomino t x r D) := Fintype.ofFinite _

noncomputable instance {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point) :
    Fintype (TilingAwayDomino t x r D) := Fintype.ofFinite _

abbrev TilingDistinguishedCoordinates {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :=
  (b : TilingDistinguishedDomino t x r D) →
    TilingCoordinatesAt t x r b.1 → Fin (cap + 1)

abbrev TilingAwayCoordinates {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :=
  (b : TilingAwayDomino t x r D) →
    TilingCoordinatesAt t x r b.1 → Fin (cap + 1)

noncomputable def tilingDominoSplitEquiv {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :
    TilingDistinguishedDomino t x r D ⊕ TilingAwayDomino t x r D ≃
      TilingExternalDomino t x r := by
  classical
  exact Equiv.sumCompl (fun b : TilingExternalDomino t x r ↦ b.1 ∈ D)

noncomputable def splitGroupedCoordinatesEquiv {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :
    ((b : TilingExternalDomino t x r) →
        TilingCoordinatesAt t x r b → Fin (cap + 1)) ≃
      TilingDistinguishedCoordinates (cap := cap) t x r D ×
        TilingAwayCoordinates (cap := cap) t x r D := by
  classical
  let e := tilingDominoSplitEquiv t x r D
  exact (Equiv.piCongrLeft
    (fun b : TilingExternalDomino t x r ↦
      TilingCoordinatesAt t x r b → Fin (cap + 1)) e).symm.trans
        (Equiv.sumPiEquivProdPi (fun z ↦
          TilingCoordinatesAt t x r (e z) → Fin (cap + 1)))

noncomputable def splitTilingCoordinatesEquiv {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :
    TilingCappedCoordinates i cap ≃
      TilingDistinguishedCoordinates (cap := cap) t x r D ×
        TilingAwayCoordinates (cap := cap) t x r D :=
  (regroupTilingCoordinatesEquiv t x r (Fin (cap + 1))).trans
    (splitGroupedCoordinatesEquiv t x r D)

noncomputable def tilingGroupedMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (Q : (b : TilingExternalDomino t x r) →
      TilingCoordinatesAt t x r b → Fin (cap + 1)) : ℝ :=
  ∏ b, ∏ k, geometricGapMass (Q b k : ℕ)

noncomputable def tilingDistinguishedAssignmentMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (d : TilingDistinguishedCoordinates (cap := cap) t x r D) : ℝ :=
  ∏ b, ∏ k, geometricGapMass (d b k : ℕ)

noncomputable def tilingAwayAssignmentMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (a : TilingAwayCoordinates (cap := cap) t x r D) : ℝ :=
  ∏ b, ∏ k, geometricGapMass (a b k : ℕ)

theorem tilingGroupedMass_split {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (d : TilingDistinguishedCoordinates (cap := cap) t x r D)
    (a : TilingAwayCoordinates (cap := cap) t x r D) :
    tilingGroupedMass t x r ((splitGroupedCoordinatesEquiv t x r D).symm (d, a)) =
      tilingDistinguishedAssignmentMass t x r D d *
        tilingAwayAssignmentMass t x r D a := by
  classical
  unfold tilingGroupedMass tilingDistinguishedAssignmentMass
    tilingAwayAssignmentMass splitGroupedCoordinatesEquiv
  let e := tilingDominoSplitEquiv t x r D
  let P := fun b : TilingExternalDomino t x r ↦
    TilingCoordinatesAt t x r b → Fin (cap + 1)
  let Q := Equiv.piCongrLeft P e
    ((Equiv.sumPiEquivProdPi (fun z ↦ P (e z))).symm (d, a))
  change (∏ b, ∏ k, geometricGapMass (Q b k : ℕ)) = _
  rw [← Fintype.prod_equiv e
    (fun z ↦ ∏ k, geometricGapMass (Q (e z) k : ℕ))
    (fun b ↦ ∏ k, geometricGapMass (Q b k : ℕ)) (fun _ ↦ rfl)]
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Fintype.prod_congr
    intro b
    apply Fintype.prod_congr
    intro k
    congr 1
    exact congrArg (fun z : Fin (cap + 1) ↦ (z : ℕ))
      (congrFun (Equiv.piCongrLeft_sumInl P e d a b) k)
  · apply Fintype.prod_congr
    intro b
    apply Fintype.prod_congr
    intro k
    congr 1
    exact congrArg (fun z : Fin (cap + 1) ↦ (z : ℕ))
      (congrFun (Equiv.piCongrLeft_sumInr P e d a b) k)

theorem gapVectorMass_eq_tilingGroupedMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : TilingCappedCoordinates i cap) :
    gapVectorMass (fun k ↦ (q k : ℕ)) =
      tilingGroupedMass t x r
        (regroupTilingCoordinatesEquiv t x r (Fin (cap + 1)) q) := by
  rw [TilingStoppedProductDisintegration.gapVectorMass_tiling_factorization]
  unfold TilingStoppedProductDisintegration.tilingDominoCoordinateMass
    tilingGroupedMass
  apply Fintype.prod_congr
  intro b
  apply Fintype.prod_congr
  intro k
  rfl

theorem gapVectorMass_split {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (d : TilingDistinguishedCoordinates (cap := cap) t x r D)
    (a : TilingAwayCoordinates (cap := cap) t x r D) :
    gapVectorMass (fun k ↦
        (((splitTilingCoordinatesEquiv t x r D).symm (d, a)) k : ℕ)) =
      tilingDistinguishedAssignmentMass t x r D d *
        tilingAwayAssignmentMass t x r D a := by
  rw [gapVectorMass_eq_tilingGroupedMass]
  let q := (splitTilingCoordinatesEquiv t x r D).symm (d, a)
  have hcoord : regroupTilingCoordinatesEquiv t x r (Fin (cap + 1)) q =
      (splitGroupedCoordinatesEquiv t x r D).symm (d, a) := by
    apply (splitGroupedCoordinatesEquiv t x r D).injective
    rw [Equiv.apply_symm_apply]
    exact (splitTilingCoordinatesEquiv t x r D).apply_symm_apply (d, a)
  rw [hcoord]
  exact tilingGroupedMass_split t x r D d a

@[simp] theorem splitTilingCoordinatesEquiv_away_apply {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q : TilingCappedCoordinates i cap)
    (b : TilingAwayDomino t x r D) (k : TilingCoordinatesAt t x r b.1) :
    (splitTilingCoordinatesEquiv t x r D q).2 b k = q k.1 := by
  classical
  let e := tilingDominoSplitEquiv t x r D
  let P := fun b : TilingExternalDomino t x r ↦
    TilingCoordinatesAt t x r b → Fin (cap + 1)
  let Q := regroupTilingCoordinatesEquiv t x r (Fin (cap + 1)) q
  change ((Equiv.piCongrLeft P e).symm Q (Sum.inr b)) k = q k.1
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

@[simp] theorem splitTilingCoordinatesEquiv_distinguished_apply {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q : TilingCappedCoordinates i cap)
    (b : TilingDistinguishedDomino t x r D)
    (k : TilingCoordinatesAt t x r b.1) :
    (splitTilingCoordinatesEquiv t x r D q).1 b k = q k.1 := by
  classical
  let e := tilingDominoSplitEquiv t x r D
  let P := fun b : TilingExternalDomino t x r ↦
    TilingCoordinatesAt t x r b → Fin (cap + 1)
  let Q := regroupTilingCoordinatesEquiv t x r (Fin (cap + 1)) q
  change ((Equiv.piCongrLeft P e).symm Q (Sum.inl b)) k = q k.1
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

/-- Fixing the distinguished coordinate projection fixes the complete
insertion total on every represented distinguished domino. -/
theorem tilingDominoTotal_eq_of_distinguished_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (h : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (b : TilingExternalDomino t x r) (hb : b.1 ∈ D) :
    tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b =
      tilingDominoTotal t x r (fun k ↦ (q' k : ℕ)) b := by
  let bd : TilingDistinguishedDomino t x r D := ⟨b, hb⟩
  unfold tilingDominoTotal
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrFun (congrFun h bd) k
  simpa only [splitTilingCoordinatesEquiv_distinguished_apply] using
    congrArg (fun u : Fin (cap + 1) ↦ (u : ℕ)) hk

def tilingAwayTotal {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (a : TilingAwayCoordinates (cap := cap) t x r D)
    (b : TilingAwayDomino t x r D) : ℕ :=
  ∑ k, (a b k : ℕ)

noncomputable def tilingAwayExactTotalMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (b : TilingAwayDomino t x r D) (ℓ : ℕ) : ℝ :=
  ∑ v : TilingCoordinatesAt t x r b.1 → Fin (cap + 1),
    if (∑ k, (v k : ℕ)) = ℓ then
      ∏ k, geometricGapMass (v k : ℕ) else 0

theorem tilingAwayFixedTotalsMass_factorization {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (ℓ : TilingAwayDomino t x r D → ℕ) :
    (∑ a : TilingAwayCoordinates (cap := cap) t x r D,
        if (∀ b, tilingAwayTotal t x r D a b = ℓ b) then
          tilingAwayAssignmentMass t x r D a else 0) =
      ∏ b, tilingAwayExactTotalMass (cap := cap) t x r D b (ℓ b) := by
  classical
  let F : (b : TilingAwayDomino t x r D) →
      (TilingCoordinatesAt t x r b.1 → Fin (cap + 1)) → ℝ :=
    fun b v ↦ if (∑ k, (v k : ℕ)) = ℓ b then
      ∏ k, geometricGapMass (v k : ℕ) else 0
  calc
    (∑ a : TilingAwayCoordinates (cap := cap) t x r D,
        if (∀ b, tilingAwayTotal t x r D a b = ℓ b) then
          tilingAwayAssignmentMass t x r D a else 0) =
        ∑ a : TilingAwayCoordinates (cap := cap) t x r D,
          ∏ b, F b (a b) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : ∀ b, tilingAwayTotal t x r D a b = ℓ b
      · rw [if_pos ha]
        unfold tilingAwayAssignmentMass
        apply Finset.prod_congr rfl
        intro b _
        have hb := ha b
        change (∑ k, (a b k : ℕ)) = ℓ b at hb
        rw [show F b (a b) = ∏ k, geometricGapMass (a b k : ℕ) by
          simp only [F, if_pos hb]]
      · rw [if_neg ha]
        push Not at ha
        obtain ⟨b, hb⟩ := ha
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ b)
        have hb' : (∑ k, (a b k : ℕ)) ≠ ℓ b := by
          simpa only [tilingAwayTotal] using hb
        simp only [F, if_neg hb']
    _ = ∏ b, ∑ v, F b v :=
      (Fintype.prod_sum fun b v ↦ F b v).symm
    _ = ∏ b, tilingAwayExactTotalMass (cap := cap) t x r D b (ℓ b) := by
      apply Finset.prod_congr rfl
      intro b _
      rfl

noncomputable def tilingDistinguishedSelectedMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop) : ℝ := by
  classical
  exact ∑ d, if selected d then
    tilingDistinguishedAssignmentMass t x r D d else 0

theorem tilingCappedFixedAwayTotalsMass_factorization {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (ℓ : TilingAwayDomino t x r D → ℕ) :
    (∑ q : TilingCappedCoordinates i cap,
        if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
            (∀ b, tilingAwayTotal t x r D
              (splitTilingCoordinatesEquiv t x r D q).2 b = ℓ b) then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
      tilingDistinguishedSelectedMass t x r D selected *
        ∏ b, tilingAwayExactTotalMass (cap := cap) t x r D b (ℓ b) := by
  classical
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
            (∀ b, tilingAwayTotal t x r D
              (splitTilingCoordinatesEquiv t x r D q).2 b = ℓ b) then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
        ∑ p : TilingDistinguishedCoordinates (cap := cap) t x r D ×
            TilingAwayCoordinates (cap := cap) t x r D,
          if selected p.1 ∧
              (∀ b, tilingAwayTotal t x r D p.2 b = ℓ b) then
            tilingDistinguishedAssignmentMass t x r D p.1 *
              tilingAwayAssignmentMass t x r D p.2 else 0 := by
      apply Fintype.sum_equiv (splitTilingCoordinatesEquiv t x r D)
      intro q
      by_cases hq : selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          ∀ b, tilingAwayTotal t x r D
            (splitTilingCoordinatesEquiv t x r D q).2 b = ℓ b
      · rw [if_pos hq, if_pos hq]
        have hsplit := gapVectorMass_split t x r D
          (splitTilingCoordinatesEquiv t x r D q).1
          (splitTilingCoordinatesEquiv t x r D q).2
        simpa using hsplit
      · rw [if_neg hq, if_neg hq]
    _ = ∑ d : TilingDistinguishedCoordinates (cap := cap) t x r D,
        ∑ a : TilingAwayCoordinates (cap := cap) t x r D,
          if selected d ∧ (∀ b, tilingAwayTotal t x r D a b = ℓ b) then
            tilingDistinguishedAssignmentMass t x r D d *
              tilingAwayAssignmentMass t x r D a else 0 :=
      Fintype.sum_prod_type _
    _ = tilingDistinguishedSelectedMass t x r D selected *
        (∑ a : TilingAwayCoordinates (cap := cap) t x r D,
          if (∀ b, tilingAwayTotal t x r D a b = ℓ b) then
            tilingAwayAssignmentMass t x r D a else 0) := by
      unfold tilingDistinguishedSelectedMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hd : selected d <;>
        by_cases ha : ∀ b, tilingAwayTotal t x r D a b = ℓ b <;>
        simp [hd, ha]
    _ = tilingDistinguishedSelectedMass t x r D selected *
        ∏ b, tilingAwayExactTotalMass (cap := cap) t x r D b (ℓ b) := by
      rw [tilingAwayFixedTotalsMass_factorization]

def TilingAwayTotalsScreen {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    (a : TilingAwayCoordinates (cap := cap) t x r D) : Prop :=
  ∃ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
    screen ℓ ∧ ∀ b, tilingAwayTotal t x r D a b = ℓ b

theorem tilingAwayTotalsScreen_true_iff {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (a : TilingAwayCoordinates (cap := cap) t x r D) :
    TilingAwayTotalsScreen t x r D upper (fun _ ↦ True) a ↔
      ∀ b, tilingAwayTotal t x r D a b < upper b := by
  constructor
  · rintro ⟨ℓ, _htrue, hℓ⟩ b
    rw [hℓ b]
    exact (ℓ b).isLt
  · intro h
    let ℓ : FiniteDominoProductLaw.TruncatedTotals upper :=
      fun b ↦ ⟨tilingAwayTotal t x r D a b, h b⟩
    exact ⟨ℓ, trivial, fun _ ↦ rfl⟩

theorem tilingAwayTotal_split_eq_dominoTotal {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (q : TilingCappedCoordinates i cap)
    (b : TilingAwayDomino t x r D) :
    tilingAwayTotal t x r D (splitTilingCoordinatesEquiv t x r D q).2 b =
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 := by
  unfold tilingAwayTotal tilingDominoTotal
  apply Finset.sum_congr rfl
  intro k _
  simp only [splitTilingCoordinatesEquiv_away_apply]

def tilingFavoriteAwayUpper {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (level : ℕ) (D : Finset Point)
    (b : TilingAwayDomino t x r D) : ℕ :=
  level - TilingInsertedLocalTime.tilingFixedBoundaryDominoMax
    x r terminal b.1

/-- The actual-total support of the finite product is exactly the strict
favorite cutoff supplied by the optional-terminal local-time formula. -/
theorem tilingAwayTotalsScreen_true_iff_dominoTruncation {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (level : ℕ) (D : Finset Point)
    (q : TilingCappedCoordinates i cap) :
    TilingAwayTotalsScreen t x r D
        (tilingFavoriteAwayUpper t x r terminal level D) (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t x r D q).2 ↔
      TilingInsertedLocalTime.TilingDominoTruncation
        t x r terminal level D (fun k ↦ (q k : ℕ)) := by
  rw [tilingAwayTotalsScreen_true_iff]
  constructor
  · intro h b hb
    simpa only [tilingFavoriteAwayUpper,
      tilingAwayTotal_split_eq_dominoTotal] using h ⟨b, hb⟩
  · intro h b
    simpa only [tilingFavoriteAwayUpper,
      tilingAwayTotal_split_eq_dominoTotal] using h b.1 b.2

noncomputable instance instDecidablePredTilingAwayTotalsScreen {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop) :
    DecidablePred (TilingAwayTotalsScreen (cap := cap) t x r D upper screen) :=
  Classical.decPred _

noncomputable def tilingAwayPointMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (b : TilingAwayDomino t x r D) (ℓ : ℕ) : ℝ :=
  tilingAwayExactTotalMass (cap := cap) t x r D b ℓ

noncomputable instance instDecidablePredTilingStoppingAccepted
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) :
    DecidablePred (fun q : TilingCappedCoordinates i cap ↦
      TilingStoppingAccepted tau t x r (fun k ↦ (q k : ℕ)) tail) :=
  Classical.decPred _

theorem tilingCappedScreenedMass_factorization {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    [DecidablePred screen] :
    (∑ q : TilingCappedCoordinates i cap,
        if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
            TilingAwayTotalsScreen t x r D upper screen
              (splitTilingCoordinatesEquiv t x r D q).2 then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
      ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
        if screen ℓ then
          FiniteDominoProductLaw.distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ℓ
        else 0 := by
  classical
  let mass : TilingCappedCoordinates i cap → ℝ := fun q ↦
    gapVectorMass (fun k ↦ (q k : ℕ))
  let exactAt : TilingCappedCoordinates i cap →
      FiniteDominoProductLaw.TruncatedTotals upper → Prop := fun q ℓ ↦
    ∀ b, tilingAwayTotal t x r D
      (splitTilingCoordinatesEquiv t x r D q).2 b = ℓ b
  have hone : ∀ q,
      (∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
        if screen ℓ ∧ exactAt q ℓ then mass q else 0) =
        if TilingAwayTotalsScreen t x r D upper screen
            (splitTilingCoordinatesEquiv t x r D q).2 then mass q else 0 := by
    intro q
    by_cases hex : ∃ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
        screen ℓ ∧ exactAt q ℓ
    · obtain ⟨ℓ0, hs0, he0⟩ := hex
      rw [if_pos]
      · rw [Finset.sum_eq_single ℓ0]
        · simp [hs0, he0]
        · intro ℓ _ hne
          have hnexact : ¬ exactAt q ℓ := by
            intro he
            apply hne
            funext b
            apply Fin.ext
            exact (he b).symm.trans (he0 b)
          simp [hnexact]
        · exact fun hnot ↦ (hnot (Finset.mem_univ ℓ0)).elim
      · exact ⟨ℓ0, hs0, he0⟩
    · rw [if_neg]
      · apply Finset.sum_eq_zero
        intro ℓ _
        have hnot : ¬ (screen ℓ ∧ exactAt q ℓ) := fun h ↦
          hex ⟨ℓ, h⟩
        simp [hnot]
      · exact hex
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
            TilingAwayTotalsScreen t x r D upper screen
              (splitTilingCoordinatesEquiv t x r D q).2 then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
        ∑ q : TilingCappedCoordinates i cap,
          if selected ((splitTilingCoordinatesEquiv t x r D q).1) then
            ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
              if screen ℓ ∧ exactAt q ℓ then mass q else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hd : selected ((splitTilingCoordinatesEquiv t x r D q).1)
      · rw [if_pos hd]
        simpa only [hd, true_and, mass] using (hone q).symm
      · simp [hd]
    _ = ∑ q : TilingCappedCoordinates i cap,
          ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
            if screen ℓ then
              if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                  exactAt q ℓ then mass q else 0
            else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hd : selected ((splitTilingCoordinatesEquiv t x r D q).1)
      · rw [if_pos hd]
        apply Finset.sum_congr rfl
        intro ℓ _
        by_cases hs : screen ℓ <;> by_cases he : exactAt q ℓ <;>
          simp [hd, hs, he]
      · rw [if_neg hd]
        symm
        apply Finset.sum_eq_zero
        intro ℓ _
        simp [hd]
    _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          if screen ℓ then
            ∑ q : TilingCappedCoordinates i cap,
              if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                  exactAt q ℓ then mass q else 0
          else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ℓ _
      by_cases hs : screen ℓ <;> simp [hs]
    _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
        if screen ℓ then
          tilingDistinguishedSelectedMass t x r D selected *
            ∏ b, tilingAwayExactTotalMass (cap := cap) t x r D b (ℓ b)
        else 0 := by
      apply Finset.sum_congr rfl
      intro ℓ _
      by_cases hs : screen ℓ
      · simp only [hs, if_true]
        simpa only [mass, exactAt] using
          (tilingCappedFixedAwayTotalsMass_factorization
            t x r D selected (fun b ↦ (ℓ b : ℕ)))
      · simp [hs]
    _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
        if screen ℓ then
          FiniteDominoProductLaw.distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ℓ
        else 0 := by
      apply Finset.sum_congr rfl
      intro ℓ _
      by_cases hs : screen ℓ
      · rw [if_pos hs, if_pos hs]
        unfold FiniteDominoProductLaw.distinguishedAwayMass
          FiniteDominoProductLaw.jointMass tilingAwayPointMass
          tilingDistinguishedSelectedMass
        rw [← Finset.mul_sum]
        ring_nf
      · simp [hs]

theorem tilingStoppedAcceptedGeometricMass_eq_indicatorSum
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (P : TilingCappedCoordinates i cap → Prop)
    [DecidablePred P] :
    TilingStoppedProductDisintegration.tilingStoppedAcceptedGeometricMass
        tau t x r cap tail P =
      ∑ q : TilingCappedCoordinates i cap,
        if P q ∧ TilingStoppingAccepted tau t x r
            (fun k ↦ (q k : ℕ)) tail then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
  classical
  unfold TilingStoppedProductDisintegration.tilingStoppedAcceptedGeometricMass
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The exact stopped product law after the spatial part has been reduced to
an arbitrary predicate on the distinguished coordinates and a predicate on
the actual away-domino total vector.  The two marginal identities are proved
here by finite reindexing; they are not assumptions. -/
theorem tilingStoppedAcceptedGeometricMass_product_of_factorization
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (base screened : TilingCappedCoordinates i cap → Prop)
    [DecidablePred base] [DecidablePred screened]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    [DecidablePred screen]
    (hbase : ∀ q,
      base q ∧ TilingStoppingAccepted tau t x r (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
            (splitTilingCoordinatesEquiv t x r D q).2)
    (hscreen : ∀ q,
      screened q ∧ TilingStoppingAccepted tau t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screen
            (splitTilingCoordinatesEquiv t x r D q).2)
    (htotal : (∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
      FiniteDominoProductLaw.jointMass
        (tilingAwayPointMass (cap := cap) t x r D) upper ℓ) ≠ 0) :
    TilingStoppedProductDisintegration.tilingStoppedAcceptedGeometricMass
        tau t x r cap tail screened =
      FiniteDominoProductLaw.screenMass
          (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        TilingStoppedProductDisintegration.tilingStoppedAcceptedGeometricMass
          tau t x r cap tail base := by
  classical
  apply TilingStoppedProductDisintegration.tilingStoppedAcceptedGeometricMass_eq_screenMass_mul_of_marginals
      t x r tail base screened D upper
      (tilingAwayPointMass (cap := cap) t x r D) screen
      (fun d ↦ if selected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) htotal
  · rw [tilingStoppedAcceptedGeometricMass_eq_indicatorSum]
    calc
      (∑ q : TilingCappedCoordinates i cap,
          if base q ∧ TilingStoppingAccepted tau t x r
              (fun k ↦ (q k : ℕ)) tail then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
          ∑ q : TilingCappedCoordinates i cap,
            if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
                  (splitTilingCoordinatesEquiv t x r D q).2 then
              gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        exact if_congr (hbase q) rfl rfl
      _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          FiniteDominoProductLaw.distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ℓ := by
        simpa using (tilingCappedScreenedMass_factorization
          t x r D selected upper (fun _ ↦ True))
  · rw [tilingStoppedAcceptedGeometricMass_eq_indicatorSum]
    calc
      (∑ q : TilingCappedCoordinates i cap,
          if screened q ∧ TilingStoppingAccepted tau t x r
              (fun k ↦ (q k : ℕ)) tail then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
          ∑ q : TilingCappedCoordinates i cap,
            if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                TilingAwayTotalsScreen t x r D upper screen
                  (splitTilingCoordinatesEquiv t x r D q).2 then
              gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        exact if_congr (hscreen q) rfl rfl
      _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          if screen ℓ then
            FiniteDominoProductLaw.distinguishedAwayMass
              (tilingAwayPointMass (cap := cap) t x r D) upper
              (fun d ↦ if selected d then
                tilingDistinguishedAssignmentMass t x r D d else 0) ℓ
          else 0 := tilingCappedScreenedMass_factorization
            t x r D selected upper screen

theorem tilingAwayExactTotalMass_nonneg {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (b : TilingAwayDomino t x r D) (ℓ : ℕ) :
    0 ≤ tilingAwayExactTotalMass (cap := cap) t x r D b ℓ := by
  unfold tilingAwayExactTotalMass
  apply Finset.sum_nonneg
  intro v _
  split
  · exact Finset.prod_nonneg fun k _ ↦ geometricGapMass_nonneg _
  · exact le_rfl

theorem tilingAwayExactTotalMass_zero_pos {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (b : TilingAwayDomino t x r D) :
    0 < tilingAwayExactTotalMass (cap := cap) t x r D b 0 := by
  classical
  let v0 : TilingCoordinatesAt t x r b.1 → Fin (cap + 1) := fun _ ↦ 0
  have hterm : 0 <
      (if (∑ k, (v0 k : ℕ)) = 0 then
        ∏ k, geometricGapMass (v0 k : ℕ) else 0) := by
    rw [if_pos (by simp [v0])]
    apply Finset.prod_pos
    intro k _
    unfold geometricGapMass
    positivity
  apply hterm.trans_le
  unfold tilingAwayExactTotalMass
  exact Finset.single_le_sum (s := Finset.univ) (a := v0)
    (f := fun v : TilingCoordinatesAt t x r b.1 → Fin (cap + 1) ↦
      if (∑ k, (v k : ℕ)) = 0 then
        ∏ k, geometricGapMass (v k : ℕ) else 0) (fun v _ ↦ by
    split
    · exact Finset.prod_nonneg fun k _ ↦ geometricGapMass_nonneg _
    · exact le_rfl) (Finset.mem_univ v0)

theorem tilingAwayPointMass_normalization_ne_zero_of_upper_pos {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, 0 < upper b) :
    (∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
      FiniteDominoProductLaw.jointMass
        (tilingAwayPointMass (cap := cap) t x r D) upper ℓ) ≠ 0 := by
  classical
  let ℓ0 : FiniteDominoProductLaw.TruncatedTotals upper :=
    fun b ↦ ⟨0, hupper b⟩
  have hterm : 0 < FiniteDominoProductLaw.jointMass
      (tilingAwayPointMass (cap := cap) t x r D) upper ℓ0 := by
    unfold FiniteDominoProductLaw.jointMass tilingAwayPointMass
    apply Finset.prod_pos
    intro b _
    exact tilingAwayExactTotalMass_zero_pos t x r D b
  apply ne_of_gt (hterm.trans_le ?_)
  apply Finset.single_le_sum
  · intro ℓ _
    unfold FiniteDominoProductLaw.jointMass tilingAwayPointMass
    exact Finset.prod_nonneg fun b _ ↦
      tilingAwayExactTotalMass_nonneg t x r D b (ℓ b)
  · exact Finset.mem_univ ℓ0

/-! ## Constructor for stopped-coordinate certificates -/

/-- Spatial input sufficient to construct a complete all-six stopped
coordinate specification.  In contrast with
`TilingStoppedCoordinateProductSpec`, this structure asks only for the
pointwise identification of accepted coordinates with distinguished data
and the actual away-total screen.  The normalized product identity is then
derived by `tilingStoppedCoordinateProductSpecOfFactoredData`. -/
structure TilingFactoredStoppedCoordinateData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  tiling : index → ℕ → DominoTiling
  retainedCount : index → ℕ → ℕ
  start : index → ℕ → Point
  retained : ∀ z cap,
    TilingRetainedWord (tiling z cap) (start z cap) (retainedCount z cap)
  tail : index → ℕ → List Direction
  stoppingTime : index → ℕ → StepPath → ℕ
  isStoppingTime : ∀ z cap, IsFiniteStoppingTime (stoppingTime z cap)
  basePredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screenedPredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) cap → Prop
  screened_subset_base : ∀ z cap q,
    screenedPredicate z cap q → basePredicate z cap q
  base_subset_piece : ∀ z cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (basePredicate z cap)) ⊆ piece z
  distinguished : index → ℕ → Finset Point
  selected : ∀ z cap,
    TilingDistinguishedCoordinates (cap := cap)
      (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → Prop
  upper : ∀ z cap,
    TilingAwayDomino (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → ℕ
  accepts : ∀ z cap, FiniteDominoProductLaw.TruncatedTotals (upper z cap) → Bool
  base_factorization : ∀ z cap q,
    basePredicate z cap q ∧
        TilingStoppingAccepted (stoppingTime z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun _ ↦ True)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  screened_factorization : ∀ z cap q,
    screenedPredicate z cap q ∧
        TilingStoppingAccepted (stoppingTime z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun ℓ ↦ accepts z cap ℓ = true)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  upper_pos : ∀ z cap b, 0 < upper z cap b
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (tilingPreStoppingFiberEvent (stoppingTime z cap)
      (tiling z cap) (start z cap) (retained z cap) cap (tail z cap)
      (screenedPredicate z cap))
  product_bound : ∀ z cap,
    FiniteDominoProductLaw.screenMass
      (tilingAwayPointMass (cap := cap) (tiling z cap) (start z cap)
        (retained z cap) (distinguished z cap)) (upper z cap)
      (fun ℓ ↦ accepts z cap ℓ = true) ≤ cost.toReal

/-- Construct the literal capped stopped-coordinate product specification.
The point mass is the exact finite geometric mass of all insertion
coordinates above one away domino with prescribed total. -/
noncomputable def tilingStoppedCoordinateProductSpecOfFactoredData
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next cost) :
    TilingStoppedProductDisintegration.TilingStoppedCoordinateProductSpec
      piece next cost := by
  classical
  refine {
    tiling := data.tiling
    retainedCount := data.retainedCount
    start := data.start
    retained := data.retained
    tail := data.tail
    stoppingTime := data.stoppingTime
    isStoppingTime := data.isStoppingTime
    basePredicate := data.basePredicate
    screenedPredicate := data.screenedPredicate
    screened_subset_base := data.screened_subset_base
    base_subset_piece := data.base_subset_piece
    distinguished := data.distinguished
    upper := data.upper
    pointMass := fun z cap ↦ tilingAwayPointMass (cap := cap)
      (data.tiling z cap) (data.start z cap) (data.retained z cap)
      (data.distinguished z cap)
    accepts := data.accepts
    coordinate_identity := ?_
    monotone_screened := data.monotone_screened
    transition_covered := data.transition_covered
    product_bound := data.product_bound }
  intro z cap
  exact tilingStoppedAcceptedGeometricMass_product_of_factorization
    (data.stoppingTime z cap) (data.tiling z cap) (data.start z cap)
    (data.retained z cap) (data.tail z cap) (data.basePredicate z cap)
    (data.screenedPredicate z cap) (data.distinguished z cap)
    (data.selected z cap) (data.upper z cap)
    (fun ℓ ↦ data.accepts z cap ℓ = true)
    (data.base_factorization z cap) (data.screened_factorization z cap)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      (data.tiling z cap) (data.start z cap) (data.retained z cap)
      (data.distinguished z cap) (data.upper z cap) (data.upper_pos z cap))

end Erdos1165.TilingCappedMarginalization
