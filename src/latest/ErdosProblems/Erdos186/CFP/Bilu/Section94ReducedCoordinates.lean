/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section94RpowContainerAssembly

/-!
# Coefficient coordinates of a reduced outer realization

The lattice lifts stored in a `ReducedOuterRealization` have canonical
coordinates in its proper Mahler box.  Enlarged injectivity makes this
coordinate realization Freiman of order two.  Consequently its real
coefficient set has exactly the source cardinality and no larger doubling
constant than the original integer set.
-/

namespace Erdos186.CFP.Bilu.Section94ReducedCoordinates

open CFP.BiluFreiman
open Section5SortedTail Section7FreimanMap
open Section9ContainerIntegration Section94SortedContainerAssembly
open MahlerBox MahlerOuterContainer

noncomputable section

set_option autoImplicit false

namespace ReducedOuterRealization

variable {s volumeConstant rankBound : ℕ} {A : Finset ℤ}

/-- A selected unit-ball lattice lift of a source element. -/
def latticeLift
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) : Mahler.IntegralPoint R.rank :=
  (R.lifts a a.property).choose

theorem latticeLift_mem_unitBall
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) :
    R.seminorm (Mahler.integralEmbed (latticeLift R a)) ≤ 1 :=
  (R.lifts a a.property).choose_spec.1

@[simp] theorem map_latticeLift
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) : R.map (latticeLift R a) = a :=
  (R.lifts a a.property).choose_spec.2

theorem latticeLift_mem_source
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) : latticeLift R a ∈ R.outer.source.carrier :=
  R.outer.unitBall_integral_subset _ (latticeLift_mem_unitBall R a)

/-- Coordinates of the selected lift in the proper source Mahler box. -/
def coordinateLift
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) : R.outer.source.Coord :=
  (GAP.mem_carrier_iff.mp (latticeLift_mem_source R a)).choose

@[simp] theorem coordPoint_coordinateLift
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) :
    R.outer.source.coordPoint (coordinateLift R a) = latticeLift R a :=
  (GAP.mem_carrier_iff.mp (latticeLift_mem_source R a)).choose_spec

@[simp] theorem map_coordPoint_coordinateLift
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a : A) :
    R.map (R.outer.source.coordPoint (coordinateLift R a)) = a := by
  rw [coordPoint_coordinateLift, map_latticeLift]

theorem coordinateLift_injective
    (R : ReducedOuterRealization s volumeConstant rankBound A) :
    Function.Injective (coordinateLift R) := by
  intro a b hab
  apply Subtype.ext
  have := congrArg
    (fun c ↦ R.map (R.outer.source.coordPoint c)) hab
  simpa using this

/-- The coefficient set corresponding bijectively to the source set. -/
def coefficientSet
    (R : ReducedOuterRealization s volumeConstant rankBound A) :
    Finset R.outer.source.Coord :=
  A.attach.image (coordinateLift R)

@[simp] theorem card_coefficientSet
    (R : ReducedOuterRealization s volumeConstant rankBound A) :
    (coefficientSet R).card = A.card := by
  rw [coefficientSet, Finset.card_image_of_injective]
  · simp
  · exact coordinateLift_injective R

theorem coefficientSet_nonempty
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hA : A.Nonempty) : (coefficientSet R).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨coordinateLift R ⟨a, ha⟩,
    Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩⟩

theorem volume_le_coefficientSet
    (R : ReducedOuterRealization s volumeConstant rankBound A) :
    R.outer.source.volume ≤ volumeConstant * (coefficientSet R).card := by
  simpa only [card_coefficientSet] using R.volume_le

/-- The raw coordinate sum, represented in the doubled coefficient box. -/
def pairCoord {ambient rank : ℕ} (P : GAP ambient rank)
    (c e : P.Coord) : (P.dilate 2).Coord :=
  fun i ↦ ⟨(c i : ℕ) + (e i : ℕ), by
    have hc := (c i).isLt
    have he := (e i).isLt
    simp only [GAP.dilate_widths]
    omega⟩

@[simp] theorem pairCoord_apply {ambient rank : ℕ}
    (P : GAP ambient rank) (c e : P.Coord) (i : Fin rank) :
    ((pairCoord P c e i : Fin _) : ℕ) = (c i : ℕ) + (e i : ℕ) :=
  rfl

theorem coordPoint_pairCoord {ambient rank : ℕ}
    (P : GAP ambient rank) (c e : P.Coord) :
    (P.dilate 2).coordPoint (pairCoord P c e) =
      P.coordPoint c + P.coordPoint e := by
  funext j
  simp only [GAP.coordPoint, GAP.dilate_offset, Pi.add_apply, pairCoord,
    GAP.dilate_steps]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

theorem realCoord_add_eq_of_pairCoord_eq {ambient rank : ℕ}
    (P : GAP ambient rank) {c e c' e' : P.Coord}
    (h : pairCoord P c e = pairCoord P c' e') :
    realCoord P c + realCoord P e =
      realCoord P c' + realCoord P e' := by
  funext i
  have hi := congrArg (fun q : (P.dilate 2).Coord ↦ (q i : ℕ)) h
  change ((c i : ℕ) : ℝ) + (e i : ℕ) =
    ((c' i : ℕ) : ℝ) + (e' i : ℕ)
  exact_mod_cast hi

/-- The doubled source Mahler box lies in the `2s` box whenever `s>0`. -/
theorem dilate_two_subset_enlarged
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hs : 0 < s) :
    (R.outer.source.dilate 2).carrier ⊆
      (R.outer.source.dilate (2 * s)).carrier := by
  intro z hz
  rw [MappedOuterContainer.source,
    dilate_centeredBasisGAP] at hz ⊢
  obtain ⟨u, hu, huz⟩ :=
    exists_bounded_coefficients_of_mem_centeredBasisGAP hz
  apply mem_centeredBasisGAP_of_repr_abs_le
  intro i
  have hrepri : R.outer.basis.repr z i = u i := by
    rw [huz]
    exact congrFun (R.outer.basis.repr_sum_self u) i
  rw [hrepri]
  have hui := hu i
  push_cast at hui ⊢
  have hsone : 1 ≤ s := hs
  have hradius :
      (2 : ℤ) * outerRadius R.seminorm i ≤
        (2 * s : ℤ) * outerRadius R.seminorm i := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.mul_le_mul_left 2 hsone
    · positivity
  exact hui.trans hradius

/-- Equality of source pair sums forces equality of their real coefficient
pair sums.  This is the order-two Freiman property supplied by enlarged
injectivity. -/
theorem realCoordinate_pair_eq_of_integer_pair_eq
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hs : 0 < s) (a b c d : A)
    (h : (a : ℤ) + b = c + d) :
    realCoord R.outer.source (coordinateLift R a) +
        realCoord R.outer.source (coordinateLift R b) =
      realCoord R.outer.source (coordinateLift R c) +
        realCoord R.outer.source (coordinateLift R d) := by
  let qa := coordinateLift R a
  let qb := coordinateLift R b
  let qc := coordinateLift R c
  let qd := coordinateLift R d
  have hmap : R.map (R.outer.source.coordPoint qa +
        R.outer.source.coordPoint qb) =
      R.map (R.outer.source.coordPoint qc +
        R.outer.source.coordPoint qd) := by
    simp only [map_add, qa, qb, qc, qd, map_coordPoint_coordinateLift]
    exact h
  have hleft : R.outer.source.coordPoint qa +
      R.outer.source.coordPoint qb ∈
        (R.outer.source.dilate (2 * s)).carrier :=
    dilate_two_subset_enlarged R hs
      (by rw [← coordPoint_pairCoord]; exact GAP.coordPoint_mem_carrier _ _)
  have hright : R.outer.source.coordPoint qc +
      R.outer.source.coordPoint qd ∈
        (R.outer.source.dilate (2 * s)).carrier :=
    dilate_two_subset_enlarged R hs
      (by rw [← coordPoint_pairCoord]; exact GAP.coordPoint_mem_carrier _ _)
  have hpoint : R.outer.source.coordPoint qa +
        R.outer.source.coordPoint qb =
      R.outer.source.coordPoint qc + R.outer.source.coordPoint qd := by
    apply R.enlarged_injective hleft hright
    funext i
    simpa only [integerPointHom_apply, CFP.BiluFreiman.integerPoint] using hmap
  have hcoord : pairCoord R.outer.source qa qb =
      pairCoord R.outer.source qc qd := by
    exact R.outer.source_dilates_proper 2
      ((coordPoint_pairCoord R.outer.source qa qb).trans
        (hpoint.trans (coordPoint_pairCoord R.outer.source qc qd).symm))
  exact realCoord_add_eq_of_pairCoord_eq R.outer.source hcoord

/-- Real coefficient pair equality also forces equality of the represented
integer pair sums.  This direction only uses the stored lift identities. -/
theorem integer_pair_eq_of_realCoordinate_pair_eq
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (a b c d : A)
    (h : realCoord R.outer.source (coordinateLift R a) +
          realCoord R.outer.source (coordinateLift R b) =
        realCoord R.outer.source (coordinateLift R c) +
          realCoord R.outer.source (coordinateLift R d)) :
    (a : ℤ) + b = c + d := by
  have hcoord : pairCoord R.outer.source (coordinateLift R a)
        (coordinateLift R b) =
      pairCoord R.outer.source (coordinateLift R c)
        (coordinateLift R d) := by
    funext i
    apply Fin.ext
    have hi := congrFun h i
    change (((coordinateLift R a i : ℕ) : ℝ) +
        (coordinateLift R b i : ℕ)) =
      (((coordinateLift R c i : ℕ) : ℝ) +
        (coordinateLift R d i : ℕ)) at hi
    exact_mod_cast hi
  have hpoint : R.outer.source.coordPoint (coordinateLift R a) +
        R.outer.source.coordPoint (coordinateLift R b) =
      R.outer.source.coordPoint (coordinateLift R c) +
        R.outer.source.coordPoint (coordinateLift R d) := by
    have := congrArg
      (fun q ↦ (R.outer.source.dilate 2).coordPoint q) hcoord
    simpa only [coordPoint_pairCoord] using this
  have hmap := congrArg R.map hpoint
  simpa only [map_add, map_coordPoint_coordinateLift] using hmap

/-- Ordered source pairs, used to compare the two finite sumset images. -/
def sourcePairs : Finset (A × A) := A.attach.product A.attach

/-- The integer sum attached to an ordered source pair. -/
def integerPairSum (p : A × A) : ℤ := p.1 + p.2

/-- The corresponding sum in the real coefficient realization. -/
def realPairSum
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (p : A × A) : Fin R.rank → ℝ :=
  realCoord R.outer.source (coordinateLift R p.1) +
    realCoord R.outer.source (coordinateLift R p.2)

theorem image_integerPairSum (A : Finset ℤ) :
    (sourcePairs (A := A)).image integerPairSum = twoA A := by
  ext z
  rw [Finset.mem_image, mem_twoA_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    exact ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩),
      Finset.mem_product.mpr ⟨by simp, by simp⟩, rfl⟩

theorem image_realPairSum
    (R : ReducedOuterRealization s volumeConstant rankBound A) :
    (sourcePairs (A := A)).image (realPairSum R) =
      pairSumset (realCoordinateSet R.outer.source (coefficientSet R)) := by
  ext z
  rw [Finset.mem_image, mem_pairSumset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    refine ⟨realCoord R.outer.source (coordinateLift R p.1), ?_,
      realCoord R.outer.source (coordinateLift R p.2), ?_, rfl⟩
    · exact Finset.mem_image.mpr ⟨coordinateLift R p.1,
        Finset.mem_image.mpr ⟨p.1, by simp, rfl⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨coordinateLift R p.2,
        Finset.mem_image.mpr ⟨p.2, by simp, rfl⟩, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨cx, hcx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcx
    obtain ⟨cy, hcy, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hcy
    exact ⟨(a, b), Finset.mem_product.mpr ⟨by simp, by simp⟩, hxy⟩

/-- The coefficient realization has exactly the original integer doubling
cardinality. -/
theorem card_pairSumset_realCoordinateSet_eq_twoA
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hs : 0 < s) (hA : A.Nonempty) :
    (pairSumset
      (realCoordinateSet R.outer.source (coefficientSet R))).card =
      (twoA A).card := by
  let a₀ : A := ⟨hA.choose, hA.choose_spec⟩
  let : Inhabited A := ⟨a₀⟩
  have hcard := card_image_eq_card_image_of_eq_iff
    (sourcePairs (A := A)) integerPairSum (realPairSum R)
    (fun x _ y _ ↦ ⟨
      fun h ↦ realCoordinate_pair_eq_of_integer_pair_eq R hs
        x.1 x.2 y.1 y.2 h,
      fun h ↦ integer_pair_eq_of_realCoordinate_pair_eq R
        x.1 x.2 y.1 y.2 h⟩)
  rw [image_integerPairSum, image_realPairSum] at hcard
  exact hcard.symm

/-- The canonical coefficient set discharges the complete terminal
coordinate clause from the original source doubling inequality. -/
theorem exists_coefficientSet_of_sourceDoubling
    (R : ReducedOuterRealization s volumeConstant rankBound A)
    (hs : 0 < s) (hA : A.Nonempty) {d : ℕ} {delta : ℝ}
    (hdouble : ((twoA A).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card) :
    ∃ K : Finset R.outer.source.Coord,
      K.Nonempty ∧
      R.outer.source.volume ≤ volumeConstant * K.card ∧
      ((pairSumset (realCoordinateSet R.outer.source K)).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) *
          (realCoordinateSet R.outer.source K).card := by
  refine ⟨coefficientSet R, coefficientSet_nonempty R hA,
    volume_le_coefficientSet R, ?_⟩
  simpa only [card_pairSumset_realCoordinateSet_eq_twoA R hs hA,
    card_realCoordinateSet, card_coefficientSet] using hdouble

end ReducedOuterRealization

/-! ## Exact remaining source-facing existence boundary -/

/-- The analytic part of the Section 9 source construction, after removing
the now-automatic coefficient realization.  It asks only for the reduced
outer body, its lift map, injectivity, volume, and rank data. -/
def ReducedOuterExistenceStatement : Prop :=
  ∀ s d : ℕ, 0 < s → 0 < d →
    ∀ delta : ℝ, 0 < delta →
      ∃ volumeConstant rankBound : ℕ,
        0 < volumeConstant ∧
        ∀ A : Finset ℤ, A.Nonempty →
          ((twoA A).card : ℝ) ≤
              Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
            Nonempty (ReducedOuterRealization
              s volumeConstant rankBound A)

/-- Once a reduced outer realization exists, no further analytic input is
needed for the public Section 9--4 statement. -/
theorem reducedOuterRealizationStatement_of_existence
    (hsource : ReducedOuterExistenceStatement) :
    Section94RpowContainerAssembly.ReducedOuterRealizationStatement := by
  intro s d hs hd delta hdelta
  obtain ⟨volumeConstant, rankBound, hvolumeConstant, hrealize⟩ :=
    hsource s d hs hd delta hdelta
  refine ⟨volumeConstant, rankBound, hvolumeConstant, ?_⟩
  intro A hA hdouble
  obtain ⟨R⟩ := hrealize A hA hdouble
  refine ⟨R, ?_⟩
  intro _
  exact ReducedOuterRealization.exists_coefficientSet_of_sourceDoubling
    R hs hA hdouble

/-- The automatic coefficient construction identifies the public source
statement exactly with reduced-body existence. -/
theorem reducedOuterRealizationStatement_iff_existence :
    Section94RpowContainerAssembly.ReducedOuterRealizationStatement ↔
      ReducedOuterExistenceStatement := by
  constructor
  · intro hsource s d hs hd delta hdelta
    obtain ⟨volumeConstant, rankBound, hvolumeConstant, hrealize⟩ :=
      hsource s d hs hd delta hdelta
    refine ⟨volumeConstant, rankBound, hvolumeConstant, ?_⟩
    intro A hA hdouble
    obtain ⟨R, -⟩ := hrealize A hA hdouble
    exact ⟨R⟩
  · exact reducedOuterRealizationStatement_of_existence

end


end Erdos186.CFP.Bilu.Section94ReducedCoordinates

#print axioms
  Erdos186.CFP.Bilu.Section94ReducedCoordinates.ReducedOuterRealization.card_pairSumset_realCoordinateSet_eq_twoA
#print axioms
  Erdos186.CFP.Bilu.Section94ReducedCoordinates.ReducedOuterRealization.exists_coefficientSet_of_sourceDoubling
#print axioms
  Erdos186.CFP.Bilu.Section94ReducedCoordinates.reducedOuterRealizationStatement_iff_existence
