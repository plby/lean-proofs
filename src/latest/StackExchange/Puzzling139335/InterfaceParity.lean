import StackExchange.Puzzling139335.InterfacePairing.Involution
import StackExchange.Puzzling139335.BoundaryGerm
import StackExchange.Puzzling139335.InterfaceParity.ColoredPairs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Parity of straight interface occurrences

An actual interface and its partner occurrence have the same carrier.  The
fixed-point-free involution on occurrences therefore preserves straightness
at a given point.  Its finite orbits have even total cardinality.  Separating
the exterior boundary from the four tile boundaries gives the parity used
at square corners.
-/

open Set
open scoped BigOperators

namespace Puzzling139335

/-- A finite set preserved by a fixed-point-free involution has even
cardinality. -/
theorem even_card_finset_of_involutive {α : Type*} (s : Finset α) (τ : α → α)
    (hmem : ∀ a ∈ s, τ a ∈ s) (hinv : ∀ a ∈ s, τ (τ a) = a)
    (hne : ∀ a ∈ s, τ a ≠ a) : Even s.card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hsum : (∑ _a ∈ s, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun a _ => τ a)
    · intro a ha
      simpa only [Nat.cast_ofNat, one_add_one_eq_two] using ZMod.natCast_self 2
    · intro a ha _
      exact hne a ha
    · exact hmem
    · exact hinv
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hsum

namespace ExactBoundaryArcFamily

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- The actual arc occurrences containing a straight initial segment at `v`. -/
noncomputable def straightOccurrences (v : Plane) : Finset F.Occurrence := by
  classical
  exact Finset.univ.filter (fun a => IsStraightAt (F.carrier a) v)

/-- Straight arc occurrences on one specified boundary. -/
noncomputable def straightBoundaryOccurrences (i : ExtendedPieceIndex) (v : Plane) :
    Finset (Fin (F.n i)) := by
  classical
  exact Finset.univ.filter (fun k => IsStraightAt (F.arc i k) v)

@[simp] theorem mem_straightOccurrences {v : Plane} {a : F.Occurrence} :
    a ∈ F.straightOccurrences v ↔ IsStraightAt (F.carrier a) v := by
  classical
  simp [straightOccurrences]

@[simp] theorem mem_straightBoundaryOccurrences {i : ExtendedPieceIndex} {v : Plane}
    {k : Fin (F.n i)} :
    k ∈ F.straightBoundaryOccurrences i v ↔ IsStraightAt (F.arc i k) v := by
  classical
  simp [straightBoundaryOccurrences]

/-- At a junction, every selected straight occurrence is incident to the
junction as an endpoint. -/
theorem straightOccurrence_endpoint {v : Plane}
    (hv : v ∈ tripleContactSet d.extendedPiece) {a : F.Occurrence}
    (ha : a ∈ F.straightOccurrences v) :
    v = F.left a.1 a.2 ∨ v = F.right a.1 a.2 := by
  have hmem := (F.mem_straightOccurrences.mp ha).mem
  by_contra hnot
  exact Set.disjoint_left.mp (F.arcInterior_disjoint a.1 a.2) ⟨hmem, hnot⟩ hv

/-- Straightness is preserved by the actual interface pairing. -/
theorem mate_mem_straightOccurrences_iff (v : Plane) (a : F.Occurrence) :
    F.mate a ∈ F.straightOccurrences v ↔ a ∈ F.straightOccurrences v := by
  simp only [F.mem_straightOccurrences, F.carrier_mate]

/-- The straight occurrences across all five boundaries have even total
cardinality. -/
theorem even_card_straightOccurrences (v : Plane) :
    Even (F.straightOccurrences v).card := by
  apply even_card_finset_of_involutive (F.straightOccurrences v) F.mate
  · intro a ha
    exact (F.mate_mem_straightOccurrences_iff v a).mpr ha
  · intro a _
    exact F.mate_involutive a
  · intro a _
    exact F.mate_ne a

/-- Counting all selected occurrences is the sum of the counts on each
boundary. -/
theorem card_straightOccurrences_eq_sum (v : Plane) :
    (F.straightOccurrences v).card =
      ∑ i : ExtendedPieceIndex, (F.straightBoundaryOccurrences i v).card := by
  classical
  let e : {a : F.Occurrence // IsStraightAt (F.carrier a) v} ≃
      Σ i : ExtendedPieceIndex, {k : Fin (F.n i) // IsStraightAt (F.arc i k) v} :=
    { toFun := fun a => ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
      left_inv := by rintro ⟨⟨i, k⟩, h⟩; rfl
      right_inv := by rintro ⟨i, ⟨k, h⟩⟩; rfl }
  calc
    (F.straightOccurrences v).card =
        Fintype.card {a : F.Occurrence // IsStraightAt (F.carrier a) v} := by
      simp only [straightOccurrences, Fintype.card_subtype]
    _ = Fintype.card
        (Σ i : ExtendedPieceIndex, {k : Fin (F.n i) // IsStraightAt (F.arc i k) v}) :=
      Fintype.card_congr e
    _ = ∑ i : ExtendedPieceIndex, (F.straightBoundaryOccurrences i v).card := by
      simp only [Fintype.card_sigma, Fintype.card_subtype, straightBoundaryOccurrences]

/-- Separate the exterior contribution from the four tile contributions. -/
theorem card_straightOccurrences_eq_tile_sum_add_exterior (v : Plane) :
    (F.straightOccurrences v).card =
      (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card) +
        (F.straightBoundaryOccurrences (.inr ()) v).card := by
  rw [F.card_straightOccurrences_eq_sum, Fintype.sum_sum_type]
  simp

/-- Restricting the global occurrence set to one boundary recovers the
occurrences indexed on that boundary. -/
theorem straightOccurrences_filter_fst_eq_image (i : ExtendedPieceIndex) (v : Plane) :
    ((F.straightOccurrences v).filter (fun a => a.1 = i)) =
      (F.straightBoundaryOccurrences i v).image
        (fun k => (⟨i, k⟩ : F.Occurrence)) := by
  classical
  ext a
  simp only [Finset.mem_filter, F.mem_straightOccurrences, Finset.mem_image]
  constructor
  · rintro ⟨ha, hi⟩
    rcases a with ⟨j, k⟩
    dsimp only at hi
    subst j
    exact ⟨k, F.mem_straightBoundaryOccurrences.mpr ha, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨F.mem_straightBoundaryOccurrences.mp hk, rfl⟩

/-- Count occurrences on a fixed boundary using the global occurrence set. -/
theorem card_straightOccurrences_filter_fst (i : ExtendedPieceIndex) (v : Plane) :
    ((F.straightOccurrences v).filter (fun a => a.1 = i)).card =
      (F.straightBoundaryOccurrences i v).card := by
  classical
  rw [F.straightOccurrences_filter_fst_eq_image]
  apply Finset.card_image_of_injective
  intro j k h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- Removing the exterior occurrences leaves exactly the sum over tiles. -/
theorem card_straightOccurrences_filter_ne_exterior (v : Plane) :
    ((F.straightOccurrences v).filter
      (fun a => a.1 ≠ (.inr () : ExtendedPieceIndex))).card =
      ∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := F.straightOccurrences v)
    (fun a => a.1 = (.inr () : ExtendedPieceIndex))
  rw [F.card_straightOccurrences_filter_fst,
    F.card_straightOccurrences_eq_tile_sum_add_exterior] at h
  exact Nat.add_left_cancel (h.trans (Nat.add_comm _ _))

/-- Straight occurrences whose two incident regions are both tiles. -/
noncomputable def internalStraightOccurrences (v : Plane) : Finset F.Occurrence := by
  classical
  exact (F.straightOccurrences v).filter
    (fun a => a.1 ≠ (.inr () : ExtendedPieceIndex) ∧
      (F.mate a).1 ≠ (.inr () : ExtendedPieceIndex))

/-- The number of straight internal interfaces, counting each paired
interface once. -/
noncomputable def internalStraightInterfaceCount (v : Plane) : ℕ :=
  (F.internalStraightOccurrences v).card / 2

/-- Each internal interface contributes two tile occurrences, whereas
each exterior interface contributes one. -/
theorem exists_internal_straight_pair_count (v : Plane) :
    ∃ k : ℕ, (F.internalStraightOccurrences v).card = 2 * k ∧
      (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card) =
        2 * k + (F.straightBoundaryOccurrences (.inr ()) v).card := by
  classical
  obtain ⟨k, hk, hcount⟩ := colored_pair_card_with_internal_count
    (F.straightOccurrences v) F.mate
    (fun a : F.Occurrence => a.1 = (.inr () : ExtendedPieceIndex))
    (fun a ha => (F.mate_mem_straightOccurrences_iff v a).mpr ha)
    (fun a _ => F.mate_involutive a)
    (fun a _ => F.mate_ne a)
    (by
      intro a _ ha hm
      rw [F.mate_fst] at hm
      exact F.partner_ne a.1 a.2 (hm.trans ha.symm))
  refine ⟨k, hk, ?_⟩
  rw [F.card_straightOccurrences_filter_ne_exterior,
    F.card_straightOccurrences_filter_fst] at hcount
  exact hcount

/-- The explicit count identity for the actual paired interfaces. -/
theorem tile_straight_count_eq_twice_internal_add_exterior (v : Plane) :
    (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card) =
      2 * F.internalStraightInterfaceCount v +
        (F.straightBoundaryOccurrences (.inr ()) v).card := by
  obtain ⟨k, hk, hcount⟩ := F.exists_internal_straight_pair_count v
  dsimp only [internalStraightInterfaceCount]
  omega

/-- Every straight exterior interface also has one tile occurrence. -/
theorem exterior_card_le_tile_sum (v : Plane) :
    (F.straightBoundaryOccurrences (.inr ()) v).card ≤
      ∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card := by
  rw [F.tile_straight_count_eq_twice_internal_add_exterior]
  omega

/-- Two exterior occurrences force a positive tile occurrence count. -/
theorem tile_straight_count_pos_of_exterior_card_two (v : Plane)
    (hext : (F.straightBoundaryOccurrences (.inr ()) v).card = 2) :
    0 < ∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card := by
  have h := F.exterior_card_le_tile_sum v
  omega

/-- An even exterior count leaves an even sum on the tile boundaries. -/
theorem even_tile_straight_count_of_exterior_even (v : Plane)
    (hext : Even (F.straightBoundaryOccurrences (.inr ()) v).card) :
    Even (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card) := by
  have htotal := F.even_card_straightOccurrences v
  rw [F.card_straightOccurrences_eq_tile_sum_add_exterior] at htotal
  exact (Nat.even_add.mp htotal).mpr hext

/-- The form used at a square corner: remove the two exterior straight
occurrences from the even total. -/
theorem even_tile_straight_count_of_exterior_card_two (v : Plane)
    (hext : (F.straightBoundaryOccurrences (.inr ()) v).card = 2) :
    Even (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) v).card) := by
  apply F.even_tile_straight_count_of_exterior_even v
  rw [hext]
  exact even_two

end ExactBoundaryArcFamily

end Puzzling139335
