import StackExchange.Puzzling139335.InterfacePairing

/-!
# The involution on interface arc occurrences

Choosing the unique matching arc on the partner boundary pairs the two
occurrences of each interface.  This pairing preserves the carrier, has no
fixed points, and is involutive.
-/

namespace Puzzling139335.ExactBoundaryArcFamily

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- An arc occurrence consists of its boundary and its index on that boundary. -/
abbrev Occurrence := Σ i : ExtendedPieceIndex, Fin (F.n i)

/-- The geometric carrier of an arc occurrence. -/
def carrier (a : F.Occurrence) : Set Plane := F.arc a.1 a.2

/-- The boundary and carrier uniquely determine an arc occurrence. -/
theorem occurrence_eq_of_fst_eq_of_carrier_eq (a b : F.Occurrence)
    (hi : a.1 = b.1) (hC : F.carrier a = F.carrier b) : a = b := by
  rcases a with ⟨i, k⟩
  rcases b with ⟨j, l⟩
  dsimp at hi
  subst j
  change F.arc i k = F.arc i l at hC
  obtain ⟨x, hx, hxnot⟩ := F.exists_mem_off_junctions i k
  have hkl : k = l :=
    F.index_eq_of_mem_off_junctions i hx (hC ▸ hx) hxnot
  cases hkl
  rfl

/-- The unique occurrence of the same interface on its partner boundary. -/
noncomputable def mate (a : F.Occurrence) : F.Occurrence :=
  ⟨F.partner a.1 a.2, (F.exists_unique_partner_arc a.1 a.2).exists.choose⟩

@[simp] theorem mate_fst (a : F.Occurrence) :
    (F.mate a).1 = F.partner a.1 a.2 := rfl

/-- Passing to the partner occurrence leaves the geometric arc unchanged. -/
@[simp] theorem carrier_mate (a : F.Occurrence) :
    F.carrier (F.mate a) = F.carrier a :=
  (F.exists_unique_partner_arc a.1 a.2).exists.choose_spec.symm

/-- The partner occurrence names the original boundary as its partner. -/
@[simp] theorem partner_mate (a : F.Occurrence) :
    F.partner (F.mate a).1 (F.mate a).2 = a.1 :=
  F.partner_reverse_of_arc_eq a.1 a.2 (F.mate a).2 (F.carrier_mate a).symm

/-- No occurrence is paired with itself, since its partner boundary is distinct. -/
theorem mate_ne (a : F.Occurrence) : F.mate a ≠ a := by
  intro h
  exact F.partner_ne a.1 a.2 (congrArg Sigma.fst h)

/-- Pairing the partner occurrence returns the original occurrence. -/
theorem mate_involutive : Function.Involutive F.mate := by
  intro a
  apply F.occurrence_eq_of_fst_eq_of_carrier_eq
  · exact F.partner_mate a
  · simp only [F.carrier_mate]

end Puzzling139335.ExactBoundaryArcFamily
