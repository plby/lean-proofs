import ErdosProblems.Erdos807.HostFamily
import ErdosProblems.Erdos807.HostMoments
import ErdosProblems.Erdos807.Overlap

/-!
# Compatibility of stable-slot structured witnesses

Two stable host choices may share many of their selected vertices.  If a
single host graph realizes a matrix on each choice, then every matrix entry
whose left and right template vertices are both shared is forced.  The
remaining entries have the `10 * r * j`-bit encoding constructed in
`HostMoments`: `r * j` bits cover missing right vertices, while the other
`9 * r * j` bits split the right side into ten chunks and cover a row when
the corresponding left vertex is missing.

This file connects that concrete matrix reconstruction with the actual
`SlotMatrixEvent` predicates used by the random-graph argument.
-/

namespace Erdos807
namespace SlotCompatibility

open StructuredFamily
open HostFamily

/-! ## Differing stable slots -/

/-- The template slots at which two stable host choices select different
vertices. -/
def differingSlots {n r : ℕ} (c d : Choice n r) : Finset (Fin (templateOrder r)) :=
  Finset.univ.filter fun s ↦ c s ≠ d s

theorem differingSlots_eq_hostMoments {n r : ℕ} (c d : Choice n r) :
    differingSlots c d = HostMoments.differingSlots c d := rfl

@[simp] theorem mem_differingSlots {n r : ℕ} {c d : Choice n r}
    {s : Fin (templateOrder r)} :
    s ∈ differingSlots c d ↔ c s ≠ d s := by
  simp [differingSlots]

/-! ## Event compatibility forces agreement on visible entries -/

/-- Matrices on two choices are compatible when some labelled host graph
realizes both stable-slot matrix events. -/
def Compatible {n r : ℕ} (c : Choice n r) (M : Matrix r)
    (d : Choice n r) (N : Matrix r) : Prop :=
  ∃ G : SimpleGraph (Fin n), SlotMatrixEvent c M G ∧ SlotMatrixEvent d N G

private theorem slotEmbedding_eq_of_choice_eq {n r : ℕ} {c d : Choice n r}
    {s : Fin (templateOrder r)} (hs : c s = d s) :
    slotEmbedding c s = slotEmbedding d s := by
  apply Fin.ext
  simp only [slotEmbedding_apply_val]
  rw [hs]

/-- Compatibility of the actual graph events implies the coordinatewise
matrix compatibility used by the reconstruction code. -/
theorem matrixCompatible_of_compatible {n r : ℕ} {c d : Choice n r}
    {M N : Matrix r} (h : Compatible c M d N) :
    HostMoments.MatrixCompatible c M d N := by
  rcases h with ⟨G, hc, hd⟩
  intro i a b hleft hright
  have hleft' : slotEmbedding c (leftVertex r i a) =
      slotEmbedding d (leftVertex r i a) :=
    slotEmbedding_eq_of_choice_eq hleft
  have hright' : slotEmbedding c (rightVertex r b) =
      slotEmbedding d (rightVertex r b) :=
    slotEmbedding_eq_of_choice_eq hright
  apply Bool.eq_iff_iff.mpr
  calc
    M i b = true ↔
        (graph M).Adj (leftVertex r i a) (rightVertex r b) :=
      (graph_adj_left_right_iff M i a b).symm
    _ ↔ (G.comap (slotEmbedding c)).Adj
        (leftVertex r i a) (rightVertex r b) := by rw [hc]
    _ ↔ G.Adj (slotEmbedding c (leftVertex r i a))
        (slotEmbedding c (rightVertex r b)) := Iff.rfl
    _ ↔ G.Adj (slotEmbedding d (leftVertex r i a))
        (slotEmbedding d (rightVertex r b)) := by rw [hleft', hright']
    _ ↔ (G.comap (slotEmbedding d)).Adj
        (leftVertex r i a) (rightVertex r b) := Iff.rfl
    _ ↔ (graph N).Adj (leftVertex r i a) (rightVertex r b) := by rw [hd]
    _ ↔ N i b = true := graph_adj_left_right_iff N i a b

/-! ## The free-slot injection -/

/-- The matrices on `d` which can coexist with a fixed matrix `M` on `c` in
one labelled graph. -/
noncomputable def compatibleMatrices {n r : ℕ}
    (c : Choice n r) (M : Matrix r) (d : Choice n r) : Finset (Matrix r) := by
  classical
  exact Finset.univ.filter fun N ↦ Compatible c M d N

/-- The concrete stable-slot code for a compatible extension.  The first
component records entries at missing right slots; the second component uses
the ten-way chunking of the right side at missing left slots. -/
noncomputable def extensionCode {n r j : ℕ} (c d : Choice n r)
    (hdiff : (differingSlots c d).card = j) (N : Matrix r) :
    Overlap.SlotFreeCode r j :=
  HostMoments.matrixExtensionCode c d
    (by simpa [differingSlots_eq_hostMoments] using hdiff) N

/-- Compatible matrices inject into the concrete `10 * r * j`-bit code. -/
theorem extensionCode_injOn {n r j : ℕ} (c d : Choice n r)
    (hdiff : (differingSlots c d).card = j) (M : Matrix r) :
    ((compatibleMatrices c M d : Finset (Matrix r)) : Set (Matrix r)).InjOn
      (extensionCode c d hdiff) := by
  classical
  let hdiff' : (HostMoments.differingSlots c d).card = j := by
    simpa [differingSlots_eq_hostMoments] using hdiff
  have hinj := HostMoments.matrixExtensionCode_injOn c d hdiff' M
    (compatibleMatrices c M d) (by
      intro N hN
      exact matrixCompatible_of_compatible (Finset.mem_filter.mp hN).2)
  exact hinj

/-- If exactly `j` stable slots differ, at most `2^(10*r*j)` matrices on the
second choice can coexist with a fixed matrix on the first choice. -/
theorem card_compatibleMatrices_le {n r j : ℕ} (c d : Choice n r)
    (hdiff : (differingSlots c d).card = j) (M : Matrix r) :
    (compatibleMatrices c M d).card ≤ 2 ^ (10 * r * j) := by
  exact Overlap.card_extensions_le_slotFree (compatibleMatrices c M d) r j
    (extensionCode c d hdiff) (extensionCode_injOn c d hdiff M)

end SlotCompatibility
end Erdos807
