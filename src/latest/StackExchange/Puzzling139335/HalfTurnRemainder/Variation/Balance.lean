import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.Defs
import StackExchange.Puzzling139335.InterfacePairing.Involution

/-!
# Interface variation balance from the actual mate involution

Every occurrence on pieces `2`, `3`, or the exterior has a different matching
occurrence on piece `0` or `1`, provided its partner label is one of those two
pieces.  Matching preserves the carrier and therefore its intrinsic variation.
Any remaining occurrences on pieces `0` and `1` have nonnegative variation.
-/

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

/-- An injective matching that preserves weights cannot increase the total
weight when all additional target weights are nonnegative. -/
theorem sum_le_sum_of_injective_matching {α β : Type*}
    (s : Finset α) (t : Finset β) (u : α → ℝ) (v : β → ℝ) (m : α → β)
    (hinj : Function.Injective m) (hmap : ∀ a ∈ s, m a ∈ t)
    (hweight : ∀ a ∈ s, v (m a) = u a) (hnonneg : ∀ b ∈ t, 0 ≤ v b) :
    ∑ a ∈ s, u a ≤ ∑ b ∈ t, v b := by
  classical
  calc
    ∑ a ∈ s, u a = ∑ a ∈ s, v (m a) :=
      Finset.sum_congr rfl fun a ha => (hweight a ha).symm
    _ = ∑ b ∈ s.image m, v b :=
      (Finset.sum_image fun a _ b _ hab => hinj hab).symm
    _ ≤ ∑ b ∈ t, v b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact hmap a ha
      · intro b hb _
        exact hnonneg b hb

/-- Concrete balance for the intrinsic variations of the actual exact
interface family.  The only matching hypothesis concerns its partner labels;
injectivity and equality of arc weights follow from the proved mate involution.
-/
theorem boundaryArcSum_balance_of_partner_restriction
    {d : SquareDissection} (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε)
    (hpartner : ∀ (i : ExtendedPieceIndex), i ≠ Sum.inl 0 → i ≠ Sum.inl 1 →
      ∀ k : Fin (F.n i), F.partner i k = Sum.inl 0 ∨ F.partner i k = Sum.inl 1) :
    boundaryArcSum F ε (Sum.inl 2) + boundaryArcSum F ε (Sum.inl 3) +
        boundaryArcSum F ε (Sum.inr ()) ≤
      boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) := by
  classical
  let s : Finset F.Occurrence :=
    Finset.univ.filter fun a => a.1 ≠ Sum.inl 0 ∧ a.1 ≠ Sum.inl 1
  let t : Finset F.Occurrence :=
    Finset.univ.filter fun a => a.1 = Sum.inl 0 ∨ a.1 = Sum.inl 1
  let w : F.Occurrence → ℝ := fun a => LoopVariation.arcVariation ε (F.carrier a)
  have hmap : ∀ a ∈ s, F.mate a ∈ t := by
    intro a ha
    obtain ⟨ha0, ha1⟩ := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hpartner a.1 ha0 ha1 a.2⟩
  have hweight : ∀ a ∈ s, w (F.mate a) = w a := by
    intro a _
    dsimp only [w]
    rw [F.carrier_mate]
  have hnonneg : ∀ a ∈ t, 0 ≤ w a := by
    intro a _
    exact LoopVariation.arcVariation_nonneg (F.arc_between a.1 a.2).isArc hε
  have hsum := sum_le_sum_of_injective_matching s t w w F.mate
    F.mate_involutive.injective hmap hweight hnonneg
  simpa [s, t, w, Finset.sum_filter, Fintype.sum_sigma,
    Fintype.sum_sum_type, Fin.sum_univ_succ, ExactBoundaryArcFamily.carrier,
    boundaryArcSum, add_assoc] using hsum

end

end Puzzling139335.HalfTurnRemainder
