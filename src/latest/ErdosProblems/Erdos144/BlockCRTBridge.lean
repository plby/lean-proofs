/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos144.BlockCRTClose
import ErdosProblems.Erdos144.Harmonic
import ErdosProblems.Erdos144.OccupancyTransfer

open scoped BigOperators

namespace Erdos144.BlockCRTBridge

noncomputable section

def valueEmbedding (S : Finset ℕ) : ↥S ↪ ℕ where
  toFun := Subtype.val
  inj' := Subtype.val_injective

def liftToSubtype (S A : Finset ℕ) : Finset ↥S :=
  S.attach.filter fun x ↦ x.1 ∈ A

@[simp] theorem mem_liftToSubtype {S A : Finset ℕ} (x : ↥S) :
    x ∈ liftToSubtype S A ↔ x.1 ∈ A := by
  simp [liftToSubtype]

theorem map_liftToSubtype {S A : Finset ℕ} (hAS : A ⊆ S) :
    (liftToSubtype S A).map (valueEmbedding S) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_liftToSubtype y).mp hy
  · intro hx
    let y : ↥S := ⟨x, hAS hx⟩
    exact Finset.mem_map.mpr ⟨y, (mem_liftToSubtype y).mpr hx, rfl⟩

theorem sum_liftToSubtype {S A : Finset ℕ} (hAS : A ⊆ S) :
    (∑ x ∈ liftToSubtype S A, (x : ℕ)) = ∑ x ∈ A, x := by
  calc
    (∑ x ∈ liftToSubtype S A, (x : ℕ)) =
        ∑ x ∈ (liftToSubtype S A).map (valueEmbedding S), x := by
      rw [Finset.sum_map]
      simp [valueEmbedding]
    _ = ∑ x ∈ A, x := by rw [map_liftToSubtype hAS]

theorem nonempty_liftToSubtype {S A : Finset ℕ} (hAS : A ⊆ S)
    (hA : A.Nonempty) :
    (liftToSubtype S A).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  let y : ↥S := ⟨x, hAS hx⟩
  exact ⟨y, (mem_liftToSubtype y).mpr hx⟩

theorem blockGood_subtype_iff
    {I : Finset ℕ} (T : Finset ↥I) (L : ℕ) :
    BlockCRTClose.BlockGood Subtype.val L T ↔
      Harmonic.HasEqualSubsums (T.image Subtype.val) ∧ T.card ≤ L := by
  unfold BlockCRTClose.BlockGood BlockCRTClose.occupiedLabels
  let e : ↥(T.image Subtype.val) ↪ ℕ :=
    valueEmbedding (T.image Subtype.val)
  have hcardS : (T.image Subtype.val).card = T.card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact Subtype.val_injective hab
  constructor
  · rintro ⟨hcard, A, B, hdisj, hA, hB, hsum⟩
    have hneA : (A.map e).Nonempty := Finset.Nonempty.map hA
    have hneB : (B.map e).Nonempty := Finset.Nonempty.map hB
    have hsubA : A.map e ⊆ T.image Subtype.val := by
      intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hx
      exact a.2
    have hsubB : B.map e ⊆ T.image Subtype.val := by
      intro x hx
      obtain ⟨b, _hb, rfl⟩ := Finset.mem_map.mp hx
      exact b.2
    have hdisjMap : Disjoint (A.map e) (B.map e) := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hxA
      obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hxB
      have hab : a = b := e.injective (hax.trans hbx.symm)
      exact (Finset.disjoint_left.mp hdisj) ha (hab ▸ hb)
    have hsumMap :
        (∑ x ∈ A.map e, x) = ∑ x ∈ B.map e, x := by
      calc
        (∑ x ∈ A.map e, x) = ∑ a ∈ A, (a : ℕ) := by
          rw [Finset.sum_map]
          simp [e, valueEmbedding]
        _ = ∑ b ∈ B, (b : ℕ) := hsum
        _ = ∑ x ∈ B.map e, x := by
          rw [Finset.sum_map]
          simp [e, valueEmbedding]
    refine ⟨⟨A.map e, B.map e, hsubA, hsubB, hdisjMap,
      hneA, hneB, hsumMap⟩, ?_⟩
    simpa [hcardS] using hcard
  · rintro ⟨⟨A, B, hAS, hBS, hdisj, hA, hB, hsum⟩, hcard⟩
    let A' : Finset ↥(T.image Subtype.val) :=
      liftToSubtype (T.image Subtype.val) A
    let B' : Finset ↥(T.image Subtype.val) :=
      liftToSubtype (T.image Subtype.val) B
    have hdisj' : Disjoint A' B' := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.disjoint_left.mp hdisj)
        ((mem_liftToSubtype x).mp hxA) ((mem_liftToSubtype x).mp hxB)
    have hsum' :
        (∑ x ∈ A', (x : ℕ)) = ∑ x ∈ B', (x : ℕ) := by
      rw [show A' = liftToSubtype (T.image Subtype.val) A from rfl,
        show B' = liftToSubtype (T.image Subtype.val) B from rfl,
        sum_liftToSubtype hAS, sum_liftToSubtype hBS]
      exact hsum
    refine ⟨?_, A', B', hdisj', ?_, ?_, hsum'⟩
    · simpa [hcardS] using hcard
    · exact nonempty_liftToSubtype hAS hA
    · exact nonempty_liftToSubtype hBS hB

variable {I : Finset ℕ}
variable (κ : ↥I → Type*) [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

theorem occupiedLabels_sigma_value_eq
    (Z : Finset (Sigma κ)) :
    BlockCRTClose.occupiedLabels
        (fun z : Sigma κ ↦ z.1.val) Z =
      (OccupancyTransfer.occupiedLabels κ Z).image Subtype.val := by
  ext j
  constructor
  · intro hj
    obtain ⟨z, hz, hlabel⟩ :=
      (BlockCRTClose.mem_occupiedLabels_iff _ _ _).mp hj
    obtain ⟨i, x⟩ := z
    exact Finset.mem_image.mpr ⟨i,
      (OccupancyTransfer.mem_occupiedLabels κ Z i).mpr ⟨x, hz⟩,
      hlabel⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨x, hx⟩ := (OccupancyTransfer.mem_occupiedLabels κ Z i).mp hi
    exact (BlockCRTClose.mem_occupiedLabels_iff _ _ _).mpr
      ⟨⟨i, x⟩, hx, rfl⟩

end

end Erdos144.BlockCRTBridge
