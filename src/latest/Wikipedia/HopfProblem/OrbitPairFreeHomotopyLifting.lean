import Wikipedia.HopfProblem.OrbitPairCharacterTransport

/-!
# Compact homotopy lifting for the actual free circle quotient

The compact image is contained in a finite-character neighborhood.
The constructed phase-alignment transport lifts the homotopy there,
and inclusion returns a lift in the original free locus. Initial data
and every stationary parameter are preserved exactly.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Actual compact homotopy lifting, including all stationary boundary parameters. -/
theorem freeOrbitProjection_exists_homotopy_lift
    (H : C(I × X, freeOrbitLocus)) (a₀ : C(X, freeLocus))
    (ha₀ : ∀ x, freeOrbitProjection (a₀ x) = H (0, x)) :
    ∃ G : C(I × X, freeLocus), (∀ x, G (0, x) = a₀ x) ∧
      (∀ t x, freeOrbitProjection (G (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = a₀ x := by
  obtain ⟨s, hs⟩ := compact_free_quotient_in_finiteCharacterOrbitImage (range H)
    (isCompact_range H.continuous)
  let H' : C(I × X, finiteCharacterOrbitImage s) :=
    ⟨fun z => ⟨(H z).val, hs (H z) (mem_range_self z)⟩,
      (continuous_subtype_val.comp H.continuous).subtype_mk _⟩
  have ha (x : X) : (a₀ x).val ∈ finiteCharacterDomain s := by
    apply (Set.ext_iff.mp (quotientMap_preimage_finiteCharacterOrbitImage s) (a₀ x).val).mp
    change (freeOrbitProjection (a₀ x)).val ∈ finiteCharacterOrbitImage s
    rw [ha₀ x]
    exact hs (H (0, x)) (mem_range_self (0, x))
  let a' : C(X, finiteCharacterDomain s) :=
    ⟨fun x => ⟨(a₀ x).val, ha x⟩, (continuous_subtype_val.comp a₀.continuous).subtype_mk _⟩
  have ha' (x : X) : finiteCharacterProjection s (a' x) = H' (0, x) := by
    apply Subtype.ext
    exact congrArg (fun y : freeOrbitLocus => y.val) (ha₀ x)
  obtain ⟨G', hG₀, hGp, hGfix⟩ :=
    (finiteCharacterLocalTransport s).exists_lift_stationary H' a' ha'
  let G : C(I × X, freeLocus) :=
    ⟨fun z => ⟨(G' z).val, finiteCharacterDomain_subset_freeLocus s (G' z).property⟩,
      (continuous_subtype_val.comp G'.continuous).subtype_mk _⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg (fun y : finiteCharacterDomain s => y.val) (hG₀ x)
  · intro t x
    apply Subtype.ext
    exact congrArg (fun y : finiteCharacterOrbitImage s => y.val) (hGp t x)
  · intro x hx t
    have hx' (u : I) : H' (u, x) = H' (0, x) := by
      apply Subtype.ext
      exact congrArg (fun y : freeOrbitLocus => y.val) (hx u)
    apply Subtype.ext
    exact congrArg (fun y : finiteCharacterDomain s => y.val) (hGfix x hx' t)

end Wikipedia.HopfProblem.OrbitPair
