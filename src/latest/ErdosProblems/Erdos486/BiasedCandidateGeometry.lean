import ErdosProblems.Erdos486.BiasedCollision
import ErdosProblems.Erdos486.ColoringEnumeration

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Candidate-oracle geometry for the biased block

Outside the arithmetic collision union, the anchor coordinates and all fresh
candidate queries form an injective oracle family.  This is the exact bridge
between the modular arithmetic and the generic finite-colouring enumeration.
-/

namespace Erdos486

/-- Anchor queried at prime `i` by a common-period representative `x`. -/
noncomputable def biasedAnchor (j x : ℕ) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  endpointCoordinate j x i

/-- Query made by the canonical candidate for subset `S`. -/
noncomputable def biasedQuery (j x : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  endpointCoordinate j
    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i

/-- `S` has an actual endpoint representative for the residue of `x`. -/
def HasBiasedCandidate (j x : ℕ)
    (S : Finset (Fin (biasedK j))) : Prop :=
  biasedCandidate j S (x : ZMod (biasedModulus j S)) ∈
    candidateEndpoints j S (x : ZMod (biasedModulus j S))

/-- No subset/index collision occurs at `x`. -/
def HasNoBiasedCollision (j x : ℕ) : Prop :=
  ∀ (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)),
    i ∉ S → ¬IsBiasedCollision j S i x

theorem biasedQuery_eq_anchor_of_mem {j x : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j))
    (hi : i ∈ S) (hvalid : HasBiasedCandidate j x S) :
    biasedQuery j x S i = biasedAnchor j x i := by
  apply Sigma.ext
  · rfl
  · simp only [biasedQuery, biasedAnchor, endpointCoordinate]
    have hq :
        (biasedCandidate j S (x : ZMod (biasedModulus j S)) :
            ZMod (biasedModulus j S)) =
          (x : ZMod (biasedModulus j S)) := by
      exact (Finset.mem_filter.mp hvalid).2
    have hpq : skeletonPrime (biasedK j) i ∣ biasedModulus j S :=
      (skeletonPrime_dvd_biasedModulus_iff j S i).2 hi
    have := congrArg (ZMod.castHom hpq
      (ZMod (skeletonPrime (biasedK j) i))) hq
    simpa [ZMod.castHom_apply] using this

/-- Outside collisions, the combined anchor/fresh-query oracle is injective. -/
theorem biasedCandidateOracle_injective {j x : ℕ}
    (hno : HasNoBiasedCollision j x)
    (S : Finset (Fin (biasedK j))) :
    Function.Injective
      (candidateOracle (biasedAnchor j x) (biasedQuery j x S) S) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl i' =>
          have hi : i = i' := congrArg Sigma.fst hab
          cases hi
          rfl
      | inr i' =>
          have hi : i = i'.1 := congrArg Sigma.fst hab
          subst i
          have hcollision : IsBiasedCollision j S i'.1 x := by
            unfold IsBiasedCollision
            have hab' :
                endpointCoordinate j x i'.1 =
                  endpointCoordinate j
                    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i'.1 := by
              simpa [candidateOracle, biasedAnchor, biasedQuery] using hab
            exact eq_of_heq (Sigma.mk.inj_iff.mp hab').2
          have hi' : i'.1 ∉ S := Finset.mem_compl.mp i'.property
          exact (hno S i'.1 hi' hcollision).elim
  | inr i =>
      cases b with
      | inl i' =>
          have hi : i.1 = i' := congrArg Sigma.fst hab
          subst i'
          have hcollision : IsBiasedCollision j S i.1 x := by
            unfold IsBiasedCollision
            have hab' :
                endpointCoordinate j x i.1 =
                  endpointCoordinate j
                    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i.1 := by
              simpa [candidateOracle, biasedAnchor, biasedQuery] using hab.symm
            exact eq_of_heq (Sigma.mk.inj_iff.mp hab').2
          have hi' : i.1 ∉ S := Finset.mem_compl.mp i.property
          exact (hno S i.1 hi' hcollision).elim
      | inr i' =>
          have hi : i.1 = i'.1 := congrArg Sigma.fst hab
          have hii' : i = i' := Subtype.ext hi
          subst i'
          rfl

/-- If a colouring selects exactly `S` at its canonical valid candidate,
then the generic candidate event occurs. -/
theorem candidateOccurs_of_selectedPrimes_eq {j x : ℕ}
    (S : Finset (Fin (biasedK j))) (c : BiasedColoring j)
    (hvalid : HasBiasedCandidate j x S)
    (hselected : selectedPrimes j c
      (biasedCandidate j S (x : ZMod (biasedModulus j S))) = S) :
    CandidateOccurs (biasedAnchor j x) (biasedQuery j x S) S c := by
  constructor
  · intro i hi
    have hmem : i ∈ selectedPrimes j c
        (biasedCandidate j S (x : ZMod (biasedModulus j S))) := by
      rw [hselected]
      exact hi
    have hquery : c (biasedQuery j x S i) = 0 := by
      simpa [biasedQuery] using
        (mem_selectedPrimes_iff j c
          (biasedCandidate j S (x : ZMod (biasedModulus j S))) i).1 hmem
    rw [biasedQuery_eq_anchor_of_mem S i hi hvalid] at hquery
    exact hquery
  · intro i hi hblack
    have hmem : i ∈ selectedPrimes j c
        (biasedCandidate j S (x : ZMod (biasedModulus j S))) := by
      rw [mem_selectedPrimes_iff]
      exact hblack
    rw [hselected] at hmem
    exact hi hmem

/-- Footprint membership supplies a valid canonical subset candidate. -/
theorem exists_candidate_of_isBiasedCovered {j : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (x : ZMod (biasedPeriod j))
    (hcovered : IsBiasedCovered j c x) :
    ∃ S : Finset (Fin (biasedK j)),
      HasBiasedCandidate j x.val S ∧
        selectedPrimes j c
          (biasedCandidate j S (x.val : ZMod (biasedModulus j S))) = S := by
  rcases hcovered with ⟨m, hm, hx⟩
  let S := selectedPrimes j c m
  letI : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  have hx' :
      (x.val : ZMod (biasedModulus j S)) =
        (m : ZMod (biasedModulus j S)) := by
    calc
      (x.val : ZMod (biasedModulus j S)) =
          reduceBiasedPeriod j S x := by
            simp [reduceBiasedPeriod, ZMod.castHom_apply]
      _ = (m : ZMod (biasedModulus j S)) := by simpa [S] using hx
  have hmCandidate : m ∈
      candidateEndpoints j S (x.val : ZMod (biasedModulus j S)) := by
    rw [candidateEndpoints, Finset.mem_filter]
    exact ⟨hm, hx'.symm⟩
  have hcandidate :
      biasedCandidate j S (x.val : ZMod (biasedModulus j S)) = m :=
    biasedCandidate_eq_of_mem hj S _ hmCandidate
  refine ⟨S, ?_, ?_⟩
  · change biasedCandidate j S (x.val : ZMod (biasedModulus j S)) ∈
        candidateEndpoints j S (x.val : ZMod (biasedModulus j S))
    rw [hcandidate]
    exact hmCandidate
  · exact hcandidate ▸ rfl

end Erdos486
