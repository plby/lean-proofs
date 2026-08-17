import ErdosProblems.Erdos842.TriangleToggle

/-!
# Unoriented chord keys of canonical survivors

A nonempty proper restriction of a cyclically directed triangle has boundary values `+1`, `-1`,
and `0`.  The unique zero-boundary vertex is the side/chord key; complementing the restriction
reverses its orientation while preserving this key.  This file records the exact two-element
fiber over every key and lifts the construction to canonical survivor selections.
-/

namespace Erdos842.SurvivorChords

open Erdos842.Coefficient
open Erdos842.TriangleToggle

/-! ## One directed triangle -/

/-- The unoriented chord represented by a triangle restriction: the unique zero-boundary vertex
for a nondegenerate restriction. -/
def unorientedChordKey (S : Finset (Fin 3)) : Fin 3 :=
  triangleChordIndex S

/-- The positive boundary endpoint, with a harmless default on degenerate restrictions. -/
def positiveBoundaryEndpoint (S : Finset (Fin 3)) : Fin 3 :=
  if triangleBoundary S 0 = 1 then 0
  else if triangleBoundary S 1 = 1 then 1 else 2

/-- A canonical representative of the two orientations of the chord opposite `k`. -/
def baseRestriction (k : Fin 3) : Finset (Fin 3) :=
  {triSucc k}

/-- An orientation bit relative to `baseRestriction`: whether its distinguished side is selected. -/
def orientationBit (S : Finset (Fin 3)) : Bool :=
  decide (triSucc (unorientedChordKey S) ∈ S)

theorem zero_boundary_existsUnique
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    ∃! k, triangleBoundary S k = 0 := by
  refine ⟨unorientedChordKey S, triangleBoundary_chordIndex_eq_zero S hne hfull, ?_⟩
  intro k hk
  obtain ⟨p, q, hpq, hp, hq, hrest⟩ := triangleBoundary_nondegenerate S hne hfull
  have hkey := triangleBoundary_chordIndex_eq_zero S hne hfull
  have huniq : ∀ a b : Fin 3,
      triangleBoundary S a = 0 → triangleBoundary S b = 0 → a = b := by
    intro a b ha hb
    fin_cases p <;> fin_cases q <;> fin_cases a <;> fin_cases b <;> simp_all
  exact huniq k (unorientedChordKey S) hk hkey

theorem zero_boundary_iff_key
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) (k : Fin 3) :
    triangleBoundary S k = 0 ↔ k = unorientedChordKey S := by
  constructor
  · intro hk
    exact (zero_boundary_existsUnique S hne hfull).unique hk
      (triangleBoundary_chordIndex_eq_zero S hne hfull)
  · rintro rfl
    exact triangleBoundary_chordIndex_eq_zero S hne hfull

theorem positive_boundary_existsUnique
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    ∃! p, triangleBoundary S p = 1 := by
  obtain ⟨p, q, hpq, hp, hq, hrest⟩ := triangleBoundary_nondegenerate S hne hfull
  refine ⟨p, hp, ?_⟩
  intro r hr
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

theorem positiveBoundaryEndpoint_spec
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    triangleBoundary S (positiveBoundaryEndpoint S) = 1 := by
  obtain ⟨p, hp, hpu⟩ := positive_boundary_existsUnique S hne hfull
  unfold positiveBoundaryEndpoint
  fin_cases p <;> simp_all

theorem positive_boundary_iff_endpoint
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) (p : Fin 3) :
    triangleBoundary S p = 1 ↔ p = positiveBoundaryEndpoint S := by
  constructor
  · intro hp
    exact (positive_boundary_existsUnique S hne hfull).unique hp
      (positiveBoundaryEndpoint_spec S hne hfull)
  · rintro rfl
    exact positiveBoundaryEndpoint_spec S hne hfull

/-- Complementation reverses orientation but preserves the unoriented chord. -/
@[simp] theorem unorientedChordKey_compl (S : Finset (Fin 3)) :
    unorientedChordKey (Finset.univ \ S) = unorientedChordKey S :=
  triangleChordIndex_compl S

@[simp] theorem baseRestriction_ne_empty (k : Fin 3) : baseRestriction k ≠ ∅ := by
  simp [baseRestriction]

@[simp] theorem baseRestriction_ne_univ (k : Fin 3) :
    baseRestriction k ≠ (Finset.univ : Finset (Fin 3)) := by
  intro h
  have hc := congrArg Finset.card h
  simp [baseRestriction] at hc

@[simp] theorem unorientedChordKey_baseRestriction (k : Fin 3) :
    unorientedChordKey (baseRestriction k) = k := by
  fin_cases k <;> decide

lemma fin3_eq_self_or_succ_or_pred (k j : Fin 3) :
    j = k ∨ j = triSucc k ∨ j = triPred k := by
  fin_cases k <;> fin_cases j <;> simp

lemma triangleBoundary_eq_zero_iff_mem (S : Finset (Fin 3)) (k : Fin 3) :
    triangleBoundary S k = 0 ↔ (triPred k ∈ S ↔ k ∈ S) := by
  by_cases hp : triPred k ∈ S <;> by_cases hk : k ∈ S <;>
    simp [triangleBoundary, hp, hk]

theorem restriction_eq_base_or_compl
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    S = baseRestriction (unorientedChordKey S) ∨
      S = Finset.univ \ baseRestriction (unorientedChordKey S) := by
  decide +revert

theorem restriction_classification_at_key
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ)
    (k : Fin 3) (hkey : unorientedChordKey S = k) :
    S = baseRestriction k ∨ S = Finset.univ \ baseRestriction k := by
  simpa only [hkey] using restriction_eq_base_or_compl S hne hfull

/-- The positive endpoint together with the unoriented key determines the restriction. -/
theorem restriction_eq_of_key_eq_of_positive_eq
    {S T : Finset (Fin 3)}
    (hSne : S ≠ ∅) (hSfull : S ≠ Finset.univ)
    (hTne : T ≠ ∅) (hTfull : T ≠ Finset.univ)
    (hkey : unorientedChordKey S = unorientedChordKey T)
    (hpos : positiveBoundaryEndpoint S = positiveBoundaryEndpoint T) :
    S = T := by
  decide +revert

/-- Equivalently, the orientation bit together with the unoriented key determines the restriction. -/
theorem restriction_eq_of_key_eq_of_orientationBit_eq
    {S T : Finset (Fin 3)}
    (hSne : S ≠ ∅) (hSfull : S ≠ Finset.univ)
    (hTne : T ≠ ∅) (hTfull : T ≠ Finset.univ)
    (hkey : unorientedChordKey S = unorientedChordKey T)
    (hbit : orientationBit S = orientationBit T) :
    S = T := by
  decide +revert

/-- The finite fiber of nondegenerate triangle restrictions over one unoriented chord. -/
noncomputable def restrictionsForChord (k : Fin 3) : Finset (Finset (Fin 3)) :=
  Finset.univ.filter fun S ↦
    S ≠ ∅ ∧ S ≠ Finset.univ ∧ unorientedChordKey S = k

@[simp] theorem mem_restrictionsForChord (S : Finset (Fin 3)) (k : Fin 3) :
    S ∈ restrictionsForChord k ↔
      S ≠ ∅ ∧ S ≠ Finset.univ ∧ unorientedChordKey S = k := by
  classical
  simp [restrictionsForChord]

theorem restrictionsForChord_eq_pair (k : Fin 3) :
    restrictionsForChord k =
      {baseRestriction k, Finset.univ \ baseRestriction k} := by
  classical
  ext S
  simp only [mem_restrictionsForChord, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, hfull, hkey⟩
    exact restriction_classification_at_key S hne hfull k hkey
  · rintro (rfl | rfl)
    · exact ⟨baseRestriction_ne_empty k, baseRestriction_ne_univ k,
        unorientedChordKey_baseRestriction k⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro h
        have : baseRestriction k = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro j
          by_contra hj
          have hm : j ∈ Finset.univ \ baseRestriction k := by simp [hj]
          rw [h] at hm
          simp at hm
        exact baseRestriction_ne_univ k this
      · intro h
        have hm : triSucc k ∈ Finset.univ \ baseRestriction k := by
          rw [h]
          simp
        simp [baseRestriction] at hm
      · rw [unorientedChordKey_compl, unorientedChordKey_baseRestriction]

/-- There are exactly two orientations of every unoriented triangle chord. -/
@[simp] theorem card_restrictionsForChord (k : Fin 3) :
    (restrictionsForChord k).card = 2 := by
  rw [restrictionsForChord_eq_pair]
  have hne : baseRestriction k ≠ Finset.univ \ baseRestriction k := by
    intro h
    have hm := congrArg (fun S : Finset (Fin 3) ↦ triSucc k ∈ S) h
    simp [baseRestriction] at hm
  simp [hne]

/-! ## Canonical survivors -/

/-- Pointwise unoriented chord key of a canonical selection. -/
def survivorUnorientedChordKey {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Fin n → Fin 3 := fun t ↦
  unorientedChordKey (triangleRestriction triangleCoord S t)

theorem survivorUnorientedChordKey_eq_canonicalChordKey {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    survivorUnorientedChordKey triangleCoord S =
      canonicalChordKey n triangleCoord S := rfl

/-- At each triangle, a survivor chooses one of the two complementary orientations of its
unoriented chord. -/
theorem survivorRestriction_classification {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : IsSurvivor triangleCoord S) (t : Fin n) :
    triangleRestriction triangleCoord S t =
        baseRestriction (survivorUnorientedChordKey triangleCoord S t) ∨
      triangleRestriction triangleCoord S t = Finset.univ \
        baseRestriction (survivorUnorientedChordKey triangleCoord S t) := by
  apply restriction_eq_base_or_compl
  · intro h
    exact hS t (Or.inl h)
  · intro h
    exact hS t (Or.inr h)

/-- Pointwise, a survivor's unoriented key and positive endpoint determine all of its triangle
restrictions. -/
theorem survivorRestrictions_eq_of_key_eq_of_positive_eq {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S T : Finset (CanonicalOccurrence n)}
    (hS : IsSurvivor triangleCoord S) (hT : IsSurvivor triangleCoord T)
    (hkey : survivorUnorientedChordKey triangleCoord S =
      survivorUnorientedChordKey triangleCoord T)
    (hpos : ∀ t, positiveBoundaryEndpoint (triangleRestriction triangleCoord S t) =
      positiveBoundaryEndpoint (triangleRestriction triangleCoord T t)) :
    ∀ t, triangleRestriction triangleCoord S t = triangleRestriction triangleCoord T t := by
  intro t
  apply restriction_eq_of_key_eq_of_positive_eq
  · intro h
    exact hS t (Or.inl h)
  · intro h
    exact hS t (Or.inr h)
  · intro h
    exact hT t (Or.inl h)
  · intro h
    exact hT t (Or.inr h)
  · exact congrFun hkey t
  · exact hpos t

/-- Pointwise, the Boolean orientation and the unoriented key also determine every triangle
restriction of a survivor. -/
theorem survivorRestrictions_eq_of_key_eq_of_orientationBit_eq {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S T : Finset (CanonicalOccurrence n)}
    (hS : IsSurvivor triangleCoord S) (hT : IsSurvivor triangleCoord T)
    (hkey : survivorUnorientedChordKey triangleCoord S =
      survivorUnorientedChordKey triangleCoord T)
    (hbit : ∀ t, orientationBit (triangleRestriction triangleCoord S t) =
      orientationBit (triangleRestriction triangleCoord T t)) :
    ∀ t, triangleRestriction triangleCoord S t = triangleRestriction triangleCoord T t := by
  intro t
  apply restriction_eq_of_key_eq_of_orientationBit_eq
  · intro h
    exact hS t (Or.inl h)
  · intro h
    exact hS t (Or.inr h)
  · intro h
    exact hT t (Or.inl h)
  · intro h
    exact hT t (Or.inr h)
  · exact congrFun hkey t
  · exact hbit t

theorem survivorUnorientedChordKey_spec {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : IsSurvivor triangleCoord S) (t : Fin n) :
    triangleBoundary (triangleRestriction triangleCoord S t)
      (survivorUnorientedChordKey triangleCoord S t) = 0 := by
  apply triangleBoundary_chordIndex_eq_zero
  · intro h
    exact hS t (Or.inl h)
  · intro h
    exact hS t (Or.inr h)

theorem survivorUnorientedChordKey_unique {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : IsSurvivor triangleCoord S) (t : Fin n) (k : Fin 3) :
    triangleBoundary (triangleRestriction triangleCoord S t) k = 0 ↔
      k = survivorUnorientedChordKey triangleCoord S t := by
  apply zero_boundary_iff_key
  · intro h
    exact hS t (Or.inl h)
  · intro h
    exact hS t (Or.inr h)

/-- Global complementation preserves every pointwise unoriented chord key. -/
@[simp] theorem survivorUnorientedChordKey_compl {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    survivorUnorientedChordKey triangleCoord (Finset.univ \ S) =
      survivorUnorientedChordKey triangleCoord S := by
  rw [survivorUnorientedChordKey_eq_canonicalChordKey,
    survivorUnorientedChordKey_eq_canonicalChordKey]
  exact canonicalChordKey_compl n triangleCoord S

end Erdos842.SurvivorChords
