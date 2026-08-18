import Mathlib

/-!
# Finite-displacement Hall matching

This file packages the purely combinatorial end of a translation-equidecomposition
argument.  Given two sets in an additive group, a finite set of allowed left
translation displacements, and Hall inequalities in both directions, it constructs
a bijection between the sets which uses only those displacements.  The final theorem
records the bijection as Mathlib's `Equidecomp` structure for the canonical action of
`Multiplicative X` on `X` by translations.
-/

open Function Set

namespace Erdos1124

section AddGroup

variable {X : Type*} [AddGroup X]

/-- The allowed points of `B` obtainable from `a` by a displacement in `D`.

The convention is left translation: `d` sends `a` to `d + a`, equivalently
the left displacement of the target from the source is `(d + a) - a = d`.
-/
noncomputable def forwardNeighbors (B : Set X) (D : Finset X) (a : X) : Finset B := by
  classical
  exact (D.image fun d => d + a).subtype (· ∈ B)

/-- The allowed points of `A` which can be sent to `b` by a displacement in `D`. -/
noncomputable def backwardNeighbors (A : Set X) (D : Finset X) (b : X) : Finset A := by
  classical
  exact (D.image fun d => -d + b).subtype (· ∈ A)

@[simp]
theorem mem_forwardNeighbors {B : Set X} {D : Finset X} {a : X} (b : B) :
    b ∈ forwardNeighbors B D a ↔ (b : X) - a ∈ D := by
  classical
  simp [forwardNeighbors, sub_eq_add_neg]

@[simp]
theorem mem_backwardNeighbors {A : Set X} {D : Finset X} {b : X} (a : A) :
    a ∈ backwardNeighbors A D b ↔ b - (a : X) ∈ D := by
  classical
  simp only [backwardNeighbors, Finset.mem_subtype, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, hda⟩
    have hba : b - (a : X) = d := by
      rw [← hda]
      simp
    rwa [hba]
  · intro h
    exact ⟨b - (a : X), h, by simp⟩

/-- Exact finite Hall conditions for the translation relation determined by `D`.

Both inequalities are needed: the first produces an adjacency-preserving injection
from `A` to `B`, and the second one produces such an injection from `B` to `A`.
Relation-preserving Schröder--Bernstein then gives an adjacency-preserving bijection.
-/
def FiniteDisplacementHall (A B : Set X) (D : Finset X) : Prop := by
  classical
  exact
    (∀ s : Finset A,
        s.card ≤ (s.biUnion fun a => forwardNeighbors B D (a : X)).card) ∧
      ∀ t : Finset B,
        t.card ≤ (t.biUnion fun b => backwardNeighbors A D (b : X)).card

/-- Two finite Hall systems for the same translation relation yield a subtype
bijection whose displacement always belongs to the prescribed finite set. -/
theorem exists_bijective_displacement_of_hall {A B : Set X} {D : Finset X}
    (hHall : FiniteDisplacementHall A B D) :
    ∃ f : A → B, Bijective f ∧ ∀ a : A, ((f a : B) : X) - (a : X) ∈ D := by
  classical
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun a : A => forwardNeighbors B D (a : X))).mp hHall.1
  obtain ⟨g, hg_inj, hg_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun b : B => backwardNeighbors A D (b : X))).mp hHall.2
  exact Embedding.schroeder_bernstein_of_rel hf_inj hg_inj
    (fun a b => ((b : B) : X) - (a : X) ∈ D)
    (fun a => mem_forwardNeighbors (f a) |>.mp (hf_mem a))
    (fun b => mem_backwardNeighbors (g b) |>.mp (hg_mem b))

/-- The subtype equivalence form of `exists_bijective_displacement_of_hall`. -/
theorem exists_equiv_displacement_of_hall {A B : Set X} {D : Finset X}
    (hHall : FiniteDisplacementHall A B D) :
    ∃ e : A ≃ B, ∀ a : A, ((e a : B) : X) - (a : X) ∈ D := by
  obtain ⟨f, hf, hD⟩ := exists_bijective_displacement_of_hall hHall
  exact ⟨Equiv.ofBijective f hf, hD⟩

/-- Extend a subtype equivalence to an ambient function, using the identity away
from its source. -/
noncomputable def ambientEquivFun {A B : Set X} (e : A ≃ B) (x : X) : X := by
  classical
  exact if hx : x ∈ A then (e ⟨x, hx⟩ : B) else x

@[simp]
theorem ambientEquivFun_apply_mem {A B : Set X} (e : A ≃ B) {x : X} (hx : x ∈ A) :
    ambientEquivFun e x = e ⟨x, hx⟩ := by
  simp [ambientEquivFun, hx]

/-- An ambient `BijOn` with the prescribed finite displacement set. -/
theorem exists_bijOn_displacement_of_hall {A B : Set X} {D : Finset X}
    (hHall : FiniteDisplacementHall A B D) :
    ∃ f : X → X, BijOn f A B ∧ ∀ x ∈ A, f x - x ∈ D := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_displacement_of_hall hHall
  refine ⟨ambientEquivFun e, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simpa [ambientEquivFun, hx] using (e ⟨x, hx⟩).property
    · intro x hx y hy hxy
      have hv : ((e ⟨x, hx⟩ : B) : X) = ((e ⟨y, hy⟩ : B) : X) := by
        simpa only [ambientEquivFun_apply_mem e hx,
          ambientEquivFun_apply_mem e hy] using hxy
      exact congrArg Subtype.val (e.injective (Subtype.ext hv))
    · intro y hy
      let x : A := e.symm ⟨y, hy⟩
      refine ⟨(x : X), x.property, ?_⟩
      rw [ambientEquivFun_apply_mem e x.property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  · intro x hx
    simpa [ambientEquivFun, hx] using he ⟨x, hx⟩

/-- The finite set of elements of `Multiplicative X` corresponding to the
additive displacement set `D`. -/
def multiplicativeDisplacements (D : Finset X) : Finset (Multiplicative X) :=
  D.map Multiplicative.ofAdd.toEmbedding

@[simp]
theorem mem_multiplicativeDisplacements {D : Finset X} {d : X} :
    Multiplicative.ofAdd d ∈ multiplicativeDisplacements D ↔ d ∈ D := by
  simp [multiplicativeDisplacements]

/-- Exact translation equidecomposition obtained from the two finite Hall
inequalities.  Besides fixing the source and target exactly, the conclusion keeps
the original displacement finset as an explicit decomposition witness. -/
theorem exists_equidecomp_of_hall {A B : Set X} {D : Finset X}
    (hHall : FiniteDisplacementHall A B D) :
    ∃ e : Equidecomp X (Multiplicative X),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  classical
  obtain ⟨f, hf, hD⟩ := exists_bijOn_displacement_of_hall hHall
  let pe : PartialEquiv X X := hf.toPartialEquiv f A B
  have hdecomp : Equidecomp.IsDecompOn f A (multiplicativeDisplacements D) := by
    intro x hx
    refine ⟨Multiplicative.ofAdd (f x - x), ?_, ?_⟩
    · exact mem_multiplicativeDisplacements.mpr (hD x hx)
    · change f x = (f x - x) + x
      simp
  let e : Equidecomp X (Multiplicative X) :=
    { toPartialEquiv := pe
      isDecompOn' := ⟨multiplicativeDisplacements D, hdecomp⟩ }
  exact ⟨e, rfl, rfl, hdecomp⟩

end AddGroup

end Erdos1124
