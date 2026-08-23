/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterPhase
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Integral lattices inside rational frequency spaces

For a rational subspace `V ≤ ℚ^D`, its integral points form a free
`ℤ`-module.  We choose a finite integral basis.  Killing the characters of
that basis kills every integral character lying in `V`, with no coefficient
loss; this is the saturation step needed in Hunter's center lemma.
-/

namespace Erdos721.HunterLattice

open Function Set

open HunterTorus HunterPhase

/-- Coordinatewise cast of an integral frequency to a rational vector. -/
def castIntVector {D : ℕ} (ξ : Fin D → ℤ) : Fin D → ℚ :=
  fun i ↦ (ξ i : ℚ)

@[simp] lemma castIntVector_apply {D : ℕ} (ξ : Fin D → ℤ) (i : Fin D) :
    castIntVector ξ i = (ξ i : ℚ) := rfl

/-- The saturated lattice of integral points in a rational subspace. -/
def rationalLattice {D : ℕ} (V : Submodule ℚ (Fin D → ℚ)) :
    Submodule ℤ (Fin D → ℤ) where
  carrier := {ξ | castIntVector ξ ∈ V}
  zero_mem' := by
    change castIntVector (0 : Fin D → ℤ) ∈ V
    convert V.zero_mem
    ext i
    simp [castIntVector]
  add_mem' {x y} hx hy := by
    have hxy := V.add_mem hx hy
    change castIntVector (x + y) ∈ V
    convert hxy using 1
    ext i
    simp [castIntVector]
  smul_mem' c x hx := by
    have hcx := V.smul_mem (c : ℚ) hx
    change castIntVector (c • x) ∈ V
    convert hcx using 1
    ext i
    simp [castIntVector, smul_eq_mul]

@[simp] lemma mem_rationalLattice {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) (ξ : Fin D → ℤ) :
    ξ ∈ rationalLattice V ↔ castIntVector ξ ∈ V := Iff.rfl

/-- A chosen finite `ℤ`-basis of the saturated lattice. -/
noncomputable def latticeBasisData {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    Σ n : ℕ, Module.Basis (Fin n) ℤ (rationalLattice V) :=
  Submodule.basisOfPid (Pi.basisFun ℤ (Fin D)) (rationalLattice V)

/-- Rank of the chosen integral lattice basis. -/
noncomputable def latticeRank {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) : ℕ :=
  (latticeBasisData V).1

/-- The chosen integral lattice basis, viewed in ambient coordinates. -/
noncomputable def latticeBasis {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    Fin (latticeRank V) → Fin D → ℤ :=
  fun i ↦ ((latticeBasisData V).2 i : rationalLattice V)

lemma latticeBasis_mem {D : ℕ} (V : Submodule ℚ (Fin D → ℚ))
    (i : Fin (latticeRank V)) :
    castIntVector (latticeBasis V i) ∈ V := by
  exact ((latticeBasisData V).2 i).property

/-- The chosen lattice basis remains independent after scalar extension from
`ℤ` to `ℚ`. -/
lemma latticeBasis_linearIndependent {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    LinearIndependent ℚ
      (fun i ↦ castIntVector (latticeBasis V i)) := by
  have hZsub : LinearIndependent ℤ
      (fun i : Fin (latticeRank V) ↦
        (latticeBasisData V).2 i) :=
    (latticeBasisData V).2.linearIndependent
  have hker : (rationalLattice V).subtype.ker = ⊥ :=
    Submodule.ker_subtype _
  have hZ : LinearIndependent ℤ (latticeBasis V) := by
    change LinearIndependent ℤ (fun i : Fin (latticeRank V) ↦
      (((latticeBasisData V).2 i : rationalLattice V) : Fin D → ℤ))
    exact hZsub.map' (rationalLattice V).subtype hker
  exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).2 hZ

/-- The lattice rank is at most the rational dimension of the ambient
subspace. -/
lemma latticeRank_le_finrank {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    latticeRank V ≤ Module.finrank ℚ V := by
  let bV : Fin (latticeRank V) → V := fun i ↦
    ⟨castIntVector (latticeBasis V i), latticeBasis_mem V i⟩
  have hbV : LinearIndependent ℚ bV := by
    apply LinearIndependent.of_comp V.subtype
    change LinearIndependent ℚ
      (fun i ↦ castIntVector (latticeBasis V i))
    exact latticeBasis_linearIndependent V
  simpa using hbV.fintype_card_le_finrank

/-- Every integral point of `V` is an integral linear combination of the
chosen saturated basis. -/
lemma exists_latticeBasis_coefficients {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) {η : Fin D → ℤ}
    (hη : castIntVector η ∈ V) :
    ∃ c : Fin (latticeRank V) → ℤ,
      η = ∑ i, c i • latticeBasis V i := by
  let ηL : rationalLattice V := ⟨η, hη⟩
  let c : Fin (latticeRank V) → ℤ := fun i ↦
    ((latticeBasisData V).2.repr ηL) i
  refine ⟨c, ?_⟩
  have hsum := (latticeBasisData V).2.sum_repr ηL
  change η = ∑ i,
    ((latticeBasisData V).2.repr (⟨η, hη⟩ : rationalLattice V)) i •
      ((((latticeBasisData V).2 i : rationalLattice V) : Fin D → ℤ))
  funext j
  have hj := congrArg
    (fun z : rationalLattice V ↦ ((z : Fin D → ℤ) j)) hsum
  change ((rationalLattice V).subtype
      (∑ i, ((latticeBasisData V).2.repr ηL) i •
        (latticeBasisData V).2 i)) j = η j at hj
  rw [map_sum] at hj
  simp only [map_smul] at hj
  exact hj.symm

lemma integerDot_sum_smul {D n : ℕ} (c : Fin n → ℤ)
    (ξ : Fin n → Fin D → ℤ) (x : Torus D) :
    integerDot (∑ i, c i • ξ i) x =
      ∑ i, c i • integerDot (ξ i) x := by
  classical
  simp only [integerDot_apply, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_smul]

/-- If the basis characters vanish, every integral character in the rational
subspace vanishes. -/
lemma integerDot_eq_zero_of_latticeBasis {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) (x : Torus D)
    (hx : phaseHom (latticeBasis V) x = 0)
    {η : Fin D → ℤ} (hη : castIntVector η ∈ V) :
    integerDot η x = 0 := by
  obtain ⟨c, rfl⟩ := exists_latticeBasis_coefficients V hη
  rw [integerDot_sum_smul]
  have hi (i : Fin (latticeRank V)) :
      integerDot (latticeBasis V i) x = 0 := by
    exact congrFun hx i
  simp [hi]

end Erdos721.HunterLattice
