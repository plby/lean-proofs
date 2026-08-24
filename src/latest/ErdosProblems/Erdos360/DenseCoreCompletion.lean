import ErdosProblems.Erdos360.CarryCompletion

open scoped Pointwise

namespace Erdos360

/-!
# A constant-loss alternative to carry completion

The exact Deshouillers--Freiman endpoint tries to extend an affine fibre
description from the dense Fourier core to the whole cyclic set without any
loss.  For the order-of-growth theorem, a simpler observation is useful:
the cardinal collision argument already writes every point of the whole set
as `c₁ + c₂ - c₃` with all three `cᵢ` in the core.  Consequently a cyclic
coset progression containing the core expands by only a factor three and
contains the whole set.  This route is independent of carry separation.
-/

/-- The sum of two cyclic coset progressions with the same subgroup and step
is contained in the progression obtained by adding their starting points and
their displayed lengths.  The deliberately harmless extra endpoint avoids
case distinctions at length zero. -/
lemma cyclicCosetProgression_add_subset_same
    {t L M : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    (a b d : ZMod t) :
    cyclicCosetProgression H a d L +
        cyclicCosetProgression H b d M ⊆
      cyclicCosetProgression H (a + b) d (L + M) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp hx
  obtain ⟨j, hj, hyj⟩ := mem_cyclicCosetProgression_iff.mp hy
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i + j, by omega, ?_⟩
  have hadd := H.add_mem hxi hyj
  convert hadd using 1
  simp only [add_nsmul]
  abel

/-- A ternary expression in a length-`L` cyclic coset progression lies in
the same subgroup progression of displayed length `3L`. -/
lemma cyclicCosetProgression_ternary_subset
    {t L : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    (a d : ZMod t) :
    cyclicCosetProgression H a d L +
        (cyclicCosetProgression H a d L -
          cyclicCosetProgression H a d L) ⊆
      cyclicCosetProgression H (a + (-(L • d))) d (3 * L) := by
  have hsub :
      cyclicCosetProgression H a d L -
          cyclicCosetProgression H a d L ⊆
        cyclicCosetProgression H (-(L • d)) d (2 * L) :=
    cyclicCosetProgression_sub_subset
      (H := H) (a := a) (d := d) (L := L) Finset.Subset.rfl
  intro z hz
  have hz' : z ∈ cyclicCosetProgression H a d L +
      cyclicCosetProgression H (-(L • d)) d (2 * L) :=
    Finset.add_subset_add Finset.Subset.rfl hsub hz
  have hsum := cyclicCosetProgression_add_subset_same H a (-(L • d)) d hz'
  simpa only [show L + 2 * L = 3 * L by omega] using hsum

/-- Every point of the ambient set belongs to the ternary sum-difference of
the dense core once the core double sumset has size at least `3|C|/2`.
This is the set-theoretic form of the collision lemma. -/
theorem subset_add_sub_of_dense_core
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {B C : Finset G}
    (hB : B.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 3 * C.card ≤ 2 * (C + C).card) :
    B ⊆ C + (C - C) := by
  intro z hz
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hrel⟩ :=
    exists_core_ternary_collision_of_dense_smallDoubling
      hB hCB hdense hsmall hcore z hz
  apply Finset.mem_add.mpr
  refine ⟨c₁, hc₁, c₂ - c₃, ?_, ?_⟩
  · exact Finset.mem_sub.mpr ⟨c₂, hc₂, c₃, hc₃, rfl⟩
  · have hzEq : z = c₁ + c₂ - c₃ := eq_sub_of_add_eq hrel
    rw [hzEq]
    abel

/-- Constant-loss completion of a cyclic coset progression from the Fourier
core to the original cyclic set.  Unlike exact carry completion, this needs
no affine fibre formula and no forbidden-carry hypothesis. -/
theorem dense_core_cosetProgression_ternary_completion
    {t L : ℕ} [NeZero t]
    {B C : Finset (ZMod t)} {H : AddSubgroup (ZMod t)}
    {a d : ZMod t}
    (hB : B.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 3 * C.card ≤ 2 * (C + C).card)
    (hCprog : C ⊆ cyclicCosetProgression H a d L) :
    B ⊆ cyclicCosetProgression H (a + (-(L • d))) d (3 * L) := by
  have hternary : C + (C - C) ⊆
      cyclicCosetProgression H a d L +
        (cyclicCosetProgression H a d L -
          cyclicCosetProgression H a d L) := by
    apply Finset.add_subset_add hCprog
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    exact Finset.mem_sub.mpr ⟨x, hCprog hx, y, hCprog hy, rfl⟩
  exact (subset_add_sub_of_dense_core hB hCB hdense hsmall hcore).trans
    (hternary.trans (cyclicCosetProgression_ternary_subset H a d))

/-- The completion loses exactly a factor three in displayed progression
mass.  This arithmetic wrapper is convenient when the core inverse theorem
has already supplied a mass estimate. -/
theorem dense_core_cosetProgression_ternary_completion_mass
    {t L R : ℕ} [NeZero t]
    {B C : Finset (ZMod t)} {H : AddSubgroup (ZMod t)}
    {a d : ZMod t}
    (hB : B.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 3 * C.card ≤ 2 * (C + C).card)
    (hCprog : C ⊆ cyclicCosetProgression H a d L)
    (hmass : L * Nat.card H ≤ R) :
    ∃ a' : ZMod t, B ⊆ cyclicCosetProgression H a' d (3 * L) ∧
      (3 * L) * Nat.card H ≤ 3 * R := by
  refine ⟨a + (-(L • d)),
    dense_core_cosetProgression_ternary_completion
      hB hCB hdense hsmall hcore hCprog, ?_⟩
  nlinarith

end Erdos360

#print axioms Erdos360.cyclicCosetProgression_add_subset_same
#print axioms Erdos360.subset_add_sub_of_dense_core
#print axioms Erdos360.dense_core_cosetProgression_ternary_completion_mass
