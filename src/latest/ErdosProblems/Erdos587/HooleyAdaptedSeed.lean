import ErdosProblems.Erdos587.HooleyLatticeModelMaps
import ErdosProblems.Erdos587.HooleySeedProgression

/-! # A full lattice seed covers the adapted-coordinate rounding errors -/

namespace Erdos587.GeneralizedAP

def deltaSeedLatticeFactor (d : ℕ) : ℕ := (4 ^ (d + 2) + d + 1) * 4 ^ d

noncomputable def DeltaLatticeModel.seedRadius {X : ConvexProgression}
    {Γ : AddSubgroup (Fin X.rank → ℤ)} (D : DeltaLatticeModel X Γ) (i : Fin X.rank) : ℝ :=
  ((4 ^ (X.rank + 2) : ℕ) : ℝ) * (D.bound i + 1)

lemma delta_adapted_seed_radius {X : ConvexProgression} {Γ : AddSubgroup (Fin X.rank → ℤ)}
    (D : DeltaLatticeModel X Γ) (i : Fin X.rank) :
    2 ≤ D.seedRadius i ∧ (4 : ℝ) ^ (X.rank + 2) ≤ 2 * D.seedRadius i := by
  have hp : (1 : ℝ) ≤ 4 ^ X.rank := one_le_pow₀ (by norm_num)
  have hb := D.bound_nonneg i
  dsimp only [DeltaLatticeModel.seedRadius]
  push_cast
  rw [pow_add]
  norm_num
  constructor <;> nlinarith

theorem delta_adapted_seed_coverage {X : ConvexProgression}
    {Γ : AddSubgroup (Fin X.rank → ℤ)} (D : DeltaLatticeModel X Γ)
    (f : (Fin X.rank → ℤ) →+ ℤ) (c : Γ.toIntSubmodule) (A : Finset ℤ)
    (hseed : ∀ w : Γ.toIntSubmodule,
      intCastVec w.val ∈ bodyDilate (deltaSeedLatticeFactor X.rank : ℝ) X.body →
        f (c.val + w.val) ∈ A.subsetSum) :
    ∀ u : Fin X.rank → ℤ,
      (∀ i, |(u i : ℝ)| ≤ D.seedRadius i + (X.rank : ℝ) * D.bound i + 1 / 2) →
      D.coordinateEval f (D.coordinates c + u) ∈ A.subsetSum := by
  intro u hu
  let t : ℝ := ((4 ^ (X.rank + 2) : ℕ) : ℝ) + X.rank + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hb (i : Fin X.rank) : |(u i : ℝ)| ≤ t * (D.bound i + 1) := by
    have hbi := D.bound_nonneg i
    have hri : (0 : ℝ) ≤ X.rank := by positivity
    have hh := hu i
    dsimp only [DeltaLatticeModel.seedRadius] at hh
    dsimp only [t]
    nlinarith
  have hmem := D.synthesis t ht u hb
  have hscale : t * ((4 ^ X.rank : ℕ) : ℝ) = (deltaSeedLatticeFactor X.rank : ℝ) := by
    dsimp only [t, deltaSeedLatticeFactor]
    push_cast
    rfl
  rw [hscale] at hmem
  have hvalue : D.coordinateEval f (D.coordinates c + u) =
      f (c.val + (D.coordinates.symm u).val) := by
    change f (D.coordinates.symm (D.coordinates c + u)).val = _
    rw [map_add, D.coordinates.symm_apply_apply]
    rfl
  rw [hvalue]
  exact hseed _ hmem

end Erdos587.GeneralizedAP
