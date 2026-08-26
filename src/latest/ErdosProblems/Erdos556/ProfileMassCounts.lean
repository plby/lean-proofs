import ErdosProblems.Erdos556.ThreeColourDecomposition
import ErdosProblems.Erdos556.FiberCardSums

/-! Vertex and free-coordinate totals for the profile partition. -/

namespace Erdos556

open SimpleGraph Finset

theorem ThreeColourDecomposition.mem_profileClass_iff {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (p : CubeProfile) (v : V) :
    v ∈ h.profileClass p ↔ h.profile v = p := by
  simp only [profileClass, mem_filter, mem_univ, true_and]

theorem ThreeColourDecomposition.profileClass_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (p q : CubeProfile) (hpq : p ≠ q) : Disjoint (h.profileClass p) (h.profileClass q) := by
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  exact hpq ((h.mem_profileClass_iff p v).mp hvp |>.symm.trans ((h.mem_profileClass_iff q v).mp hvq))

theorem ThreeColourDecomposition.sum_profileClass_card {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    (∑ p, (h.profileClass p).card) = Fintype.card V := sum_fiber_card_eq h.profile

theorem ThreeColourDecomposition.profile_none_iff {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (v : V) (i : Fin 3) :
    h.profile v i = none ↔ v ∈ h.stars i := by
  by_cases hv : v ∈ h.stars i <;> simp [profile, hv]

theorem ThreeColourDecomposition.sum_stars_card {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    (∑ i, (h.stars i).card) = ∑ p, profileDimension p * (h.profileClass p).card := by
  classical
  have hstar (i : Fin 3) : (h.stars i).card = ∑ v, if h.profile v i = none then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and, h.profile_none_iff]
  calc
    _ = ∑ i, ∑ v, if h.profile v i = none then 1 else 0 := sum_congr rfl (fun i _ => hstar i)
    _ = ∑ v, ∑ i, if h.profile v i = none then 1 else 0 := sum_comm
    _ = ∑ v, profileDimension (h.profile v) := by
      apply sum_congr rfl
      intro v _
      rw [profileDimension, sum_boole]
      simp only [Nat.cast_id]
    _ = ∑ p, (h.profileClass p).card * profileDimension p := sum_by_fiber_card h.profile profileDimension
    _ = _ := sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

#print axioms ThreeColourDecomposition.sum_stars_card

end Erdos556
