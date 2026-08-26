import ErdosProblems.Erdos593.TripleSystem.HighPairSelection
import ErdosProblems.Erdos593.TripleSystem.HighPairGraph
import ErdosProblems.Erdos593.TripleSystem.PairCodegree
import ErdosProblems.Erdos593.TripleSystem.RainbowExpansionEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matrix assembly from high-codegree pairs

This module turns independently witnessed large pair-codegrees on a complete
left/right grid into the locally bounded matrix required by the finite
rainbow extraction. Hall selection makes all third vertices globally
distinct, which is stronger than the local multiplicity bound needed below.
-/

namespace Erdos593

universe u v

namespace TripleSystem

/-- A globally injective matrix of colors is locally `2`-bounded. -/
theorem locallyBounded_two_of_injective
    {W : Type u} {q : Nat} (apex : Fin q → Fin q → W)
    (hinj : Function.Injective
      (fun ij : Fin q × Fin q => apex ij.1 ij.2)) :
    RainbowBipartite.LocallyBounded 2 apex := by
  constructor
  · intro x a
    apply Nat.lt_succ_iff.mpr
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    intro y z
    apply Subtype.ext
    have hp : (x, y.1) = (x, z.1) := hinj (by
      change apex x y.1 = apex x z.1
      exact y.2.trans z.2.symm)
    exact congrArg Prod.snd hp
  · intro y a
    apply Nat.lt_succ_iff.mpr
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    intro x z
    apply Subtype.ext
    have hp : (x.1, y) = (z.1, y) := hinj (by
      change apex x.1 y = apex z.1 y
      exact x.2.trans z.2.symm)
    exact congrArg Prod.fst hp

/-- Pair-codegree reservoirs whose total capacity exceeds a finite protected
core and all grid cells yield a witnessed bipartite matrix. -/
theorem exists_witnessedBipartiteMatrix_of_pairCodegree
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n T : Nat}
    (left right : Fin n ↪ W) (core : Finset W)
    (hleft : ∀ i, left i ∈ core)
    (hright : ∀ j, right j ∈ core)
    (hcore_disjoint : ∀ i j, left i ≠ right j)
    (completion : ∀ ij : Fin n × Fin n,
      PairCodegreeWitness H (left ij.1) (right ij.2) T)
    (hcap : core.card + Fintype.card (Fin n × Fin n) ≤ T) :
    ∃ M : WitnessedBipartiteMatrix H n 2, M.left = left ∧ M.right = right := by
  classical
  obtain ⟨choose, hchoose_inj, hchoose_avoid⟩ :=
    exists_injective_choice_of_fintype_card_add_le
      (ι := Fin n × Fin n) (W := W) core
      (fun ij => (completion ij).third) hcap
  let apex : Fin n → Fin n → W :=
    fun i j => (completion (i, j)).third (choose (i, j))
  have hapex_inj : Function.Injective
      (fun ij : Fin n × Fin n => apex ij.1 ij.2) := by
    intro ij kl h
    apply hchoose_inj
    simpa [apex] using! h
  have hapex_avoid : ∀ i j, apex i j ∉ core := by
    intro i j
    simpa [apex] using! hchoose_avoid (i, j)
  refine ⟨{
    left := left
    right := right
    apex := apex
    edge := fun i j => (completion (i, j)).edge (choose (i, j))
    core_disjoint := hcore_disjoint
    apex_ne_left := fun i j k h => hapex_avoid i j (h.symm ▸ hleft k)
    apex_ne_right := fun i j k h => hapex_avoid i j (h.symm ▸ hright k)
    edgeSet_eq := fun i j => by
      simpa [apex] using! (completion (i, j)).edgeSet_eq (choose (i, j))
    locallyBounded := locallyBounded_two_of_injective apex hapex_inj
  }, rfl, rfl⟩

/-- The canonical protected core is the union of the chosen left and right
rows. -/
theorem exists_witnessedBipartiteMatrix_of_pairCodegree_core_union
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n T : Nat}
    (left right : Fin n ↪ W)
    (hcore_disjoint : ∀ i j, left i ≠ right j)
    (completion : ∀ ij : Fin n × Fin n,
      PairCodegreeWitness H (left ij.1) (right ij.2) T)
    (hcap : (Finset.univ.map left ∪ Finset.univ.map right).card +
        Fintype.card (Fin n × Fin n) ≤ T) :
    ∃ M : WitnessedBipartiteMatrix H n 2, M.left = left ∧ M.right = right := by
  apply exists_witnessedBipartiteMatrix_of_pairCodegree left right
    (Finset.univ.map left ∪ Finset.univ.map right)
  · intro i
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · intro j
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · exact hcore_disjoint
  · exact completion
  · exact hcap

/-- A uniform pair-codegree threshold of `2n + n²` supplies the capacity
needed to select globally distinct third vertices for an `n × n` matrix. -/
theorem exists_witnessedBipartiteMatrix_of_quadratic_pairCodegree
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hcore_disjoint : ∀ i j, left i ≠ right j)
    (completion : ∀ ij : Fin n × Fin n,
      PairCodegreeWitness H (left ij.1) (right ij.2) (2 * n + n * n)) :
    ∃ M : WitnessedBipartiteMatrix H n 2, M.left = left ∧ M.right = right := by
  apply exists_witnessedBipartiteMatrix_of_pairCodegree_core_union left right
    hcore_disjoint completion
  have hcore : (Finset.univ.map left ∪ Finset.univ.map right).card ≤ 2 * n := by
    calc
      (Finset.univ.map left ∪ Finset.univ.map right).card ≤
          (Finset.univ.map left).card + (Finset.univ.map right).card :=
        Finset.card_union_le _ _
      _ = 2 * n := by simp [two_mul]
  simpa using! Nat.add_le_add_right hcore (n * n)

/-- A complete finite grid of high pairs at the quadratic threshold supplies
the pair-codegree witnesses needed for the matrix construction. -/
theorem exists_witnessedBipartiteMatrix_of_quadratic_highPair
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hhigh : ∀ i j,
      HighPair H (2 * n + n * n) (left i) (right j)) :
    ∃ M : WitnessedBipartiteMatrix H n 2, M.left = left ∧ M.right = right := by
  apply exists_witnessedBipartiteMatrix_of_quadratic_pairCodegree left right
  · intro i j
    exact (hhigh i j).1
  · intro ij
    exact Classical.choice (hhigh ij.1 ij.2).2

/-- The quadratic Hall threshold can select the apex of every grid cell
globally injectively.  This strengthens the local `2`-boundedness supplied by
`exists_witnessedBipartiteMatrix_of_quadratic_highPair`, and is useful when a
single high-pair grid is itself intended to be a rainbow submatrix. -/
theorem exists_injectiveWitnessedBipartiteMatrix_of_quadratic_highPair
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hhigh : ∀ i j,
      HighPair H (2 * n + n * n) (left i) (right j)) :
    ∃ M : WitnessedBipartiteMatrix H n 2,
      M.left = left ∧ M.right = right ∧
        Function.Injective (fun ij : Fin n × Fin n => M.apex ij.1 ij.2) := by
  classical
  let core : Finset W := Finset.univ.map left ∪ Finset.univ.map right
  have hcap : core.card + Fintype.card (Fin n × Fin n) ≤ 2 * n + n * n := by
    have hcore : core.card ≤ 2 * n := by
      calc
        core.card ≤ (Finset.univ.map left).card + (Finset.univ.map right).card :=
          Finset.card_union_le _ _
        _ = 2 * n := by simp [two_mul]
    simpa using! Nat.add_le_add_right hcore (n * n)
  let completion : ∀ ij : Fin n × Fin n,
      PairCodegreeWitness H (left ij.1) (right ij.2) (2 * n + n * n) :=
    fun ij => Classical.choice (hhigh ij.1 ij.2).2
  obtain ⟨choose, hchoose_inj, hchoose_avoid⟩ :=
    exists_injective_choice_of_fintype_card_add_le
      (ι := Fin n × Fin n) (W := W) core
      (fun ij => (completion ij).third) hcap
  let apex : Fin n → Fin n → W :=
    fun i j => (completion (i, j)).third (choose (i, j))
  have hapex_inj : Function.Injective
      (fun ij : Fin n × Fin n => apex ij.1 ij.2) := by
    intro ij kl h
    apply hchoose_inj
    simpa [apex] using! h
  have hapex_avoid : ∀ i j, apex i j ∉ core := by
    intro i j
    simpa [apex] using! hchoose_avoid (i, j)
  refine ⟨{
    left := left
    right := right
    apex := apex
    edge := fun i j => (completion (i, j)).edge (choose (i, j))
    core_disjoint := fun i j => (hhigh i j).1
    apex_ne_left := fun i j k h =>
      hapex_avoid i j (h.symm ▸ Finset.mem_union_left _
        (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
    apex_ne_right := fun i j k h =>
      hapex_avoid i j (h.symm ▸ Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
    edgeSet_eq := fun i j => by
      simpa [apex] using! (completion (i, j)).edgeSet_eq (choose (i, j))
    locallyBounded := locallyBounded_two_of_injective apex hapex_inj
  }, rfl, rfl, hapex_inj⟩

end TripleSystem

end Erdos593
