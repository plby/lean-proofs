/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 578.
https://www.erdosproblems.com/forum/thread/578

Informal authors:
- Oliver Riordan

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos578.md
-/
/-
Erdős Problem 578 (Erdős--Bollobás, proved by Riordan).

For `n = 2 ^ d`, a uniformly random simple graph on `n` labelled vertices
contains a spanning copy of the `d`-dimensional cube with probability tending
to one as `d → ∞`.  Uniformity is exactly the independent-edge model with
edge probability `1 / 2`.

The accompanying mathematical reconstruction is `tex/578.tex`.
-/

import Mathlib

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

/-- The vertices of the `d`-dimensional discrete cube. -/
abbrev CubeVertex (d : ℕ) := Fin d → ZMod 2

local instance twoNeZero : NeZero (2 : ℕ) := Nat.instNeZeroSucc

/-- The `d`-dimensional cube: two bit vectors are adjacent when they differ
in exactly one coordinate. -/
abbrev cubeGraph (d : ℕ) : SimpleGraph (CubeVertex d) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h ↦ by simpa [hammingDist_comm] using h⟩
  loopless := ⟨fun x h ↦ by simp [hammingDist] at h⟩

theorem card_cubeVertex (d : ℕ) : Fintype.card (CubeVertex d) = 2 ^ d := by
  simp [CubeVertex]

/-- The neighbours of a cube vertex are obtained by flipping one coordinate. -/
theorem cube_neighborFinset (d : ℕ) (v : CubeVertex d) :
    (cubeGraph d).neighborFinset v =
      Finset.univ.image (fun i ↦ Function.update v i (v i + 1)) := by
  ext w
  simp [cubeGraph]
  constructor <;> intro h <;> simp_all +decide [hammingDist]
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    use i
    ext j
    by_cases hj : j = i <;> simp_all +decide [Finset.ext_iff]
    · cases Fin.exists_fin_two.mp ⟨v i, rfl⟩ <;>
        cases Fin.exists_fin_two.mp ⟨w i, rfl⟩ <;>
        specialize hi i <;> simp_all +decide [ZMod]
    · specialize hi j
      aesop
  · obtain ⟨i, rfl⟩ := h
    rw [Finset.card_eq_one]
    use i
    ext j
    by_cases hj : j = i <;> simp +decide [hj]

theorem cube_degree (d : ℕ) (v : CubeVertex d) : (cubeGraph d).degree v = d := by
  rw [SimpleGraph.degree, cube_neighborFinset, Finset.card_image_of_injective]
  · simp
  · intro i j h
    replace h := congr_fun h i
    by_cases hij : i = j <;> simp_all +decide

/-- `Q_d` has `d * 2^(d-1)` edges. -/
theorem cube_card_edges (d : ℕ) :
    (cubeGraph d).edgeFinset.card = d * 2 ^ (d - 1) := by
  have hdeg : ∀ v : CubeVertex d, (cubeGraph d).degree v = d := cube_degree d
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (cubeGraph d)
  simp_all +decide [mul_comm]
  cases d <;> simp_all +decide [pow_succ']
  linarith

/-- The number of simple graphs on a finite labelled vertex type. -/
theorem card_simpleGraph {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
  let edgeSetEquiv : SimpleGraph V ≃ Set {e : Sym2 V // ¬e.IsDiag} :=
    { toFun := fun G ↦ {e | e.1 ∈ G.edgeSet}
      invFun := fun S ↦
        { Adj := fun v w ↦ ∃ h : ¬(Sym2.mk v w).IsDiag,
            (⟨Sym2.mk v w, h⟩ : {e : Sym2 V // ¬e.IsDiag}) ∈ S
          symm := by
            constructor
            rintro v w ⟨h, hs⟩
            refine ⟨?_, ?_⟩
            · simpa [Sym2.eq_swap] using h
            · simpa only [Sym2.eq_swap] using hs
          loopless := by
            refine ⟨fun v h ↦ ?_⟩
            rcases h with ⟨hdiag, -⟩
            exact hdiag (by simp) }
      left_inv := by
        intro G
        ext v w
        constructor
        · rintro ⟨_, h⟩
          simpa using h
        · intro h
          exact ⟨G.not_isDiag_of_mem_edgeSet (by simpa using h), by simpa using h⟩
      right_inv := by
        intro S
        ext e
        rcases e with ⟨e, he⟩
        induction e using Sym2.inductionOn with
        | _ v w =>
          change (∃ h : ¬(Sym2.mk v w).IsDiag,
              (⟨Sym2.mk v w, h⟩ : {e : Sym2 V // ¬e.IsDiag}) ∈ S) ↔
            (⟨Sym2.mk v w, he⟩ : {e : Sym2 V // ¬e.IsDiag}) ∈ S
          constructor
          · rintro ⟨h, hs⟩
            convert hs
          · exact fun hs ↦ ⟨he, hs⟩ }
  rw [Fintype.card_congr edgeSetEquiv, Fintype.card_set,
    Sym2.card_subtype_not_diag]

/-- The finite universe of possible edges on a labelled vertex type. -/
def allEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  (⊤ : SimpleGraph V).edgeFinset

theorem card_allEdges (V : Type*) [Fintype V] [DecidableEq V] :
    (allEdges V).card = (Fintype.card V).choose 2 := by
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

/-- Convert a finite set of unordered pairs into the graph having precisely
its nondiagonal pairs as edges. -/
def graphOfEdges {V : Type*} [DecidableEq V] (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

noncomputable instance graphOfEdgesEdgeSetFintype {V : Type*} [Fintype V]
    [DecidableEq V] (S : Finset (Sym2 V)) : Fintype (graphOfEdges S).edgeSet :=
  Fintype.ofFinite _

theorem graphOfEdges_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    {S : Finset (Sym2 V)} (hS : S ⊆ allEdges V) :
    (graphOfEdges S).edgeFinset = S := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Finset.mem_coe]
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    have htop := hS he
    simpa [allEdges] using htop

/-- Relabel a finite edge set by a permutation of its vertices. -/
def permutedEdges {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (S : Finset (Sym2 V)) : Finset (Sym2 V) :=
  S.map σ.toEmbedding.sym2Map

@[simp] theorem card_permutedEdges {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (S : Finset (Sym2 V)) :
    (permutedEdges σ S).card = S.card := by
  simp [permutedEdges]

/-- The edge set of the cube after a relabelling of all vertices. -/
def cubePattern (d : ℕ) (σ : Equiv.Perm (CubeVertex d)) :
    Finset (Sym2 (CubeVertex d)) :=
  permutedEdges σ (cubeGraph d).edgeFinset

@[simp] theorem card_cubePattern (d : ℕ) (σ : Equiv.Perm (CubeVertex d)) :
    (cubePattern d σ).card = d * 2 ^ (d - 1) := by
  simp [cubePattern, cube_card_edges]

theorem cubePattern_subset_allEdges (d : ℕ) (σ : Equiv.Perm (CubeVertex d)) :
    cubePattern d σ ⊆ allEdges (CubeVertex d) := by
  intro e he
  rw [cubePattern, permutedEdges, Finset.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  rw [allEdges, SimpleGraph.mem_edgeFinset]
  have hnd : ¬e'.IsDiag := by
    have := (cubeGraph d).not_isDiag_of_mem_edgeSet
      (SimpleGraph.mem_edgeFinset.mp he')
    exact this
  simpa [SimpleGraph.edgeSet_top, Sym2.isDiag_map σ.injective] using hnd

/-- Number of relabellings of the cube whose required edges all lie in `S`. -/
noncomputable def copyMultiplicity (d : ℕ)
    (S : Finset (Sym2 (CubeVertex d))) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
    fun σ ↦ cubePattern d σ ⊆ S).card

/-- A positive relabelling count gives an actual (not necessarily induced)
copy of the cube in the graph represented by `S`. -/
theorem cube_isContained_graphOfEdges_of_copyMultiplicity_pos (d : ℕ)
    {S : Finset (Sym2 (CubeVertex d))} (hpos : 0 < copyMultiplicity d S) :
    cubeGraph d ⊑ graphOfEdges S := by
  classical
  rw [copyMultiplicity, Finset.card_pos] at hpos
  obtain ⟨σ, hσ⟩ := hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  refine ⟨{ toHom :=
              { toFun := σ
                map_rel' := ?_ }
            injective' := σ.injective }⟩
  intro x y hxy
  rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
  constructor
  · have he : s(x, y) ∈ (cubeGraph d).edgeFinset := by simpa using hxy
    have hmap : s(σ x, σ y) ∈ cubePattern d σ := by
      rw [cubePattern, permutedEdges, Finset.mem_map]
      exact ⟨s(x, y), he, by simp⟩
    exact hσ hmap
  · exact σ.injective.ne ((cubeGraph d).ne_of_adj hxy)

/-- The uniform `M`-edge sample space on the cube's labelled vertex set. -/
def fixedEdgeSamples (d M : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) :=
  (allEdges (CubeVertex d)).powersetCard M

@[simp] theorem card_fixedEdgeSamples (d M : ℕ) :
    (fixedEdgeSamples d M).card =
      Nat.choose ((2 ^ d).choose 2) M := by
  simp [fixedEdgeSamples, Finset.card_powersetCard, card_allEdges,
    card_cubeVertex]

/-- Double-counting incidences between fixed-size samples and relabelled
cubes gives the exact first moment. -/
theorem sum_copyMultiplicity (d M : ℕ)
    (hM : d * 2 ^ (d - 1) ≤ M) :
    (∑ S ∈ fixedEdgeSamples d M, copyMultiplicity d S) =
      Fintype.card (Equiv.Perm (CubeVertex d)) *
        Nat.choose ((2 ^ d).choose 2 - d * 2 ^ (d - 1))
          (M - d * 2 ^ (d - 1)) := by
  classical
  let P : Finset (Equiv.Perm (CubeVertex d)) := Finset.univ
  have hcard (σ : Equiv.Perm (CubeVertex d)) :
      ((fixedEdgeSamples d M).filter fun S ↦ cubePattern d σ ⊆ S).card =
        Nat.choose ((2 ^ d).choose 2 - d * 2 ^ (d - 1))
          (M - d * 2 ^ (d - 1)) := by
    rw [fixedEdgeSamples]
    simpa [card_allEdges, card_cubeVertex] using
      Finset.card_filter_powersetCard_subset
        (cubePattern d σ) (allEdges (CubeVertex d)) M
        (cubePattern_subset_allEdges d σ) (by simpa using hM)
  calc
    (∑ S ∈ fixedEdgeSamples d M, copyMultiplicity d S) =
        ∑ S ∈ fixedEdgeSamples d M,
          ∑ σ ∈ P, if cubePattern d σ ⊆ S then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro S hS
            simp [copyMultiplicity, P]
    _ = ∑ σ ∈ P, ∑ S ∈ fixedEdgeSamples d M,
          if cubePattern d σ ⊆ S then 1 else 0 := by
            exact Finset.sum_comm
    _ = ∑ σ ∈ P,
          ((fixedEdgeSamples d M).filter fun S ↦ cubePattern d σ ⊆ S).card := by
            apply Finset.sum_congr rfl
            intro σ hσ
            simp
    _ = _ := by simp [hcard, P]

/-- Exact second moment in the uniform `M`-edge model.  A pair of relabelled
cubes is present precisely when the union of its two edge patterns is
contained in the sample. -/
theorem sum_sq_copyMultiplicity (d M : ℕ)
    (hM : 2 * (d * 2 ^ (d - 1)) ≤ M) :
    (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S) ^ 2) =
      ∑ σ : Equiv.Perm (CubeVertex d),
        ∑ τ : Equiv.Perm (CubeVertex d),
          Nat.choose
            ((2 ^ d).choose 2 - (cubePattern d σ ∪ cubePattern d τ).card)
            (M - (cubePattern d σ ∪ cubePattern d τ).card) := by
  classical
  let P : Finset (Equiv.Perm (CubeVertex d)) := Finset.univ
  have hunion_sub (σ τ : Equiv.Perm (CubeVertex d)) :
      cubePattern d σ ∪ cubePattern d τ ⊆ allEdges (CubeVertex d) :=
    Finset.union_subset (cubePattern_subset_allEdges d σ)
      (cubePattern_subset_allEdges d τ)
  have hunion_card (σ τ : Equiv.Perm (CubeVertex d)) :
      (cubePattern d σ ∪ cubePattern d τ).card ≤ M := by
    calc
      (cubePattern d σ ∪ cubePattern d τ).card ≤
          (cubePattern d σ).card + (cubePattern d τ).card :=
        Finset.card_union_le (cubePattern d σ) (cubePattern d τ)
      _ = 2 * (d * 2 ^ (d - 1)) := by simp [two_mul]
      _ ≤ M := hM
  have hcard (σ τ : Equiv.Perm (CubeVertex d)) :
      ((fixedEdgeSamples d M).filter fun S ↦
          cubePattern d σ ∪ cubePattern d τ ⊆ S).card =
        Nat.choose
          ((2 ^ d).choose 2 - (cubePattern d σ ∪ cubePattern d τ).card)
          (M - (cubePattern d σ ∪ cubePattern d τ).card) := by
    rw [fixedEdgeSamples]
    simpa [card_allEdges, card_cubeVertex] using
      Finset.card_filter_powersetCard_subset
        (cubePattern d σ ∪ cubePattern d τ) (allEdges (CubeVertex d)) M
        (hunion_sub σ τ) (hunion_card σ τ)
  have hsq (S : Finset (Sym2 (CubeVertex d))) :
      (copyMultiplicity d S) ^ 2 =
        ∑ σ ∈ P, ∑ τ ∈ P,
          if cubePattern d σ ⊆ S ∧ cubePattern d τ ⊆ S then 1 else 0 := by
    let A : Equiv.Perm (CubeVertex d) → Prop := fun σ ↦ cubePattern d σ ⊆ S
    have hinner (σ : Equiv.Perm (CubeVertex d)) :
        (∑ τ ∈ P, if A σ ∧ A τ then 1 else 0) =
          if A σ then (P.filter A).card else 0 := by
      by_cases hσ : A σ
      · simpa [hσ] using (Finset.sum_boole (R := ℕ) A P)
      · simp [hσ]
    change (P.filter A).card ^ 2 =
      ∑ σ ∈ P, ∑ τ ∈ P, if A σ ∧ A τ then 1 else 0
    simp_rw [hinner]
    rw [← Finset.sum_filter A]
    simp [pow_two]
  calc
    (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S) ^ 2) =
        ∑ S ∈ fixedEdgeSamples d M,
          ∑ σ ∈ P, ∑ τ ∈ P,
            if cubePattern d σ ⊆ S ∧ cubePattern d τ ⊆ S then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              exact hsq S
    _ = ∑ σ ∈ P, ∑ τ ∈ P, ∑ S ∈ fixedEdgeSamples d M,
          if cubePattern d σ ⊆ S ∧ cubePattern d τ ⊆ S then 1 else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ P, ∑ τ ∈ P,
          ((fixedEdgeSamples d M).filter fun S ↦
            cubePattern d σ ∪ cubePattern d τ ⊆ S).card := by
              apply Finset.sum_congr rfl
              intro σ hσ
              apply Finset.sum_congr rfl
              intro τ hτ
              simp [Finset.union_subset_iff]
    _ = _ := by simp [hcard, P]

/-! ## The finite second-moment inequality -/

/-- Cauchy--Schwarz restricted to the positive support of a natural-valued
counting function. -/
theorem sq_sum_natCast_le_card_pos_mul_sum_sq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ) :
    (∑ i ∈ S, (R i : ℝ)) ^ 2 ≤
      ((S.filter fun i ↦ 0 < R i).card : ℝ) *
        ∑ i ∈ S, (R i : ℝ) ^ 2 := by
  let T := S.filter fun i ↦ 0 < R i
  have hsum : (∑ i ∈ T, (R i : ℝ)) = ∑ i ∈ S, (R i : ℝ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_lt] at hiT
    have hi : R i = 0 := by omega
    simp [hi]
  have hsumSq : (∑ i ∈ T, (R i : ℝ) ^ 2) =
      ∑ i ∈ S, (R i : ℝ) ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_lt] at hiT
    have hi : R i = 0 := by omega
    simp [hi]
  calc
    (∑ i ∈ S, (R i : ℝ)) ^ 2 = (∑ i ∈ T, (R i : ℝ)) ^ 2 := by rw [hsum]
    _ ≤ (T.card : ℝ) * ∑ i ∈ T, (R i : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = ((S.filter fun i ↦ 0 < R i).card : ℝ) *
        ∑ i ∈ S, (R i : ℝ) ^ 2 := by rw [hsumSq]

/-- The number of fixed-size edge samples which contain a cube. -/
noncomputable def fixedSuccessCount (d M : ℕ) : ℕ := by
  classical
  exact ((fixedEdgeSamples d M).filter fun S ↦
    cubeGraph d ⊑ graphOfEdges S).card

/-- Success probability in the uniform `M`-edge model. -/
noncomputable def fixedSuccessProbability (d M : ℕ) : ℝ :=
  (fixedSuccessCount d M : ℝ) / (fixedEdgeSamples d M).card

theorem fixedSuccessProbability_nonneg (d M : ℕ) :
    0 ≤ fixedSuccessProbability d M := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem fixedSuccessProbability_le_one (d M : ℕ)
    (hsamples : 0 < (fixedEdgeSamples d M).card) :
    fixedSuccessProbability d M ≤ 1 := by
  classical
  rw [fixedSuccessProbability, div_le_one (by exact_mod_cast hsamples)]
  unfold fixedSuccessCount
  exact_mod_cast
    (Finset.card_filter_le (s := fixedEdgeSamples d M)
      (p := fun S ↦ cubeGraph d ⊑ graphOfEdges S))

theorem positive_copyMultiplicity_card_le_fixedSuccessCount (d M : ℕ) :
    ((fixedEdgeSamples d M).filter fun S ↦ 0 < copyMultiplicity d S).card ≤
      fixedSuccessCount d M := by
  classical
  unfold fixedSuccessCount
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, cube_isContained_graphOfEdges_of_copyMultiplicity_pos d hS.2⟩

/-- Finite Paley--Zygmund: the normalized first and second moments give a
lower bound for the success probability in the uniform layer. -/
theorem moment_ratio_le_fixedSuccessProbability (d M : ℕ)
    (hsamples : 0 < (fixedEdgeSamples d M).card)
    (hsecond : 0 < ∑ S ∈ fixedEdgeSamples d M,
      (copyMultiplicity d S : ℝ) ^ 2) :
    (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ)) ^ 2 /
        ((fixedEdgeSamples d M).card *
          ∑ S ∈ fixedEdgeSamples d M,
            (copyMultiplicity d S : ℝ) ^ 2) ≤
      fixedSuccessProbability d M := by
  classical
  let A : ℝ := ((fixedEdgeSamples d M).card : ℝ)
  let B : ℝ := ∑ S ∈ fixedEdgeSamples d M,
    (copyMultiplicity d S : ℝ) ^ 2
  have hA : 0 < A := by
    change 0 < ((fixedEdgeSamples d M).card : ℝ)
    exact_mod_cast hsamples
  have hAB : 0 < A * B := mul_pos hA hsecond
  have hcs := sq_sum_natCast_le_card_pos_mul_sum_sq
    (fixedEdgeSamples d M) (copyMultiplicity d)
  have hdiv :
      (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ)) ^ 2 /
          (A * B) ≤
        (((fixedEdgeSamples d M).filter fun S ↦
          0 < copyMultiplicity d S).card : ℝ) / A := by
    rw [div_le_div_iff₀ hAB hA]
    simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hcs (le_of_lt hA)
  calc
    _ ≤ (((fixedEdgeSamples d M).filter fun S ↦
          0 < copyMultiplicity d S).card : ℝ) / A := by
      simpa [A, B] using hdiv
    _ ≤ (fixedSuccessCount d M : ℝ) / A := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast positive_copyMultiplicity_card_le_fixedSuccessCount d M)
        (le_of_lt hA)
    _ = fixedSuccessProbability d M := by
      simp [fixedSuccessProbability, A]

/-! ## Exact overlap generating function -/

/-- The number of common edges of two labelled cube copies. -/
def overlapCard (d : ℕ) (σ τ : Equiv.Perm (CubeVertex d)) : ℕ :=
  (cubePattern d σ ∩ cubePattern d τ).card

theorem card_union_cubePattern (d : ℕ)
    (σ τ : Equiv.Perm (CubeVertex d)) :
    (cubePattern d σ ∪ cubePattern d τ).card =
      2 * (d * 2 ^ (d - 1)) - overlapCard d σ τ := by
  rw [Finset.card_union]
  simp [overlapCard, two_mul]

theorem permutedEdges_mul {V : Type*} [DecidableEq V]
    (σ τ : Equiv.Perm V) (S : Finset (Sym2 V)) :
    permutedEdges (σ * τ) S = permutedEdges σ (permutedEdges τ S) := by
  simp only [permutedEdges, Finset.map_map]
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y => simp

@[simp] theorem permutedEdges_one {V : Type*} [DecidableEq V]
    (S : Finset (Sym2 V)) :
    permutedEdges (1 : Equiv.Perm V) S = S := by
  ext e
  simp [permutedEdges]

theorem permutedEdges_inter {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (S T : Finset (Sym2 V)) :
    permutedEdges σ (S ∩ T) = permutedEdges σ S ∩ permutedEdges σ T := by
  exact Finset.map_inter S T

@[simp] theorem cubePattern_one (d : ℕ) :
    cubePattern d (1 : Equiv.Perm (CubeVertex d)) = (cubeGraph d).edgeFinset := by
  simp [cubePattern]

theorem overlapCard_eq_relative (d : ℕ)
    (σ τ : Equiv.Perm (CubeVertex d)) :
    overlapCard d σ τ = overlapCard d 1 (σ⁻¹ * τ) := by
  rw [overlapCard, overlapCard]
  rw [← card_permutedEdges σ⁻¹]
  rw [permutedEdges_inter, cubePattern, cubePattern,
    ← permutedEdges_mul, ← permutedEdges_mul]
  simp [cubePattern]

theorem sum_overlap_pow_independent (d : ℕ)
    (σ : Equiv.Perm (CubeVertex d)) (c : ℝ) :
    (∑ τ : Equiv.Perm (CubeVertex d), c ^ overlapCard d σ τ) =
      ∑ τ : Equiv.Perm (CubeVertex d), c ^ overlapCard d 1 τ := by
  calc
    (∑ τ : Equiv.Perm (CubeVertex d), c ^ overlapCard d σ τ) =
        ∑ τ : Equiv.Perm (CubeVertex d),
          c ^ overlapCard d 1 ((Equiv.mulLeft σ⁻¹) τ) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [overlapCard_eq_relative]
            rfl
    _ = _ := Equiv.sum_comp (Equiv.mulLeft σ⁻¹)
      (fun τ ↦ c ^ overlapCard d 1 τ)

/-- Finite binomial expansion of the overlap weight.  It is important that
`F` is merely a chosen subgraph of the common edge set, rather than the
entire intersection. -/
theorem sum_overlap_pow_eq_subgraph_sum (d : ℕ)
    (σ : Equiv.Perm (CubeVertex d)) (a : ℝ) :
    (∑ τ : Equiv.Perm (CubeVertex d),
        (1 + a) ^ overlapCard d σ τ) =
      ∑ F ∈ (cubePattern d σ).powerset,
        a ^ F.card *
          (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun τ ↦ F ⊆ cubePattern d τ).card : ℝ) := by
  classical
  let P : Finset (Equiv.Perm (CubeVertex d)) := Finset.univ
  have hexpand (τ : Equiv.Perm (CubeVertex d)) :
      (1 + a) ^ overlapCard d σ τ =
        ∑ F ∈ (cubePattern d σ).powerset,
          if F ⊆ cubePattern d τ then a ^ F.card else 0 := by
    calc
      (1 + a) ^ overlapCard d σ τ =
          ∏ _e ∈ cubePattern d σ ∩ cubePattern d τ, (1 + a) := by
            simp [overlapCard]
      _ = ∑ F ∈ (cubePattern d σ ∩ cubePattern d τ).powerset,
          a ^ F.card := by
            rw [Finset.prod_one_add]
            apply Finset.sum_congr rfl
            intro F hF
            simp
      _ = ∑ F ∈ (cubePattern d σ).powerset,
          if F ⊆ cubePattern d τ then a ^ F.card else 0 := by
            rw [← Finset.sum_filter (fun F ↦ F ⊆ cubePattern d τ)]
            have hfilter :
                ((cubePattern d σ).powerset.filter fun F ↦
                    F ⊆ cubePattern d τ) =
                  (cubePattern d σ ∩ cubePattern d τ).powerset := by
              ext F
              simp only [Finset.mem_filter, Finset.mem_powerset]
              constructor
              · rintro ⟨hFσ, hFτ⟩
                exact Finset.subset_inter hFσ hFτ
              · intro hF
                exact ⟨hF.trans Finset.inter_subset_left,
                  hF.trans Finset.inter_subset_right⟩
            rw [hfilter]
  calc
    (∑ τ : Equiv.Perm (CubeVertex d),
        (1 + a) ^ overlapCard d σ τ) =
      ∑ τ ∈ P, ∑ F ∈ (cubePattern d σ).powerset,
        if F ⊆ cubePattern d τ then a ^ F.card else 0 := by
          apply Finset.sum_congr rfl
          intro τ hτ
          exact hexpand τ
    _ = ∑ F ∈ (cubePattern d σ).powerset, ∑ τ ∈ P,
        if F ⊆ cubePattern d τ then a ^ F.card else 0 := by
          exact Finset.sum_comm
    _ = ∑ F ∈ (cubePattern d σ).powerset,
        a ^ F.card *
          ((P.filter fun τ ↦ F ⊆ cubePattern d τ).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro F hF
          rw [← Finset.sum_filter (fun τ ↦ F ⊆ cubePattern d τ)]
          simp [mul_comm]
    _ = _ := by rfl

/-! ### Deleting isolated common edges -/

/-- The vertices incident with at least one edge of `F`. -/
def edgeSupport {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset V :=
  F.biUnion Sym2.toFinset

/-- An edge is an isolated component of `F` when it is disjoint from every
other edge of `F`. -/
def IsIsolatedEdge {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  e ∈ F ∧ ∀ f ∈ F, f ≠ e → Disjoint e.toFinset f.toFinset

noncomputable def isolatedEdges {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact F.filter (IsIsolatedEdge F)

/-- The overlap core obtained by deleting all isolated-edge components. -/
noncomputable def overlapCore {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact F \ isolatedEdges F

theorem isolatedEdges_subset {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : isolatedEdges F ⊆ F := by
  classical
  exact Finset.filter_subset _ _

theorem overlapCore_union_isolatedEdges {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    overlapCore F ∪ isolatedEdges F = F := by
  classical
  rw [overlapCore, Finset.sdiff_union_of_subset (isolatedEdges_subset F)]

theorem disjoint_overlapCore_isolatedEdges {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    Disjoint (overlapCore F) (isolatedEdges F) := by
  classical
  rw [Finset.disjoint_left]
  intro e he he'
  exact (Finset.mem_sdiff.mp he).2 he'

theorem isolatedEdges_pairwiseDisjoint {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    ((isolatedEdges F : Finset (Sym2 V)) : Set (Sym2 V)).PairwiseDisjoint
      Sym2.toFinset := by
  classical
  intro e he f hf hef
  simp only [isolatedEdges, Finset.mem_coe, Finset.mem_filter] at he hf
  exact he.2.2 f hf.1 hef.symm

theorem edgeSupport_disjoint_core_isolated {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    Disjoint (edgeSupport (overlapCore F)) (edgeSupport (isolatedEdges F)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvCore hvIso
  simp only [edgeSupport, Finset.mem_biUnion] at hvCore hvIso
  obtain ⟨e, heCore, hve⟩ := hvCore
  obtain ⟨f, hfIso, hvf⟩ := hvIso
  have hef : e ≠ f := by
    intro h
    subst f
    exact Finset.disjoint_left.mp (disjoint_overlapCore_isolatedEdges F) heCore hfIso
  have hf := (Finset.mem_filter.mp hfIso).2.2 e
    ((Finset.mem_sdiff.mp heCore).1) hef
  exact (Finset.disjoint_left.mp hf) hvf hve

theorem edgeSupport_isolatedEdges_card {V : Type*} [DecidableEq V]
    {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (edgeSupport (isolatedEdges F)).card = 2 * (isolatedEdges F).card := by
  classical
  rw [edgeSupport, Finset.card_biUnion (isolatedEdges_pairwiseDisjoint F)]
  calc
    (∑ e ∈ isolatedEdges F, e.toFinset.card) =
        ∑ _e ∈ isolatedEdges F, 2 := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Sym2.card_toFinset_of_not_isDiag]
          exact hdiag e (isolatedEdges_subset F he)
    _ = 2 * (isolatedEdges F).card := by simp [mul_comm]

/-! ## Asymptotic arithmetic for the cube -/

theorem abs_sqrt_three_div_two_lt_one :
    |Real.sqrt 3 / 2| < (1 : ℝ) := by
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))]
  rw [div_lt_one (by norm_num)]
  exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- Every fixed polynomial is dominated by the geometric factor
`(√3 / 2)^d`. -/
theorem polynomial_mul_sqrt_three_div_two_pow_tendsto_zero (k : ℕ) :
    Tendsto (fun d : ℕ ↦ (d : ℝ) ^ k * (Real.sqrt 3 / 2) ^ d)
      atTop (nhds 0) := by
  have h := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) k (r₁ := Real.sqrt 3 / 2) (r₂ := 1)
      abs_sqrt_three_div_two_lt_one
  simpa using h.tendsto_div_nhds_zero

theorem three_pow_half_le_sqrt_three_pow (m : ℕ) :
    (3 : ℝ) ^ (m / 2) ≤ (Real.sqrt 3) ^ m := by
  have hsquare : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  obtain hmod | hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  · have hm : m = 2 * (m / 2) := by omega
    rw [hm, pow_mul, hsquare]
    norm_num
  · have hm : m = 2 * (m / 2) + 1 := by omega
    rw [hm, pow_add, pow_mul, hsquare, pow_one]
    rw [show (2 * (m / 2) + 1) / 2 = m / 2 by omega]
    exact le_mul_of_one_le_right
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (m / 2)) hsqrt

/-! ## Fixed-layer inclusion probabilities -/

/-- The probability that `k` prescribed edges occur in an `M`-edge subset
of an `N`-edge universe, written as a falling product. -/
noncomputable def fallingProbability (N M k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k,
    ((M - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)

theorem choose_ratio_eq_fallingProbability {N M k : ℕ}
    (hkM : k ≤ M) (hMN : M ≤ N) :
    (Nat.choose (N - k) (M - k) : ℝ) / Nat.choose N M =
      fallingProbability N M k := by
  have hMkNk : M - k ≤ N - k := Nat.sub_le_sub_right hMN k
  have hMN' : N - M = (N - k) - (M - k) := by omega
  rw [Nat.cast_choose ℝ hMkNk, Nat.cast_choose ℝ hMN]
  rw [hMN']
  have hMfac : (M.factorial : ℝ) =
      ((M - k).factorial : ℝ) * (M.descFactorial k : ℝ) := by
    norm_cast
    exact (Nat.factorial_mul_descFactorial hkM).symm
  have hNfac : (N.factorial : ℝ) =
      ((N - k).factorial : ℝ) * (N.descFactorial k : ℝ) := by
    norm_cast
    exact (Nat.factorial_mul_descFactorial (hkM.trans hMN)).symm
  rw [hMfac, hNfac]
  field_simp
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  simp only [Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  rfl

theorem fallingProbability_add (N M k j : ℕ) :
    fallingProbability N M (k + j) =
      fallingProbability N M k *
        fallingProbability (N - k) (M - k) j := by
  simp [fallingProbability, Finset.prod_range_add, Nat.sub_sub,
    div_eq_mul_inv]

/-- The factor recovered when `j` common edges reduce a union of size `k`
to size `k-j`. -/
noncomputable def recoveryProbability (N M k j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    ((N - ((k - j) + i) : ℕ) : ℝ) /
      ((M - ((k - j) + i) : ℕ) : ℝ)

theorem fallingProbability_sub_eq_mul_recovery {N M k j : ℕ}
    (hj : j ≤ k) (hkM : k ≤ M) (hMN : M ≤ N) :
    fallingProbability N M (k - j) =
      fallingProbability N M k * recoveryProbability N M k j := by
  have hq : k - j + j = k := Nat.sub_add_cancel hj
  have hpos :
      0 < fallingProbability (N - (k - j)) (M - (k - j)) j := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    apply div_pos <;> norm_cast <;> omega
  have hadd := fallingProbability_add N M (k - j) j
  rw [hq] at hadd
  have hinv :
      (fallingProbability (N - (k - j)) (M - (k - j)) j)⁻¹ =
        recoveryProbability N M k j := by
    rw [fallingProbability, recoveryProbability, Finset.prod_div_distrib,
      inv_div]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    congr 2 <;> omega
  rw [← hinv]
  calc
    fallingProbability N M (k - j) =
        fallingProbability N M (k - j) * 1 := by ring
    _ = fallingProbability N M (k - j) *
        (fallingProbability (N - (k - j)) (M - (k - j)) j *
          (fallingProbability (N - (k - j))
            (M - (k - j)) j)⁻¹) := by
              rw [mul_inv_cancel₀ (ne_of_gt hpos)]
    _ = fallingProbability N M k *
        (fallingProbability (N - (k - j))
          (M - (k - j)) j)⁻¹ := by
            rw [hadd]
            ring

theorem sub_div_sub_le_sub_div_sub {N M k r : ℕ}
    (hrk : r ≤ k) (hkM : k < M) (hMN : M ≤ N) :
    ((N - r : ℕ) : ℝ) / (M - r : ℕ) ≤
      ((N - k : ℕ) : ℝ) / (M - k : ℕ) := by
  have hrM : r ≤ M := hrk.trans hkM.le
  have hrN : r ≤ N := hrM.trans hMN
  have hkN : k ≤ N := hkM.le.trans hMN
  have hden : (0 : ℝ) < (M - r : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hrk.trans_lt hkM)
  have hden' : (0 : ℝ) < (M - k : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hkM
  rw [div_le_div_iff₀ hden hden']
  rw [Nat.cast_sub hrN, Nat.cast_sub hkM.le, Nat.cast_sub hkN,
    Nat.cast_sub hrM]
  have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hrkreal : (r : ℝ) ≤ k := by exact_mod_cast hrk
  nlinarith [mul_nonneg (sub_nonneg.mpr hMNreal)
    (sub_nonneg.mpr hrkreal)]

theorem recoveryProbability_le_pow {N M k j : ℕ}
    (hj : j ≤ k) (hkM : k < M) (hMN : M ≤ N) :
    recoveryProbability N M k j ≤
      (((N - k : ℕ) : ℝ) / (M - k : ℕ)) ^ j := by
  rw [recoveryProbability]
  have hconst :
      (∏ _i ∈ Finset.range j,
        ((N - k : ℕ) : ℝ) / (M - k : ℕ)) =
      (((N - k : ℕ) : ℝ) / (M - k : ℕ)) ^ j := by
        simp [div_pow]
  rw [← hconst]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    simp only [Finset.mem_range] at hi
    apply sub_div_sub_le_sub_div_sub
    · omega
    · exact hkM
    · exact hMN

/-- The part of the normalized second moment which is independent of the
number of common edges. -/
noncomputable def backgroundProbability (N M e : ℕ) : ℝ :=
  fallingProbability N M (2 * e) / (fallingProbability N M e) ^ 2

noncomputable def backgroundProduct (N M e : ℕ) : ℝ :=
  ∏ i ∈ Finset.range e,
    (((M - e - i : ℕ) : ℝ) * ((N - i : ℕ) : ℝ)) /
      (((N - e - i : ℕ) : ℝ) * ((M - i : ℕ) : ℝ))

theorem backgroundProbability_eq_product {N M e : ℕ}
    (h2eM : 2 * e ≤ M) (hMN : M ≤ N) :
    backgroundProbability N M e = backgroundProduct N M e := by
  have heM : e ≤ M := by omega
  have heN : e ≤ N := heM.trans hMN
  have hp : 0 < fallingProbability N M e := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    apply div_pos <;> norm_cast <;> omega
  rw [backgroundProbability, show 2 * e = e + e by omega,
    fallingProbability_add]
  rw [pow_two]
  field_simp
  rw [fallingProbability, fallingProbability, backgroundProduct,
    Finset.prod_div_distrib, Finset.prod_div_distrib]
  simp only [Nat.sub_sub]
  have hprod :
      (∏ i ∈ Finset.range e,
        (((M - (e + i) : ℕ) : ℝ) * ((N - i : ℕ) : ℝ)) /
          (((N - (e + i) : ℕ) : ℝ) * ((M - i : ℕ) : ℝ))) =
        ((∏ i ∈ Finset.range e, ((M - (e + i) : ℕ) : ℝ)) *
          ∏ i ∈ Finset.range e, ((N - i : ℕ) : ℝ)) /
          ((∏ i ∈ Finset.range e, ((N - (e + i) : ℕ) : ℝ)) *
          ∏ i ∈ Finset.range e, ((M - i : ℕ) : ℝ)) := by
            rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
              Finset.prod_mul_distrib]
  have hM2 : 0 < (∏ i ∈ Finset.range e,
      ((M - (e + i) : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    exact_mod_cast Nat.sub_pos_of_lt (by omega : e + i < M)
  have hN2 : 0 < (∏ i ∈ Finset.range e,
      ((N - (e + i) : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    exact_mod_cast Nat.sub_pos_of_lt (by omega : e + i < N)
  have hM1 : 0 < (∏ i ∈ Finset.range e,
      ((M - i : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    exact_mod_cast Nat.sub_pos_of_lt (by omega : i < M)
  have hN1 : 0 < (∏ i ∈ Finset.range e,
      ((N - i : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    exact_mod_cast Nat.sub_pos_of_lt (by omega : i < N)
  rw [hprod]
  field_simp [ne_of_gt hM2, ne_of_gt hN2, ne_of_gt hM1, ne_of_gt hN1]

/-- Exact finite form of the negative exponential in Riordan's uniform-model
second moment. -/
theorem backgroundProduct_le_exp {N M e : ℕ}
    (he : 0 < e) (h2eM : 2 * e ≤ M) (hMN : M ≤ N) :
    backgroundProduct N M e ≤
      Real.exp (-((e : ℝ) ^ 2 * (N - M : ℕ) /
        ((N : ℝ) * M))) := by
  have hM : 0 < M := by omega
  have hN : 0 < N := hM.trans_le hMN
  let x₀ : ℝ := (e : ℝ) * (N - M : ℕ) / ((N : ℝ) * M)
  rw [backgroundProduct]
  calc
    (∏ i ∈ Finset.range e,
      (((M - e - i : ℕ) : ℝ) * ((N - i : ℕ) : ℝ)) /
        (((N - e - i : ℕ) : ℝ) * ((M - i : ℕ) : ℝ))) ≤
        ∏ _i ∈ Finset.range e, Real.exp (-x₀) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact div_nonneg
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          · intro i hi
            simp only [Finset.mem_range] at hi
            have heiM : e + i < M := by omega
            have heiN : e + i < N := heiM.trans_le hMN
            have hiM : i < M := by omega
            have hiN : i < N := hiM.trans_le hMN
            let xi : ℝ := (e : ℝ) * (N - M : ℕ) /
              (((N - e - i : ℕ) : ℝ) * (M - i : ℕ))
            have hden :
                0 < (((N - e - i : ℕ) : ℝ) * (M - i : ℕ)) :=
              mul_pos (by exact_mod_cast (show 0 < N - e - i by omega))
                (by exact_mod_cast Nat.sub_pos_of_lt hiM)
            have hden₀ : 0 < (N : ℝ) * M := by positivity
            have hden_le :
                (((N - e - i : ℕ) : ℝ) * (M - i : ℕ)) ≤
                  (N : ℝ) * M := by
              gcongr <;> norm_cast <;> omega
            have hx₀_nonneg : 0 ≤ (e : ℝ) * (N - M : ℕ) := by
              positivity
            have hx : x₀ ≤ xi := by
              dsimp [x₀, xi]
              exact (div_le_div_iff₀ hden₀ hden).2
                (mul_le_mul_of_nonneg_left hden_le hx₀_nonneg)
            have hfactor :
                (((M - e - i : ℕ) : ℝ) * ((N - i : ℕ) : ℝ)) /
                    (((N - e - i : ℕ) : ℝ) * ((M - i : ℕ) : ℝ)) =
                  1 - xi := by
              dsimp [xi]
              rw [div_eq_iff (ne_of_gt hden), sub_mul, one_mul,
                div_mul_cancel₀ _ (ne_of_gt hden)]
              rw [Nat.cast_sub (by omega : i ≤ M - e),
                Nat.cast_sub (by omega : e ≤ M),
                Nat.cast_sub (by omega : i ≤ M),
                Nat.cast_sub (by omega : i ≤ N - e),
                Nat.cast_sub (by omega : e ≤ N),
                Nat.cast_sub (by omega : i ≤ N),
                Nat.cast_sub hMN]
              ring
            rw [hfactor]
            exact (Real.one_sub_le_exp_neg xi).trans
              (Real.exp_le_exp.mpr (neg_le_neg hx))
    _ = Real.exp (-((e : ℝ) ^ 2 * (N - M : ℕ) /
        ((N : ℝ) * M))) := by
      rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
      congr 1
      dsimp [x₀]
      ring

/-! ## The comparison layer -/

/-- Number of possible edges on the `2^d` labelled vertices. -/
def ambientEdgeCount (d : ℕ) : ℕ := (2 ^ d).choose 2

/-- Number of edges of the spanning cube. -/
def cubeEdgeCount (d : ℕ) : ℕ := d * 2 ^ (d - 1)

/-- A layer below the half-edge layer by twice the number of cube edges.
This gap is much larger than the standard deviation but is `o(N)`. -/
def comparisonLayer (d : ℕ) : ℕ :=
  ambientEdgeCount d / 2 - 2 * cubeEdgeCount d

lemma eight_mul_add_one_lt_two_pow {d : ℕ} (hd : 6 ≤ d) :
    8 * d + 1 < 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      rw [pow_succ]
      omega

lemma sixteen_mul_add_one_lt_two_pow {d : ℕ} (hd : 8 ≤ d) :
    16 * d + 1 < 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      rw [pow_succ]
      omega

lemma two_mul_cubeEdgeCount (d : ℕ) :
    2 * cubeEdgeCount d = d * 2 ^ d := by
  cases d with
  | zero => simp [cubeEdgeCount]
  | succ d => simp [cubeEdgeCount, pow_succ]; ring

lemma ambientEdgeCount_eq (d : ℕ) :
    ambientEdgeCount d = 2 ^ d * (2 ^ d - 1) / 2 := by
  rw [ambientEdgeCount, Nat.choose_two_right]

lemma ambientEdgeCount_eq_mul {d : ℕ} (hd : 0 < d) :
    ambientEdgeCount d = 2 ^ (d - 1) * (2 ^ d - 1) := by
  rw [ambientEdgeCount, Nat.choose_two_right]
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  calc
    (2 ^ d * (2 ^ d - 1)) / 2 =
        (2 ^ (d - 1) * 2 * (2 ^ d - 1)) / 2 := by rw [hpow]
    _ = 2 * (2 ^ (d - 1) * (2 ^ d - 1)) / 2 := by ring
    _ = _ := by simp

lemma ambientEdgeCount_div_two_eq {d : ℕ} (hd : 2 ≤ d) :
    ambientEdgeCount d / 2 = 2 ^ (d - 2) * (2 ^ d - 1) := by
  rw [ambientEdgeCount_eq_mul (by omega)]
  have hpow : 2 ^ (d - 1) = 2 ^ (d - 2) * 2 := by
    conv_lhs => rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  calc
    (2 ^ (d - 1) * (2 ^ d - 1)) / 2 =
        (2 ^ (d - 2) * 2 * (2 ^ d - 1)) / 2 := by rw [hpow]
    _ = 2 * (2 ^ (d - 2) * (2 ^ d - 1)) / 2 := by ring
    _ = _ := by simp

lemma comparisonLayer_conditions {d : ℕ} (hd : 8 ≤ d) :
    2 * cubeEdgeCount d < comparisonLayer d ∧
      comparisonLayer d ≤ ambientEdgeCount d := by
  have hn := sixteen_mul_add_one_lt_two_pow hd
  have hmain : 4 * (d * 2 ^ d) < ambientEdgeCount d / 2 := by
    rw [ambientEdgeCount_div_two_eq (by omega)]
    have hpow : 4 * 2 ^ (d - 2) = 2 ^ d := by
      calc
        4 * 2 ^ (d - 2) = 2 ^ (d - 2) * 2 ^ 2 := by norm_num; ring
        _ = 2 ^ ((d - 2) + 2) := by rw [pow_add]
        _ = 2 ^ d := by congr 1; omega
    have hx : 0 < 2 ^ (d - 2) := by positivity
    have hsmall : 16 * d < 2 ^ d - 1 := by omega
    calc
      4 * (d * 2 ^ d) = (16 * d) * 2 ^ (d - 2) := by rw [← hpow]; ring
      _ < (2 ^ d - 1) * 2 ^ (d - 2) :=
        Nat.mul_lt_mul_of_pos_right hsmall hx
      _ = _ := by ring
  constructor
  · rw [comparisonLayer, two_mul_cubeEdgeCount]
    omega
  · exact (Nat.sub_le _ _).trans (Nat.div_le_self _ _)

lemma cubeEdgeCount_pos {d : ℕ} (hd : 0 < d) :
    0 < cubeEdgeCount d := by
  simp [cubeEdgeCount, hd]

/-! ## Monotonicity between uniform edge-count layers -/

noncomputable def upwardLayer [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) :
    Finset (Finset α) := by
  classical
  exact (U.powersetCard k).filter P

noncomputable def upPairs [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) :=
  (upwardLayer U P k).sigma fun S => U \ S

noncomputable def downPairs [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) :=
  (upwardLayer U P (k + 1)).sigma fun T => T

theorem card_upPairs [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    {k : ℕ} (hk : k ≤ U.card) :
    (upPairs U P k).card = (upwardLayer U P k).card * (U.card - k) := by
  classical
  rw [upPairs, Finset.card_sigma]
  calc
    (∑ S ∈ upwardLayer U P k, (U \ S).card) =
        ∑ _S ∈ upwardLayer U P k, (U.card - k) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hSpow := (Finset.mem_filter.mp hS).1
          have hsub := (Finset.mem_powersetCard.mp hSpow).1
          have hcard := (Finset.mem_powersetCard.mp hSpow).2
          rw [Finset.card_sdiff_of_subset hsub, hcard]
    _ = _ := by simp

theorem card_downPairs [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    (k : ℕ) :
    (downPairs U P k).card = (upwardLayer U P (k + 1)).card * (k + 1) := by
  classical
  rw [downPairs, Finset.card_sigma]
  calc
    (∑ T ∈ upwardLayer U P (k + 1), T.card) =
        ∑ _T ∈ upwardLayer U P (k + 1), (k + 1) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    _ = _ := by simp

theorem upwardLayer_mul_card_sub_le_succ
    [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃S T : Finset α⦄, S ⊆ T → P S → P T)
    {k : ℕ} (hk : k < U.card) :
    (upwardLayer U P k).card * (U.card - k) ≤
      (upwardLayer U P (k + 1)).card * (k + 1) := by
  classical
  let f : ((_S : Finset α) × α) → ((_T : Finset α) × α) :=
    fun x => ⟨insert x.2 x.1, x.2⟩
  have hmaps : Set.MapsTo f (upPairs U P k) (downPairs U P k) := by
    intro x hx
    change x ∈ upPairs U P k at hx
    change f x ∈ downPairs U P k
    rw [upPairs, Finset.mem_sigma] at hx
    rw [downPairs, Finset.mem_sigma]
    rcases x with ⟨S, e⟩
    dsimp [f]
    simp only [upwardLayer, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_sdiff] at hx ⊢
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.insert_subset hx.2.1 hx.1.1.1
    · simp [hx.1.1.2, hx.2.2]
    · exact hP (Finset.subset_insert _ _) hx.1.2
    · exact Finset.mem_insert_self _ _
  have hinj : Set.InjOn f (upPairs U P k) := by
    intro x hx y hy heq
    change x ∈ upPairs U P k at hx
    change y ∈ upPairs U P k at hy
    rw [upPairs, Finset.mem_sigma] at hx hy
    rcases x with ⟨S, e⟩
    rcases y with ⟨T, f'⟩
    dsimp [f] at heq
    simp only [upwardLayer, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_sdiff] at hx hy
    have hef : e = f' := by exact congr_arg Sigma.snd heq
    subst f'
    have hST : insert e S = insert e T := by exact congr_arg Sigma.fst heq
    have herase := congr_arg (Finset.erase · e) hST
    simp [hx.2.2, hy.2.2] at herase
    subst T
    rfl
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [card_upPairs U P hk.le, card_downPairs] at hcard
  exact hcard

noncomputable def upwardLayerProbability [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) : ℝ :=
  (upwardLayer U P k).card / Nat.choose U.card k

theorem upwardLayerProbability_le_succ
    [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃S T : Finset α⦄, S ⊆ T → P S → P T)
    {k : ℕ} (hk : k < U.card) :
    upwardLayerProbability U P k ≤ upwardLayerProbability U P (k + 1) := by
  classical
  have hcount := upwardLayer_mul_card_sub_le_succ U P hP hk
  have hchoose := Nat.choose_succ_right_eq U.card k
  have hC : (0 : ℝ) < Nat.choose U.card k := by
    exact_mod_cast Nat.choose_pos hk.le
  have hD : (0 : ℝ) < Nat.choose U.card (k + 1) := by
    exact_mod_cast Nat.choose_pos hk
  have hx : (0 : ℝ) < ((U.card - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hcount' :
      ((upwardLayer U P k).card : ℝ) * ((U.card - k : ℕ) : ℝ) ≤
        ((upwardLayer U P (k + 1)).card : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hchoose' :
      (Nat.choose U.card (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (Nat.choose U.card k : ℝ) * ((U.card - k : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  rw [upwardLayerProbability, upwardLayerProbability,
    div_le_div_iff₀ hC hD]
  calc
    ((upwardLayer U P k).card : ℝ) * Nat.choose U.card (k + 1) =
        (((upwardLayer U P k).card : ℝ) * ((U.card - k : ℕ) : ℝ)) *
          (Nat.choose U.card (k + 1) : ℝ) / ((U.card - k : ℕ) : ℝ) := by
            field_simp
    _ ≤ (((upwardLayer U P (k + 1)).card : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          (Nat.choose U.card (k + 1) : ℝ) / ((U.card - k : ℕ) : ℝ) := by
            gcongr
    _ = ((upwardLayer U P (k + 1)).card : ℝ) *
          Nat.choose U.card k := by
            rw [mul_assoc, mul_comm ((k + 1 : ℕ) : ℝ), hchoose']
            field_simp

theorem upwardLayerProbability_mono
    [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃S T : Finset α⦄, S ⊆ T → P S → P T)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ U.card) :
    upwardLayerProbability U P k ≤ upwardLayerProbability U P l := by
  classical
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih =>
      exact ih (Nat.le_of_succ_le hl) |>.trans
        (upwardLayerProbability_le_succ U P hP (Nat.lt_of_succ_le hl))

theorem graphOfEdges_mono {V : Type*} [DecidableEq V]
    {S T : Finset (Sym2 V)} (hST : S ⊆ T) :
    graphOfEdges S ≤ graphOfEdges T := by
  intro v w hvw
  rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj] at hvw ⊢
  exact ⟨hST hvw.1, hvw.2⟩

theorem cubeEvent_mono (d : ℕ) {S T : Finset (Sym2 (CubeVertex d))}
    (hST : S ⊆ T) (hS : cubeGraph d ⊑ graphOfEdges S) :
    cubeGraph d ⊑ graphOfEdges T :=
  hS.mono_right (graphOfEdges_mono hST)

theorem fixedSuccessProbability_eq_upwardLayerProbability (d M : ℕ) :
    fixedSuccessProbability d M =
      upwardLayerProbability (allEdges (CubeVertex d))
        (fun S => cubeGraph d ⊑ graphOfEdges S) M := by
  classical
  simp only [fixedSuccessProbability, upwardLayerProbability,
    fixedSuccessCount, upwardLayer, fixedEdgeSamples, card_allEdges,
    card_cubeVertex, Finset.card_powersetCard]

theorem fixedSuccessProbability_mono (d : ℕ) {M K : ℕ}
    (hMK : M ≤ K) (hK : K ≤ ambientEdgeCount d) :
    fixedSuccessProbability d M ≤ fixedSuccessProbability d K := by
  classical
  rw [fixedSuccessProbability_eq_upwardLayerProbability,
    fixedSuccessProbability_eq_upwardLayerProbability]
  apply upwardLayerProbability_mono
  · intro S T hST hS
    exact cubeEvent_mono d hST hS
  · exact hMK
  · simpa [ambientEdgeCount, card_allEdges, card_cubeVertex] using hK

/-! ## The half-edge model is concentrated above the comparison layer -/

/-- Exact variance identity for the cardinality of a uniformly chosen
subset, with denominators cleared: the sum of `(2|S|-|U|)^2` is
`|U| 2^|U|`. -/
theorem sum_powerset_doubled_deviation_sq
    {α : Type*} [DecidableEq α] (U : Finset α) :
    (∑ S ∈ U.powerset,
        ((2 : ℝ) * S.card - U.card) ^ 2) =
      (U.card : ℝ) * 2 ^ U.card := by
  induction U using Finset.induction with
  | empty => simp
  | @insert a U ha ih =>
      rw [Finset.sum_powerset_insert ha]
      simp only [Finset.card_insert_of_notMem ha]
      have hcard (S : Finset α) (hS : S ∈ U.powerset) :
          (insert a S).card = S.card + 1 := by
        rw [Finset.card_insert_of_notMem]
        exact fun haS => ha ((Finset.mem_powerset.mp hS) haS)
      calc
        (∑ S ∈ U.powerset,
            ((2 : ℝ) * S.card - ((U.card + 1 : ℕ) : ℝ)) ^ 2) +
            ∑ S ∈ U.powerset,
              ((2 : ℝ) * (insert a S).card - ((U.card + 1 : ℕ) : ℝ)) ^ 2 =
          ∑ S ∈ U.powerset,
            (2 * ((2 : ℝ) * S.card - U.card) ^ 2 + 2) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro S hS
              rw [hcard S hS]
              push_cast
              ring
        _ = 2 * (∑ S ∈ U.powerset,
              ((2 : ℝ) * S.card - U.card) ^ 2) +
            2 * (U.powerset.card : ℝ) := by
              simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
              simp [mul_comm]
        _ = 2 * ((U.card : ℝ) * 2 ^ U.card) + 2 * 2 ^ U.card := by
              rw [ih, Finset.card_powerset]
              norm_cast
        _ = ((U.card + 1 : ℕ) : ℝ) * 2 ^ (U.card + 1) := by
              push_cast
              rw [pow_succ]
              norm_cast
              ring

noncomputable def lowCardSubsets [DecidableEq α]
    (U : Finset α) (m : ℕ) : Finset (Finset α) := by
  classical
  exact U.powerset.filter fun S => S.card < m

theorem card_lowCardSubsets_mul_sq_le
    {α : Type*} [DecidableEq α] (U : Finset α) {m a : ℕ}
    (hgap : 2 * m + a ≤ U.card) :
    ((lowCardSubsets U m).card : ℝ) * (a : ℝ) ^ 2 ≤
      (U.card : ℝ) * 2 ^ U.card := by
  classical
  calc
    ((lowCardSubsets U m).card : ℝ) * (a : ℝ) ^ 2 =
        ∑ _S ∈ lowCardSubsets U m, (a : ℝ) ^ 2 := by simp
    _ ≤ ∑ S ∈ lowCardSubsets U m,
        ((2 : ℝ) * S.card - U.card) ^ 2 := by
          apply Finset.sum_le_sum
          intro S hS
          have hSm : S.card < m := (Finset.mem_filter.mp hS).2
          have hnat : 2 * S.card + a ≤ U.card := by omega
          have hreal : (2 : ℝ) * S.card + a ≤ U.card := by exact_mod_cast hnat
          nlinarith [sq_nonneg ((2 : ℝ) * S.card - U.card + a)]
    _ ≤ ∑ S ∈ U.powerset,
        ((2 : ℝ) * S.card - U.card) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro S hS hSlow
            positivity
    _ = _ := sum_powerset_doubled_deviation_sq U

/-- Proportion of half-edge samples whose edge count lies below the
comparison layer. -/
noncomputable def lowEdgeProbability (d : ℕ) : ℝ :=
  (lowCardSubsets (allEdges (CubeVertex d)) (comparisonLayer d)).card /
    2 ^ ambientEdgeCount d

lemma comparisonLayer_gap {d : ℕ} (hd : 8 ≤ d) :
    2 * comparisonLayer d + 4 * cubeEdgeCount d ≤ ambientEdgeCount d := by
  have hcond := comparisonLayer_conditions hd
  have hehalf : 2 * cubeEdgeCount d ≤ ambientEdgeCount d / 2 := by
    rw [comparisonLayer] at hcond
    omega
  rw [comparisonLayer, Nat.mul_sub_left_distrib]
  omega

theorem lowEdgeProbability_le_ratio {d : ℕ} (hd : 8 ≤ d) :
    lowEdgeProbability d ≤
      (ambientEdgeCount d : ℝ) / (4 * cubeEdgeCount d : ℕ) ^ 2 := by
  have hU : (allEdges (CubeVertex d)).card = ambientEdgeCount d := by
    simp [ambientEdgeCount, card_allEdges]
  have hcard := card_lowCardSubsets_mul_sq_le
    (allEdges (CubeVertex d)) (m := comparisonLayer d)
      (a := 4 * cubeEdgeCount d) (by simpa [hU] using comparisonLayer_gap hd)
  have he : (0 : ℝ) < (4 * cubeEdgeCount d : ℕ) ^ 2 := by
    exact_mod_cast pow_pos
      (mul_pos (by omega) (cubeEdgeCount_pos (by omega))) 2
  have hpow : (0 : ℝ) < 2 ^ ambientEdgeCount d := by positivity
  rw [lowEdgeProbability]
  rw [div_le_div_iff₀ hpow he]
  rw [hU] at hcard
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcard

lemma four_mul_cubeEdgeCount (d : ℕ) :
    4 * cubeEdgeCount d = 2 * d * 2 ^ d := by
  rw [show 4 * cubeEdgeCount d = 2 * (2 * cubeEdgeCount d) by ring,
    two_mul_cubeEdgeCount]
  ring

theorem ambient_div_four_cube_sq_le_inv_sq {d : ℕ} (hd : 0 < d) :
    (ambientEdgeCount d : ℝ) / (4 * cubeEdgeCount d : ℕ) ^ 2 ≤
      1 / (d : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : (ambientEdgeCount d : ℝ) ≤ (2 ^ d : ℕ) ^ 2 := by
    norm_cast
    rw [ambientEdgeCount_eq]
    exact Nat.div_le_of_le_mul (by nlinarith [Nat.sub_le (2 ^ d) 1])
  have heq : ((4 * cubeEdgeCount d : ℕ) : ℝ) =
      2 * (d : ℝ) * (2 ^ d : ℕ) := by
    norm_cast
    exact four_mul_cubeEdgeCount d
  rw [heq]
  rw [div_le_div_iff₀ (sq_pos_of_pos (by positivity)) (sq_pos_of_pos hdR)]
  nlinarith [sq_nonneg ((d : ℝ) * (2 ^ d : ℕ))]

theorem lowEdgeProbability_le_inv_sq {d : ℕ} (hd : 8 ≤ d) :
    lowEdgeProbability d ≤ 1 / (d : ℝ) ^ 2 :=
  (lowEdgeProbability_le_ratio hd).trans
    (ambient_div_four_cube_sq_le_inv_sq (by omega))

theorem lowEdgeProbability_tendsto_zero :
    Tendsto lowEdgeProbability atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun d =>
      div_nonneg (Nat.cast_nonneg _) (by positivity)
  · filter_upwards [eventually_ge_atTop 8] with d hd
    exact lowEdgeProbability_le_inv_sq hd
  · simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
          tendsto_natCast_atTop_atTop)

/-- Number of labelled host graphs which contain a copy of `Q_d`. -/
noncomputable def successCount (d : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph (CubeVertex d))).filter
    fun G ↦ cubeGraph d ⊑ G).card

/-- Exact probability that `G(2^d, 1/2)` contains `Q_d`.

Every labelled simple graph has the same probability in the independent
half-edge model, so this finite ratio is the binomial random-graph
probability without any measure-theoretic encoding choices. -/
noncomputable def successProbability (d : ℕ) : ℝ :=
  (successCount d : ℝ) / (Fintype.card (SimpleGraph (CubeVertex d)) : ℝ)

theorem successProbability_eq (d : ℕ) :
    successProbability d =
      (successCount d : ℝ) / (2 ^ ((2 ^ d).choose 2) : ℝ) := by
  rw [successProbability, card_simpleGraph, card_cubeVertex]
  norm_num

theorem successProbability_nonneg (d : ℕ) : 0 ≤ successProbability d := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem successProbability_le_one (d : ℕ) : successProbability d ≤ 1 := by
  classical
  rw [successProbability]
  apply (div_le_one (by positivity)).2
  norm_cast
  unfold successCount
  exact Finset.card_filter_le _ _

/-! ## Exact transfer from graphs to edge subsets -/

noncomputable def finiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact (allEdges V).filter fun e => e ∈ G.edgeSet

theorem finiteEdges_subset_allEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : finiteEdges G ⊆ allEdges V := by
  classical
  exact Finset.filter_subset _ _

theorem graphOfEdges_finiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : graphOfEdges (finiteEdges G) = G := by
  classical
  ext v w
  simp [graphOfEdges, finiteEdges, allEdges, SimpleGraph.edgeSet_top]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨G.ne_of_adj h, h⟩, G.ne_of_adj h⟩⟩

theorem finiteEdges_graphOfEdges {V : Type*} [Fintype V] [DecidableEq V]
    {S : Finset (Sym2 V)} (hS : S ⊆ allEdges V) :
    finiteEdges (graphOfEdges S) = S := by
  classical
  ext e
  simp only [finiteEdges, Finset.mem_filter]
  constructor
  · rintro ⟨heAll, heGraph⟩
    have hpair : e ∈ S ∧ ¬e.IsDiag := by
      simpa [graphOfEdges] using heGraph
    exact hpair.1
  · intro he
    have hnd : ¬e.IsDiag := by
      have htop := hS he
      simpa [allEdges, SimpleGraph.mem_edgeFinset,
        SimpleGraph.edgeSet_top] using htop
    exact ⟨hS he, by simp [graphOfEdges, he, hnd]⟩

noncomputable def graphEdgeFinsetEquiv (V : Type*) [Fintype V] [DecidableEq V] :
    SimpleGraph V ≃ {S : Finset (Sym2 V) // S ⊆ allEdges V} := by
  classical
  refine
    { toFun := fun G => ⟨finiteEdges G, ?_⟩
      invFun := fun S => graphOfEdges S
      left_inv := ?_
      right_inv := ?_ }
  · exact finiteEdges_subset_allEdges G
  · exact graphOfEdges_finiteEdges
  · intro S
    apply Subtype.ext
    exact finiteEdges_graphOfEdges S.property

noncomputable def successGraphEquiv (d : ℕ) :
    {G : SimpleGraph (CubeVertex d) // cubeGraph d ⊑ G} ≃
      {S : {S : Finset (Sym2 (CubeVertex d)) //
        S ⊆ allEdges (CubeVertex d)} // cubeGraph d ⊑ graphOfEdges S.1} := by
  classical
  apply Equiv.subtypeEquiv (graphEdgeFinsetEquiv (CubeVertex d))
  intro G
  change (cubeGraph d ⊑ G) ↔ cubeGraph d ⊑ graphOfEdges (finiteEdges G)
  rw [graphOfEdges_finiteEdges]

noncomputable def successEdgeSetSubtypeEquiv (d : ℕ) :
    {S : {S : Finset (Sym2 (CubeVertex d)) //
        S ⊆ allEdges (CubeVertex d)} // cubeGraph d ⊑ graphOfEdges S.1} ≃
      {S // S ∈ (allEdges (CubeVertex d)).powerset ∧
        cubeGraph d ⊑ graphOfEdges S} where
  toFun S := ⟨S.1.1, Finset.mem_powerset.mpr S.1.2, S.2⟩
  invFun S := ⟨⟨S.1, (Finset.mem_powerset.mp S.2.1)⟩, S.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def successEdgeSets (d : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (allEdges (CubeVertex d)).powerset.filter fun S =>
    cubeGraph d ⊑ graphOfEdges S

noncomputable def successGraphs (d : ℕ) :
    Finset (SimpleGraph (CubeVertex d)) := by
  classical
  exact (Finset.univ : Finset (SimpleGraph (CubeVertex d))).filter fun G =>
    cubeGraph d ⊑ G

noncomputable def successGraphFilterEquiv (d : ℕ) :
    ↥(successGraphs d) ≃
      {G : SimpleGraph (CubeVertex d) // cubeGraph d ⊑ G} := by
  classical
  refine
    { toFun := fun G => ⟨G.1, (Finset.mem_filter.mp G.2).2⟩
      invFun := fun G => ⟨G.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def successEdgeFilterEquiv (d : ℕ) :
    ↥(successEdgeSets d) ≃
      {S // S ∈ (allEdges (CubeVertex d)).powerset ∧
        cubeGraph d ⊑ graphOfEdges S} := by
  classical
  refine
    { toFun := fun S => ⟨S.1, Finset.mem_filter.mp S.2⟩
      invFun := fun S => ⟨S.1, Finset.mem_filter.mpr S.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem successCount_eq_successEdgeSet_card (d : ℕ) :
    successCount d = (successEdgeSets d).card := by
  classical
  calc
    successCount d = Fintype.card ↥(successGraphs d) := by
      change (successGraphs d).card = Fintype.card ↥(successGraphs d)
      exact (Fintype.card_coe _).symm
    _ = Fintype.card ↥(successEdgeSets d) := Fintype.card_congr
      ((successGraphFilterEquiv d).trans
        ((successGraphEquiv d).trans
          ((successEdgeSetSubtypeEquiv d).trans (successEdgeFilterEquiv d).symm)))
    _ = (successEdgeSets d).card := Fintype.card_coe _

theorem successEdgeSets_card_eq_sum_layers (d : ℕ) :
    (successEdgeSets d).card =
      ∑ K ∈ Finset.range (ambientEdgeCount d + 1), fixedSuccessCount d K := by
  classical
  have hmaps : ∀ S ∈ successEdgeSets d,
      S.card ∈ Finset.range (ambientEdgeCount d + 1) := by
    intro S hS
    have hpow : S ∈ (allEdges (CubeVertex d)).powerset :=
      (Finset.mem_filter.mp hS).1
    have hsub := Finset.mem_powerset.mp hpow
    rw [Finset.mem_range, Nat.lt_succ_iff]
    simpa [ambientEdgeCount, card_allEdges, card_cubeVertex] using
      Finset.card_le_card hsub
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro K hK
  congr 1
  ext S
  simp only [Finset.mem_filter, successEdgeSets, fixedSuccessCount,
    fixedEdgeSamples, Finset.mem_powersetCard]
  aesop

noncomputable def highCardSubsets [DecidableEq α]
    (U : Finset α) (m : ℕ) : Finset (Finset α) := by
  classical
  exact U.powerset.filter fun S => m ≤ S.card

theorem card_highCardSubsets_eq_sum_choose
    {α : Type*} [DecidableEq α] (U : Finset α) (m : ℕ) :
    (highCardSubsets U m).card =
      ∑ K ∈ Finset.Icc m U.card, Nat.choose U.card K := by
  classical
  have hmaps : ∀ S ∈ highCardSubsets U m, S.card ∈ Finset.Icc m U.card := by
    intro S hS
    have hs := Finset.mem_filter.mp hS
    exact Finset.mem_Icc.mpr ⟨hs.2, Finset.card_le_card (Finset.mem_powerset.mp hs.1)⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro K hK
  rw [← Finset.card_powersetCard]
  congr 1
  ext S
  simp only [Finset.mem_filter, highCardSubsets, Finset.mem_powersetCard]
  have hKm : m ≤ K := (Finset.mem_Icc.mp hK).1
  aesop

theorem successEdgeSets_card_ge_fixed_mul_high (d M : ℕ)
    (hM : M ≤ ambientEdgeCount d) :
    (fixedSuccessProbability d M) *
        ((highCardSubsets (allEdges (CubeVertex d)) M).card : ℝ) ≤
      (successEdgeSets d).card := by
  classical
  let N := ambientEdgeCount d
  have hUN : (allEdges (CubeVertex d)).card = N := by
    simp [N, ambientEdgeCount, card_allEdges, card_cubeVertex]
  have hsumSub :
      (∑ K ∈ Finset.Icc M N, (fixedSuccessCount d K : ℝ)) ≤
        ∑ K ∈ Finset.range (N + 1), (fixedSuccessCount d K : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro K hK
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.mem_Icc.mp hK).2
    · intro K hK hKIcc
      positivity
  have hterm (K : ℕ) (hK : K ∈ Finset.Icc M N) :
      fixedSuccessProbability d M * Nat.choose N K ≤ fixedSuccessCount d K := by
    have hMK := (Finset.mem_Icc.mp hK).1
    have hKN := (Finset.mem_Icc.mp hK).2
    have hmono := fixedSuccessProbability_mono d hMK hKN
    have hchoose : (0 : ℝ) < Nat.choose N K := by
      exact_mod_cast Nat.choose_pos hKN
    have heq : fixedSuccessProbability d K * Nat.choose N K =
        fixedSuccessCount d K := by
      rw [fixedSuccessProbability, card_fixedEdgeSamples]
      change (fixedSuccessCount d K : ℝ) / Nat.choose N K * Nat.choose N K = _
      field_simp
    calc
      fixedSuccessProbability d M * Nat.choose N K ≤
          fixedSuccessProbability d K * Nat.choose N K :=
        mul_le_mul_of_nonneg_right hmono hchoose.le
      _ = _ := heq
  calc
    fixedSuccessProbability d M *
        ((highCardSubsets (allEdges (CubeVertex d)) M).card : ℝ) =
      ∑ K ∈ Finset.Icc M N,
        fixedSuccessProbability d M * Nat.choose N K := by
          rw [card_highCardSubsets_eq_sum_choose, hUN]
          simp only [Nat.cast_sum]
          rw [Finset.mul_sum]
    _ ≤ ∑ K ∈ Finset.Icc M N, (fixedSuccessCount d K : ℝ) := by
      exact Finset.sum_le_sum fun K hK => hterm K hK
    _ ≤ ∑ K ∈ Finset.range (N + 1), (fixedSuccessCount d K : ℝ) := hsumSub
    _ = (successEdgeSets d).card := by
      exact_mod_cast (successEdgeSets_card_eq_sum_layers d).symm

theorem card_highCardSubsets_add_lowCardSubsets
    {α : Type*} [DecidableEq α] (U : Finset α) (m : ℕ) :
    (highCardSubsets U m).card + (lowCardSubsets U m).card = 2 ^ U.card := by
  classical
  have hdis : Disjoint (highCardSubsets U m) (lowCardSubsets U m) := by
    rw [Finset.disjoint_left]
    intro S hhigh hlow
    have hh := (Finset.mem_filter.mp hhigh).2
    have hl := (Finset.mem_filter.mp hlow).2
    omega
  have hunion : highCardSubsets U m ∪ lowCardSubsets U m = U.powerset := by
    ext S
    simp only [highCardSubsets, lowCardSubsets, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      exact if hm : m ≤ S.card then Or.inl ⟨h, hm⟩ else Or.inr ⟨h, by omega⟩
  rw [← Finset.card_union_of_disjoint hdis, hunion, Finset.card_powerset]

theorem highEdgeRatio_eq_one_sub_low (d : ℕ) :
    ((highCardSubsets (allEdges (CubeVertex d)) (comparisonLayer d)).card : ℝ) /
        2 ^ ambientEdgeCount d =
      1 - lowEdgeProbability d := by
  have hcard := card_highCardSubsets_add_lowCardSubsets
    (allEdges (CubeVertex d)) (comparisonLayer d)
  have hU : (allEdges (CubeVertex d)).card = ambientEdgeCount d := by
    simp [ambientEdgeCount, card_allEdges, card_cubeVertex]
  rw [hU] at hcard
  rw [lowEdgeProbability]
  have hpow : (0 : ℝ) < 2 ^ ambientEdgeCount d := by positivity
  rw [div_eq_iff (ne_of_gt hpow), sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hpow)]
  have hcardR :
      ((highCardSubsets (allEdges (CubeVertex d)) (comparisonLayer d)).card : ℝ) +
        ((lowCardSubsets (allEdges (CubeVertex d)) (comparisonLayer d)).card : ℝ) =
          ((2 ^ ambientEdgeCount d : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hpcast : ((2 ^ ambientEdgeCount d : ℕ) : ℝ) =
      (2 : ℝ) ^ ambientEdgeCount d := by norm_cast
  nlinarith

theorem successProbability_eq_successEdgeRatio (d : ℕ) :
    successProbability d =
      (successEdgeSets d).card / 2 ^ ambientEdgeCount d := by
  rw [successProbability_eq, successCount_eq_successEdgeSet_card]
  simp [ambientEdgeCount]

theorem fixed_mul_one_sub_low_le_successProbability (d : ℕ) :
    fixedSuccessProbability d (comparisonLayer d) * (1 - lowEdgeProbability d) ≤
      successProbability d := by
  have hM : comparisonLayer d ≤ ambientEdgeCount d :=
    (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  have hcount := successEdgeSets_card_ge_fixed_mul_high d (comparisonLayer d) hM
  have hpow : (0 : ℝ) < 2 ^ ambientEdgeCount d := by positivity
  rw [successProbability_eq_successEdgeRatio, ← highEdgeRatio_eq_one_sub_low]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_right hcount (inv_nonneg.mpr hpow.le)

/-! ## Reduction of the uniform-layer second moment to an overlap average -/

/-- The normalized second moment of the labelled cube-copy count in one
uniform edge-count layer. -/
noncomputable def fixedMomentRatio (d M : ℕ) : ℝ :=
  ((fixedEdgeSamples d M).card : ℝ) *
      (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ) ^ 2) /
    (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ)) ^ 2

theorem one_le_fixedMomentRatio (d M : ℕ)
    (hfirst : 0 < ∑ S ∈ fixedEdgeSamples d M,
      (copyMultiplicity d S : ℝ)) :
    1 ≤ fixedMomentRatio d M := by
  rw [fixedMomentRatio, le_div_iff₀ (sq_pos_of_pos hfirst)]
  simpa [mul_comm] using
    (sq_sum_le_card_mul_sum_sq (s := fixedEdgeSamples d M)
      (f := fun S ↦ (copyMultiplicity d S : ℝ)))

theorem one_div_fixedMomentRatio_le_fixedSuccessProbability (d M : ℕ)
    (hsamples : 0 < (fixedEdgeSamples d M).card)
    (hfirst : 0 < ∑ S ∈ fixedEdgeSamples d M,
      (copyMultiplicity d S : ℝ))
    (hsecond : 0 < ∑ S ∈ fixedEdgeSamples d M,
      (copyMultiplicity d S : ℝ) ^ 2) :
    1 / fixedMomentRatio d M ≤ fixedSuccessProbability d M := by
  have hA : (0 : ℝ) < (fixedEdgeSamples d M).card := by
    exact_mod_cast hsamples
  have hid :
      1 / fixedMomentRatio d M =
        (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ)) ^ 2 /
          ((fixedEdgeSamples d M).card *
            ∑ S ∈ fixedEdgeSamples d M,
              (copyMultiplicity d S : ℝ) ^ 2) := by
    rw [fixedMomentRatio]
    field_simp
  rw [hid]
  exact moment_ratio_le_fixedSuccessProbability d M hsamples hsecond

/-- The exponential overlap moment of two independently and uniformly
relabelled cube copies. -/
noncomputable def overlapAverage (d : ℕ) (c : ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (CubeVertex d),
      ∑ τ : Equiv.Perm (CubeVertex d), c ^ overlapCard d σ τ) /
    (Fintype.card (Equiv.Perm (CubeVertex d)) : ℝ) ^ 2

/-- Exact finite reduction of the fixed-layer second moment.  The first
factor is the overlap-independent background product; each recovered common
edge costs at most the displayed factor in the overlap generating function. -/
theorem fixedMomentRatio_le_background_mul_overlapAverage
    (d M : ℕ)
    (he : 0 < d * 2 ^ (d - 1))
    (h2eM : 2 * (d * 2 ^ (d - 1)) < M)
    (hMN : M ≤ (2 ^ d).choose 2) :
    fixedMomentRatio d M ≤
      backgroundProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)) *
        overlapAverage d
          ((((2 ^ d).choose 2 - 2 * (d * 2 ^ (d - 1)) : ℕ) : ℝ) /
            (M - 2 * (d * 2 ^ (d - 1)) : ℕ)) := by
  classical
  let N := (2 ^ d).choose 2
  let e := d * 2 ^ (d - 1)
  let P := Fintype.card (Equiv.Perm (CubeVertex d))
  let p₁ := fallingProbability N M e
  let c : ℝ := ((N - 2 * e : ℕ) : ℝ) / (M - 2 * e : ℕ)
  have heM : e ≤ M := by omega
  have heN : e ≤ N := heM.trans hMN
  have h2eN : 2 * e ≤ N := h2eM.le.trans hMN
  have hMNchoose : 0 < Nat.choose N M := Nat.choose_pos hMN
  have hP : 0 < P := Fintype.card_pos
  have hp₁ : 0 < p₁ := by
    dsimp [p₁]
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_range] at hi
    apply div_pos <;> norm_cast <;> omega
  have hfirstNat := sum_copyMultiplicity d M heM
  have hfirst :
      (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ)) =
        (P : ℝ) * Nat.choose (N - e) (M - e) := by
    dsimp [P, N, e]
    exact_mod_cast hfirstNat
  have hchooseOne :
      (Nat.choose (N - e) (M - e) : ℝ) =
        Nat.choose N M * p₁ := by
    have h := choose_ratio_eq_fallingProbability heM hMN
    dsimp [p₁] at h ⊢
    rw [div_eq_iff (by positivity : (Nat.choose N M : ℝ) ≠ 0)] at h
    nlinarith
  have hsecondNat := sum_sq_copyMultiplicity d M h2eM.le
  have hsecond :
      (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ) ^ 2) =
        (Nat.choose N M : ℝ) *
          ∑ σ : Equiv.Perm (CubeVertex d),
            ∑ τ : Equiv.Perm (CubeVertex d),
              fallingProbability N M (2 * e - overlapCard d σ τ) := by
    have hcast :
        (∑ S ∈ fixedEdgeSamples d M, (copyMultiplicity d S : ℝ) ^ 2) =
          ∑ σ : Equiv.Perm (CubeVertex d),
            ∑ τ : Equiv.Perm (CubeVertex d),
              (Nat.choose
                (N - (cubePattern d σ ∪ cubePattern d τ).card)
                (M - (cubePattern d σ ∪ cubePattern d τ).card) : ℝ) := by
      exact_mod_cast hsecondNat
    rw [hcast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [card_union_cubePattern]
    have hunionM : 2 * e - overlapCard d σ τ ≤ M := by omega
    have hunionN : 2 * e - overlapCard d σ τ ≤ N :=
      hunionM.trans hMN
    have h := choose_ratio_eq_fallingProbability hunionM hMN
    rw [div_eq_iff (by positivity : (Nat.choose N M : ℝ) ≠ 0)] at h
    simpa [N, e, mul_comm] using h
  have hoverlap_le (σ τ : Equiv.Perm (CubeVertex d)) :
      fallingProbability N M (2 * e - overlapCard d σ τ) ≤
        fallingProbability N M (2 * e) * c ^ overlapCard d σ τ := by
    have hj : overlapCard d σ τ ≤ 2 * e := by
      calc
        overlapCard d σ τ ≤ (cubePattern d σ).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = e := card_cubePattern d σ
        _ ≤ 2 * e := by omega
    rw [fallingProbability_sub_eq_mul_recovery hj h2eM.le hMN]
    exact mul_le_mul_of_nonneg_left
      (recoveryProbability_le_pow hj (by omega) hMN)
      (le_of_lt (by
        dsimp [fallingProbability]
        apply Finset.prod_pos
        intro i hi
        simp only [Finset.mem_range] at hi
        apply div_pos <;> norm_cast <;> omega))
  rw [fixedMomentRatio, overlapAverage]
  rw [card_fixedEdgeSamples, hfirst, hchooseOne, hsecond]
  dsimp [N, e, P, p₁, c] at *
  have hsum :
      (∑ σ : Equiv.Perm (CubeVertex d),
        ∑ τ : Equiv.Perm (CubeVertex d),
          fallingProbability ((2 ^ d).choose 2) M
            (2 * (d * 2 ^ (d - 1)) - overlapCard d σ τ)) ≤
        fallingProbability ((2 ^ d).choose 2) M
            (2 * (d * 2 ^ (d - 1))) *
          ∑ σ : Equiv.Perm (CubeVertex d),
            ∑ τ : Equiv.Perm (CubeVertex d),
              ((((2 ^ d).choose 2 - 2 * (d * 2 ^ (d - 1)) : ℕ) : ℝ) /
                (M - 2 * (d * 2 ^ (d - 1)) : ℕ)) ^ overlapCard d σ τ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ hσ
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ hτ ↦ hoverlap_le σ τ
  have hbg :
      fallingProbability ((2 ^ d).choose 2) M
          (2 * (d * 2 ^ (d - 1))) /
        fallingProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)) ^ 2 =
      backgroundProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)) := rfl
  have hchoosepos : (0 : ℝ) < Nat.choose ((2 ^ d).choose 2) M := by
    exact_mod_cast hMNchoose
  have hPpos : (0 : ℝ) < Fintype.card (Equiv.Perm (CubeVertex d)) := by
    exact_mod_cast hP
  calc
    ((Nat.choose ((2 ^ d).choose 2) M : ℝ) *
          ((Nat.choose ((2 ^ d).choose 2) M : ℝ) *
            ∑ σ : Equiv.Perm (CubeVertex d),
              ∑ τ : Equiv.Perm (CubeVertex d),
                fallingProbability ((2 ^ d).choose 2) M
                  (2 * (d * 2 ^ (d - 1)) - overlapCard d σ τ))) /
        ((Fintype.card (Equiv.Perm (CubeVertex d)) : ℝ) *
          ((Nat.choose ((2 ^ d).choose 2) M : ℝ) *
            fallingProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)))) ^ 2 =
      (∑ σ : Equiv.Perm (CubeVertex d),
        ∑ τ : Equiv.Perm (CubeVertex d),
          fallingProbability ((2 ^ d).choose 2) M
            (2 * (d * 2 ^ (d - 1)) - overlapCard d σ τ)) /
        ((Fintype.card (Equiv.Perm (CubeVertex d)) : ℝ) ^ 2 *
          fallingProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)) ^ 2) := by
            field_simp
    _ ≤ (fallingProbability ((2 ^ d).choose 2) M
              (2 * (d * 2 ^ (d - 1))) *
            ∑ σ : Equiv.Perm (CubeVertex d),
              ∑ τ : Equiv.Perm (CubeVertex d),
                ((((2 ^ d).choose 2 - 2 * (d * 2 ^ (d - 1)) : ℕ) : ℝ) /
                  (M - 2 * (d * 2 ^ (d - 1)) : ℕ)) ^ overlapCard d σ τ) /
        ((Fintype.card (Equiv.Perm (CubeVertex d)) : ℝ) ^ 2 *
          fallingProbability ((2 ^ d).choose 2) M (d * 2 ^ (d - 1)) ^ 2) := by
            exact div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by
      rw [mul_div_assoc, ← hbg]
      field_simp

/-! ## Encoding walks in the cube -/

theorem walk_cons_intermediate_eq {V : Type*} {G : SimpleGraph V}
    {u v w z : V} (huw : G.Adj u w) (huz : G.Adj u z)
    (p : G.Walk w v) (q : G.Walk z v)
    (h : Walk.cons huw p = Walk.cons huz q) : w = z := by
  have hs := congr_arg (fun r : G.Walk u v => r.support) h
  simp only [Walk.support_cons] at hs
  have htail : p.support = q.support := (List.cons.inj hs).2
  calc
    w = p.support.head p.support_ne_nil := p.head_support.symm
    _ = q.support.head q.support_ne_nil := by simpa [htail]
    _ = z := q.head_support

/-- A length-`l` cube walk from a fixed start has `d ^ l` possible endpoints
and paths in total. -/
theorem sum_card_finsetWalkLength_cube (d l : ℕ) (u : CubeVertex d) :
    (∑ v : CubeVertex d, ((cubeGraph d).finsetWalkLength l u v).card) = d ^ l := by
  induction l generalizing u with
  | zero =>
      classical
      rw [Finset.sum_eq_single u]
      · simp [SimpleGraph.finsetWalkLength]
      · intro v hv hvu
        simp [SimpleGraph.finsetWalkLength, hvu, Ne.symm hvu]
      · simp
  | succ l ih =>
      simp only [SimpleGraph.finsetWalkLength]
      calc
        (∑ v : CubeVertex d,
            ((Finset.univ.biUnion fun w : (cubeGraph d).neighborSet u =>
              ((cubeGraph d).finsetWalkLength l w v).map
                ⟨fun p => Walk.cons w.property p, fun _ _ h => by
                  cases h
                  rfl⟩)).card) =
            ∑ v : CubeVertex d, ∑ w : (cubeGraph d).neighborSet u,
              ((cubeGraph d).finsetWalkLength l w v).card := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [Finset.card_biUnion]
                · simp
                · intro w hw z hz hwz
                  change Disjoint
                    (((cubeGraph d).finsetWalkLength l (w : CubeVertex d) v).map
                      ⟨fun p => Walk.cons (show (cubeGraph d).Adj u w from w.property) p,
                        fun _ _ h => by cases h; rfl⟩)
                    (((cubeGraph d).finsetWalkLength l (z : CubeVertex d) v).map
                      ⟨fun p => Walk.cons (show (cubeGraph d).Adj u z from z.property) p,
                        fun _ _ h => by cases h; rfl⟩)
                  rw [Finset.disjoint_left]
                  intro p hp hp'
                  simp only [Finset.mem_map] at hp hp'
                  obtain ⟨p₁, hp₁, h₁⟩ := hp
                  obtain ⟨p₂, hp₂, h₂⟩ := hp'
                  subst p
                  have hfirst : (z : CubeVertex d) = (w : CubeVertex d) :=
                    walk_cons_intermediate_eq _ _ _ _ h₂
                  exact hwz (Subtype.ext hfirst.symm)
        _ = ∑ w : (cubeGraph d).neighborSet u,
              ∑ v : CubeVertex d,
                ((cubeGraph d).finsetWalkLength l w v).card := by
              rw [Finset.sum_comm]
        _ = ∑ _w : (cubeGraph d).neighborSet u, d ^ l := by
              apply Finset.sum_congr rfl
              intro w hw
              exact ih w
        _ = d ^ (l + 1) := by
              rw [Finset.sum_const, Finset.card_univ]
              rw [SimpleGraph.card_neighborSet_eq_degree, cube_degree]
              simp [pow_succ, Nat.mul_comm]

/-! ## Closed covering walks in connected graphs -/

theorem connected_exists_covering_closedWalk :
    ∀ n : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected →
        ∃ u : V, ∃ p : G.Walk u u,
          p.support.toFinset = Finset.univ ∧ p.length = 2 * (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V _ _ G _ hcard hconn
      have hnpos : 0 < n := by
        rw [← hcard]
        exact Fintype.card_pos_iff.mpr hconn.nonempty
      by_cases hn : n = 1
      · let u : V := Classical.choice hconn.nonempty
        refine ⟨u, .nil, ?_, by simp [hn]⟩
        apply Finset.eq_univ_of_card
        simpa using (hcard.trans hn).symm
      · have hn2 : 2 ≤ n := by omega
        letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨v, hvconn⟩ :=
          hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
        obtain ⟨z, hzv⟩ := exists_ne v
        have hne : v ≠ z := Ne.symm hzv
        have hdeg : 0 < G.degree v :=
          (hconn.preconnected v z).degree_pos_left hne
        obtain ⟨w, hw⟩ := G.degree_pos_iff_nonempty.mp hdeg
        have hwAdj : G.Adj v w := hw
        let V' : Set V := ({v} : Set V)ᶜ
        have hcard' : Fintype.card V' = n - 1 := by
          change Fintype.card ↑(({v} : Set V)ᶜ) = n - 1
          rw [Fintype.card_compl_set ({v} : Set V)]
          simp [hcard]
        obtain ⟨u', p', hp'supp, hp'len⟩ :=
          ih (n - 1) (by omega) V' (G.induce ({v} : Set V)ᶜ) hcard' hvconn
        have hwne : w ≠ v := hw.ne.symm
        let w' : V' := ⟨w, by simp [V', hwne]⟩
        have hwmem : w' ∈ p'.support := by
          have : w' ∈ p'.support.toFinset := by simp [hp'supp]
          simpa using this
        let pr := p'.rotate w' hwmem
        let q : G.Walk (w : V) w :=
          pr.map (Embedding.induce _).toHom
        let excursion : G.Walk (w : V) w :=
          hwAdj.symm.toWalk.append hwAdj.toWalk
        let p : G.Walk (w : V) w := excursion.append q
        refine ⟨w, p, ?_, ?_⟩
        · ext x
          simp only [p, Walk.support_append, List.toFinset_append,
            Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hx : x = v
          · subst x
            left
            simp [excursion]
          · by_cases hxw : x = w
            · subst x
              left
              simp [excursion]
            · right
              have hx' : (⟨x, by simpa [V'] using hx⟩ : V') ∈ pr.support := by
                rw [Walk.mem_support_rotate_iff]
                have : (⟨x, by simpa [V'] using hx⟩ : V') ∈ p'.support.toFinset := by
                  simp [hp'supp]
                simpa using this
              have hxq : x ∈ q.support := by
                change x ∈ (pr.map (Embedding.induce _).toHom).support
                rw [Walk.support_map]
                exact List.mem_map.mpr
                  ⟨(⟨x, by simpa [V'] using hx⟩ : V'), hx', rfl⟩
              have hcons : w :: q.support.tail = q.support := by
                simpa using List.cons_head_tail q.support_ne_nil
              rw [← hcons] at hxq
              simpa only [List.mem_toFinset] using
                (List.mem_cons.mp hxq).resolve_left hxw
        · have hqLen : q.length = p'.length := by
            change (pr.map (Embedding.induce _).toHom).length = p'.length
            rw [Walk.length_map]
            simp [pr]
          have hexcLen : excursion.length = 2 := by
            change (hwAdj.symm.toWalk.append hwAdj.toWalk).length = 2
            simp
          change (excursion.append q).length = 2 * (n - 1)
          rw [Walk.length_append, hexcLen, hqLen, hp'len]
          omega

/-! ## Finite certificates for component-covering walks -/

/-- A cube walk of a prescribed length, with both endpoints bundled. -/
abbrev CubeWalkLength (d l : ℕ) :=
  Σ u : CubeVertex d, Σ v : CubeVertex d,
    {p : (cubeGraph d).Walk u v // p.length = l}

theorem card_cubeWalkLength (d l : ℕ) :
    Fintype.card (CubeWalkLength d l) = 2 ^ d * d ^ l := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ u : CubeVertex d,
        Fintype.card (Σ v : CubeVertex d,
          {p : (cubeGraph d).Walk u v // p.length = l})) =
      ∑ u : CubeVertex d, ∑ v : CubeVertex d,
        ((cubeGraph d).finsetWalkLength l u v).card := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Fintype.card_sigma]
          apply Finset.sum_congr rfl
          intro v hv
          exact (SimpleGraph.card_set_walk_length_eq (cubeGraph d) u v l)
    _ = ∑ _u : CubeVertex d, d ^ l := by
      apply Finset.sum_congr rfl
      intro u hu
      exact sum_card_finsetWalkLength_cube d l u
    _ = 2 ^ d * d ^ l := by simp [card_cubeVertex]

/-- The walk tuple associated with one integer composition. -/
abbrev CubeWalkTuple (d r : ℕ) (c : Composition r) :=
  ∀ i : Fin c.length, CubeWalkLength d (2 * c.blocksFun i)

theorem card_cubeWalkTuple (d r : ℕ) (c : Composition r) :
    Fintype.card (CubeWalkTuple d r c) =
      (2 ^ d) ^ c.length * d ^ (2 * r) := by
  classical
  rw [Fintype.card_pi]
  simp_rw [card_cubeWalkLength]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_pow_eq_pow_sum]
  simp only [Fintype.card_fin]
  congr 1
  rw [← Finset.mul_sum, c.sum_blocksFun]

/-- All component-covering certificates with total rank `r` and exactly
`k` components. -/
abbrev CubeWalkCoverCertificate (d r k : ℕ) :=
  Σ c : {c : Composition r // c.length = k}, CubeWalkTuple d r c.1

theorem card_cubeWalkCoverCertificate_le (d r k : ℕ) :
    Fintype.card (CubeWalkCoverCertificate d r k) ≤
      2 ^ r * (2 ^ d) ^ k * d ^ (2 * r) := by
  classical
  let C : ℕ := (2 ^ d) ^ k * d ^ (2 * r)
  calc
    Fintype.card (CubeWalkCoverCertificate d r k) =
        ∑ c : {c : Composition r // c.length = k},
          Fintype.card (CubeWalkTuple d r c.1) := by
            rw [Fintype.card_sigma]
    _ = ∑ _c : {c : Composition r // c.length = k}, C := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [card_cubeWalkTuple, c.property]
    _ = Fintype.card {c : Composition r // c.length = k} * C := by
      simp [mul_comm]
    _ ≤ Fintype.card (Composition r) * C := by
      gcongr
      exact Fintype.card_subtype_le _
    _ ≤ 2 ^ r * C := by
      gcongr
      rw [composition_card]
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le r 1)
    _ = _ := by simp [C, mul_assoc]

/-- The union of the vertex supports of a covering certificate. -/
noncomputable def CubeWalkCoverCertificate.support {d r k : ℕ}
    (z : CubeWalkCoverCertificate d r k) : Finset (CubeVertex d) := by
  classical
  exact Finset.univ.biUnion fun i : Fin z.1.1.1.length =>
    z.2 i |>.2.2.1.support.toFinset

noncomputable def walkCoverSupportSets (d r k : ℕ) :
    Finset (Finset (CubeVertex d)) := by
  classical
  exact (Finset.univ : Finset (CubeWalkCoverCertificate d r k)).image
    CubeWalkCoverCertificate.support

theorem card_walkCoverSupportSets_le (d r k : ℕ) :
    (walkCoverSupportSets d r k).card ≤
      2 ^ r * (2 ^ d) ^ k * d ^ (2 * r) := by
  classical
  exact Finset.card_image_le.trans (card_cubeWalkCoverCertificate_le d r k)

end Erdos578

/-! ## Exact permutation fibers for an overlap edge set -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

/-- If `F` is carried into the cube by `σ`, restricting `σ` to the
vertices touched by `F` gives a copy of the graph induced by `F`. -/
noncomputable def permutationCopyOfSubset (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (σ : Equiv.Perm (CubeVertex d))
    (hσ : F ⊆ cubePattern d σ⁻¹) :
    SimpleGraph.Copy
      ((graphOfEdges F).induce (edgeSupport F : Set (CubeVertex d)))
      (cubeGraph d) where
  toHom :=
    { toFun := fun x => σ x.1
      map_rel' := by
        intro x y hxy
        have heF : s(x.1, y.1) ∈ F := by
          rw [SimpleGraph.induce_adj] at hxy
          rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj] at hxy
          exact hxy.1
        have hePerm : s(x.1, y.1) ∈ cubePattern d σ⁻¹ := hσ heF
        have heMap : s(σ x.1, σ y.1) ∈
            permutedEdges σ (cubePattern d σ⁻¹) := by
          rw [permutedEdges, Finset.mem_map]
          exact ⟨s(x.1, y.1), hePerm, by simp⟩
        rw [cubePattern, ← permutedEdges_mul] at heMap
        simpa using heMap }
  injective' := fun x y h => Subtype.ext (σ.injective h)

/-- Inversion is a bijection between the two convenient orientations of
the containment condition. -/
theorem card_perms_subset_cubePattern_eq_inverse (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card =
      ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ⁻¹).card := by
  classical
  let e : Equiv.Perm (Equiv.Perm (CubeVertex d)) :=
    { toFun := fun σ => σ⁻¹
      invFun := fun σ => σ⁻¹
      left_inv := inv_inv
      right_inv := inv_inv }
  apply Finset.card_equiv e
  intro σ
  simp [e]

end Erdos578

/- Integrated from CopyBound578.lean -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable instance connectedComponentVertexFintype
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (c : G.ConnectedComponent) : Fintype c :=
  Fintype.ofFinite c

def connectedComponentEquivSupp {V : Type*} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : c ≃ c.supp where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := rfl
  right_inv x := rfl

theorem sum_card_connectedComponent_supp {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
  classical
  have hpair :
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint
        (fun c => c.supp.toFinset) := by
    intro c hc c' hc' hcc'
    exact Set.disjoint_toFinset.mpr
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hcc')
  have hunion :
      (Finset.univ : Finset G.ConnectedComponent).biUnion
        (fun c => c.supp.toFinset) = (Finset.univ : Finset V) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, Set.mem_toFinset,
      true_and]
    exact ⟨fun _ => trivial, fun _ =>
      ⟨G.connectedComponentMk v, ConnectedComponent.connectedComponentMk_mem⟩⟩
  calc
    (∑ c : G.ConnectedComponent, Fintype.card c) =
        ∑ c : G.ConnectedComponent, c.supp.toFinset.card := by
          apply Finset.sum_congr rfl
          intro c hc
          exact (Fintype.card_congr (connectedComponentEquivSupp c)).trans
            ((Set.fintypeCard_eq_ncard c.supp).trans
              (Set.ncard_eq_toFinset_card' c.supp))
    _ = ((Finset.univ : Finset G.ConnectedComponent).biUnion
        fun c => c.supp.toFinset).card :=
      (Finset.card_biUnion hpair).symm
    _ = Fintype.card V := by rw [hunion, Finset.card_univ]

noncomputable def connectedComponentCover {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    Σ u : c, {p : c.toSimpleGraph.Walk u u //
      p.support.toFinset = Finset.univ ∧
        p.length = 2 * (Fintype.card c - 1)} := by
  classical
  let h :=
    connected_exists_covering_closedWalk (Fintype.card c) c
      c.toSimpleGraph rfl c.connected_toSimpleGraph
  let u := Classical.choose h
  let p := Classical.choose (Classical.choose_spec h)
  exact ⟨u, p, Classical.choose_spec (Classical.choose_spec h)⟩

def CopyWalkCode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :=
  ∀ c : G.ConnectedComponent,
    CubeWalkLength d (2 * (Fintype.card c - 1))

theorem copyWalkCode_finite {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Finite (CopyWalkCode G d) := by
  unfold CopyWalkCode
  infer_instance

noncomputable def copyWalkCode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (f : SimpleGraph.Copy G (cubeGraph d)) : CopyWalkCode G d := by
  classical
  intro c
  let z := connectedComponentCover G c
  let q : (cubeGraph d).Walk (f z.1.1) (f z.1.1) :=
    z.2.1.map (f.toHom.comp c.toSimpleGraph_hom)
  exact ⟨f z.1.1, f z.1.1, ⟨q, by
    change (z.2.1.map (f.toHom.comp c.toSimpleGraph_hom)).length = _
    rw [Walk.length_map]
    exact z.2.2.2⟩⟩

theorem copyWalkCode_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Function.Injective (copyWalkCode G d) := by
  classical
  intro f g hfg
  apply SimpleGraph.Copy.ext
  intro v
  let c := G.connectedComponentMk v
  let z := connectedComponentCover G c
  let x : c := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
  have hx : x ∈ z.2.1.support := by
    have : x ∈ z.2.1.support.toFinset := by rw [z.2.2.1]; simp
    simpa using this
  have hcode := congr_fun hfg c
  have hsupp := congr_arg
    (fun w : CubeWalkLength d (2 * (Fintype.card c - 1)) =>
      w.2.2.1.support) hcode
  simp only [copyWalkCode] at hsupp
  have hlist :
      (connectedComponentCover G c).2.1.support.map
          (f.toHom.comp c.toSimpleGraph_hom) =
        (connectedComponentCover G c).2.1.support.map
          (g.toHom.comp c.toSimpleGraph_hom) := by
    rw [← Walk.support_map, ← Walk.support_map]
    exact hsupp
  have hx' : x ∈ (connectedComponentCover G c).2.1.support := by
    simpa [z] using hx
  have hmaps := List.map_inj_left.mp hlist x hx'
  rw [← SimpleGraph.Copy.toHom_apply f v,
    ← SimpleGraph.Copy.toHom_apply g v]
  simpa only [RelHom.comp_apply, ConnectedComponent.toSimpleGraph_hom_apply,
    x] using hmaps

theorem natCard_CopyWalkCode (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (d : ℕ) :
    Nat.card (CopyWalkCode G d) =
      (2 ^ d) ^ Fintype.card G.ConnectedComponent *
        d ^ (2 * (Fintype.card V - Fintype.card G.ConnectedComponent)) := by
  classical
  letI : Fintype (CopyWalkCode G d) := by
    unfold CopyWalkCode
    exact Pi.instFintype
  rw [Nat.card_eq_fintype_card]
  unfold CopyWalkCode
  rw [Fintype.card_pi]
  simp_rw [card_cubeWalkLength]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  have htsub := Finset.sum_tsub_distrib
    (Finset.univ : Finset G.ConnectedComponent)
    (f := fun c => Fintype.card c) (g := fun _ => 1)
    (by
      intro c hc
      obtain ⟨v, hv⟩ := c.nonempty_supp
      exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩)
  calc
    (∑ i : G.ConnectedComponent, (Fintype.card i - 1)) =
        (∑ i : G.ConnectedComponent, Fintype.card i) -
          ∑ _i : G.ConnectedComponent, 1 := by simpa using htsub
    _ = Fintype.card V - Fintype.card G.ConnectedComponent := by
      rw [sum_card_connectedComponent_supp]
      simp

theorem natCard_copy_le_cube_walk_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Nat.card (SimpleGraph.Copy G (cubeGraph d)) ≤
      (2 ^ d) ^ Fintype.card G.ConnectedComponent *
        d ^ (2 * (Fintype.card V - Fintype.card G.ConnectedComponent)) := by
  classical
  letI : Finite (CopyWalkCode G d) := copyWalkCode_finite G d
  rw [← natCard_CopyWalkCode G d]
  exact Nat.card_le_card_of_injective (copyWalkCode G d)
    (copyWalkCode_injective G d)

end Erdos578


/- Integrated from PermFiber578.lean -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem card_perms_fixing_finset {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, σ x = x).card = Nat.factorial (Fintype.card α - S.card) := by
  classical
  let T : Finset (Equiv.Perm α) :=
    (Finset.univ : Finset (Equiv.Perm {x : α // x ∉ S})).image
      Equiv.Perm.ofSubtype
  have hT : T =
      (Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, σ x = x := by
    ext σ
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨τ, rfl⟩ x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa)
    · intro hfix
      have hsupp : (σ.support : Set α) ⊆ {x | x ∉ S} := by
        intro x hx
        simpa only [Set.mem_setOf_eq] using fun hxS =>
          (Equiv.Perm.mem_support.mp hx) (hfix x hxS)
      rw [← Equiv.Perm.mem_range_ofSubtype_iff] at hsupp
      obtain ⟨τ, hτ⟩ := hsupp
      exact ⟨τ, hτ⟩
  rw [← hT]
  rw [Finset.card_image_iff.mpr Equiv.Perm.ofSubtype_injective.injOn,
    Finset.card_univ, Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

theorem card_perms_agreeing_on_finset {α : Type*} [Fintype α]
    [DecidableEq α] (S : Finset α) (σ₀ : Equiv.Perm α) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, σ x = σ₀ x).card = Nat.factorial (Fintype.card α - S.card) := by
  classical
  let e : Equiv.Perm α ≃ Equiv.Perm α := Equiv.mulLeft σ₀⁻¹
  have he (σ : Equiv.Perm α) :
      (∀ x ∈ S, σ x = σ₀ x) ↔
        ∀ x ∈ S, e σ x = x := by
    constructor
    · intro h x hx
      simp [e, h x hx]
    · intro h x hx
      have hx' := h x hx
      simpa [e] using congr_arg σ₀ hx'
  calc
    ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, σ x = σ₀ x).card =
      ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, e σ x = x).card := by
          congr 1
          ext σ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact he σ
    _ = ((Finset.univ : Finset (Equiv.Perm α)).filter fun τ =>
        ∀ x ∈ S, τ x = x).card := by
          apply Finset.card_equiv e
          intro σ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = _ := card_perms_fixing_finset S

theorem card_perms_extending_injection {α : Type*} [Fintype α]
    [DecidableEq α] (S : Finset α) (f : S → α) (hf : Function.Injective f) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x : S, σ x = f x).card = Nat.factorial (Fintype.card α - S.card) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := Equiv.Perm.exists_extending_pair
    (fun x : S => (x : α)) f Subtype.val_injective hf
  have hfilter :
      ((Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x : S, σ x = f x) =
      (Finset.univ : Finset (Equiv.Perm α)).filter fun σ =>
        ∀ x ∈ S, σ x = σ₀ x := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h x hx
      simpa [hσ₀ ⟨x, hx⟩] using h ⟨x, hx⟩
    · intro h x
      simpa [hσ₀ x] using h x x.property
  rw [hfilter, card_perms_agreeing_on_finset]

end Erdos578


/- Integrated from Components578.lean -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def ambientSetFinset {V : Type*} [Fintype V]
    (S : Set V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ S

@[simp] theorem mem_ambientSetFinset {V : Type*} [Fintype V]
    {S : Set V} {v : V} : v ∈ ambientSetFinset S ↔ v ∈ S := by
  classical
  simp [ambientSetFinset]

theorem support_graphOfEdges_eq_edgeSupport {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ambientSetFinset (graphOfEdges F).support = edgeSupport F := by
  classical
  ext v
  simp only [mem_ambientSetFinset, edgeSupport, Finset.mem_biUnion]
  constructor
  · intro hv
    rw [SimpleGraph.mem_support] at hv
    obtain ⟨w, hvw⟩ := hv
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj] at hvw
    exact ⟨s(v, w), hvw.1, by simp [Sym2.mem_toFinset]⟩
  · rintro ⟨e, heF, hve⟩
    rw [Sym2.mem_toFinset, Sym2.mem_iff_exists] at hve
    obtain ⟨w, rfl⟩ := hve
    rw [SimpleGraph.mem_support]
    refine ⟨w, ?_⟩
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
    exact ⟨heF, by simpa using hdiag s(v, w) heF⟩

noncomputable def supportComponents {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V)) :
    Finset (graphOfEdges F).ConnectedComponent := by
  classical
  exact (edgeSupport F).image (graphOfEdges F).connectedComponentMk

theorem supportComponent_supp_subset_edgeSupport {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag)
    {c : (graphOfEdges F).ConnectedComponent} (hc : c ∈ supportComponents F) :
    ambientSetFinset c.supp ⊆ edgeSupport F := by
  classical
  rw [supportComponents, Finset.mem_image] at hc
  obtain ⟨v, hvF, rfl⟩ := hc
  intro x hx
  have hvSupport : v ∈ (graphOfEdges F).support := by
    rw [← mem_ambientSetFinset, support_graphOfEdges_eq_edgeSupport hdiag]
    exact hvF
  have hxreach : (graphOfEdges F).Reachable x v := by
    simpa only [mem_ambientSetFinset, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq] using hx
  have hxSupport : x ∈ (graphOfEdges F).support := by
    by_cases hxv : x = v
    · simpa [hxv] using hvSupport
    · exact SimpleGraph.mem_support_of_reachable hxv hxreach
  rw [← mem_ambientSetFinset,
    support_graphOfEdges_eq_edgeSupport hdiag] at hxSupport
  exact hxSupport

theorem biUnion_supportComponents_eq_edgeSupport {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (supportComponents F).biUnion (fun c => ambientSetFinset c.supp) =
      edgeSupport F := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    simp only [Finset.mem_biUnion] at hv
    obtain ⟨c, hc, hvc⟩ := hv
    exact supportComponent_supp_subset_edgeSupport hdiag hc hvc
  · intro v hv
    simp only [Finset.mem_biUnion]
    refine ⟨(graphOfEdges F).connectedComponentMk v, ?_, ?_⟩
    · rw [supportComponents, Finset.mem_image]
      exact ⟨v, hv, rfl⟩
    · rw [mem_ambientSetFinset]
      exact ConnectedComponent.connectedComponentMk_mem

theorem supportComponents_pairwiseDisjoint {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V)) :
    ((supportComponents F : Finset (graphOfEdges F).ConnectedComponent) :
      Set (graphOfEdges F).ConnectedComponent).PairwiseDisjoint
        (fun c => ambientSetFinset c.supp) := by
  classical
  intro c hc c' hc' hcc'
  change Disjoint (ambientSetFinset c.supp) (ambientSetFinset c'.supp)
  rw [Finset.disjoint_left]
  intro v hvc hvc'
  rw [mem_ambientSetFinset] at hvc hvc'
  exact Set.disjoint_left.mp
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (graphOfEdges F) hcc')
      hvc hvc'

theorem sum_card_supportComponents {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (∑ c ∈ supportComponents F, (ambientSetFinset c.supp).card) =
      (edgeSupport F).card := by
  classical
  rw [← Finset.card_biUnion (supportComponents_pairwiseDisjoint F),
    biUnion_supportComponents_eq_edgeSupport hdiag]

theorem supportComponent_connected_in_cube (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    {c : (graphOfEdges F).ConnectedComponent} :
    ((cubeGraph d).induce c.supp).Connected := by
  classical
  have hgraph : graphOfEdges F ≤ cubeGraph d := by
    intro v w hvw
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj] at hvw
    exact SimpleGraph.mem_edgeFinset.mp (hF hvw.1)
  exact c.connected_toSimpleGraph.mono fun v w hvw => hgraph hvw

theorem card_union_sym2_toFinset_eq_three {V : Type*} [DecidableEq V]
    {e f : Sym2 V} (he : ¬e.IsDiag) (hf : ¬f.IsDiag) (hef : e ≠ f)
    (hinter : ¬Disjoint e.toFinset f.toFinset) :
    (e.toFinset ∪ f.toFinset).card = 3 := by
  classical
  obtain ⟨x, hxe, hxf⟩ := Finset.not_disjoint_iff.mp hinter
  rw [Sym2.mem_toFinset, Sym2.mem_iff_exists] at hxe hxf
  obtain ⟨y, rfl⟩ := hxe
  obtain ⟨z, rfl⟩ := hxf
  have hxy : x ≠ y := by simpa using he
  have hxz : x ≠ z := by simpa using hf
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hef rfl
  rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
  simp [hxy, hxz, hyz]

theorem edge_toFinset_subset_component {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    {c : (graphOfEdges F).ConnectedComponent} {e : Sym2 V} {v : V}
    (heF : e ∈ F) (heDiag : ¬e.IsDiag)
    (hve : v ∈ e.toFinset) (hvc : v ∈ c.supp) :
    e.toFinset ⊆ ambientSetFinset c.supp := by
  classical
  rw [Sym2.mem_toFinset, Sym2.mem_iff_exists] at hve
  obtain ⟨w, rfl⟩ := hve
  intro x hx
  simp only [mem_ambientSetFinset]
  have hx' : x = v ∨ x = w := by
    simpa [Sym2.toFinset_mk_eq] using hx
  rcases hx' with hxv | hxw
  · simpa [hxv] using hvc
  · have hvx : (graphOfEdges F).Adj v x := by
      rw [hxw]
      rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
      exact ⟨heF, by simpa using heDiag⟩
    exact (c.mem_supp_congr_adj hvx).mp hvc

theorem overlapCore_hasNoIsolatedEdge {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ overlapCore F) :
    ¬IsIsolatedEdge (overlapCore F) e := by
  classical
  have heF : e ∈ F := (Finset.mem_sdiff.mp he).1
  have hnotIsoF : ¬IsIsolatedEdge F e := by
    intro heIso
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_filter.mpr ⟨heF, heIso⟩)
  intro heIsoCore
  have hex : ∃ f ∈ F, f ≠ e ∧ ¬Disjoint e.toFinset f.toFinset := by
    unfold IsIsolatedEdge at hnotIsoF
    push_neg at hnotIsoF
    exact hnotIsoF heF
  obtain ⟨f, hfF, hfe, hndis⟩ := hex
  have hfNotIso : f ∉ isolatedEdges F := by
    intro hfIso
    have hfprop := (Finset.mem_filter.mp hfIso).2
    exact hndis (hfprop.2 e heF hfe.symm).symm
  have hfCore : f ∈ overlapCore F := Finset.mem_sdiff.mpr ⟨hfF, hfNotIso⟩
  exact hndis (heIsoCore.2 f hfCore hfe)

theorem supportComponent_card_core_three_le {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag)
    {c : (graphOfEdges (overlapCore F)).ConnectedComponent}
    (hc : c ∈ supportComponents (overlapCore F)) :
    3 ≤ (ambientSetFinset c.supp).card := by
  classical
  rw [supportComponents, Finset.mem_image] at hc
  obtain ⟨v, hvSupport, rfl⟩ := hc
  simp only [edgeSupport, Finset.mem_biUnion] at hvSupport
  obtain ⟨e, heCore, hve⟩ := hvSupport
  have heF : e ∈ F := (Finset.mem_sdiff.mp heCore).1
  have hediag : ¬e.IsDiag := hdiag e heF
  have hnotIso := overlapCore_hasNoIsolatedEdge F heCore
  unfold IsIsolatedEdge at hnotIso
  push_neg at hnotIso
  obtain ⟨f, hfCore, hfe, hndis⟩ := hnotIso heCore
  have hfF : f ∈ F := (Finset.mem_sdiff.mp hfCore).1
  have hfdiag : ¬f.IsDiag := hdiag f hfF
  have hvcomp : v ∈
      ((graphOfEdges (overlapCore F)).connectedComponentMk v).supp :=
    ConnectedComponent.connectedComponentMk_mem
  have heSub := edge_toFinset_subset_component heCore hediag hve hvcomp
  obtain ⟨x, hxe, hxf⟩ := Finset.not_disjoint_iff.mp hndis
  have hxcomp : x ∈
      ((graphOfEdges (overlapCore F)).connectedComponentMk v).supp := by
    exact mem_ambientSetFinset.mp (heSub hxe)
  have hfSub := edge_toFinset_subset_component hfCore hfdiag hxf hxcomp
  have hunion : e.toFinset ∪ f.toFinset ⊆
      ambientSetFinset
        ((graphOfEdges (overlapCore F)).connectedComponentMk v).supp :=
    Finset.union_subset heSub hfSub
  calc
    3 = (e.toFinset ∪ f.toFinset).card :=
      (card_union_sym2_toFinset_eq_three hediag hfdiag hfe.symm hndis).symm
    _ ≤ _ := Finset.card_le_card hunion

end Erdos578


/- Integrated from Density578.lean -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem cube_induce_degree_le (d : ℕ) (S : Finset (CubeVertex d))
    (v : S) : ((cubeGraph d).induce (S : Set (CubeVertex d))).degree v ≤ d := by
  classical
  let f :
      ((cubeGraph d).induce (S : Set (CubeVertex d))).neighborSet v →
        (cubeGraph d).neighborSet (v : CubeVertex d) :=
    fun w => ⟨w.1.1, w.2⟩
  calc
    ((cubeGraph d).induce (S : Set (CubeVertex d))).degree v =
        Fintype.card
          (((cubeGraph d).induce (S : Set (CubeVertex d))).neighborSet v) := by
            rw [SimpleGraph.card_neighborSet_eq_degree]
    _ ≤ Fintype.card ((cubeGraph d).neighborSet (v : CubeVertex d)) :=
      Fintype.card_le_of_injective f (fun x y h => by
        have hval : (x.1.1 : CubeVertex d) = y.1.1 :=
          congr_arg
            (fun z : (cubeGraph d).neighborSet (v : CubeVertex d) =>
              (z : CubeVertex d)) h
        exact Subtype.ext (Subtype.ext hval))
    _ = (cubeGraph d).degree (v : CubeVertex d) :=
      SimpleGraph.card_neighborSet_eq_degree _ _
    _ = d := cube_degree d v

/-- A deliberately elementary version of the cube-density estimate used in
Riordan's overlap argument.  The two inputs are only the maximum-degree
bound and the complete-graph bound. -/
theorem two_mul_card_edges_induce_cube_le (d : ℕ)
    (S : Finset (CubeVertex d)) (hS : 3 ≤ S.card) :
    2 * ((cubeGraph d).induce (S : Set (CubeVertex d))).edgeFinset.card ≤
      (d + 4) * (S.card - 2) := by
  classical
  let H := (cubeGraph d).induce (S : Set (CubeVertex d))
  have hcard : Fintype.card S = S.card := Fintype.card_coe _
  have hdeg : 2 * H.edgeFinset.card ≤ d * S.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      (∑ v : S, H.degree v) ≤ ∑ _v : S, d := by
        exact Finset.sum_le_sum fun v _ => cube_induce_degree_le d S v
      _ = d * S.card := by simp [hcard, mul_comm]
  have hcomplete : 2 * H.edgeFinset.card ≤ S.card * (S.card - 1) := by
    calc
      2 * H.edgeFinset.card ≤ 2 * (Fintype.card S).choose 2 := by
        gcongr
        exact H.card_edgeFinset_le_card_choose_two
      _ = S.card * (S.card - 1) := by
        rw [hcard, mul_comm 2, Nat.choose_two_right,
          Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self S.card)]
  have hsub_two : S.card - 2 + 2 = S.card := Nat.sub_add_cancel (by omega)
  have hsub_one : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
  by_cases hsmall : d + 4 ≤ 2 * S.card
  · exact hdeg.trans (by nlinarith)
  · exact hcomplete.trans (by nlinarith)

end Erdos578


/- Integrated from CoverFamily578.lean -/

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem connectedCubeSet_exists_covering_walk (d : ℕ)
    (S : Finset (CubeVertex d))
    (hconn : ((cubeGraph d).induce (S : Set (CubeVertex d))).Connected) :
    ∃ z : CubeWalkLength d (2 * (S.card - 1)),
      z.2.2.1.support.toFinset = S := by
  classical
  have hcardSubtype : Fintype.card S = S.card := Fintype.card_coe S
  obtain ⟨u, p, hpsupp, hplen⟩ :=
    connected_exists_covering_closedWalk S.card S
      ((cubeGraph d).induce (S : Set (CubeVertex d))) hcardSubtype hconn
  let q : (cubeGraph d).Walk (u : CubeVertex d) u :=
    p.map (Embedding.induce _).toHom
  have hqlen : q.length = 2 * (S.card - 1) := by
    change (p.map (Embedding.induce _).toHom).length = _
    rw [Walk.length_map]
    exact hplen
  have hqsupp : q.support.toFinset = S := by
    ext x
    change x ∈ (p.map (Embedding.induce _).toHom).support.toFinset ↔ x ∈ S
    rw [Walk.support_map]
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.property
    · intro hx
      let y : S := ⟨x, hx⟩
      have hy : y ∈ p.support := by
        have : y ∈ p.support.toFinset := by rw [hpsupp]; simp
        simpa using this
      exact ⟨y, hy, rfl⟩
  exact ⟨⟨u, u, ⟨q, hqlen⟩⟩, hqsupp⟩

theorem family_connected_support_mem_walkCoverSupportSets (d : ℕ)
    (C : Finset (Finset (CubeVertex d)))
    (hcard : ∀ S ∈ C, 2 ≤ S.card)
    (hconn : ∀ S ∈ C,
      ((cubeGraph d).induce (S : Set (CubeVertex d))).Connected) :
    C.biUnion id ∈
      walkCoverSupportSets d (∑ S ∈ C, (S.card - 1)) C.card := by
  classical
  let L : List (Finset (CubeVertex d)) := C.toList
  let r : ℕ := ∑ S ∈ C, (S.card - 1)
  let blocks : List ℕ := L.map fun S => S.card - 1
  have hblocks_pos : ∀ {i}, i ∈ blocks → 0 < i := by
    intro i hi
    simp only [blocks, List.mem_map] at hi
    obtain ⟨S, hSL, rfl⟩ := hi
    have hSC : S ∈ C := by simpa [L] using hSL
    have hSCard := hcard S hSC
    omega
  have hblocks_sum : blocks.sum = r := by
    simp [blocks, L, r]
  let c : Composition r := ⟨blocks, hblocks_pos, hblocks_sum⟩
  have hLlength : L.length = C.card := by simp [L]
  have hclength : c.length = L.length := by
    change blocks.length = L.length
    simp [blocks]
  have hcertlength : c.length = C.card := hclength.trans hLlength
  have hget (i : Fin c.length) :
      c.blocksFun i = (L.get (Fin.cast hclength i)).card - 1 := by
    simp [c, Composition.blocksFun, blocks]
  have hLC (i : Fin c.length) : L.get (Fin.cast hclength i) ∈ C := by
    have hm : L.get (Fin.cast hclength i) ∈ L :=
      L.get_mem (Fin.cast hclength i)
    have hm' : L.get (Fin.cast hclength i) ∈ C.toList := by
      simpa only [L] using hm
    exact Finset.mem_toList.mp hm'
  choose z hz using fun i : Fin c.length =>
    connectedCubeSet_exists_covering_walk d
      (L.get (Fin.cast hclength i))
      (hconn _ (hLC i))
  let tuple : CubeWalkTuple d r c := fun i =>
    ⟨(z i).1, (z i).2.1, ⟨(z i).2.2.1, by
      rw [hget i]
      exact (z i).2.2.2⟩⟩
  let cert : CubeWalkCoverCertificate d r C.card :=
    ⟨⟨c, hcertlength⟩, tuple⟩
  have hcert : CubeWalkCoverCertificate.support cert = C.biUnion id := by
    ext x
    simp only [CubeWalkCoverCertificate.support, cert, tuple,
      Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨i, hi⟩
      have hi' : x ∈ L.get (Fin.cast hclength i) := by
        rw [← hz i]
        simpa [tuple] using hi
      exact ⟨L.get (Fin.cast hclength i), hLC i, hi'⟩
    · rintro ⟨S, hSC, hxS⟩
      have hSL : S ∈ L := by simpa [L] using hSC
      obtain ⟨j, hj⟩ := List.get_of_mem hSL
      let i : Fin c.length := Fin.cast hclength.symm j
      refine ⟨i, ?_⟩
      have hSi : L.get (Fin.cast hclength i) = S := by
        simpa [i] using hj
      simpa [hget i, hSi] using
        (show x ∈ (z i).2.2.1.support.toFinset by
          rw [hz i, hSi]
          exact hxS)
  simp only [walkCoverSupportSets, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨cert, hcert⟩

end Erdos578


namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

/-- Exact fiber counting: after selecting the induced copy on the support
of `F`, there are precisely `(2^d-|supp F|)!` possible extensions to an
ambient permutation. -/
theorem card_perms_containing_edge_set_le (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card ≤
      Nat.card
          (SimpleGraph.Copy
            ((graphOfEdges F).induce
              (edgeSupport F : Set (CubeVertex d)))
            (cubeGraph d)) *
        Nat.factorial (2 ^ d - (edgeSupport F).card) := by
  classical
  let S : Finset (CubeVertex d) := edgeSupport F
  let H : SimpleGraph S :=
    (graphOfEdges F).induce (S : Set (CubeVertex d))
  let A : Finset (Equiv.Perm (CubeVertex d)) :=
    (Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
      F ⊆ cubePattern d σ⁻¹
  letI : Fintype (SimpleGraph.Copy H (cubeGraph d)) := Fintype.ofFinite _
  let φ : A → SimpleGraph.Copy H (cubeGraph d) := fun a =>
    permutationCopyOfSubset d F a.1 (by
      have ha := a.2
      change a.1 ∈
        ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
          F ⊆ cubePattern d σ⁻¹) at ha
      exact (Finset.mem_filter.mp ha).2)
  rw [card_perms_subset_cubePattern_eq_inverse]
  change A.card ≤ _
  calc
    A.card = A.attach.card := Finset.card_attach.symm
    _ = ∑ f : SimpleGraph.Copy H (cubeGraph d),
          ((A.attach.filter fun a => φ a = f).card) := by
      exact Finset.card_eq_sum_card_fiberwise
        (s := A.attach)
        (t := (Finset.univ : Finset (SimpleGraph.Copy H (cubeGraph d))))
        (f := φ) (fun a _ha => Finset.mem_univ (φ a))
    _ ≤ ∑ _f : SimpleGraph.Copy H (cubeGraph d),
          Nat.factorial (2 ^ d - S.card) := by
      apply Finset.sum_le_sum
      intro f _hf
      let E : Finset (Equiv.Perm (CubeVertex d)) :=
        (Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
          ∀ x : S, σ x = f x
      have hfiber : (A.attach.filter fun a => φ a = f).card ≤ E.card := by
        apply Finset.card_le_card_of_injOn (fun a : A => a.1)
        · intro a ha
          have haφ : φ a = f := (Finset.mem_filter.mp ha).2
          show a.1 ∈ E
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro x
          rw [← haφ]
          rfl
        · intro a _ha b _hb hab
          exact Subtype.ext hab
      exact hfiber.trans_eq (by
        rw [show E =
            ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
              fun σ => ∀ x : S, σ x = f x) by rfl]
        simpa [S, card_cubeVertex] using
          card_perms_extending_injection S f f.injective)
    _ = Nat.card (SimpleGraph.Copy H (cubeGraph d)) *
          Nat.factorial (2 ^ d - S.card) := by
      simp [Nat.card_eq_fintype_card]
    _ = _ := by rfl

/-- The graph carried by an overlap edge set after discarding ambient
vertices which do not meet an overlap edge. -/
noncomputable def overlapSupportGraph (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    SimpleGraph (edgeSupport F) :=
  (graphOfEdges F).induce (edgeSupport F : Set (CubeVertex d))

/-- Number of nontrivial connected components of an overlap edge set. -/
noncomputable def overlapComponentCount (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) : ℕ :=
  Nat.card (overlapSupportGraph d F).ConnectedComponent

/-- The factorial fiber estimate and the component-walk code combined in
the form used in the overlap sum. -/
theorem card_perms_containing_edge_set_le_walk_bound (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card ≤
      (2 ^ d) ^ overlapComponentCount d F *
        d ^ (2 * ((edgeSupport F).card - overlapComponentCount d F)) *
        Nat.factorial (2 ^ d - (edgeSupport F).card) := by
  classical
  have hcopy := natCard_copy_le_cube_walk_bound
    (overlapSupportGraph d F) d
  rw [← Nat.card_eq_fintype_card] at hcopy
  have hfiber := card_perms_containing_edge_set_le d F hF
  have hmul := Nat.mul_le_mul_right
    (Nat.factorial (2 ^ d - (edgeSupport F).card)) hcopy
  exact hfiber.trans (by
    simpa [overlapSupportGraph, overlapComponentCount, card_cubeVertex,
      mul_assoc] using hmul)

end Erdos578


namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

def cubeStep (d : ℕ) (v : CubeVertex d) (i : Fin d) : CubeVertex d :=
  Function.update v i (v i + 1)

theorem cubeStep_injective (d : ℕ) (v : CubeVertex d) :
    Function.Injective (cubeStep d v) := by
  intro i j h
  replace h := congr_fun h i
  by_cases hij : i = j <;> simp_all +decide [cubeStep]

theorem cubeStep_step (d : ℕ) (v : CubeVertex d) (i : Fin d) :
    cubeStep d (cubeStep d v i) i = v := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have htwo' : (1 + 1 : ZMod 2) = 0 := by
    change (2 : ZMod 2) = 0
    exact htwo
  ext j
  by_cases hji : j = i
  · subst j
    simpa [cubeStep, add_assoc] using htwo'
  · simp [cubeStep, hji, Ne.symm hji]

noncomputable def cubeStepCoordinate (d : ℕ) {x y : CubeVertex d}
    (h : (cubeGraph d).Adj x y) : Fin d := by
  classical
  have hy : y ∈ (cubeGraph d).neighborFinset x := by simpa using h
  rw [cube_neighborFinset] at hy
  exact Classical.choose (Finset.mem_image.mp hy)

theorem cubeStepCoordinate_spec (d : ℕ) {x y : CubeVertex d}
    (h : (cubeGraph d).Adj x y) :
    cubeStep d x (cubeStepCoordinate d h) = y := by
  classical
  have hy : y ∈ (cubeGraph d).neighborFinset x := by simpa using h
  rw [cube_neighborFinset] at hy
  exact (Classical.choose_spec (Finset.mem_image.mp hy)).2

theorem cubeStepCoordinate_unique (d : ℕ) {x y : CubeVertex d}
    (h : (cubeGraph d).Adj x y) {i : Fin d}
    (hi : cubeStep d x i = y) : cubeStepCoordinate d h = i := by
  apply cubeStep_injective d x
  rw [cubeStepCoordinate_spec, hi]

theorem cubeStepCoordinate_symm (d : ℕ) {x y : CubeVertex d}
    (h : (cubeGraph d).Adj x y) :
    cubeStepCoordinate d h.symm = cubeStepCoordinate d h := by
  apply cubeStepCoordinate_unique d h.symm
  let i := cubeStepCoordinate d h
  have hxy : cubeStep d x i = y := cubeStepCoordinate_spec d h
  calc
    cubeStep d y i = cubeStep d (cubeStep d x i) i := by rw [hxy]
    _ = x := cubeStep_step d x i

theorem cube_adj_second_eq_of_first_eq_coordinate_eq (d : ℕ)
    {x y x' y' : CubeVertex d}
    (h : (cubeGraph d).Adj x y) (h' : (cubeGraph d).Adj x' y')
    (hx : x = x')
    (hc : cubeStepCoordinate d h = cubeStepCoordinate d h') : y = y' := by
  subst x'
  calc
    y = cubeStep d x (cubeStepCoordinate d h) :=
      (cubeStepCoordinate_spec d h).symm
    _ = cubeStep d x (cubeStepCoordinate d h') :=
      congrArg (cubeStep d x) hc
    _ = y' := cubeStepCoordinate_spec d h'

theorem copy_eq_along_walk {V : Type*} {G T : SimpleGraph V}
    (hTG : T ≤ G) (d : ℕ)
    (f g : SimpleGraph.Copy G (cubeGraph d))
    {u v : V} (p : T.Walk u v)
    (hcoord : ∀ {x y : V} (hxy : T.Adj x y),
      cubeStepCoordinate d (f.toHom.map_rel (hTG hxy)) =
        cubeStepCoordinate d (g.toHom.map_rel (hTG hxy)))
    (hu : f u = g u) : f v = g v := by
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
      apply ih
      exact cube_adj_second_eq_of_first_eq_coordinate_eq d
        (f.toHom.map_rel (hTG huw)) (g.toHom.map_rel (hTG huw)) hu
        (hcoord huw)

theorem cubeStepCoordinate_eq_of_edge_eq (d : ℕ)
    {x y x' y' : CubeVertex d}
    (h : (cubeGraph d).Adj x y) (h' : (cubeGraph d).Adj x' y')
    (he : s(x, y) = s(x', y')) :
    cubeStepCoordinate d h = cubeStepCoordinate d h' := by
  have hep : (x, y) = (x', y') ∨ (x, y) = (x', y').swap :=
    Sym2.mk_eq_mk_iff.mp he
  rcases hep with he | he
  · cases he
    rfl
  · have hxy : x = y' := congrArg Prod.fst he
    have hyx : y = x' := congrArg Prod.snd he
    subst y'
    subst x'
    exact (cubeStepCoordinate_symm d h).symm

noncomputable def componentSpanningTree {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) : SimpleGraph c :=
  Classical.choose c.connected_toSimpleGraph.exists_isTree_le

theorem componentSpanningTree_le {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    componentSpanningTree G c ≤ c.toSimpleGraph :=
  (Classical.choose_spec c.connected_toSimpleGraph.exists_isTree_le).1

theorem componentSpanningTree_isTree {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    (componentSpanningTree G c).IsTree :=
  (Classical.choose_spec c.connected_toSimpleGraph.exists_isTree_le).2

noncomputable def componentRoot {V : Type*} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : c :=
  ⟨Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp⟩

noncomputable def treeEdgeAdj {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent)
    (e : (componentSpanningTree G c).edgeSet) :
    (componentSpanningTree G c).Adj e.1.out.1 e.1.out.2 := by
  rw [← (componentSpanningTree G c).mem_edgeSet]
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
    exact e.1.out_eq
  rw [hout]
  exact e.2

noncomputable def copyOnComponent {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (f : SimpleGraph.Copy G (cubeGraph d))
    (c : G.ConnectedComponent) :
    SimpleGraph.Copy c.toSimpleGraph (cubeGraph d) where
  toHom := f.toHom.comp c.toSimpleGraph_hom
  injective' := f.injective.comp Subtype.val_injective

noncomputable instance componentSpanningTreeEdgeSetFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    Fintype (componentSpanningTree G c).edgeSet := Fintype.ofFinite _

abbrev SharpCopyCode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :=
  ∀ c : G.ConnectedComponent,
    CubeVertex d × ((componentSpanningTree G c).edgeSet → Fin d)

noncomputable def sharpCopyCode {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (f : SimpleGraph.Copy G (cubeGraph d)) : SharpCopyCode G d :=
  fun c =>
    ⟨f (componentRoot c).1, fun e =>
      cubeStepCoordinate d
        ((copyOnComponent G d f c).toHom.map_rel
          (componentSpanningTree_le G c (treeEdgeAdj G c e)))⟩

theorem sharpCopyCode_coordinate_eq {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (f g : SimpleGraph.Copy G (cubeGraph d))
    (hfg : sharpCopyCode G d f = sharpCopyCode G d g)
    (c : G.ConnectedComponent) {x y : c}
    (hxy : (componentSpanningTree G c).Adj x y) :
    cubeStepCoordinate d
        ((copyOnComponent G d f c).toHom.map_rel
          (componentSpanningTree_le G c hxy)) =
      cubeStepCoordinate d
        ((copyOnComponent G d g c).toHom.map_rel
          (componentSpanningTree_le G c hxy)) := by
  classical
  let e : (componentSpanningTree G c).edgeSet :=
    ⟨s(x, y), by simpa using hxy⟩
  have hfun : (sharpCopyCode G d f c).2 =
      (sharpCopyCode G d g c).2 :=
    congrArg Prod.snd (congrFun hfg c)
  have heq := congrFun hfun e
  have hout : s(e.1.out.1, e.1.out.2) = s(x, y) := by
    exact e.1.out_eq
  have hfedge :
      s((copyOnComponent G d f c) e.1.out.1,
          (copyOnComponent G d f c) e.1.out.2) =
        s((copyOnComponent G d f c) x,
          (copyOnComponent G d f c) y) := by
    simpa using congrArg (Sym2.map (copyOnComponent G d f c)) hout
  have hgedge :
      s((copyOnComponent G d g c) e.1.out.1,
          (copyOnComponent G d g c) e.1.out.2) =
        s((copyOnComponent G d g c) x,
          (copyOnComponent G d g c) y) := by
    simpa using congrArg (Sym2.map (copyOnComponent G d g c)) hout
  have hfcoord := cubeStepCoordinate_eq_of_edge_eq d
    ((copyOnComponent G d f c).toHom.map_rel
      (componentSpanningTree_le G c (treeEdgeAdj G c e)))
    ((copyOnComponent G d f c).toHom.map_rel
      (componentSpanningTree_le G c hxy)) hfedge
  have hgcoord := cubeStepCoordinate_eq_of_edge_eq d
    ((copyOnComponent G d g c).toHom.map_rel
      (componentSpanningTree_le G c (treeEdgeAdj G c e)))
    ((copyOnComponent G d g c).toHom.map_rel
      (componentSpanningTree_le G c hxy)) hgedge
  exact hfcoord.symm.trans (heq.trans hgcoord)

theorem sharpCopyCode_injective {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Function.Injective (sharpCopyCode G d) := by
  classical
  intro f g hfg
  apply SimpleGraph.Copy.ext
  intro v
  let c := G.connectedComponentMk v
  let x : c := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
  have hreach : (componentSpanningTree G c).Reachable (componentRoot c) x :=
    (componentSpanningTree_isTree G c).connected.preconnected _ _
  let p : (componentSpanningTree G c).Walk (componentRoot c) x :=
    Classical.choice hreach
  have hroot : (copyOnComponent G d f c) (componentRoot c) =
      (copyOnComponent G d g c) (componentRoot c) := by
    exact congrArg Prod.fst (congrFun hfg c)
  have hx := copy_eq_along_walk (componentSpanningTree_le G c) d
    (copyOnComponent G d f c) (copyOnComponent G d g c) p
    (fun hxy => sharpCopyCode_coordinate_eq G d f g hfg c hxy) hroot
  exact hx

theorem card_componentSpanningTree_edgeSet {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    Fintype.card (componentSpanningTree G c).edgeSet = Fintype.card c - 1 := by
  have htree := (componentSpanningTree_isTree G c).card_edgeFinset
  rw [(componentSpanningTree G c).edgeFinset_card] at htree
  omega

theorem sharpCopyCode_finite {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Finite (SharpCopyCode G d) := by
  unfold SharpCopyCode
  infer_instance

theorem natCard_SharpCopyCode {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Nat.card (SharpCopyCode G d) =
      (2 ^ d) ^ Nat.card G.ConnectedComponent *
        d ^ (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  letI : Fintype (SharpCopyCode G d) := by
    exact Pi.instFintype
  rw [Nat.card_eq_fintype_card]
  unfold SharpCopyCode
  rw [Fintype.card_pi]
  simp_rw [Fintype.card_prod, card_cubeVertex, Fintype.card_fun,
    Fintype.card_fin, card_componentSpanningTree_edgeSet]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  · rw [Nat.card_eq_fintype_card]
  · congr 1
    have htsub := Finset.sum_tsub_distrib
      (Finset.univ : Finset G.ConnectedComponent)
      (f := fun c => Fintype.card c) (g := fun _ => 1)
      (by
        intro c hc
        obtain ⟨v, hv⟩ := c.nonempty_supp
        exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩)
    calc
      (∑ i : G.ConnectedComponent, (Fintype.card i - 1)) =
          (∑ i : G.ConnectedComponent, Fintype.card i) -
            ∑ _i : G.ConnectedComponent, 1 := by simpa using htsub
      _ = _ := by
        rw [sum_card_connectedComponent_supp]
        simp [Nat.card_eq_fintype_card]

theorem natCard_copy_le_cube_tree_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Nat.card (SimpleGraph.Copy G (cubeGraph d)) ≤
      (2 ^ d) ^ Nat.card G.ConnectedComponent *
        d ^ (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  letI : Finite (SharpCopyCode G d) := sharpCopyCode_finite G d
  rw [← natCard_SharpCopyCode G d]
  exact Nat.card_le_card_of_injective (sharpCopyCode G d)
    (sharpCopyCode_injective G d)

theorem card_perms_containing_edge_set_le_tree_bound (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card ≤
      (2 ^ d) ^ overlapComponentCount d F *
        d ^ ((edgeSupport F).card - overlapComponentCount d F) *
        Nat.factorial (2 ^ d - (edgeSupport F).card) := by
  classical
  have hcopy := natCard_copy_le_cube_tree_bound
    (overlapSupportGraph d F) d
  have hfiber := card_perms_containing_edge_set_le d F hF
  have hmul := Nat.mul_le_mul_right
    (Nat.factorial (2 ^ d - (edgeSupport F).card)) hcopy
  exact hfiber.trans (by
    simpa [overlapSupportGraph, overlapComponentCount, card_cubeVertex,
      mul_assoc] using hmul)

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem pow_le_nine_pow_mul_descFactorial {n s : ℕ}
    (hn : 0 < n) (hs : s ≤ n) :
    (n : ℝ) ^ s ≤ 9 ^ s * (n.descFactorial s : ℝ) := by
  by_cases hsmall : 2 * s ≤ n
  · have hhalf : n ≤ 2 * (n + 1 - s) := by omega
    have hpowNat : n ^ s ≤ 2 ^ s * (n + 1 - s) ^ s := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left hhalf s
    have hdescNat := n.pow_sub_le_descFactorial s
    have hmainNat : n ^ s ≤ 9 ^ s * n.descFactorial s := by
      calc
        n ^ s ≤ 2 ^ s * (n + 1 - s) ^ s := hpowNat
        _ ≤ 9 ^ s * n.descFactorial s := by gcongr <;> omega
    exact_mod_cast hmainNat
  · have hn2s : n ≤ 2 * s := by omega
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
      rw [Real.one_le_sqrt]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hbase : 0 ≤ (n : ℝ) / Real.exp 1 := by positivity
    have hfactorialLower :
        ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
      exact (le_mul_of_one_le_left (pow_nonneg hbase n) hsqrt).trans
        (Stirling.le_factorial_stirling n)
    have hexp : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    have hremainingNat : (n - s).factorial ≤ n ^ (n - s) :=
      (n - s).factorial_le_pow.trans
        (Nat.pow_le_pow_left (Nat.sub_le n s) (n - s))
    have hremaining : ((n - s).factorial : ℝ) ≤ (n : ℝ) ^ (n - s) := by
      exact_mod_cast hremainingNat
    have hfacIdentity :
        ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) =
          (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hs
    have hnexp : (n : ℝ) ^ n ≤
        (3 : ℝ) ^ n * (n : ℝ) ^ (n - s) *
          (n.descFactorial s : ℝ) := by
      calc
        (n : ℝ) ^ n = (Real.exp 1) ^ n *
            (((n : ℝ) / Real.exp 1) ^ n) := by
              rw [div_pow]
              field_simp
        _ ≤ (Real.exp 1) ^ n * (n.factorial : ℝ) := by gcongr
        _ ≤ (3 : ℝ) ^ n * (n.factorial : ℝ) := by gcongr
        _ = (3 : ℝ) ^ n * ((n - s).factorial : ℝ) *
            (n.descFactorial s : ℝ) := by rw [← hfacIdentity]; ring
        _ ≤ (3 : ℝ) ^ n * (n : ℝ) ^ (n - s) *
            (n.descFactorial s : ℝ) := by gcongr
    have hcancel : (n : ℝ) ^ s ≤
        (3 : ℝ) ^ n * (n.descFactorial s : ℝ) := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hpowpos : (0 : ℝ) < (n : ℝ) ^ (n - s) := pow_pos hnpos _
      have hpowEq : (n : ℝ) ^ n =
          (n : ℝ) ^ (n - s) * (n : ℝ) ^ s := by
        rw [← pow_add]
        congr 1
        omega
      have hmul : (n : ℝ) ^ (n - s) * (n : ℝ) ^ s ≤
          (n : ℝ) ^ (n - s) *
            ((3 : ℝ) ^ n * (n.descFactorial s : ℝ)) := by
        rw [← hpowEq]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hnexp
      exact le_of_mul_le_mul_left hmul hpowpos
    have hthreeNine : (3 : ℝ) ^ n ≤ 9 ^ s := by
      calc
        (3 : ℝ) ^ n ≤ 3 ^ (2 * s) := by gcongr <;> norm_num
        _ = 9 ^ s := by rw [pow_mul]; norm_num
    exact hcancel.trans (mul_le_mul_of_nonneg_right hthreeNine (by positivity))

theorem rooted_factorial_ratio_le {n s k : ℕ}
    (hn : 0 < n) (hs : s ≤ n) (hk : k ≤ s)
    (hs2 : s ≤ 2 * (s - k)) :
    (n : ℝ) ^ k * ((n - s).factorial : ℝ) /
        (n.factorial : ℝ) ≤
      ((81 : ℝ) / n) ^ (s - k) := by
  have hdescPosNat : 0 < n.descFactorial s :=
    Nat.descFactorial_pos.mpr hs
  have hdescPos : (0 : ℝ) < n.descFactorial s := by
    exact_mod_cast hdescPosNat
  have hremainPos : (0 : ℝ) < (n - s).factorial := by positivity
  have hfac : ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hs
  have hratio :
      (n : ℝ) ^ k * ((n - s).factorial : ℝ) /
          (n.factorial : ℝ) =
        (n : ℝ) ^ k / (n.descFactorial s : ℝ) := by
    rw [← hfac]
    field_simp
  rw [hratio, div_pow]
  have hpow := pow_le_nine_pow_mul_descFactorial hn hs
  have hpowSplit : (n : ℝ) ^ s =
      (n : ℝ) ^ k * (n : ℝ) ^ (s - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (n : ℝ) ^ k / (n.descFactorial s : ℝ) ≤
      (9 : ℝ) ^ s / (n : ℝ) ^ (s - k) := by
    rw [div_le_div_iff₀ hdescPos (pow_pos hnR _)]
    rw [hpowSplit] at hpow
    nlinarith [pow_pos hnR k]
  have hnine : (9 : ℝ) ^ s ≤ 81 ^ (s - k) := by
    calc
      (9 : ℝ) ^ s ≤ 9 ^ (2 * (s - k)) := by gcongr <;> norm_num
      _ = 81 ^ (s - k) := by rw [pow_mul]; norm_num
  exact hbase.trans (by
    apply div_le_div_of_nonneg_right hnine
    positivity)

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem overlapSupportGraph_component_card_two_le (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (c : (overlapSupportGraph d F).ConnectedComponent) :
    2 ≤ Fintype.card c := by
  classical
  obtain ⟨x, hxc⟩ := c.nonempty_supp
  have hxSupport : x.1 ∈ edgeSupport F := x.2
  simp only [edgeSupport, Finset.mem_biUnion] at hxSupport
  obtain ⟨e, heF, hxe⟩ := hxSupport
  rw [Sym2.mem_toFinset, Sym2.mem_iff_exists] at hxe
  obtain ⟨y, hey⟩ := hxe
  subst e
  have hcube : (cubeGraph d).Adj x.1 y :=
    SimpleGraph.mem_edgeFinset.mp (hF heF)
  have hySupport : y ∈ edgeSupport F := by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨s(x.1, y), heF, by simp [Sym2.mem_toFinset]⟩
  let yS : edgeSupport F := ⟨y, hySupport⟩
  have hxy : (overlapSupportGraph d F).Adj x yS := by
    rw [overlapSupportGraph, SimpleGraph.induce_adj]
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
    exact ⟨heF, hcube.ne⟩
  have hyc : yS ∈ c.supp := (c.mem_supp_congr_adj hxy).mp hxc
  let xc : c := ⟨x, hxc⟩
  let yc : c := ⟨yS, hyc⟩
  have hxyne : xc ≠ yc := by
    intro h
    have hval : x.1 = y := congrArg (fun z : c => z.1.1) h
    exact hcube.ne hval
  exact (Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨xc, yc, hxyne⟩⟩)

theorem two_mul_overlapComponentCount_le_support_card (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    2 * overlapComponentCount d F ≤ (edgeSupport F).card := by
  classical
  let H := overlapSupportGraph d F
  have hsum : (∑ c : H.ConnectedComponent, Fintype.card c) =
      (edgeSupport F).card := by
    rw [sum_card_connectedComponent_supp]
    exact Fintype.card_coe _
  calc
    2 * overlapComponentCount d F =
      ∑ _c : H.ConnectedComponent, 2 := by
      simp [overlapComponentCount, H, Nat.card_eq_fintype_card, Nat.mul_comm]
    _ ≤ ∑ c : H.ConnectedComponent, Fintype.card c := by
      exact Finset.sum_le_sum fun c _ =>
        overlapSupportGraph_component_card_two_le d F hF c
    _ = _ := hsum

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

def overlapSupportHom (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    overlapSupportGraph d F →g graphOfEdges F where
  toFun := fun x => x.1
  map_rel' := by
    intro x y hxy
    exact hxy

noncomputable def overlapSupportComponentMap (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    (overlapSupportGraph d F).ConnectedComponent →
      (graphOfEdges F).ConnectedComponent :=
  fun c => c.map (overlapSupportHom d F)

theorem overlapSupportComponentMap_mem (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (c : (overlapSupportGraph d F).ConnectedComponent) :
    overlapSupportComponentMap d F c ∈ supportComponents F := by
  classical
  induction c using ConnectedComponent.ind with
  | _ x =>
      rw [overlapSupportComponentMap, ConnectedComponent.map_mk,
        supportComponents, Finset.mem_image]
      exact ⟨x.1, x.2, rfl⟩

theorem overlapSupportComponentMap_injective (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    Function.Injective (overlapSupportComponentMap d F) := by
  classical
  intro c c' hcc'
  induction c, c' using ConnectedComponent.ind₂ with
  | _ x y =>
      simp only [overlapSupportComponentMap, ConnectedComponent.map_mk] at hcc'
      rw [ConnectedComponent.eq] at hcc' ⊢
      apply hcc'.elim
      intro p
      have hpall : ∀ z ∈ p.support, z ∈ edgeSupport F := by
        intro z hz
        by_cases hp : p.Nil
        · have hpSupp : p.support = [x.1] := Walk.nil_iff_support_eq.mp hp
          have hzEq : z = x.1 := by simpa [hpSupp] using hz
          simpa [hzEq] using x.2
        · have hzSupp : z ∈ (graphOfEdges F).support :=
            mem_support_of_mem_walk_support p hp hz
          rw [← mem_ambientSetFinset,
            support_graphOfEdges_eq_edgeSupport hdiag] at hzSupp
          exact hzSupp
      have q := p.induce (edgeSupport F : Set (CubeVertex d)) hpall
      refine ⟨q.copy ?_ ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl

noncomputable def mappedSupportComponents (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    Finset (graphOfEdges F).ConnectedComponent := by
  classical
  exact (Finset.univ :
    Finset (overlapSupportGraph d F).ConnectedComponent).image
      (overlapSupportComponentMap d F)

theorem image_overlapSupportComponentMap_eq_supportComponents (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    mappedSupportComponents d F = supportComponents F := by
  classical
  rw [mappedSupportComponents]
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c', rfl⟩
    exact overlapSupportComponentMap_mem d F c'
  · intro hc
    rw [supportComponents, Finset.mem_image] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    let x : edgeSupport F := ⟨v, hv⟩
    refine ⟨(overlapSupportGraph d F).connectedComponentMk x, ?_⟩
    simp only [overlapSupportComponentMap, ConnectedComponent.map_mk]
    rw [ConnectedComponent.eq]
    exact Reachable.refl v

theorem card_supportComponents_eq_overlapComponentCount (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (supportComponents F).card = overlapComponentCount d F := by
  classical
  rw [← image_overlapSupportComponentMap_eq_supportComponents]
  rw [mappedSupportComponents]
  rw [Finset.card_image_of_injective _
    (overlapSupportComponentMap_injective d F hdiag)]
  simp [overlapComponentCount, Nat.card_eq_fintype_card]

end Erdos578


namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem normalized_permutation_fiber_le (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card : ℝ) /
        Fintype.card (Equiv.Perm (CubeVertex d)) ≤
      (((81 : ℝ) * d) / (2 ^ d : ℕ)) ^
        ((edgeSupport F).card - overlapComponentCount d F) := by
  classical
  let n := 2 ^ d
  let s := (edgeSupport F).card
  let k := overlapComponentCount d F
  let r := s - k
  have hn : 0 < n := by positivity
  have hs : s ≤ n := by
    dsimp [s, n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have h2k : 2 * k ≤ s := by
    exact two_mul_overlapComponentCount_le_support_card d F hF
  have hk : k ≤ s := by omega
  have hs2 : s ≤ 2 * r := by omega
  have hcount := card_perms_containing_edge_set_le_tree_bound d F hF
  have hcountR :
      ((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
          F ⊆ cubePattern d σ).card : ℕ) : ℝ) ≤
        (n : ℝ) ^ k * d ^ r * ((n - s).factorial : ℝ) := by
    exact_mod_cast hcount
  have hfac := rooted_factorial_ratio_le hn hs hk hs2
  have hperm : Fintype.card (Equiv.Perm (CubeVertex d)) = n.factorial := by
    rw [Fintype.card_perm, card_cubeVertex]
  rw [hperm]
  calc
    (((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
          F ⊆ cubePattern d σ).card : ℕ) : ℝ) /
        (n.factorial : ℝ)) ≤
      ((n : ℝ) ^ k * d ^ r * ((n - s).factorial : ℝ)) /
        (n.factorial : ℝ) := by gcongr
    _ = (d : ℝ) ^ r *
        ((n : ℝ) ^ k * ((n - s).factorial : ℝ) /
          (n.factorial : ℝ)) := by ring
    _ ≤ (d : ℝ) ^ r * (((81 : ℝ) / n) ^ r) := by gcongr
    _ = (((81 : ℝ) * d) / n) ^ r := by
      rw [← mul_pow]
      congr 1
      ring

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def componentEdges {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V))
    (c : (graphOfEdges F).ConnectedComponent) : Finset (Sym2 V) := by
  classical
  exact F.filter fun e => e.toFinset ⊆ ambientSetFinset c.supp

theorem componentEdges_subset {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V))
    (c : (graphOfEdges F).ConnectedComponent) : componentEdges F c ⊆ F := by
  classical
  exact Finset.filter_subset _ _

theorem edgeSupport_componentEdges {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag)
    {c : (graphOfEdges F).ConnectedComponent}
    (hc : c ∈ supportComponents F) :
    edgeSupport (componentEdges F c) = ambientSetFinset c.supp := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    simp only [edgeSupport, Finset.mem_biUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    exact (Finset.mem_filter.mp he).2 hve
  · intro v hvc
    have hvcSupp : v ∈ c.supp := by
      simpa [mem_ambientSetFinset] using hvc
    have hvSupport : v ∈ edgeSupport F :=
      supportComponent_supp_subset_edgeSupport hdiag hc hvc
    simp only [edgeSupport, Finset.mem_biUnion] at hvSupport ⊢
    obtain ⟨e, heF, hve⟩ := hvSupport
    have heSub := edge_toFinset_subset_component heF (hdiag e heF) hve hvcSupp
    exact ⟨e, Finset.mem_filter.mpr ⟨heF, heSub⟩, hve⟩

theorem biUnion_componentEdges_eq {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (supportComponents F).biUnion (componentEdges F) = F := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    simp only [Finset.mem_biUnion] at he
    obtain ⟨c, hc, hec⟩ := he
    exact componentEdges_subset F c hec
  · intro e heF
    let v : V := e.out.1
    have hve : v ∈ e.toFinset := by
      simpa [Sym2.mem_toFinset, v] using e.out_fst_mem
    have hvSupport : v ∈ edgeSupport F := by
      simp only [edgeSupport, Finset.mem_biUnion]
      exact ⟨e, heF, hve⟩
    let c := (graphOfEdges F).connectedComponentMk v
    have hc : c ∈ supportComponents F := by
      rw [supportComponents, Finset.mem_image]
      exact ⟨v, hvSupport, rfl⟩
    have hvc : v ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
    have heSub := edge_toFinset_subset_component heF (hdiag e heF) hve hvc
    simp only [Finset.mem_biUnion]
    exact ⟨c, hc, Finset.mem_filter.mpr ⟨heF, heSub⟩⟩

theorem componentEdges_pairwiseDisjoint {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V)) :
    ((supportComponents F : Finset (graphOfEdges F).ConnectedComponent) :
      Set (graphOfEdges F).ConnectedComponent).PairwiseDisjoint
        (componentEdges F) := by
  classical
  intro c hc c' hc' hcc'
  change Disjoint (componentEdges F c) (componentEdges F c')
  rw [Finset.disjoint_left]
  intro e he he'
  have heSub : e.toFinset ⊆ ambientSetFinset c.supp :=
    (Finset.mem_filter.mp he).2
  have heSub' : e.toFinset ⊆ ambientSetFinset c'.supp :=
    (Finset.mem_filter.mp he').2
  let v : V := e.out.1
  have hve : v ∈ e.toFinset := by
    simpa [Sym2.mem_toFinset, v] using e.out_fst_mem
  have hdis := supportComponents_pairwiseDisjoint F hc hc' hcc'
  exact Finset.disjoint_left.mp hdis (heSub hve) (heSub' hve)

theorem sum_card_componentEdges {V : Type*} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (∑ c ∈ supportComponents F, (componentEdges F c).card) = F.card := by
  classical
  rw [← Finset.card_biUnion (componentEdges_pairwiseDisjoint F),
    biUnion_componentEdges_eq hdiag]

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

/-- The two-permutation overlap average reduces to a single relative
permutation, and then to the finite subgraph expansion. -/
theorem overlapAverage_eq_normalized_subgraph_sum (d : ℕ) (a : ℝ) :
    overlapAverage d (1 + a) =
      (∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        a ^ F.card *
          (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ)) /
        Fintype.card (Equiv.Perm (CubeVertex d)) := by
  classical
  let P := Fintype.card (Equiv.Perm (CubeVertex d))
  have hP : (P : ℝ) ≠ 0 := by positivity
  have hrow (σ : Equiv.Perm (CubeVertex d)) :
      (∑ τ : Equiv.Perm (CubeVertex d),
          (1 + a) ^ overlapCard d σ τ) =
        ∑ F ∈ (cubeGraph d).edgeFinset.powerset,
          a ^ F.card *
            (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
              fun τ ↦ F ⊆ cubePattern d τ).card : ℝ) := by
    rw [sum_overlap_pow_independent d σ]
    simpa using sum_overlap_pow_eq_subgraph_sum d 1 a
  rw [overlapAverage]
  simp_rw [hrow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A pointwise upper bound retaining the exact falling-factorial
normalization.  This is sharp enough for isolated matching components. -/
theorem normalized_permutation_fiber_le_exact (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
        F ⊆ cubePattern d σ).card : ℝ) /
        Fintype.card (Equiv.Perm (CubeVertex d)) ≤
      ((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d F *
        (d : ℝ) ^ ((edgeSupport F).card - overlapComponentCount d F) /
          ((2 ^ d).descFactorial (edgeSupport F).card : ℕ) := by
  classical
  let n := 2 ^ d
  let s := (edgeSupport F).card
  let k := overlapComponentCount d F
  let r := s - k
  have hs : s ≤ n := by
    dsimp [s, n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have hcount := card_perms_containing_edge_set_le_tree_bound d F hF
  have hperm : Fintype.card (Equiv.Perm (CubeVertex d)) = n.factorial := by
    rw [Fintype.card_perm, card_cubeVertex]
  have hfac : (n.factorial : ℝ) =
      ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) := by
    norm_cast
    exact (Nat.factorial_mul_descFactorial hs).symm
  rw [hperm, hfac]
  have hpos : (0 : ℝ) < ((n - s).factorial : ℕ) := by positivity
  calc
    (((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
          F ⊆ cubePattern d σ).card : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) ≤
      (((n ^ k * d ^ r * (n - s).factorial : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) := by
          gcongr
    _ = (n : ℝ) ^ k * (d : ℝ) ^ r /
        (n.descFactorial s : ℕ) := by
      push_cast
      field_simp
    _ = _ := by rfl

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem edgeSupport_union {V : Type*} [DecidableEq V]
    (F K : Finset (Sym2 V)) :
    edgeSupport (F ∪ K) = edgeSupport F ∪ edgeSupport K := by
  classical
  ext v
  simp only [edgeSupport, Finset.mem_biUnion, Finset.mem_union]
  aesop

theorem edgeSupport_eq_core_union_isolated {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    edgeSupport F =
      edgeSupport (overlapCore F) ∪ edgeSupport (isolatedEdges F) := by
  rw [← edgeSupport_union, overlapCore_union_isolatedEdges]

noncomputable def coreComponentToFull {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V))
    (c : (graphOfEdges (overlapCore F)).ConnectedComponent) :
    (graphOfEdges F).ConnectedComponent :=
  (graphOfEdges F).connectedComponentMk (componentRoot c).1

theorem connectedComponentMk_eq_coreComponentToFull {V : Type*}
    [Fintype V] [DecidableEq V] (F : Finset (Sym2 V))
    {c : (graphOfEdges (overlapCore F)).ConnectedComponent}
    {v : V} (hv : v ∈ c.supp) :
    (graphOfEdges F).connectedComponentMk v = coreComponentToFull F c := by
  classical
  rw [coreComponentToFull, ConnectedComponent.eq]
  have hreach : (graphOfEdges (overlapCore F)).Reachable v (componentRoot c).1 := by
    rw [← ConnectedComponent.eq]
    exact ((ConnectedComponent.mem_supp_iff c v).mp hv).trans
      ((ConnectedComponent.mem_supp_iff c (componentRoot c).1).mp
        (componentRoot c).2).symm
  exact hreach.mono (fun x y hxy => by
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    exact ⟨(Finset.mem_sdiff.mp hxy.1).1, hxy.2⟩)

noncomputable def isolatedEdgeToFullComponent {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V)) (e : Sym2 V) :
    (graphOfEdges F).ConnectedComponent :=
  (graphOfEdges F).connectedComponentMk e.out.1

theorem connectedComponentMk_eq_isolatedEdgeToFullComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {e : Sym2 V} (heF : e ∈ F)
    (heDiag : ¬e.IsDiag) {v : V} (hve : v ∈ e.toFinset) :
    (graphOfEdges F).connectedComponentMk v =
      isolatedEdgeToFullComponent F e := by
  classical
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hve' : v = e.out.1 ∨ v = e.out.2 := by
    rw [← hout, Sym2.toFinset_mk_eq] at hve
    simpa [eq_comm] using hve
  rcases hve' with rfl | rfl
  · rfl
  · rw [isolatedEdgeToFullComponent, ConnectedComponent.eq]
    exact (show (graphOfEdges F).Adj e.out.2 e.out.1 by
      rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
      have heq : s(e.out.2, e.out.1) = e := by
        simpa [Sym2.eq_swap] using hout
      have hne : e.out.1 ≠ e.out.2 := by
        intro h
        apply heDiag
        rw [← hout]
        simp [h]
      exact ⟨by simpa [heq] using heF, hne.symm⟩).reachable

noncomputable def fullComponentCover {V : Type*} [Fintype V]
    [DecidableEq V] (F : Finset (Sym2 V)) :
    Finset (graphOfEdges F).ConnectedComponent := by
  classical
  exact
    (supportComponents (overlapCore F)).image (coreComponentToFull F) ∪
      (isolatedEdges F).image (isolatedEdgeToFullComponent F)

theorem supportComponents_subset_core_image_union_isolated_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    supportComponents F ⊆ fullComponentCover F := by
  classical
  rw [fullComponentCover]
  intro c hc
  rw [supportComponents, Finset.mem_image] at hc
  obtain ⟨v, hvF, rfl⟩ := hc
  rw [edgeSupport_eq_core_union_isolated] at hvF
  rcases Finset.mem_union.mp hvF with hvCore | hvIso
  · apply Finset.mem_union_left
    rw [Finset.mem_image]
    let c := (graphOfEdges (overlapCore F)).connectedComponentMk v
    refine ⟨c, ?_, ?_⟩
    · rw [supportComponents, Finset.mem_image]
      exact ⟨v, hvCore, rfl⟩
    · exact (connectedComponentMk_eq_coreComponentToFull F
        (c := c) ConnectedComponent.connectedComponentMk_mem).symm
  · simp only [edgeSupport, Finset.mem_biUnion] at hvIso
    obtain ⟨e, heIso, hve⟩ := hvIso
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    refine ⟨e, heIso, ?_⟩
    exact (connectedComponentMk_eq_isolatedEdgeToFullComponent
      (isolatedEdges_subset F heIso) (hdiag e (isolatedEdges_subset F heIso))
        hve).symm

theorem overlapComponentCount_le_core_add_isolated (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    overlapComponentCount d F ≤
      overlapComponentCount d (overlapCore F) + (isolatedEdges F).card := by
  classical
  have hdiag : ∀ e ∈ F, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hF he))
  have hdiagCore : ∀ e ∈ overlapCore F, ¬e.IsDiag := fun e he =>
    hdiag e (Finset.mem_sdiff.mp he).1
  rw [← card_supportComponents_eq_overlapComponentCount d F hdiag,
    ← card_supportComponents_eq_overlapComponentCount d (overlapCore F)
      hdiagCore]
  calc
    (supportComponents F).card ≤
        (fullComponentCover F).card :=
      Finset.card_le_card
        (supportComponents_subset_core_image_union_isolated_image F hdiag)
    _ ≤ ((supportComponents (overlapCore F)).image
          (coreComponentToFull F)).card +
        ((isolatedEdges F).image (isolatedEdgeToFullComponent F)).card :=
      by rw [fullComponentCover]; exact Finset.card_union_le _ _
    _ ≤ (supportComponents (overlapCore F)).card +
        (isolatedEdges F).card := Nat.add_le_add Finset.card_image_le
          Finset.card_image_le

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

lemma self_le_two_pow (d : ℕ) : d ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ d := by positivity
      omega

theorem edgeSupport_card_eq_core_add_twice_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
    (edgeSupport F).card = (edgeSupport (overlapCore F)).card +
      2 * (isolatedEdges F).card := by
  rw [edgeSupport_eq_core_union_isolated,
    Finset.card_union_of_disjoint (edgeSupport_disjoint_core_isolated F),
    edgeSupport_isolatedEdges_card hdiag]

lemma pow_rank_mono_of_component_le {n d s k K : ℕ}
    (hdn : d ≤ n) (hkK : k ≤ K) (hKs : K ≤ s) :
    n ^ k * d ^ (s - k) ≤ n ^ K * d ^ (s - K) := by
  have hks : k ≤ s := hkK.trans hKs
  have hK : K = k + (K - k) := (Nat.add_sub_of_le hkK).symm
  have hs : s - k = (s - K) + (K - k) := by omega
  rw [hs, pow_add]
  calc
    n ^ k * (d ^ (s - K) * d ^ (K - k)) =
        n ^ k * d ^ (K - k) * d ^ (s - K) := by ring
    _ ≤ n ^ k * n ^ (K - k) * d ^ (s - K) := by
      gcongr
    _ = n ^ K * d ^ (s - K) := by rw [← pow_add, ← hK]

/-- Exact pointwise fiber bound after separating the isolated matching.
Only the inequality on component counts is needed: the monotonicity of the
tree code transfers it to the sharper core-plus-isolates exponent. -/
theorem normalized_permutation_fiber_le_core_isolated (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
        F ⊆ cubePattern d σ).card : ℝ) /
        Fintype.card (Equiv.Perm (CubeVertex d)) ≤
      ((2 ^ d : ℕ) : ℝ) ^
          (overlapComponentCount d (overlapCore F) + (isolatedEdges F).card) *
        (d : ℝ) ^
          ((edgeSupport (overlapCore F)).card -
              overlapComponentCount d (overlapCore F) +
            (isolatedEdges F).card) /
        (((2 ^ d).descFactorial
          ((edgeSupport (overlapCore F)).card +
            2 * (isolatedEdges F).card)) : ℕ) := by
  classical
  let n := 2 ^ d
  let s := (edgeSupport F).card
  let k := overlapComponentCount d F
  let C := overlapCore F
  let t := (isolatedEdges F).card
  let s₀ := (edgeSupport C).card
  let k₀ := overlapComponentCount d C
  let K := k₀ + t
  have hdiag : ∀ e ∈ F, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hF he))
  have hsEq : s = s₀ + 2 * t := by
    exact edgeSupport_card_eq_core_add_twice_isolated F hdiag
  have hcore : C ⊆ (cubeGraph d).edgeFinset := fun e he =>
    hF (Finset.mem_sdiff.mp he).1
  have hk₀s₀ : k₀ ≤ s₀ := by
    have := two_mul_overlapComponentCount_le_support_card d C hcore
    omega
  have hKs : K ≤ s := by
    dsimp [K]
    rw [hsEq]
    omega
  have hkK : k ≤ K := overlapComponentCount_le_core_add_isolated d F hF
  have hmono : n ^ k * d ^ (s - k) ≤ n ^ K * d ^ (s - K) :=
    pow_rank_mono_of_component_le (self_le_two_pow d) hkK hKs
  have hcount := card_perms_containing_edge_set_le_tree_bound d F hF
  have hcount' :
      ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
          F ⊆ cubePattern d σ).card ≤
        n ^ K * d ^ (s - K) * Nat.factorial (n - s) := by
    simpa [n, s, k] using
      hcount.trans (Nat.mul_le_mul_right (Nat.factorial (n - s)) hmono)
  have hsN : s ≤ n := by
    dsimp [s, n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have hperm : Fintype.card (Equiv.Perm (CubeVertex d)) = n.factorial := by
    rw [Fintype.card_perm, card_cubeVertex]
  have hfac : (n.factorial : ℝ) =
      ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) := by
    norm_cast
    exact (Nat.factorial_mul_descFactorial hsN).symm
  have hpos : (0 : ℝ) < ((n - s).factorial : ℕ) := by positivity
  rw [hperm, hfac]
  calc
    (((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
          F ⊆ cubePattern d σ).card : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) ≤
      (((n ^ K * d ^ (s - K) * (n - s).factorial : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) := by
          gcongr
    _ = (n : ℝ) ^ K * (d : ℝ) ^ (s - K) /
        (n.descFactorial s : ℕ) := by
      push_cast
      field_simp
    _ = _ := by
      have hexp : s₀ + 2 * t - K = (s₀ - k₀) + t := by
        dsimp [K]
        omega
      rw [hsEq, hexp]

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def certificateBlockSupport {d r k : ℕ}
    (z : CubeWalkCoverCertificate d r k)
    (i : Fin z.1.1.1.length) : Finset (CubeVertex d) := by
  classical
  exact (z.2 i).2.2.1.support.toFinset

def GoodCoreCertificate {d r k : ℕ}
    (z : CubeWalkCoverCertificate d r k) : Prop :=
  ∀ i : Fin z.1.1.1.length,
    (certificateBlockSupport z i).card = z.1.1.blocksFun i + 1 ∧
      3 ≤ (certificateBlockSupport z i).card

noncomputable def ambientInducedEdges (d : ℕ)
    (S : Finset (CubeVertex d)) : Finset (Sym2 (CubeVertex d)) := by
  classical
  exact (cubeGraph d).edgeFinset ∩ S.sym2

theorem ambientInducedEdges_eq_map (d : ℕ)
    (S : Finset (CubeVertex d)) :
    ambientInducedEdges d S =
      ((cubeGraph d).induce (S : Set (CubeVertex d))).edgeFinset.map
        (Function.Embedding.subtype
          (fun x ↦ x ∈ (S : Set (CubeVertex d)))).sym2Map := by
  classical
  aesop (add simp [ambientInducedEdges, Finset.ext_iff, Sym2.exists,
    Sym2.forall, SimpleGraph.adj_comm, hammingDist_comm])

theorem card_ambientInducedEdges (d : ℕ)
    (S : Finset (CubeVertex d)) :
    (ambientInducedEdges d S).card =
      ((cubeGraph d).induce (S : Set (CubeVertex d))).edgeFinset.card := by
  classical
  rw [ambientInducedEdges_eq_map]
  apply Finset.card_map

theorem mem_ambientInducedEdges_iff (d : ℕ)
    (S : Finset (CubeVertex d)) (e : Sym2 (CubeVertex d)) :
    e ∈ ambientInducedEdges d S ↔
      e ∈ (cubeGraph d).edgeFinset ∧ e.toFinset ⊆ S := by
  classical
  simp only [ambientInducedEdges, Finset.mem_inter, Finset.mem_sym2_iff]
  constructor
  · rintro ⟨he, hs⟩
    refine ⟨he, ?_⟩
    intro x hx
    exact hs x (by simpa [Sym2.mem_toFinset] using hx)
  · rintro ⟨he, hs⟩
    refine ⟨he, ?_⟩
    intro x hx
    exact hs (by simpa [Sym2.mem_toFinset] using hx)

noncomputable def certificateAllowedEdges {d r k : ℕ}
    (z : CubeWalkCoverCertificate d r k) :
    Finset (Sym2 (CubeVertex d)) := by
  classical
  exact Finset.univ.biUnion fun i : Fin z.1.1.1.length =>
    ambientInducedEdges d (certificateBlockSupport z i)

theorem two_mul_card_certificateAllowedEdges_le {d r k : ℕ}
    (z : CubeWalkCoverCertificate d r k) (hz : GoodCoreCertificate z) :
    2 * (certificateAllowedEdges z).card ≤ (d + 4) * (r - k) := by
  classical
  let c : Composition r := z.1.1
  have hlen : c.length = k := z.1.2
  have hblock (i : Fin c.length) :
      (certificateBlockSupport z i).card = c.blocksFun i + 1 ∧
        3 ≤ (certificateBlockSupport z i).card := hz i
  have hsumSub :
      (∑ i : Fin c.length, ((certificateBlockSupport z i).card - 2)) =
        r - k := by
    have hbi : ∀ i : Fin c.length, 1 ≤ c.blocksFun i := fun i =>
      c.one_le_blocksFun i
    calc
      (∑ i : Fin c.length, ((certificateBlockSupport z i).card - 2)) =
          ∑ i : Fin c.length, (c.blocksFun i - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [(hblock i).1]
            omega
      _ = (∑ i : Fin c.length, c.blocksFun i) -
          ∑ _i : Fin c.length, 1 := by
            simpa using Finset.sum_tsub_distrib
              (Finset.univ : Finset (Fin c.length))
              (f := c.blocksFun) (g := fun _ => 1)
              (fun i _ => hbi i)
      _ = r - k := by rw [c.sum_blocksFun]; simp [hlen]
  calc
    2 * (certificateAllowedEdges z).card ≤
        2 * ∑ i : Fin c.length,
          (ambientInducedEdges d (certificateBlockSupport z i)).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ i : Fin c.length,
        2 * (ambientInducedEdges d (certificateBlockSupport z i)).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ i : Fin c.length,
        (d + 4) * ((certificateBlockSupport z i).card - 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [card_ambientInducedEdges]
      exact two_mul_card_edges_induce_cube_le d _ (hblock i).2
    _ = (d + 4) * (r - k) := by
      rw [← Finset.mul_sum, hsumSub]

theorem supportComponent_card_three_le_of_no_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ F, ¬e.IsDiag)
    (hno : ∀ e ∈ F, ¬IsIsolatedEdge F e)
    {c : (graphOfEdges F).ConnectedComponent}
    (hc : c ∈ supportComponents F) :
    3 ≤ (ambientSetFinset c.supp).card := by
  classical
  rw [supportComponents, Finset.mem_image] at hc
  obtain ⟨v, hvSupport, rfl⟩ := hc
  simp only [edgeSupport, Finset.mem_biUnion] at hvSupport
  obtain ⟨e, heF, hve⟩ := hvSupport
  have hediag := hdiag e heF
  have hnotIso := hno e heF
  unfold IsIsolatedEdge at hnotIso
  push_neg at hnotIso
  obtain ⟨f, hfF, hfe, hndis⟩ := hnotIso heF
  have hfdiag := hdiag f hfF
  have hvcomp : v ∈ ((graphOfEdges F).connectedComponentMk v).supp :=
    ConnectedComponent.connectedComponentMk_mem
  have heSub := edge_toFinset_subset_component heF hediag hve hvcomp
  obtain ⟨x, hxe, hxf⟩ := Finset.not_disjoint_iff.mp hndis
  have hxcomp : x ∈ ((graphOfEdges F).connectedComponentMk v).supp := by
    exact mem_ambientSetFinset.mp (heSub hxe)
  have hfSub := edge_toFinset_subset_component hfF hfdiag hxf hxcomp
  have hunion : e.toFinset ∪ f.toFinset ⊆
      ambientSetFinset ((graphOfEdges F).connectedComponentMk v).supp :=
    Finset.union_subset heSub hfSub
  calc
    3 = (e.toFinset ∪ f.toFinset).card :=
      (card_union_sym2_toFinset_eq_three hediag hfdiag hfe.symm hndis).symm
    _ ≤ _ := Finset.card_le_card hunion

@[simp] theorem coe_ambientSetFinset {V : Type*} [Fintype V]
    (S : Set V) : (ambientSetFinset S : Set V) = S := by
  classical
  ext v
  simp [ambientSetFinset]

/-- A core overlap graph is encoded by a certificate whose individual walk
supports are exactly its nontrivial connected components. -/
theorem core_exists_good_certificate (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (hcore : overlapCore F = F) :
    ∃ z : CubeWalkCoverCertificate d
        ((edgeSupport F).card - overlapComponentCount d F)
        (overlapComponentCount d F),
      GoodCoreCertificate z ∧ F ⊆ certificateAllowedEdges z := by
  classical
  let C := supportComponents F
  let L : List (graphOfEdges F).ConnectedComponent := C.toList
  let s := (edgeSupport F).card
  let k := overlapComponentCount d F
  have hdiag : ∀ e ∈ F, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hF he))
  have hcardC : C.card = k := by
    exact card_supportComponents_eq_overlapComponentCount d F hdiag
  have hcard3 (c : (graphOfEdges F).ConnectedComponent) (hc : c ∈ C) :
      3 ≤ (ambientSetFinset c.supp).card := by
    apply supportComponent_card_three_le_of_no_isolated hdiag
    · intro e heF' heIso
      have heInIso : e ∈ isolatedEdges F :=
        Finset.mem_filter.mpr ⟨heF', heIso⟩
      have heCore : e ∈ overlapCore F := by simpa [hcore] using heF'
      exact (Finset.mem_sdiff.mp heCore).2 heInIso
    · simpa [C] using hc
  have hsumSub :
      (∑ c ∈ C, ((ambientSetFinset c.supp).card - 1)) = s - k := by
    have hone : ∀ c ∈ C, 1 ≤ (ambientSetFinset c.supp).card := by
      intro c hc
      exact (hcard3 c hc).trans' (by omega)
    calc
      (∑ c ∈ C, ((ambientSetFinset c.supp).card - 1)) =
          (∑ c ∈ C, (ambientSetFinset c.supp).card) -
            ∑ _c ∈ C, 1 := by
              simpa using Finset.sum_tsub_distrib C
                (f := fun c => (ambientSetFinset c.supp).card)
                (g := fun _ => 1) hone
      _ = s - k := by
        rw [show (∑ c ∈ C, (ambientSetFinset c.supp).card) = s by
          simpa [C, s] using sum_card_supportComponents hdiag]
        simp [hcardC]
  let blocks : List ℕ :=
    L.map fun c => (ambientSetFinset c.supp).card - 1
  have hblocksPos : ∀ {i}, i ∈ blocks → 0 < i := by
    intro i hi
    simp only [blocks, List.mem_map] at hi
    obtain ⟨c, hcL, rfl⟩ := hi
    have hcC : c ∈ C := by simpa [L] using hcL
    have := hcard3 c hcC
    omega
  have hblocksSum : blocks.sum = s - k := by
    simpa [blocks, L] using hsumSub
  let comp : Composition (s - k) := ⟨blocks, hblocksPos, hblocksSum⟩
  have hlen : comp.length = k := by
    change blocks.length = k
    simp [blocks, L, hcardC]
  have hblocksLen : comp.length = L.length := by
    change blocks.length = L.length
    simp [blocks]
  have hget (i : Fin comp.length) :
      comp.blocksFun i =
        (ambientSetFinset (L.get (Fin.cast hblocksLen i)).supp).card - 1 := by
    simp [comp, Composition.blocksFun, blocks]
  have hLC (i : Fin comp.length) : L.get (Fin.cast hblocksLen i) ∈ C := by
    have hm := L.get_mem (Fin.cast hblocksLen i)
    have hm' : L.get (Fin.cast hblocksLen i) ∈ C.toList := by
      simpa only [L] using hm
    exact Finset.mem_toList.mp hm'
  choose w hw using fun i : Fin comp.length =>
    connectedCubeSet_exists_covering_walk d
      (ambientSetFinset (L.get (Fin.cast hblocksLen i)).supp)
      (by
        rw [coe_ambientSetFinset]
        exact supportComponent_connected_in_cube d hF
          (c := L.get (Fin.cast hblocksLen i)))
  let tuple : CubeWalkTuple d (s - k) comp := fun i =>
    ⟨(w i).1, (w i).2.1, ⟨(w i).2.2.1, by
      rw [hget i]
      exact (w i).2.2.2⟩⟩
  let cert : CubeWalkCoverCertificate d (s - k) k :=
    ⟨⟨comp, hlen⟩, tuple⟩
  have hcertBlock (i : Fin comp.length) :
      certificateBlockSupport cert i =
        ambientSetFinset (L.get (Fin.cast hblocksLen i)).supp := by
    change (w i).2.2.1.support.toFinset = _
    exact hw i
  have hgood : GoodCoreCertificate cert := by
    intro i
    have hi3 := hcard3 (L.get (Fin.cast hblocksLen i)) (hLC i)
    rw [hcertBlock i]
    constructor
    · change _ = comp.blocksFun i + 1
      rw [hget i]
      omega
    · exact hi3
  refine ⟨cert, hgood, ?_⟩
  intro e heF'
  let v : CubeVertex d := e.out.1
  have hve : v ∈ e.toFinset := by
    simpa [Sym2.mem_toFinset, v] using e.out_fst_mem
  have hvSupport : v ∈ edgeSupport F := by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨e, heF', hve⟩
  let c := (graphOfEdges F).connectedComponentMk v
  have hcC : c ∈ C := by
    rw [show C = supportComponents F by rfl, supportComponents,
      Finset.mem_image]
    exact ⟨v, hvSupport, rfl⟩
  have hcL : c ∈ L := by simpa [L] using hcC
  obtain ⟨j, hj⟩ := List.get_of_mem hcL
  let i : Fin comp.length := Fin.cast hblocksLen.symm j
  have hci : L.get (Fin.cast hblocksLen i) = c := by
    simpa [i] using hj
  have hvc : v ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
  have heSub : e.toFinset ⊆ ambientSetFinset c.supp :=
    edge_toFinset_subset_component heF' (hdiag e heF') hve hvc
  simp only [certificateAllowedEdges, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨i, mem_ambientInducedEdges_iff d _ e |>.2 ⟨hF heF', ?_⟩⟩
  rw [hcertBlock i, hci]
  exact heSub

noncomputable def coreEdgeSets (d r k : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (cubeGraph d).edgeFinset.powerset.filter fun F =>
    overlapCore F = F ∧
      (edgeSupport F).card - overlapComponentCount d F = r ∧
      overlapComponentCount d F = k

theorem goodCertificate_exists_congr {d r k r' k' : ℕ}
    {F : Finset (Sym2 (CubeVertex d))}
    (hr : r = r') (hk : k = k')
    (h : ∃ z : CubeWalkCoverCertificate d r k,
      GoodCoreCertificate z ∧ F ⊆ certificateAllowedEdges z) :
    ∃ z : CubeWalkCoverCertificate d r' k',
      GoodCoreCertificate z ∧ F ⊆ certificateAllowedEdges z := by
  subst r'
  subst k'
  exact h

theorem coreCertificate_exists (d r k : ℕ)
    (F : coreEdgeSets d r k) :
    ∃ z : CubeWalkCoverCertificate d r k,
      GoodCoreCertificate z ∧ F.1 ⊆ certificateAllowedEdges z := by
  classical
  have hmem := Finset.mem_filter.mp F.2
  rcases hmem.2 with ⟨hcore, hr, hk⟩
  exact goodCertificate_exists_congr hr hk
    (core_exists_good_certificate d F.1
      (Finset.mem_powerset.mp hmem.1) hcore)

noncomputable def coreCertificateFor (d r k : ℕ)
    (F : coreEdgeSets d r k) : CubeWalkCoverCertificate d r k :=
  Classical.choose (coreCertificate_exists d r k F)

theorem coreCertificateFor_spec (d r k : ℕ)
    (F : coreEdgeSets d r k) :
    GoodCoreCertificate (coreCertificateFor d r k F) ∧
      F.1 ⊆ certificateAllowedEdges (coreCertificateFor d r k F) := by
  classical
  exact Classical.choose_spec (coreCertificate_exists d r k F)

noncomputable def coreCertificateFiber (d r k : ℕ)
    (z : CubeWalkCoverCertificate d r k) :
    Finset (coreEdgeSets d r k) := by
  classical
  exact (coreEdgeSets d r k).attach.filter fun F =>
    coreCertificateFor d r k F = z

noncomputable def coreCertificateFiberValues (d r k : ℕ)
    (z : CubeWalkCoverCertificate d r k) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (coreCertificateFiber d r k z).map
      ⟨Subtype.val, Subtype.val_injective⟩

theorem coreCertificateFiberValues_subset (d r k : ℕ)
    (z : CubeWalkCoverCertificate d r k) :
    coreCertificateFiberValues d r k z ⊆
      (certificateAllowedEdges z).powerset := by
  classical
  intro F hF
  rw [coreCertificateFiberValues, Finset.mem_map] at hF
  obtain ⟨F', hF', rfl⟩ := hF
  have hcode := (Finset.mem_filter.mp hF').2
  rw [Finset.mem_powerset]
  simpa [hcode] using (coreCertificateFor_spec d r k F').2

theorem sum_coreCertificateFiber_eq (d r k : ℕ) (a : ℝ)
    (z : CubeWalkCoverCertificate d r k) :
    (∑ F ∈ coreCertificateFiber d r k z, a ^ F.1.card) =
      ∑ F ∈ coreCertificateFiberValues d r k z, a ^ F.card := by
  classical
  rw [coreCertificateFiberValues]
  simp

theorem sum_coreCertificateFiber_le (d r k : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hc : 1 + a ≤ 3)
    (z : CubeWalkCoverCertificate d r k) (hz : GoodCoreCertificate z) :
    (∑ F ∈ coreCertificateFiber d r k z, a ^ F.1.card) ≤
      (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) := by
  classical
  rw [sum_coreCertificateFiber_eq]
  calc
    (∑ F ∈ coreCertificateFiberValues d r k z, a ^ F.card) ≤
        ∑ F ∈ (certificateAllowedEdges z).powerset, a ^ F.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact coreCertificateFiberValues_subset d r k z
      · intro F hF hnot
        positivity
    _ = (1 + a) ^ (certificateAllowedEdges z).card := by
      calc
        (∑ F ∈ (certificateAllowedEdges z).powerset, a ^ F.card) =
            ∏ _e ∈ certificateAllowedEdges z, (1 + a) := by
              rw [Finset.prod_one_add]
              apply Finset.sum_congr rfl
              intro F hF
              simp
        _ = _ := by simp
    _ ≤ (3 : ℝ) ^ (certificateAllowedEdges z).card := by
      exact pow_le_pow_left₀ (by positivity) hc _
    _ ≤ (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) := by
      have hdens := two_mul_card_certificateAllowedEdges_le z hz
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by
        calc
          (certificateAllowedEdges z).card * 2 =
              2 * (certificateAllowedEdges z).card := Nat.mul_comm _ _
          _ ≤ _ := hdens)

theorem sum_coreEdgeSets_weight_le (d r k : ℕ) (a q : ℝ)
    (ha : 0 ≤ a) (hc : 1 + a ≤ 3) (hq : 0 ≤ q) :
    (∑ F ∈ coreEdgeSets d r k, a ^ F.card * q ^ r) ≤
      (2 ^ r * (2 ^ d) ^ k * d ^ (2 * r) : ℕ) *
        (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) * q ^ r := by
  classical
  have hfiber (z : CubeWalkCoverCertificate d r k) :
      (∑ F ∈ coreCertificateFiber d r k z, a ^ F.1.card) ≤
        (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) := by
    by_cases hz : GoodCoreCertificate z
    · exact sum_coreCertificateFiber_le d r k a ha hc z hz
    · have hempty :
          coreCertificateFiber d r k z = ∅ := by
        ext F
        constructor
        · intro hF
          rw [coreCertificateFiber] at hF
          have hcode := (Finset.mem_filter.mp hF).2
          exact (hz (hcode ▸ (coreCertificateFor_spec d r k F).1)).elim
        · simp
      rw [hempty]
      simp
  calc
    (∑ F ∈ coreEdgeSets d r k, a ^ F.card * q ^ r) =
        (∑ F ∈ coreEdgeSets d r k, a ^ F.card) * q ^ r := by
      rw [Finset.sum_mul]
    _ = (∑ F ∈ (coreEdgeSets d r k).attach, a ^ F.1.card) * q ^ r := by
      exact congrArg (fun x : ℝ => x * q ^ r)
        (Finset.sum_attach (coreEdgeSets d r k) (fun F => a ^ F.card)).symm
    _ = (∑ z : CubeWalkCoverCertificate d r k,
          ∑ F ∈ coreCertificateFiber d r k z,
            a ^ F.1.card) * q ^ r := by
      rw [show (∑ z : CubeWalkCoverCertificate d r k,
          ∑ F ∈ coreCertificateFiber d r k z, a ^ F.1.card) =
          ∑ F ∈ (coreEdgeSets d r k).attach, a ^ F.1.card by
        simpa only [coreCertificateFiber] using
          Finset.sum_fiberwise (coreEdgeSets d r k).attach
            (coreCertificateFor d r k) (fun F => a ^ F.1.card)]
    _ ≤ (Fintype.card (CubeWalkCoverCertificate d r k) *
          (3 : ℝ) ^ (((d + 4) * (r - k)) / 2)) * q ^ r := by
      gcongr
      calc
        (∑ z : CubeWalkCoverCertificate d r k,
            ∑ F ∈ coreCertificateFiber d r k z,
              a ^ F.1.card) ≤
          ∑ _z : CubeWalkCoverCertificate d r k,
            (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) := by
              exact Finset.sum_le_sum fun z _ => hfiber z
        _ = _ := by simp
    _ ≤ ((2 ^ r * (2 ^ d) ^ k * d ^ (2 * r) : ℕ) : ℝ) *
          (3 : ℝ) ^ (((d + 4) * (r - k)) / 2) * q ^ r := by
      gcongr
      exact_mod_cast card_cubeWalkCoverCertificate_le d r k
    _ = _ := by norm_num

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem overlapCore_idem {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : overlapCore (overlapCore F) = overlapCore F := by
  classical
  have hiso : isolatedEdges (overlapCore F) = ∅ := by
    ext e
    rw [isolatedEdges]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hiso⟩
      exact (overlapCore_hasNoIsolatedEdge F he hiso).elim
    · intro he
      have : False := by simpa using he
      exact this.elim
  rw [overlapCore, hiso, Finset.sdiff_empty]

noncomputable def coreAllEdgeSets (d : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (cubeGraph d).edgeFinset.powerset.filter fun C => overlapCore C = C

theorem overlapCore_mem_coreAllEdgeSets (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    overlapCore F ∈ coreAllEdgeSets d := by
  classical
  rw [coreAllEdgeSets, Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (fun e he =>
    hF (Finset.mem_sdiff.mp he).1), overlapCore_idem F⟩

theorem isolatedEdges_subset_cube (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    isolatedEdges F ⊆ (cubeGraph d).edgeFinset :=
  (isolatedEdges_subset F).trans hF

theorem card_eq_core_add_isolated {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) :
    F.card = (overlapCore F).card + (isolatedEdges F).card := by
  rw [← Finset.card_union_of_disjoint (disjoint_overlapCore_isolatedEdges F),
    overlapCore_union_isolatedEdges]

noncomputable def overlapCoreFiber (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (cubeGraph d).edgeFinset.powerset.filter fun F =>
    overlapCore F = C ∧ (isolatedEdges F).card = t

theorem card_overlapCoreFiber_le_choose (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    (overlapCoreFiber d C t).card ≤
      Nat.choose (cubeEdgeCount d) t := by
  classical
  let T := (cubeGraph d).edgeFinset.powersetCard t
  have hcardT : T.card = Nat.choose (cubeEdgeCount d) t := by
    rw [Finset.card_powersetCard, cube_card_edges]
    rfl
  rw [← hcardT]
  apply Finset.card_le_card_of_injOn (isolatedEdges)
  · intro F hF
    have hmem := Finset.mem_filter.mp hF
    change isolatedEdges F ∈ (cubeGraph d).edgeFinset.powersetCard t
    rw [Finset.mem_powersetCard]
    exact ⟨isolatedEdges_subset_cube d (Finset.mem_powerset.mp hmem.1), hmem.2.2⟩
  · intro F hF K hK heq
    have hFC := (Finset.mem_filter.mp hF).2.1
    have hKC := (Finset.mem_filter.mp hK).2.1
    calc
      F = overlapCore F ∪ isolatedEdges F :=
        (overlapCore_union_isolatedEdges F).symm
      _ = overlapCore K ∪ isolatedEdges K := by rw [hFC, hKC, heq]
      _ = K := overlapCore_union_isolatedEdges K

theorem overlapCoreFiber_maps (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ∈ (cubeGraph d).edgeFinset.powerset) :
    F ∈ overlapCoreFiber d (overlapCore F) (isolatedEdges F).card := by
  classical
  exact Finset.mem_filter.mpr ⟨hF, rfl, rfl⟩

theorem sum_powerset_by_core_isolated (d : ℕ)
    (f : Finset (Sym2 (CubeVertex d)) → ℝ) :
    (∑ F ∈ (cubeGraph d).edgeFinset.powerset, f F) =
      ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          ∑ F ∈ overlapCoreFiber d C t, f F := by
  classical
  let U := (cubeGraph d).edgeFinset.powerset
  let P := coreAllEdgeSets d ×ˢ Finset.range (cubeEdgeCount d + 1)
  let g : Finset (Sym2 (CubeVertex d)) →
      Finset (Sym2 (CubeVertex d)) × ℕ := fun F =>
    (overlapCore F, (isolatedEdges F).card)
  have hmaps : ∀ F ∈ U, g F ∈ P := by
    intro F hF
    change g F ∈ coreAllEdgeSets d ×ˢ Finset.range (cubeEdgeCount d + 1)
    rw [Finset.mem_product]
    refine ⟨overlapCore_mem_coreAllEdgeSets d (Finset.mem_powerset.mp hF), ?_⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hsub := isolatedEdges_subset_cube d (Finset.mem_powerset.mp hF)
    simpa [cubeEdgeCount, cube_card_edges] using Finset.card_le_card hsub
  have hfiber (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
      U.filter (fun F => g F = (C, t)) = overlapCoreFiber d C t := by
    ext F
    simp [U, g, overlapCoreFiber, and_assoc]
  calc
    (∑ F ∈ (cubeGraph d).edgeFinset.powerset, f F) =
        ∑ F ∈ U, f F := by rfl
    _ = ∑ p ∈ P, ∑ F ∈ U.filter (fun F => g F = p), f F := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps f).symm
    _ = ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          ∑ F ∈ overlapCoreFiber d C t, f F := by
      change (∑ p ∈ coreAllEdgeSets d ×ˢ
        Finset.range (cubeEdgeCount d + 1),
          ∑ F ∈ U.filter (fun F => g F = p), f F) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfiber]

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def coreIsolatedUpperTerm (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) : ℝ :=
  a ^ (C.card + t) *
    (((2 ^ d : ℕ) : ℝ) ^ (overlapComponentCount d C + t) *
      (d : ℝ) ^
        ((edgeSupport C).card - overlapComponentCount d C + t) /
      (((2 ^ d).descFactorial ((edgeSupport C).card + 2 * t)) : ℕ))

theorem overlapAverage_eq_sum_normalized_fibers (d : ℕ) (a : ℝ) :
    overlapAverage d (1 + a) =
      ∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        a ^ F.card *
          ((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ) /
            Fintype.card (Equiv.Perm (CubeVertex d))) := by
  rw [overlapAverage_eq_normalized_subgraph_sum]
  calc
    (∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        a ^ F.card *
          (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ)) /
        Fintype.card (Equiv.Perm (CubeVertex d)) =
      ∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        (a ^ F.card *
          (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ)) /
          Fintype.card (Equiv.Perm (CubeVertex d)) := by
            rw [Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro F hF
      ring

theorem overlapAverage_le_sum_core_isolated (d : ℕ) (a : ℝ)
    (ha : 0 ≤ a) :
    overlapAverage d (1 + a) ≤
      ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (Nat.choose (cubeEdgeCount d) t : ℝ) *
            coreIsolatedUpperTerm d a C t := by
  classical
  rw [overlapAverage_eq_sum_normalized_fibers]
  calc
    (∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        a ^ F.card *
          ((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ) /
            Fintype.card (Equiv.Perm (CubeVertex d)))) ≤
      ∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        coreIsolatedUpperTerm d a (overlapCore F) (isolatedEdges F).card := by
      apply Finset.sum_le_sum
      intro F hF
      have hsub := Finset.mem_powerset.mp hF
      have hfiber := normalized_permutation_fiber_le_core_isolated d F hsub
      rw [coreIsolatedUpperTerm, ← card_eq_core_add_isolated F]
      exact mul_le_mul_of_nonneg_left hfiber (pow_nonneg ha _)
    _ = ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          ∑ F ∈ overlapCoreFiber d C t,
            coreIsolatedUpperTerm d a (overlapCore F)
              (isolatedEdges F).card :=
      sum_powerset_by_core_isolated d _
    _ = ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (overlapCoreFiber d C t).card *
            coreIsolatedUpperTerm d a C t := by
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro t ht
      calc
        (∑ F ∈ overlapCoreFiber d C t,
            coreIsolatedUpperTerm d a (overlapCore F)
              (isolatedEdges F).card) =
            ∑ _F ∈ overlapCoreFiber d C t,
              coreIsolatedUpperTerm d a C t := by
                apply Finset.sum_congr rfl
                intro F hF
                have hmem := (Finset.mem_filter.mp hF).2
                rw [hmem.1, hmem.2]
        _ = _ := by simp
    _ ≤ ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (Nat.choose (cubeEdgeCount d) t : ℝ) *
            coreIsolatedUpperTerm d a C t := by
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro t ht
      have hcard := card_overlapCoreFiber_le_choose d C t
      have hterm : 0 ≤ coreIsolatedUpperTerm d a C t := by
        unfold coreIsolatedUpperTerm
        positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hterm

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def coreWeight (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) : ℝ :=
  a ^ C.card *
    (((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d C *
      (d : ℝ) ^ ((edgeSupport C).card - overlapComponentCount d C) /
      (((2 ^ d).descFactorial (edgeSupport C).card) : ℕ))

noncomputable def isolatedWeight (d : ℕ) (a : ℝ)
    (s t : ℕ) : ℝ :=
  (Nat.choose (cubeEdgeCount d) t : ℝ) * a ^ t *
    (((2 ^ d : ℕ) : ℝ) ^ t * (d : ℝ) ^ t /
      (((2 ^ d - s).descFactorial (2 * t)) : ℕ))

theorem choose_mul_coreIsolatedUpperTerm_eq (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ)
    (hk : overlapComponentCount d C ≤ (edgeSupport C).card) :
    (Nat.choose (cubeEdgeCount d) t : ℝ) *
        coreIsolatedUpperTerm d a C t =
      coreWeight d a C * isolatedWeight d a (edgeSupport C).card t := by
  let n := 2 ^ d
  let s := (edgeSupport C).card
  let k := overlapComponentCount d C
  let r := s - k
  have hdescNat := Nat.descFactorial_mul_descFactorial
    (n := n) (k := s) (m := s + 2 * t) (by omega : s ≤ s + 2 * t)
  have hdesc :
      (((n - s).descFactorial (2 * t) : ℕ) : ℝ) *
          (n.descFactorial s : ℕ) =
        (n.descFactorial (s + 2 * t) : ℕ) := by
    exact_mod_cast (by simpa using hdescNat)
  have hr : s - k + t = r + t := rfl
  unfold coreIsolatedUpperTerm coreWeight isolatedWeight
  dsimp [n, s, k, r] at hdesc ⊢
  rw [pow_add, pow_add, pow_add]
  push_cast
  simp only [div_eq_mul_inv]
  rw [← hdesc, mul_inv]
  ring

theorem coreWeight_le_rank_weight (d : ℕ) (a : ℝ)
    (ha : 0 ≤ a) {C : Finset (Sym2 (CubeVertex d))}
    (hC : C ∈ coreAllEdgeSets d) :
    coreWeight d a C ≤
      a ^ C.card *
        ((((81 : ℝ) * d) / (2 ^ d : ℕ)) ^
          ((edgeSupport C).card - overlapComponentCount d C)) := by
  classical
  have hmem := Finset.mem_filter.mp hC
  have hsub := Finset.mem_powerset.mp hmem.1
  let n := 2 ^ d
  let s := (edgeSupport C).card
  let k := overlapComponentCount d C
  let r := s - k
  have hn : 0 < n := by positivity
  have hs : s ≤ n := by
    dsimp [s, n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have h2k := two_mul_overlapComponentCount_le_support_card d C hsub
  have hk : k ≤ s := by omega
  have hs2 : s ≤ 2 * r := by omega
  have hratio := rooted_factorial_ratio_le hn hs hk hs2
  have hfac : ((n - s).factorial : ℝ) *
      (n.descFactorial s : ℕ) = (n.factorial : ℕ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hs
  have hratio' :
      (n : ℝ) ^ k / (n.descFactorial s : ℕ) ≤
        ((81 : ℝ) / n) ^ r := by
    calc
      (n : ℝ) ^ k / (n.descFactorial s : ℕ) =
          (n : ℝ) ^ k * ((n - s).factorial : ℕ) /
            (n.factorial : ℕ) := by
              rw [← hfac]
              field_simp
      _ ≤ _ := hratio
  unfold coreWeight
  dsimp [n, s, k, r] at hratio' ⊢
  calc
    a ^ C.card *
        (((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d C *
          (d : ℝ) ^ ((edgeSupport C).card - overlapComponentCount d C) /
          ((2 ^ d).descFactorial (edgeSupport C).card : ℕ)) =
      a ^ C.card * (d : ℝ) ^
          ((edgeSupport C).card - overlapComponentCount d C) *
        (((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d C /
          ((2 ^ d).descFactorial (edgeSupport C).card : ℕ)) := by ring
    _ ≤ a ^ C.card * (d : ℝ) ^
          ((edgeSupport C).card - overlapComponentCount d C) *
        (((81 : ℝ) / (2 ^ d : ℕ)) ^
          ((edgeSupport C).card - overlapComponentCount d C)) := by
      gcongr
    _ = a ^ C.card *
        ((d : ℝ) * ((81 : ℝ) / (2 ^ d : ℕ))) ^
          ((edgeSupport C).card - overlapComponentCount d C) := by
      rw [mul_pow]
      ring
    _ = _ := by congr 2 <;> ring

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def coreCopyOfPermutation (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (a : { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ }) :
    SimpleGraph.Copy (overlapSupportGraph d (overlapCore F)) (cubeGraph d) :=
  permutationCopyOfSubset d (overlapCore F) a.1 (fun e he =>
    a.2 (Finset.mem_sdiff.mp he).1)

noncomputable def unusedCoreVertices (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (f : SimpleGraph.Copy (overlapSupportGraph d (overlapCore F))
      (cubeGraph d)) : Finset (CubeVertex d) := by
  classical
  exact Finset.univ \ Finset.univ.image f

theorem card_unusedCoreVertices (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (f : SimpleGraph.Copy (overlapSupportGraph d (overlapCore F))
      (cubeGraph d)) :
    (unusedCoreVertices d f).card =
      2 ^ d - (edgeSupport (overlapCore F)).card := by
  classical
  have himage :
      (Finset.univ.image (fun x : edgeSupport (overlapCore F) => f x)).card =
        (edgeSupport (overlapCore F)).card := by
    calc
      (Finset.univ.image (fun x : edgeSupport (overlapCore F) => f x)).card =
          (Finset.univ : Finset (edgeSupport (overlapCore F))).card := by
            apply Finset.card_image_iff.mpr
            intro x hx y hy hxy
            exact f.injective hxy
      _ = (edgeSupport (overlapCore F)).card := by simp
  rw [unusedCoreVertices, Finset.card_sdiff]
  · simp only [Finset.inter_univ]
    rw [Finset.card_univ, card_cubeVertex, himage]

abbrev CoreIsolatedCode (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :=
  Σ f : SimpleGraph.Copy (overlapSupportGraph d (overlapCore F))
      (cubeGraph d),
    ∀ _e : isolatedEdges F, (unusedCoreVertices d f) × Fin d

noncomputable def isolatedEndpointAdj (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (a : { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ })
    (e : isolatedEdges F) :
    (cubeGraph d).Adj (a.1 e.1.out.1) (a.1 e.1.out.2) := by
  let x : edgeSupport F := ⟨e.1.out.1, by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨e.1, isolatedEdges_subset F e.2, by
      simpa [Sym2.mem_toFinset] using e.1.out_fst_mem⟩⟩
  let y : edgeSupport F := ⟨e.1.out.2, by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨e.1, isolatedEdges_subset F e.2, by
      simpa [Sym2.mem_toFinset] using e.1.out_snd_mem⟩⟩
  have hdiag : ¬e.1.IsDiag :=
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp
        (hF (isolatedEdges_subset F e.2)))
  have hxy : (overlapSupportGraph d F).Adj x y := by
    rw [overlapSupportGraph, SimpleGraph.induce_adj]
    rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    change s(e.1.out.1, e.1.out.2) ∈ F ∧ e.1.out.1 ≠ e.1.out.2
    rw [hout]
    refine ⟨isolatedEdges_subset F e.2, ?_⟩
    intro heq
    apply hdiag
    rw [← hout]
    simp [heq]
  exact (permutationCopyOfSubset d F a.1 a.2).toHom.map_rel hxy

theorem isolatedEndpoint_unused (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (a : { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ })
    (e : isolatedEdges F) :
    a.1 e.1.out.1 ∈ unusedCoreVertices d (coreCopyOfPermutation d F hF a) := by
  classical
  rw [unusedCoreVertices, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  rintro ⟨x, hx, hxe⟩
  have hsource : e.1.out.1 = x.1 := a.1.injective hxe.symm
  have heIsoSupport : e.1.out.1 ∈ edgeSupport (isolatedEdges F) := by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨e.1, e.2, by simpa [Sym2.mem_toFinset] using e.1.out_fst_mem⟩
  have hxCore : x.1 ∈ edgeSupport (overlapCore F) := x.2
  exact Finset.disjoint_left.mp (edgeSupport_disjoint_core_isolated F)
    hxCore (hsource ▸ heIsoSupport)

noncomputable def coreIsolatedCode (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (a : { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ }) :
    CoreIsolatedCode d F := by
  let f := coreCopyOfPermutation d F hF a
  refine ⟨f, fun e => ⟨⟨a.1 e.1.out.1, ?_⟩,
    cubeStepCoordinate d (isolatedEndpointAdj d hF a e)⟩⟩
  exact isolatedEndpoint_unused d hF a e

noncomputable def coreIsolatedCodeEndpoint {d : ℕ}
    {F : Finset (Sym2 (CubeVertex d))}
    (z : CoreIsolatedCode d F) (e : isolatedEdges F) : CubeVertex d :=
  (z.2 e).1.1

noncomputable def coreIsolatedCodeCoordinate {d : ℕ}
    {F : Finset (Sym2 (CubeVertex d))}
    (z : CoreIsolatedCode d F) (e : isolatedEdges F) : Fin d :=
  (z.2 e).2

theorem coreIsolatedCode_eq_on_edgeSupport (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset)
    (a b : { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ })
    (hab : coreIsolatedCode d F hF a = coreIsolatedCode d F hF b) :
    ∀ x ∈ edgeSupport F, a.1 x = b.1 x := by
  classical
  have hcopy : coreCopyOfPermutation d F hF a =
      coreCopyOfPermutation d F hF b := congrArg Sigma.fst hab
  intro x hx
  rw [edgeSupport_eq_core_union_isolated] at hx
  rcases Finset.mem_union.mp hx with hxCore | hxIso
  · let xC : edgeSupport (overlapCore F) := ⟨x, hxCore⟩
    have hxval := congrArg (fun f : SimpleGraph.Copy
        (overlapSupportGraph d (overlapCore F)) (cubeGraph d) => f xC) hcopy
    exact hxval
  · simp only [edgeSupport, Finset.mem_biUnion] at hxIso
    obtain ⟨e, heIso, hxe⟩ := hxIso
    let eI : isolatedEdges F := ⟨e, heIso⟩
    have hfirst : a.1 e.out.1 = b.1 e.out.1 := by
      exact congrArg (fun z => coreIsolatedCodeEndpoint z eI) hab
    have hcoord :
        cubeStepCoordinate d (isolatedEndpointAdj d hF a eI) =
          cubeStepCoordinate d (isolatedEndpointAdj d hF b eI) := by
      exact congrArg (fun z => coreIsolatedCodeCoordinate z eI) hab
    have hsecond : a.1 e.out.2 = b.1 e.out.2 :=
      cube_adj_second_eq_of_first_eq_coordinate_eq d
        (isolatedEndpointAdj d hF a eI)
        (isolatedEndpointAdj d hF b eI) hfirst hcoord
    have hout : s(e.out.1, e.out.2) = e := e.out_eq
    have hxout : x = e.out.1 ∨ x = e.out.2 := by
      rw [← hout, Sym2.toFinset_mk_eq] at hxe
      simpa [eq_comm] using hxe
    by_cases hx : x = e.out.1
    · simpa [hx] using hfirst
    · have hx2 : x = e.out.2 := hxout.resolve_left hx
      simpa [hx2] using hsecond

theorem natCard_CoreIsolatedCode_le (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d))) :
    Nat.card (CoreIsolatedCode d F) ≤
      (2 ^ d) ^ overlapComponentCount d (overlapCore F) *
        d ^ ((edgeSupport (overlapCore F)).card -
          overlapComponentCount d (overlapCore F)) *
        ((2 ^ d - (edgeSupport (overlapCore F)).card) * d) ^
          (isolatedEdges F).card := by
  classical
  letI : Fintype (CoreIsolatedCode d F) := by
    unfold CoreIsolatedCode
    exact Sigma.instFintype
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Σ f : SimpleGraph.Copy
      (overlapSupportGraph d (overlapCore F)) (cubeGraph d),
      ∀ _e : isolatedEdges F, (unusedCoreVertices d f) × Fin d) ≤ _
  rw [Fintype.card_sigma]
  have hterm (f : SimpleGraph.Copy
      (overlapSupportGraph d (overlapCore F)) (cubeGraph d)) :
      Fintype.card (∀ _e : isolatedEdges F,
        (unusedCoreVertices d f) × Fin d) =
        ((2 ^ d - (edgeSupport (overlapCore F)).card) * d) ^
          (isolatedEdges F).card := by
    rw [Fintype.card_pi]
    simp_rw [Fintype.card_prod, Fintype.card_coe,
      card_unusedCoreVertices, Fintype.card_fin]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcopy := natCard_copy_le_cube_tree_bound
    (overlapSupportGraph d (overlapCore F)) d
  rw [Nat.card_eq_fintype_card] at hcopy
  exact Nat.mul_le_mul_right _ (by
    simpa [overlapSupportGraph, overlapComponentCount, card_cubeVertex]
      using hcopy)

/-- Sharpened permutation fiber: after the core copy is fixed, the first
endpoint of every isolated edge must lie among the unused target vertices. -/
theorem card_perms_containing_edge_set_le_core_isolated (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
        F ⊆ cubePattern d σ).card ≤
      (2 ^ d) ^ overlapComponentCount d (overlapCore F) *
        d ^ ((edgeSupport (overlapCore F)).card -
          overlapComponentCount d (overlapCore F)) *
        ((2 ^ d - (edgeSupport (overlapCore F)).card) * d) ^
          (isolatedEdges F).card *
        Nat.factorial (2 ^ d - ((edgeSupport (overlapCore F)).card +
          2 * (isolatedEdges F).card)) := by
  classical
  let A : Finset (Equiv.Perm (CubeVertex d)) :=
    (Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
      F ⊆ cubePattern d σ⁻¹
  let toEvent (a : A) :
      { σ : Equiv.Perm (CubeVertex d) // F ⊆ cubePattern d σ⁻¹ } :=
    ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
  let φ : A → CoreIsolatedCode d F := fun a =>
    coreIsolatedCode d F hF (toEvent a)
  letI : Fintype (CoreIsolatedCode d F) := by
    unfold CoreIsolatedCode
    exact Sigma.instFintype
  have hfiber (z : CoreIsolatedCode d F) :
      (A.attach.filter fun a => φ a = z).card ≤
        Nat.factorial (2 ^ d - (edgeSupport F).card) := by
    by_cases hne : (A.attach.filter fun a => φ a = z).Nonempty
    · let a := Classical.choose hne
      have ha : a ∈ A.attach.filter fun b => φ b = z :=
        Classical.choose_spec hne
      let E : Finset (Equiv.Perm (CubeVertex d)) :=
        (Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
          ∀ x ∈ edgeSupport F, σ x = a.1 x
      have hsub : (A.attach.filter fun b => φ b = z).card ≤ E.card := by
        apply Finset.card_le_card_of_injOn (fun b => b.1)
        · intro b hb
          show b.1 ∈ E
          rw [show E =
            (Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
              ∀ x ∈ edgeSupport F, σ x = a.1 x by rfl,
            Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro x hx
          have hbcode := (Finset.mem_filter.mp hb).2
          have hacode := (Finset.mem_filter.mp ha).2
          have hcodes : coreIsolatedCode d F hF (toEvent b) =
              coreIsolatedCode d F hF (toEvent a) := hbcode.trans hacode.symm
          exact coreIsolatedCode_eq_on_edgeSupport d F hF
            (toEvent b) (toEvent a) hcodes x hx
        · intro b hb c hc hbc
          exact Subtype.ext hbc
      exact hsub.trans_eq (by
        rw [show E =
            ((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ =>
              ∀ x ∈ edgeSupport F, σ x = a.1 x) by rfl]
        simpa [card_cubeVertex] using
          card_perms_agreeing_on_finset (edgeSupport F) a.1)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hA : A.card ≤ Nat.card (CoreIsolatedCode d F) *
      Nat.factorial (2 ^ d - (edgeSupport F).card) := by
    calc
      A.card = A.attach.card := Finset.card_attach.symm
      _ = ∑ z : CoreIsolatedCode d F,
          (A.attach.filter fun a => φ a = z).card := by
            exact Finset.card_eq_sum_card_fiberwise
              (s := A.attach)
              (t := (Finset.univ : Finset (CoreIsolatedCode d F)))
              (f := φ) (fun a ha => Finset.mem_univ (φ a))
      _ ≤ ∑ _z : CoreIsolatedCode d F,
          Nat.factorial (2 ^ d - (edgeSupport F).card) := by
            exact Finset.sum_le_sum fun z _ => hfiber z
      _ = Nat.card (CoreIsolatedCode d F) *
          Nat.factorial (2 ^ d - (edgeSupport F).card) := by
            simp [Nat.card_eq_fintype_card]
  have hcode := natCard_CoreIsolatedCode_le d F
  have hdiag : ∀ e ∈ F, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hF he))
  have hsupp := edgeSupport_card_eq_core_add_twice_isolated F hdiag
  rw [card_perms_subset_cubePattern_eq_inverse d F]
  change A.card ≤ _
  calc
    A.card ≤ Nat.card (CoreIsolatedCode d F) *
        Nat.factorial (2 ^ d - (edgeSupport F).card) := hA
    _ ≤ ((2 ^ d) ^ overlapComponentCount d (overlapCore F) *
          d ^ ((edgeSupport (overlapCore F)).card -
            overlapComponentCount d (overlapCore F)) *
          ((2 ^ d - (edgeSupport (overlapCore F)).card) * d) ^
            (isolatedEdges F).card) *
        Nat.factorial (2 ^ d - (edgeSupport F).card) := by gcongr
    _ = _ := by rw [hsupp]

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def availableCoreEdges (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) :
    Finset (Sym2 (CubeVertex d)) :=
  ambientInducedEdges d (Finset.univ \ edgeSupport C)

theorem two_mul_card_availableCoreEdges_le (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) :
    2 * (availableCoreEdges d C).card ≤
      d * (2 ^ d - (edgeSupport C).card) := by
  classical
  let S : Finset (CubeVertex d) := Finset.univ \ edgeSupport C
  let H := (cubeGraph d).induce (S : Set (CubeVertex d))
  have hcardS : S.card = 2 ^ d - (edgeSupport C).card := by
    change (Finset.univ \ edgeSupport C).card = _
    rw [Finset.card_sdiff]
    simp
  have hdeg : 2 * H.edgeFinset.card ≤ d * S.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      (∑ v : S, H.degree v) ≤ ∑ _v : S, d := by
        exact Finset.sum_le_sum fun v _ => cube_induce_degree_le d S v
      _ = d * S.card := by simp [mul_comm]
  simpa [availableCoreEdges, S, H, card_ambientInducedEdges, hcardS] using hdeg

theorem isolatedEdges_subset_availableCoreEdges (d : ℕ)
    {F : Finset (Sym2 (CubeVertex d))}
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    isolatedEdges F ⊆ availableCoreEdges d (overlapCore F) := by
  classical
  intro e heIso
  rw [availableCoreEdges, mem_ambientInducedEdges_iff]
  refine ⟨hF (isolatedEdges_subset F heIso), ?_⟩
  intro x hxe
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hxCore
  have hxIso : x ∈ edgeSupport (isolatedEdges F) := by
    simp only [edgeSupport, Finset.mem_biUnion]
    exact ⟨e, heIso, hxe⟩
  exact Finset.disjoint_left.mp (edgeSupport_disjoint_core_isolated F)
    hxCore hxIso

theorem card_overlapCoreFiber_le_available_choose (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    (overlapCoreFiber d C t).card ≤
      Nat.choose (availableCoreEdges d C).card t := by
  classical
  let T := (availableCoreEdges d C).powersetCard t
  have hcardT : T.card = Nat.choose (availableCoreEdges d C).card t := by
    simpa [T] using Finset.card_powersetCard t (availableCoreEdges d C)
  rw [← hcardT]
  apply Finset.card_le_card_of_injOn isolatedEdges
  · intro F hFmem
    have hmem := Finset.mem_filter.mp hFmem
    change isolatedEdges F ∈ (availableCoreEdges d C).powersetCard t
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hmem.2.2⟩
    simpa [hmem.2.1] using isolatedEdges_subset_availableCoreEdges d
      (Finset.mem_powerset.mp hmem.1)
  · intro F hFmem K hKmem heq
    have hFC := (Finset.mem_filter.mp hFmem).2.1
    have hKC := (Finset.mem_filter.mp hKmem).2.1
    calc
      F = overlapCore F ∪ isolatedEdges F :=
        (overlapCore_union_isolatedEdges F).symm
      _ = overlapCore K ∪ isolatedEdges K := by rw [hFC, hKC, heq]
      _ = K := overlapCore_union_isolatedEdges K

noncomputable def sharpCoreIsolatedUpperTerm (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) : ℝ :=
  a ^ (C.card + t) *
    (((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d C *
      (d : ℝ) ^ ((edgeSupport C).card - overlapComponentCount d C) *
      (((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t /
      (((2 ^ d).descFactorial ((edgeSupport C).card + 2 * t)) : ℕ))

theorem normalized_permutation_fiber_le_core_isolated_sharp (d : ℕ)
    (F : Finset (Sym2 (CubeVertex d)))
    (hF : F ⊆ (cubeGraph d).edgeFinset) :
    (((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
        F ⊆ cubePattern d σ).card : ℝ) /
        Fintype.card (Equiv.Perm (CubeVertex d)) ≤
      (((2 ^ d : ℕ) : ℝ) ^ overlapComponentCount d (overlapCore F) *
        (d : ℝ) ^ ((edgeSupport (overlapCore F)).card -
          overlapComponentCount d (overlapCore F)) *
        (((2 ^ d - (edgeSupport (overlapCore F)).card) * d : ℕ) : ℝ) ^
          (isolatedEdges F).card /
        (((2 ^ d).descFactorial ((edgeSupport (overlapCore F)).card +
          2 * (isolatedEdges F).card)) : ℕ)) := by
  classical
  let n := 2 ^ d
  let s := (edgeSupport (overlapCore F)).card +
    2 * (isolatedEdges F).card
  have hdiag : ∀ e ∈ F, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hF he))
  have hsEq : (edgeSupport F).card = s :=
    edgeSupport_card_eq_core_add_twice_isolated F hdiag
  have hsN : s ≤ n := by
    rw [← hsEq]
    dsimp [n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have hcount := card_perms_containing_edge_set_le_core_isolated d F hF
  have hperm : Fintype.card (Equiv.Perm (CubeVertex d)) = n.factorial := by
    rw [Fintype.card_perm, card_cubeVertex]
  have hfac : (n.factorial : ℝ) =
      ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) := by
    norm_cast
    exact (Nat.factorial_mul_descFactorial hsN).symm
  rw [hperm, hfac]
  calc
    (((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter fun σ ↦
          F ⊆ cubePattern d σ).card : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) ≤
      (((((2 ^ d) ^ overlapComponentCount d (overlapCore F) *
          d ^ ((edgeSupport (overlapCore F)).card -
            overlapComponentCount d (overlapCore F)) *
          ((2 ^ d - (edgeSupport (overlapCore F)).card) * d) ^
            (isolatedEdges F).card) * Nat.factorial (n - s) : ℕ) : ℝ) /
        (((n - s).factorial : ℝ) * (n.descFactorial s : ℝ))) := by
          gcongr
    _ = _ := by
      dsimp [n, s]
      push_cast
      field_simp

theorem overlapAverage_le_sum_core_isolated_sharp (d : ℕ) (a : ℝ)
    (ha : 0 ≤ a) :
    overlapAverage d (1 + a) ≤
      ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (Nat.choose (availableCoreEdges d C).card t : ℝ) *
            sharpCoreIsolatedUpperTerm d a C t := by
  classical
  rw [overlapAverage_eq_sum_normalized_fibers]
  calc
    (∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        a ^ F.card *
          ((((Finset.univ : Finset (Equiv.Perm (CubeVertex d))).filter
            fun σ ↦ F ⊆ cubePattern d σ).card : ℝ) /
            Fintype.card (Equiv.Perm (CubeVertex d)))) ≤
      ∑ F ∈ (cubeGraph d).edgeFinset.powerset,
        sharpCoreIsolatedUpperTerm d a (overlapCore F)
          (isolatedEdges F).card := by
      apply Finset.sum_le_sum
      intro F hFmem
      have hsub := Finset.mem_powerset.mp hFmem
      have hfiber := normalized_permutation_fiber_le_core_isolated_sharp d F hsub
      rw [sharpCoreIsolatedUpperTerm, ← card_eq_core_add_isolated F]
      exact mul_le_mul_of_nonneg_left hfiber (pow_nonneg ha _)
    _ = ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          ∑ F ∈ overlapCoreFiber d C t,
            sharpCoreIsolatedUpperTerm d a (overlapCore F)
              (isolatedEdges F).card :=
      sum_powerset_by_core_isolated d _
    _ = ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (overlapCoreFiber d C t).card *
            sharpCoreIsolatedUpperTerm d a C t := by
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro t ht
      calc
        (∑ F ∈ overlapCoreFiber d C t,
            sharpCoreIsolatedUpperTerm d a (overlapCore F)
              (isolatedEdges F).card) =
            ∑ _F ∈ overlapCoreFiber d C t,
              sharpCoreIsolatedUpperTerm d a C t := by
                apply Finset.sum_congr rfl
                intro F hFmem
                have hmem := (Finset.mem_filter.mp hFmem).2
                rw [hmem.1, hmem.2]
        _ = _ := by simp
    _ ≤ ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (Nat.choose (availableCoreEdges d C).card t : ℝ) *
            sharpCoreIsolatedUpperTerm d a C t := by
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro t ht
      have hcard := card_overlapCoreFiber_le_available_choose d C t
      have hterm : 0 ≤ sharpCoreIsolatedUpperTerm d a C t := by
        unfold sharpCoreIsolatedUpperTerm
        positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hterm

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def sharpIsolatedWeight (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) : ℝ :=
  (Nat.choose (availableCoreEdges d C).card t : ℝ) * a ^ t *
    (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
      (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ))

theorem choose_mul_sharpCoreIsolatedUpperTerm_eq (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    (Nat.choose (availableCoreEdges d C).card t : ℝ) *
        sharpCoreIsolatedUpperTerm d a C t =
      coreWeight d a C * sharpIsolatedWeight d a C t := by
  let n := 2 ^ d
  let s := (edgeSupport C).card
  have hdescNat := Nat.descFactorial_mul_descFactorial
    (n := n) (k := s) (m := s + 2 * t) (by omega : s ≤ s + 2 * t)
  have hdesc :
      (((n - s).descFactorial (2 * t) : ℕ) : ℝ) *
          (n.descFactorial s : ℕ) =
        (n.descFactorial (s + 2 * t) : ℕ) := by
    exact_mod_cast (by simpa using hdescNat)
  unfold sharpCoreIsolatedUpperTerm coreWeight sharpIsolatedWeight
  dsimp [n, s] at hdesc ⊢
  push_cast
  simp only [div_eq_mul_inv]
  rw [← hdesc, mul_inv]
  ring

theorem choose_cast_le_pow_div_factorial (N t : ℕ) :
    (Nat.choose N t : ℝ) ≤ (N : ℝ) ^ t / (t.factorial : ℕ) := by
  have hdesc := Nat.descFactorial_le_pow N t
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hdescR : ((t.factorial : ℕ) : ℝ) * Nat.choose N t ≤
      (N : ℝ) ^ t := by exact_mod_cast hdesc
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (t.factorial : ℕ))]
  simpa [mul_comm] using hdescR

theorem sharpIsolatedWeight_nonneg (d : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    0 ≤ sharpIsolatedWeight d a C t := by
  unfold sharpIsolatedWeight
  positivity

theorem sharpIsolatedWeight_le_universal (d : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (C : Finset (Sym2 (CubeVertex d))) (t : ℕ) :
    sharpIsolatedWeight d a C t ≤
      (((81 : ℝ) * a * d ^ 2 / 2) ^ t) / (t.factorial : ℕ) := by
  classical
  let v := 2 ^ d - (edgeSupport C).card
  let E := (availableCoreEdges d C).card
  have h2E : 2 * E ≤ d * v := two_mul_card_availableCoreEdges_le d C
  have hER : (E : ℝ) ≤ (d : ℝ) * v / 2 := by
    have h2ER : (2 : ℝ) * E ≤ (d : ℝ) * v := by exact_mod_cast h2E
    linarith
  have hchoose := choose_cast_le_pow_div_factorial E t
  by_cases ht0 : t = 0
  · subst t
    simp [sharpIsolatedWeight]
  by_cases ht : 2 * t ≤ v
  · have hvpos : 0 < v := by omega
    have hdesc := pow_le_nine_pow_mul_descFactorial hvpos ht
    have hdescPos : (0 : ℝ) < (v.descFactorial (2 * t) : ℕ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr ht
    unfold sharpIsolatedWeight
    dsimp [E, v] at hchoose hER hdesc hdescPos ⊢
    calc
      (Nat.choose (availableCoreEdges d C).card t : ℝ) * a ^ t *
          (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
            (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ)) ≤
        (((availableCoreEdges d C).card : ℝ) ^ t /
            (t.factorial : ℕ)) * a ^ t *
          (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
            (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ)) := by
              gcongr
      _ ≤ ((((d : ℝ) *
            (((2 ^ d - (edgeSupport C).card : ℕ) : ℝ)) / 2) ^ t /
            (t.factorial : ℕ)) * a ^ t *
          (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
            (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ))) := by
              gcongr
      _ ≤ (((81 : ℝ) * a * d ^ 2 / 2) ^ t) /
          (t.factorial : ℕ) := by
        let V : ℝ := ((2 ^ d - (edgeSupport C).card : ℕ) : ℝ)
        let D : ℝ := (t.factorial : ℕ)
        let Q : ℝ :=
          ((2 ^ d - (edgeSupport C).card).descFactorial (2 * t) : ℕ)
        have hD : 0 < D := by dsimp [D]; positivity
        have hQ : 0 < Q := by simpa [Q] using hdescPos
        have h81 : V ^ (2 * t) ≤ (81 : ℝ) ^ t * Q := by
          dsimp [V, Q]
          rw [← show (9 : ℝ) ^ (2 * t) = 81 ^ t by
            rw [pow_mul]; norm_num]
          exact hdesc
        have hbase : 0 ≤ a * (d : ℝ) ^ 2 / 2 := by positivity
        have hnum :
            ((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t ≤
              ((81 : ℝ) * a * d ^ 2 / 2) ^ t * Q := by
          calc
            ((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t =
                (a * (d : ℝ) ^ 2 / 2) ^ t * V ^ (2 * t) := by
                  rw [pow_mul]
                  ring
            _ ≤ (a * (d : ℝ) ^ 2 / 2) ^ t *
                ((81 : ℝ) ^ t * Q) :=
              mul_le_mul_of_nonneg_left h81 (pow_nonneg hbase _)
            _ = ((81 : ℝ) * a * d ^ 2 / 2) ^ t * Q := by
              rw [← mul_assoc, ← mul_pow]
              ring
        have hmain : (((d : ℝ) * V / 2) ^ t / D) * a ^ t *
              ((V * d) ^ t / Q) ≤
            ((81 : ℝ) * a * d ^ 2 / 2) ^ t / D := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          calc
            ((d : ℝ) * V / 2) ^ t * D⁻¹ * a ^ t *
                ((V * d) ^ t * Q⁻¹) =
              (((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t) *
                (D * Q)⁻¹ := by rw [mul_inv]; ring
            _ ≤ (((81 : ℝ) * a * d ^ 2 / 2) ^ t * Q) *
                (D * Q)⁻¹ := mul_le_mul_of_nonneg_right hnum (by positivity)
            _ = ((81 : ℝ) * a * d ^ 2 / 2) ^ t * D⁻¹ := by
              field_simp
        simpa [V, D, Q, Nat.cast_mul] using hmain
  · have hzero : (v.descFactorial (2 * t) : ℕ) = 0 := by
      rw [Nat.descFactorial_eq_zero_iff_lt]
      omega
    unfold sharpIsolatedWeight
    dsimp [v] at hzero
    rw [hzero]
    simp
    positivity

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def isolatedSmallLambda (d : ℕ) (a : ℝ) (T : ℕ) : ℝ :=
  a * (d : ℝ) ^ 2 / 2 *
    ((((2 ^ d : ℕ) : ℝ) / ((2 ^ d - T : ℕ) : ℝ)) ^ 2)

theorem sharpIsolatedWeight_le_small (d : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (C : Finset (Sym2 (CubeVertex d))) (t T : ℕ)
    (hTn : T < 2 ^ d)
    (hsize : (edgeSupport C).card + 2 * t ≤ T) :
    sharpIsolatedWeight d a C t ≤
      (isolatedSmallLambda d a T ^ t) / (t.factorial : ℕ) := by
  classical
  let n := 2 ^ d
  let s := (edgeSupport C).card
  let v := n - s
  let L := n - T
  let E := (availableCoreEdges d C).card
  have hsN : s ≤ n := by
    dsimp [s, n]
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _
  have hv : v = n - s := rfl
  have h2t : 2 * t ≤ v := by omega
  have hLpos : 0 < L := by omega
  have hLv : L ≤ v + 1 - 2 * t := by omega
  have hdescNat := v.pow_sub_le_descFactorial (2 * t)
  have hLpowNat : L ^ (2 * t) ≤ v.descFactorial (2 * t) := by
    exact (Nat.pow_le_pow_left hLv (2 * t)).trans hdescNat
  have hdescPos : (0 : ℝ) < (v.descFactorial (2 * t) : ℕ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr h2t
  have h2E := two_mul_card_availableCoreEdges_le d C
  have hER : (E : ℝ) ≤ (d : ℝ) * v / 2 := by
    have h2ER : (2 : ℝ) * E ≤ (d : ℝ) * v := by
      dsimp [E, v, n, s] at *
      exact_mod_cast h2E
    linarith
  have hchoose := choose_cast_le_pow_div_factorial E t
  have hchoose' : (Nat.choose E t : ℝ) ≤
      (((d : ℝ) * v / 2) ^ t) / (t.factorial : ℕ) := by
    calc
      (Nat.choose E t : ℝ) ≤ (E : ℝ) ^ t / (t.factorial : ℕ) := hchoose
      _ ≤ (((d : ℝ) * v / 2) ^ t) / (t.factorial : ℕ) := by
        gcongr
  have hvN : (v : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n s
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hdescLower : (L : ℝ) ^ (2 * t) ≤
      (v.descFactorial (2 * t) : ℕ) := by exact_mod_cast hLpowNat
  unfold sharpIsolatedWeight isolatedSmallLambda
  dsimp [E, v, n, s, L] at hchoose hchoose' hER hdescPos hvN hLposR hdescLower ⊢
  calc
    (Nat.choose (availableCoreEdges d C).card t : ℝ) * a ^ t *
        (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
          (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ)) ≤
      ((((d : ℝ) * ((2 ^ d - (edgeSupport C).card : ℕ) : ℝ) / 2) ^ t /
          (t.factorial : ℕ)) * a ^ t *
        (((((2 ^ d - (edgeSupport C).card) * d : ℕ) : ℝ) ^ t) /
          (((2 ^ d - (edgeSupport C).card).descFactorial (2 * t)) : ℕ))) := by
            gcongr
    _ ≤ ((a * (d : ℝ) ^ 2 / 2 *
          ((((2 ^ d : ℕ) : ℝ) /
            ((2 ^ d - T : ℕ) : ℝ)) ^ 2)) ^ t) /
        (t.factorial : ℕ) := by
      let V : ℝ := ((2 ^ d - (edgeSupport C).card : ℕ) : ℝ)
      let N : ℝ := ((2 ^ d : ℕ) : ℝ)
      let R : ℝ := ((2 ^ d - T : ℕ) : ℝ)
      let D : ℝ := (t.factorial : ℕ)
      let Q : ℝ :=
        ((2 ^ d - (edgeSupport C).card).descFactorial (2 * t) : ℕ)
      have hR : 0 < R := by simpa [R] using hLposR
      have hQ : 0 < Q := by simpa [Q] using hdescPos
      have hVN : V ≤ N := by simpa [V, N] using hvN
      have hRQ : R ^ (2 * t) ≤ Q := by simpa [R, Q] using hdescLower
      have hnum :
          ((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t ≤
            (a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t * Q := by
        have hbase : 0 ≤ a * (d : ℝ) ^ 2 / 2 := by positivity
        have hVpow : V ^ (2 * t) ≤ N ^ (2 * t) := by gcongr
        have hquot : (N / R) ^ 2 * R ^ 2 = N ^ 2 := by
          field_simp
        calc
          ((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t =
              (a * (d : ℝ) ^ 2 / 2) ^ t * V ^ (2 * t) := by
                rw [pow_mul]
                ring
          _ ≤ (a * (d : ℝ) ^ 2 / 2) ^ t * N ^ (2 * t) := by gcongr
          _ = (a * (d : ℝ) ^ 2 / 2) ^ t * (N ^ 2) ^ t := by
                rw [pow_mul]
          _ = (a * (d : ℝ) ^ 2 / 2) ^ t *
                (((N / R) ^ 2 * R ^ 2) ^ t) := by rw [hquot]
          _ = (a * (d : ℝ) ^ 2 / 2) ^ t * ((N / R) ^ 2) ^ t *
                (R ^ 2) ^ t := by rw [mul_pow]; ring
          _ = (a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t *
                R ^ (2 * t) := by
                  rw [mul_pow, pow_mul]
          _ ≤ (a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t *
                Q := by gcongr
      have hmain : (((d : ℝ) * V / 2) ^ t / D) * a ^ t *
              ((V * d) ^ t / Q) ≤
            (a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t / D := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        calc
          ((d : ℝ) * V / 2) ^ t * D⁻¹ * a ^ t *
                ((V * d) ^ t * Q⁻¹) =
              (((d : ℝ) * V / 2) ^ t * a ^ t * (V * d) ^ t) *
                (D * Q)⁻¹ := by rw [mul_inv]; ring
          _ ≤ ((a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t * Q) *
                (D * Q)⁻¹ :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = (a * (d : ℝ) ^ 2 / 2 * (N / R) ^ 2) ^ t * D⁻¹ := by
            field_simp
      simpa [V, N, R, D, Q, Nat.cast_mul] using hmain

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem three_mul_overlapComponentCount_le_support_card_of_core (d : ℕ)
    {C : Finset (Sym2 (CubeVertex d))}
    (hsub : C ⊆ (cubeGraph d).edgeFinset)
    (hcore : overlapCore C = C) :
    3 * overlapComponentCount d C ≤ (edgeSupport C).card := by
  classical
  have hdiag : ∀ e ∈ C, ¬e.IsDiag := fun e he =>
    (cubeGraph d).not_isDiag_of_mem_edgeSet (by
      simpa using SimpleGraph.mem_edgeFinset.mp (hsub he))
  have hno : ∀ e ∈ C, ¬IsIsolatedEdge C e := by
    intro e he heIso
    have heIso' : e ∈ isolatedEdges C := Finset.mem_filter.mpr ⟨he, heIso⟩
    have heCore : e ∈ overlapCore C := by simpa [hcore] using he
    exact (Finset.mem_sdiff.mp heCore).2 heIso'
  rw [← card_supportComponents_eq_overlapComponentCount d C hdiag,
    ← sum_card_supportComponents hdiag]
  calc
    3 * (supportComponents C).card =
        ∑ _c ∈ supportComponents C, 3 := by simp [mul_comm]
    _ ≤ ∑ c ∈ supportComponents C,
        (ambientSetFinset c.supp).card := by
      apply Finset.sum_le_sum
      intro c hc
      exact supportComponent_card_three_le_of_no_isolated hdiag hno hc

noncomputable def coreDefect (d : ℕ)
    (C : Finset (Sym2 (CubeVertex d))) : ℕ :=
  (edgeSupport C).card - 2 * overlapComponentCount d C

noncomputable def coreDefectFiber (d u k : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (coreAllEdgeSets d).filter fun C =>
    coreDefect d C = u ∧ overlapComponentCount d C = k

theorem coreDefectFiber_eq_coreEdgeSets (d u k : ℕ) :
    coreDefectFiber d u k = coreEdgeSets d (u + k) k := by
  classical
  apply Finset.ext
  intro (C : Finset (Sym2 (CubeVertex d)))
  rw [coreDefectFiber, Finset.mem_filter]
  simp only [coreAllEdgeSets, coreEdgeSets, Finset.mem_filter,
    Finset.mem_powerset, coreDefect]
  constructor
  · rintro ⟨⟨hsub, hcore⟩, hu, hk⟩
    have h2k := two_mul_overlapComponentCount_le_support_card d C hsub
    refine ⟨hsub, hcore, ?_, hk⟩
    omega
  · rintro ⟨hsub, hcore, hr, hk⟩
    have h2k := two_mul_overlapComponentCount_le_support_card d C hsub
    refine ⟨⟨hsub, hcore⟩, ?_, hk⟩
    omega

theorem coreDefect_le_cubeVertexCard (d : ℕ)
    {C : Finset (Sym2 (CubeVertex d))}
    (hC : C ∈ coreAllEdgeSets d) : coreDefect d C ≤ 2 ^ d := by
  unfold coreDefect
  exact (Nat.sub_le _ _).trans (by
    rw [← card_cubeVertex]
    exact Finset.card_le_univ _)

theorem component_le_coreDefect (d : ℕ)
    {C : Finset (Sym2 (CubeVertex d))}
    (hC : C ∈ coreAllEdgeSets d) :
    overlapComponentCount d C ≤ coreDefect d C := by
  classical
  have hmem := Finset.mem_filter.mp hC
  have h3 := three_mul_overlapComponentCount_le_support_card_of_core d
    (Finset.mem_powerset.mp hmem.1) hmem.2
  unfold coreDefect
  omega

theorem sum_coreAll_by_defect (d : ℕ)
    (f : Finset (Sym2 (CubeVertex d)) → ℝ) :
    (∑ C ∈ coreAllEdgeSets d, f C) =
      ∑ u ∈ Finset.range (2 ^ d + 1),
        ∑ k ∈ Finset.range (u + 1),
          ∑ C ∈ coreDefectFiber d u k, f C := by
  classical
  let P := (Finset.range (2 ^ d + 1)).biUnion fun u =>
    (Finset.range (u + 1)).image fun k => (u, k)
  let g : Finset (Sym2 (CubeVertex d)) → ℕ × ℕ := fun C =>
    (coreDefect d C, overlapComponentCount d C)
  have hmap : ∀ C ∈ coreAllEdgeSets d, g C ∈ P := by
    intro C hC
    simp only [P, Finset.mem_biUnion]
    refine ⟨coreDefect d C, Finset.mem_range.mpr (by
      have := coreDefect_le_cubeVertexCard d hC
      omega), ?_⟩
    rw [Finset.mem_image]
    refine ⟨overlapComponentCount d C, Finset.mem_range.mpr (by
      have := component_le_coreDefect d hC
      omega), rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap f
  rw [← hfiber]
  dsimp [P]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      change (∑ C ∈ coreAllEdgeSets d with
          (coreDefect d C, overlapComponentCount d C) = (u, k), f C) = _
      congr 1
      ext C
      simp [coreDefectFiber]
    · intro k hk l hl hkl
      exact Prod.mk.inj hkl |>.2
  · intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨k, hk, rfl⟩ := hp
    obtain ⟨l, hl, hEq⟩ := hp'
    exact huv (Prod.mk.inj hEq |>.1.symm)

noncomputable def coreDecay (d : ℕ) : ℝ :=
  ((162 : ℝ) * d ^ 3) ^ 2 * (Real.sqrt 3) ^ (d + 4) /
    ((2 ^ d : ℕ) : ℝ)

theorem core_certificate_bound_le_decay (d u k : ℕ) (hd : 1 ≤ d)
    (hk : k ≤ u) :
    ((2 ^ (u + k) * (2 ^ d) ^ k * d ^ (2 * (u + k)) : ℕ) : ℝ) *
        (3 : ℝ) ^ (((d + 4) * u) / 2) *
        ((((81 : ℝ) * d) / (2 ^ d : ℕ)) ^ (u + k)) ≤
      coreDecay d ^ u := by
  have hn : (0 : ℝ) < ((2 ^ d : ℕ) : ℝ) := by positivity
  have hA : (1 : ℝ) ≤ (162 : ℝ) * d ^ 3 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdR 3]
  have hr : u + k ≤ 2 * u := by omega
  have hthree := three_pow_half_le_sqrt_three_pow ((d + 4) * u)
  have hpowA : ((162 : ℝ) * d ^ 3) ^ (u + k) ≤
      ((162 : ℝ) * d ^ 3) ^ (2 * u) := by
    exact pow_le_pow_right₀ hA hr
  have heq :
      ((2 ^ (u + k) * (2 ^ d) ^ k * d ^ (2 * (u + k)) : ℕ) : ℝ) *
          ((((81 : ℝ) * d) / (2 ^ d : ℕ)) ^ (u + k)) =
        ((162 : ℝ) * d ^ 3) ^ (u + k) /
          (((2 ^ d : ℕ) : ℝ) ^ u) := by
    let B : ℝ := (2 : ℝ) ^ d
    let A : ℝ := (162 : ℝ) * d ^ 3
    have hB : B ≠ 0 := by dsimp [B]; positivity
    have hnum : (2 : ℝ) ^ (u + k) * (d : ℝ) ^ (2 * (u + k)) *
          ((81 : ℝ) * d) ^ (u + k) = A ^ (u + k) := by
      calc
        (2 : ℝ) ^ (u + k) * (d : ℝ) ^ (2 * (u + k)) *
              ((81 : ℝ) * d) ^ (u + k) =
            (2 : ℝ) ^ (u + k) * ((d : ℝ) ^ 2) ^ (u + k) *
              ((81 : ℝ) * d) ^ (u + k) := by rw [pow_mul]
        _ = ((2 : ℝ) * d ^ 2 * ((81 : ℝ) * d)) ^ (u + k) := by
          rw [mul_pow, mul_pow]
          ring
        _ = A ^ (u + k) := by congr 1; dsimp [A]; ring
    push_cast
    rw [div_pow]
    change (2 : ℝ) ^ (u + k) * B ^ k * (d : ℝ) ^ (2 * (u + k)) *
        (((81 : ℝ) * d) ^ (u + k) / B ^ (u + k)) =
      A ^ (u + k) / B ^ u
    calc
      (2 : ℝ) ^ (u + k) * B ^ k * (d : ℝ) ^ (2 * (u + k)) *
          (((81 : ℝ) * d) ^ (u + k) / B ^ (u + k)) =
        B ^ k *
          ((2 : ℝ) ^ (u + k) * (d : ℝ) ^ (2 * (u + k)) *
            ((81 : ℝ) * d) ^ (u + k)) / B ^ (u + k) := by ring
      _ = B ^ k * A ^ (u + k) / B ^ (u + k) := by rw [hnum]
      _ = A ^ (u + k) / B ^ u := by
        rw [pow_add A, pow_add B]
        field_simp [hB]
  calc
    ((2 ^ (u + k) * (2 ^ d) ^ k * d ^ (2 * (u + k)) : ℕ) : ℝ) *
          (3 : ℝ) ^ (((d + 4) * u) / 2) *
          ((((81 : ℝ) * d) / (2 ^ d : ℕ)) ^ (u + k)) =
      (((2 ^ (u + k) * (2 ^ d) ^ k * d ^ (2 * (u + k)) : ℕ) : ℝ) *
          ((((81 : ℝ) * d) / (2 ^ d : ℕ)) ^ (u + k))) *
        (3 : ℝ) ^ (((d + 4) * u) / 2) := by ring
    _ = ((162 : ℝ) * d ^ 3) ^ (u + k) /
          (((2 ^ d : ℕ) : ℝ) ^ u) *
        (3 : ℝ) ^ (((d + 4) * u) / 2) := by rw [heq]
    _ ≤ ((162 : ℝ) * d ^ 3) ^ (2 * u) /
          (((2 ^ d : ℕ) : ℝ) ^ u) *
        (Real.sqrt 3) ^ ((d + 4) * u) := by gcongr
    _ = coreDecay d ^ u := by
      rw [coreDecay, div_pow, pow_mul, pow_mul]
      ring

theorem sum_coreDefectFiber_coreWeight_le (d u k : ℕ) (a : ℝ)
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hc : 1 + a ≤ 3) (hk : k ≤ u) :
    (∑ C ∈ coreDefectFiber d u k, coreWeight d a C) ≤
      coreDecay d ^ u := by
  classical
  rw [coreDefectFiber_eq_coreEdgeSets]
  let q : ℝ := (81 * d) / (2 ^ d : ℕ)
  calc
    (∑ C ∈ coreEdgeSets d (u + k) k, coreWeight d a C) ≤
        ∑ C ∈ coreEdgeSets d (u + k) k,
          a ^ C.card * q ^ (u + k) := by
      apply Finset.sum_le_sum
      intro C hC
      have hmem := Finset.mem_filter.mp hC
      have hCall : C ∈ coreAllEdgeSets d := by
        rw [coreAllEdgeSets, Finset.mem_filter]
        exact ⟨hmem.1, hmem.2.1⟩
      have h := coreWeight_le_rank_weight d a ha hCall
      rw [hmem.2.2.1] at h
      simpa [q] using h
    _ ≤ ((2 ^ (u + k) * (2 ^ d) ^ k * d ^ (2 * (u + k)) : ℕ) : ℝ) *
          (3 : ℝ) ^ (((d + 4) * ((u + k) - k)) / 2) * q ^ (u + k) :=
      sum_coreEdgeSets_weight_le d (u + k) k a q ha hc (by positivity)
    _ ≤ coreDecay d ^ u := by
      simp only [Nat.add_sub_cancel, q]
      exact core_certificate_bound_le_decay d u k hd hk

theorem sum_coreAll_coreWeight_le_defect_sum (d : ℕ) (a : ℝ)
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hc : 1 + a ≤ 3) :
    (∑ C ∈ coreAllEdgeSets d, coreWeight d a C) ≤
      ∑ u ∈ Finset.range (2 ^ d + 1),
        (u + 1 : ℝ) * coreDecay d ^ u := by
  rw [sum_coreAll_by_defect]
  apply Finset.sum_le_sum
  intro u hu
  calc
    (∑ k ∈ Finset.range (u + 1),
        ∑ C ∈ coreDefectFiber d u k, coreWeight d a C) ≤
      ∑ _k ∈ Finset.range (u + 1), coreDecay d ^ u := by
        apply Finset.sum_le_sum
        intro k hk
        exact sum_coreDefectFiber_coreWeight_le d u k a hd ha hc
          (by simpa using Finset.mem_range.mp hk)
    _ = (u + 1 : ℝ) * coreDecay d ^ u := by simp

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

theorem sum_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x)
    (s : Finset ℕ) :
    (∑ t ∈ s, x ^ t / (t.factorial : ℕ)) ≤ Real.exp x := by
  have hs := (Real.summable_pow_div_factorial x).sum_le_tsum s
    (fun t ht => by positivity)
  rw [(NormedSpace.expSeries_div_hasSum_exp x).tsum_eq] at hs
  simpa [Real.exp_eq_exp_ℝ] using hs

theorem weighted_geometric_sum_le_two {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (s : Finset ℕ) :
    (∑ u ∈ s, (u + 1 : ℝ) * b ^ u) ≤ 2 := by
  have hterm (u : ℕ) : (u + 1 : ℝ) * b ^ u ≤ ((1 : ℝ) / 2) ^ u := by
    calc
      (u + 1 : ℝ) * b ^ u ≤ (2 : ℝ) ^ u * b ^ u := by
        gcongr
        exact_mod_cast nat_succ_le_two_pow u
      _ = ((2 : ℝ) * b) ^ u := by rw [mul_pow]
      _ ≤ ((1 : ℝ) / 2) ^ u := by gcongr <;> linarith
  calc
    (∑ u ∈ s, (u + 1 : ℝ) * b ^ u) ≤
        ∑ u ∈ s, ((1 : ℝ) / 2) ^ u := by
      exact Finset.sum_le_sum fun u hu => hterm u
    _ ≤ ∑' u : ℕ, ((1 : ℝ) / 2) ^ u :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).sum_le_tsum s (fun _ _ => by positivity)
    _ = 2 := by rw [tsum_geometric_of_lt_one] <;> norm_num

theorem weighted_geometric_range_le_one_add_four_mul {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (N : ℕ) :
    (∑ u ∈ Finset.range (N + 1), (u + 1 : ℝ) * b ^ u) ≤
      1 + 4 * b := by
  let S := (Finset.range (N + 1)).filter fun u => u ≠ 0
  have hterm (u : ℕ) : (u + 1 : ℝ) * b ^ u ≤ (2 * b) ^ u := by
    calc
      (u + 1 : ℝ) * b ^ u ≤ (2 : ℝ) ^ u * b ^ u := by
        gcongr
        exact_mod_cast nat_succ_le_two_pow u
      _ = (2 * b) ^ u := by rw [mul_pow]
  have hzero : (0 : ℕ) ∈ Finset.range (N + 1) := by simp
  have hsplit :
      (∑ u ∈ Finset.range (N + 1), (u + 1 : ℝ) * b ^ u) =
        1 + ∑ u ∈ S, (u + 1 : ℝ) * b ^ u := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
      (fun u => u = 0) (fun u => (u + 1 : ℝ) * b ^ u)]
    congr 1
    · simp
  rw [hsplit]
  have htail : (∑ u ∈ S, (u + 1 : ℝ) * b ^ u) ≤ 4 * b := by
    calc
      (∑ u ∈ S, (u + 1 : ℝ) * b ^ u) ≤
          ∑ u ∈ S, (2 * b) ^ u := by
        exact Finset.sum_le_sum fun u hu => hterm u
      _ ≤ 4 * b := by
        have hratio0 : 0 ≤ 2 * b := by positivity
        have hratio1 : 2 * b < 1 := by linarith
        have hsum := (summable_geometric_of_lt_one hratio0 hratio1).sum_le_tsum
          (insert 0 S) (fun _ _ => by positivity)
        have h0S : 0 ∉ S := by simp [S]
        rw [Finset.sum_insert h0S,
          tsum_geometric_of_lt_one hratio0 hratio1] at hsum
        norm_num at hsum
        have hfrac : (1 - 2 * b)⁻¹ ≤ 1 + 4 * b := by
          rw [show (1 - 2 * b)⁻¹ = 1 / (1 - 2 * b) by rw [one_div],
            div_le_iff₀ (by linarith : 0 < 1 - 2 * b)]
          nlinarith
        linarith
  linarith

theorem weighted_geometric_tail_le {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (s : Finset ℕ) (L : ℕ)
    (hL : ∀ u ∈ s, L ≤ u) :
    (∑ u ∈ s, (u + 1 : ℝ) * b ^ u) ≤
      4 * ((2 : ℝ) / 3) ^ L := by
  have hterm (u : ℕ) (hu : u ∈ s) :
      (u + 1 : ℝ) * b ^ u ≤
        ((2 : ℝ) / 3) ^ L * ((3 : ℝ) / 4) ^ u := by
    have hgeom : ((2 : ℝ) / 3) ^ u ≤ ((2 : ℝ) / 3) ^ L :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hL u hu)
    calc
      (u + 1 : ℝ) * b ^ u ≤ ((1 : ℝ) / 2) ^ u := by
        calc
          (u + 1 : ℝ) * b ^ u ≤ (2 : ℝ) ^ u * b ^ u := by
            gcongr
            exact_mod_cast nat_succ_le_two_pow u
          _ = ((2 : ℝ) * b) ^ u := by rw [mul_pow]
          _ ≤ ((1 : ℝ) / 2) ^ u := by gcongr <;> linarith
      _ = ((2 : ℝ) / 3) ^ u * ((3 : ℝ) / 4) ^ u := by
        rw [← mul_pow]
        norm_num
      _ ≤ ((2 : ℝ) / 3) ^ L * ((3 : ℝ) / 4) ^ u := by
        gcongr
  calc
    (∑ u ∈ s, (u + 1 : ℝ) * b ^ u) ≤
        ∑ u ∈ s, ((2 : ℝ) / 3) ^ L * ((3 : ℝ) / 4) ^ u := by
      exact Finset.sum_le_sum fun u hu => hterm u hu
    _ = ((2 : ℝ) / 3) ^ L *
        ∑ u ∈ s, ((3 : ℝ) / 4) ^ u := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) / 3) ^ L *
        ∑' u : ℕ, ((3 : ℝ) / 4) ^ u := by
      gcongr
      exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 : ℝ) / 4 < 1)).sum_le_tsum s
          (fun _ _ => by positivity)
    _ = 4 * ((2 : ℝ) / 3) ^ L := by
      rw [tsum_geometric_of_lt_one] <;> norm_num
      ring

theorem pow_le_half_pow_mul_double_pow {x : ℝ} (hx : 0 ≤ x)
    {L t : ℕ} (hLt : L ≤ t) :
    x ^ t ≤ ((1 : ℝ) / 2) ^ L * (2 * x) ^ t := by
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (t - L) := one_le_pow₀ (by norm_num)
  have hid : ((1 : ℝ) / 2) ^ L * (2 * x) ^ t =
      (2 : ℝ) ^ (t - L) * x ^ t := by
    have hpowtwo : (2 : ℝ) ^ t = 2 ^ L * 2 ^ (t - L) := by
      rw [← pow_add]
      congr 1
      omega
    have hcancel : ((1 : ℝ) / 2) ^ L * 2 ^ L = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      ((1 : ℝ) / 2) ^ L * (2 * x) ^ t =
          ((1 : ℝ) / 2) ^ L * 2 ^ t * x ^ t := by
            rw [mul_pow]
            ring
      _ = (((1 : ℝ) / 2) ^ L * 2 ^ L) *
          2 ^ (t - L) * x ^ t := by rw [hpowtwo]; ring
      _ = (2 : ℝ) ^ (t - L) * x ^ t := by rw [hcancel, one_mul]
  rw [hid]
  exact le_mul_of_one_le_left (pow_nonneg hx t) hone

theorem sum_pow_div_factorial_tail_le {x : ℝ} (hx : 0 ≤ x)
    (s : Finset ℕ) (L : ℕ) (hL : ∀ t ∈ s, L ≤ t) :
    (∑ t ∈ s, x ^ t / (t.factorial : ℕ)) ≤
      ((1 : ℝ) / 2) ^ L * Real.exp (2 * x) := by
  calc
    (∑ t ∈ s, x ^ t / (t.factorial : ℕ)) ≤
        ∑ t ∈ s,
          (((1 : ℝ) / 2) ^ L * (2 * x) ^ t) /
            (t.factorial : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      gcongr
      exact pow_le_half_pow_mul_double_pow hx (hL t ht)
    _ = ((1 : ℝ) / 2) ^ L *
        ∑ t ∈ s, (2 * x) ^ t / (t.factorial : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ ((1 : ℝ) / 2) ^ L * Real.exp (2 * x) := by
      gcongr
      exact sum_pow_div_factorial_le_exp (by positivity) s

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

noncomputable def isolatedFiniteSum (d : ℕ) (a : ℝ)
    (C : Finset (Sym2 (CubeVertex d))) : ℝ :=
  ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
    sharpIsolatedWeight d a C t

noncomputable def universalIsolatedLambda (d : ℕ) (a : ℝ) : ℝ :=
  (81 : ℝ) * a * d ^ 2 / 2

theorem isolatedFiniteSum_nonneg (d : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (C : Finset (Sym2 (CubeVertex d))) :
    0 ≤ isolatedFiniteSum d a C := by
  unfold isolatedFiniteSum
  apply Finset.sum_nonneg
  intro t ht
  exact sharpIsolatedWeight_nonneg d ha C t

theorem isolatedFiniteSum_le_exp_universal (d : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (C : Finset (Sym2 (CubeVertex d))) :
    isolatedFiniteSum d a C ≤ Real.exp (universalIsolatedLambda d a) := by
  unfold isolatedFiniteSum
  calc
    (∑ t ∈ Finset.range (cubeEdgeCount d + 1),
        sharpIsolatedWeight d a C t) ≤
      ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
        universalIsolatedLambda d a ^ t / (t.factorial : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      simpa [universalIsolatedLambda] using
        sharpIsolatedWeight_le_universal d ha C t
    _ ≤ Real.exp (universalIsolatedLambda d a) :=
      sum_pow_div_factorial_le_exp (by
        unfold universalIsolatedLambda
        positivity) _

theorem isolatedFiniteSum_le_small_add_tail (d : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (C : Finset (Sym2 (CubeVertex d))) (T : ℕ)
    (hTn : T < 2 ^ d)
    (hsmallCore : 2 * (edgeSupport C).card < T) :
    isolatedFiniteSum d a C ≤
      Real.exp (isolatedSmallLambda d a T) +
        ((1 : ℝ) / 2) ^ (T / 4) *
          Real.exp (2 * universalIsolatedLambda d a) := by
  classical
  let R := Finset.range (cubeEdgeCount d + 1)
  let p : ℕ → Prop := fun t => (edgeSupport C).card + 2 * t ≤ T
  have hsplit := Finset.sum_filter_add_sum_filter_not R p
    (fun t => sharpIsolatedWeight d a C t)
  change (∑ t ∈ R, sharpIsolatedWeight d a C t) ≤ _
  rw [← hsplit]
  gcongr
  · calc
      (∑ t ∈ R with p t, sharpIsolatedWeight d a C t) ≤
          ∑ t ∈ R with p t,
            isolatedSmallLambda d a T ^ t / (t.factorial : ℕ) := by
        apply Finset.sum_le_sum
        intro t ht
        exact sharpIsolatedWeight_le_small d ha C t T hTn
          (Finset.mem_filter.mp ht).2
      _ ≤ Real.exp (isolatedSmallLambda d a T) :=
        sum_pow_div_factorial_le_exp (by
          unfold isolatedSmallLambda
          positivity) _
  · calc
      (∑ t ∈ R with ¬p t, sharpIsolatedWeight d a C t) ≤
          ∑ t ∈ R with ¬p t,
            universalIsolatedLambda d a ^ t / (t.factorial : ℕ) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa [universalIsolatedLambda] using
          sharpIsolatedWeight_le_universal d ha C t
      _ ≤ ((1 : ℝ) / 2) ^ (T / 4) *
          Real.exp (2 * universalIsolatedLambda d a) := by
        apply sum_pow_div_factorial_tail_le (by
          unfold universalIsolatedLambda
          positivity)
        intro t ht
        have hnot := (Finset.mem_filter.mp ht).2
        dsimp [p] at hnot
        omega

theorem overlapAverage_le_core_isolated (d : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    overlapAverage d (1 + a) ≤
      ∑ C ∈ coreAllEdgeSets d,
        coreWeight d a C * isolatedFiniteSum d a C := by
  calc
    overlapAverage d (1 + a) ≤
      ∑ C ∈ coreAllEdgeSets d,
        ∑ t ∈ Finset.range (cubeEdgeCount d + 1),
          (Nat.choose (availableCoreEdges d C).card t : ℝ) *
            sharpCoreIsolatedUpperTerm d a C t :=
      overlapAverage_le_sum_core_isolated_sharp d a ha
    _ = ∑ C ∈ coreAllEdgeSets d,
        coreWeight d a C * isolatedFiniteSum d a C := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [isolatedFiniteSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact choose_mul_sharpCoreIsolatedUpperTerm_eq d a C t

noncomputable def largeCoreSets (d T : ℕ) :
    Finset (Finset (Sym2 (CubeVertex d))) := by
  classical
  exact (coreAllEdgeSets d).filter fun C =>
    T ≤ 2 * (edgeSupport C).card

theorem core_support_le_three_mul_defect (d : ℕ)
    {C : Finset (Sym2 (CubeVertex d))}
    (hC : C ∈ coreAllEdgeSets d) :
    (edgeSupport C).card ≤ 3 * coreDefect d C := by
  have hk := component_le_coreDefect d hC
  have h2 := two_mul_overlapComponentCount_le_support_card d C (by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1)
  unfold coreDefect at hk ⊢
  omega

theorem sum_largeCore_coreWeight_le (d T : ℕ) {a : ℝ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hc : 1 + a ≤ 3)
    (hb : coreDecay d ≤ 1 / 4) :
    (∑ C ∈ largeCoreSets d T, coreWeight d a C) ≤
      4 * ((2 : ℝ) / 3) ^ (T / 6) := by
  classical
  have hb0 : 0 ≤ coreDecay d := by unfold coreDecay; positivity
  let f : Finset (Sym2 (CubeVertex d)) → ℝ := fun C =>
    if T ≤ 2 * (edgeSupport C).card then coreWeight d a C else 0
  have hrewrite :
      (∑ C ∈ largeCoreSets d T, coreWeight d a C) =
        ∑ C ∈ coreAllEdgeSets d, f C := by
    unfold largeCoreSets
    rw [Finset.sum_filter]
  rw [hrewrite, sum_coreAll_by_defect]
  let S := (Finset.range (2 ^ d + 1)).filter fun u => T / 6 ≤ u
  calc
    (∑ u ∈ Finset.range (2 ^ d + 1),
        ∑ k ∈ Finset.range (u + 1),
          ∑ C ∈ coreDefectFiber d u k, f C) ≤
      ∑ u ∈ S, (u + 1 : ℝ) * coreDecay d ^ u := by
      dsimp only [S]
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro u hu
      split_ifs with hLu
      · calc
          (∑ k ∈ Finset.range (u + 1),
              ∑ C ∈ coreDefectFiber d u k, f C) ≤
            ∑ k ∈ Finset.range (u + 1),
              ∑ C ∈ coreDefectFiber d u k, coreWeight d a C := by
            apply Finset.sum_le_sum
            intro k hk
            apply Finset.sum_le_sum
            intro C hC
            simp only [f]
            split_ifs
            · exact le_rfl
            · unfold coreWeight
              positivity
          _ ≤ ∑ _k ∈ Finset.range (u + 1), coreDecay d ^ u := by
            apply Finset.sum_le_sum
            intro k hk
            exact sum_coreDefectFiber_coreWeight_le d u k a hd ha hc
              (by simpa using Finset.mem_range.mp hk)
          _ = (u + 1 : ℝ) * coreDecay d ^ u := by simp
      · have hzero : ∀ k ∈ Finset.range (u + 1),
            (∑ C ∈ coreDefectFiber d u k, f C) = 0 := by
          intro k hk
          apply Finset.sum_eq_zero
          intro C hC
          have hCcore : C ∈ coreAllEdgeSets d :=
            (Finset.mem_filter.mp
              (show C ∈ coreDefectFiber d u k from hC)).1
          have hu : coreDefect d C = u :=
            (Finset.mem_filter.mp hC).2.1
          have hs := core_support_le_three_mul_defect d hCcore
          simp only [f]
          rw [if_neg]
          intro hlarge
          have : T / 6 ≤ u := by omega
          exact hLu this
        rw [Finset.sum_eq_zero hzero]
    _ ≤ 4 * ((2 : ℝ) / 3) ^ (T / 6) := by
      apply weighted_geometric_tail_le hb0 hb S (T / 6)
      intro u hu
      exact (Finset.mem_filter.mp hu).2

theorem overlapAverage_le_three_terms (d T : ℕ) {a : ℝ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hc : 1 + a ≤ 3)
    (hTn : T < 2 ^ d) (hb : coreDecay d ≤ 1 / 4) :
    overlapAverage d (1 + a) ≤
      (4 * ((2 : ℝ) / 3) ^ (T / 6)) *
        Real.exp (universalIsolatedLambda d a) +
      ((1 + 4 * coreDecay d) * Real.exp (isolatedSmallLambda d a T) +
        2 * (((1 : ℝ) / 2) ^ (T / 4) *
          Real.exp (2 * universalIsolatedLambda d a))) := by
  have hcoreTotal := sum_coreAll_coreWeight_le_defect_sum d a hd ha hc
  have hb0 : 0 ≤ coreDecay d := by unfold coreDecay; positivity
  have hweighted := weighted_geometric_range_le_one_add_four_mul hb0 hb (2 ^ d)
  have hcoreRefined : (∑ C ∈ coreAllEdgeSets d, coreWeight d a C) ≤
      1 + 4 * coreDecay d := hcoreTotal.trans hweighted
  have hcoreTwo : (∑ C ∈ coreAllEdgeSets d, coreWeight d a C) ≤ 2 := by
    calc
      (∑ C ∈ coreAllEdgeSets d, coreWeight d a C) ≤
          1 + 4 * coreDecay d := hcoreRefined
      _ ≤ 2 := by linarith
  have hlarge := sum_largeCore_coreWeight_le d T hd ha hc hb
  calc
    overlapAverage d (1 + a) ≤
        ∑ C ∈ coreAllEdgeSets d,
          coreWeight d a C * isolatedFiniteSum d a C :=
      overlapAverage_le_core_isolated d ha
    _ = (∑ C ∈ largeCoreSets d T,
          coreWeight d a C * isolatedFiniteSum d a C) +
        ∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
          coreWeight d a C * isolatedFiniteSum d a C := by
      let U := coreAllEdgeSets d
      let p : Finset (Sym2 (CubeVertex d)) → Prop := fun C =>
        T ≤ 2 * (edgeSupport C).card
      have hcomp : U.filter (fun C => C ∉ U.filter p) =
          U.filter (fun C => ¬p C) := by
        ext C
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hU, hnot⟩
          exact ⟨hU, fun hp => hnot ⟨hU, hp⟩⟩
        · rintro ⟨hU, hnp⟩
          exact ⟨hU, fun hmem => hnp hmem.2⟩
      change (∑ C ∈ U, coreWeight d a C * isolatedFiniteSum d a C) =
        (∑ C ∈ U.filter p, coreWeight d a C * isolatedFiniteSum d a C) +
        ∑ C ∈ U.filter (fun C => C ∉ U.filter p),
          coreWeight d a C * isolatedFiniteSum d a C
      rw [hcomp]
      exact (Finset.sum_filter_add_sum_filter_not U p
        (fun C => coreWeight d a C * isolatedFiniteSum d a C)).symm
    _ ≤ (∑ C ∈ largeCoreSets d T, coreWeight d a C) *
          Real.exp (universalIsolatedLambda d a) +
        (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
          coreWeight d a C) *
          (Real.exp (isolatedSmallLambda d a T) +
            ((1 : ℝ) / 2) ^ (T / 4) *
              Real.exp (2 * universalIsolatedLambda d a)) := by
      gcongr
      · rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro C hC
        exact mul_le_mul_of_nonneg_left
          (isolatedFiniteSum_le_exp_universal d ha C)
          (by unfold coreWeight; positivity)
      · rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro C hC
        have hcore := (Finset.mem_filter.mp hC).1
        have hnot := (Finset.mem_filter.mp hC).2
        have hsmall : 2 * (edgeSupport C).card < T := by
          simp [largeCoreSets, hcore] at hnot
          omega
        exact mul_le_mul_of_nonneg_left
          (isolatedFiniteSum_le_small_add_tail d ha C T hTn hsmall)
          (by unfold coreWeight; positivity)
    _ ≤ (4 * ((2 : ℝ) / 3) ^ (T / 6)) *
          Real.exp (universalIsolatedLambda d a) +
        ((1 + 4 * coreDecay d) * Real.exp (isolatedSmallLambda d a T) +
        2 * (((1 : ℝ) / 2) ^ (T / 4) *
              Real.exp (2 * universalIsolatedLambda d a))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hlarge (Real.exp_pos _).le
      · calc
          (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
              coreWeight d a C) *
              (Real.exp (isolatedSmallLambda d a T) +
                ((1 : ℝ) / 2) ^ (T / 4) *
                  Real.exp (2 * universalIsolatedLambda d a)) ≤
            (1 + 4 * coreDecay d) *
                Real.exp (isolatedSmallLambda d a T) +
              2 * (((1 : ℝ) / 2) ^ (T / 4) *
                Real.exp (2 * universalIsolatedLambda d a)) := by
            have hsmallMass :
                (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
                  coreWeight d a C) ≤ 1 + 4 * coreDecay d := by
              calc
                (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
                    coreWeight d a C) ≤
                  ∑ C ∈ coreAllEdgeSets d, coreWeight d a C := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · exact Finset.filter_subset _ _
                    · intro C hC hnot
                      unfold coreWeight
                      positivity
                _ ≤ 1 + 4 * coreDecay d := hcoreRefined
            have hsmallMassTwo :
                (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
                  coreWeight d a C) ≤ 2 := hcoreTwo.trans' (by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · exact Finset.filter_subset _ _
                    · intro C hC hnot
                      unfold coreWeight
                      positivity)
            calc
              _ = (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
                    coreWeight d a C) *
                    Real.exp (isolatedSmallLambda d a T) +
                  (∑ C ∈ coreAllEdgeSets d with C ∉ largeCoreSets d T,
                    coreWeight d a C) *
                    (((1 : ℝ) / 2) ^ (T / 4) *
                      Real.exp (2 * universalIsolatedLambda d a)) := by ring
              _ ≤ _ := add_le_add
                (mul_le_mul_of_nonneg_right hsmallMass (Real.exp_pos _).le)
                (mul_le_mul_of_nonneg_right hsmallMassTwo (by positivity))

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph Topology

theorem polynomial_div_two_pow_tendsto_zero (k : ℕ) :
    Tendsto (fun d : ℕ => (d : ℝ) ^ k / ((2 ^ d : ℕ) : ℝ))
      atTop (nhds 0) := by
  have h := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) k (r₁ := (1 : ℝ) / 2) (r₂ := 1) (by norm_num)
  simpa [div_eq_mul_inv] using h.tendsto_div_nhds_zero

theorem coreDecay_tendsto_zero : Tendsto coreDecay atTop (nhds 0) := by
  have h := polynomial_mul_sqrt_three_div_two_pow_tendsto_zero 6
  have hsqrt : (Real.sqrt 3) ^ 4 = (9 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hconst := h.const_mul ((162 : ℝ) ^ 2 * (Real.sqrt 3) ^ 4)
  convert hconst using 1
  · funext d
    unfold coreDecay
    push_cast
    rw [pow_add, div_eq_mul_inv, div_pow]
    ring
  · ring

theorem cutoff_lt_two_pow_eventually :
    ∀ᶠ d : ℕ in atTop, d ^ 4 < 2 ^ d := by
  have h := polynomial_div_two_pow_tendsto_zero 4
  have hevent : ∀ᶠ x : ℝ in nhds 0, x < 1 :=
    eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h.eventually hevent] with d hd
  have hpow : (0 : ℝ) < ((2 ^ d : ℕ) : ℝ) := by positivity
  rw [div_lt_one hpow] at hd
  exact_mod_cast hd

noncomputable def comparisonExcess (d : ℕ) : ℝ :=
  (((ambientEdgeCount d - 2 * cubeEdgeCount d : ℕ) : ℝ) /
      (comparisonLayer d - 2 * cubeEdgeCount d : ℕ)) - 1

noncomputable def comparisonBackgroundExponent (d : ℕ) : ℝ :=
  (cubeEdgeCount d : ℝ) ^ 2 *
    (ambientEdgeCount d - comparisonLayer d : ℕ) /
      ((ambientEdgeCount d : ℝ) * comparisonLayer d)

theorem cast_cubeEdgeCount {d : ℕ} (hd : 1 ≤ d) :
    (cubeEdgeCount d : ℝ) = (d : ℝ) * ((2 ^ d : ℕ) : ℝ) / 2 := by
  have h := two_mul_cubeEdgeCount d
  have hR : (2 : ℝ) * cubeEdgeCount d = (d : ℝ) * (2 ^ d : ℕ) := by
    exact_mod_cast h
  linarith

theorem cast_ambientEdgeCount {d : ℕ} (hd : 1 ≤ d) :
    (ambientEdgeCount d : ℝ) =
      ((2 ^ d : ℕ) : ℝ) * (((2 ^ d : ℕ) : ℝ) - 1) / 2 := by
  rw [ambientEdgeCount_eq_mul (by omega)]
  push_cast
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) ^ (d - 1) * 2 = 2 ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  rw [← hp]
  ring

theorem cast_ambientEdgeCount_div_two {d : ℕ} (hd : 2 ≤ d) :
    ((ambientEdgeCount d / 2 : ℕ) : ℝ) =
      ((2 ^ d : ℕ) : ℝ) * (((2 ^ d : ℕ) : ℝ) - 1) / 4 := by
  rw [ambientEdgeCount_div_two_eq hd]
  push_cast
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) ^ (d - 2) * 4 = 2 ^ d := by
    calc
      (2 : ℝ) ^ (d - 2) * 4 = 2 ^ (d - 2) * 2 ^ 2 := by norm_num
      _ = 2 ^ ((d - 2) + 2) := by rw [pow_add]
      _ = 2 ^ d := by congr 1; omega
  rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
  rw [← hp]
  ring

theorem cast_comparisonLayer {d : ℕ} (hd : 8 ≤ d) :
    (comparisonLayer d : ℝ) =
      ((2 ^ d : ℕ) : ℝ) *
        ((((2 ^ d : ℕ) : ℝ) - 1) - 4 * d) / 4 := by
  have hcond := comparisonLayer_conditions hd
  have hsub : 2 * cubeEdgeCount d ≤ ambientEdgeCount d / 2 := by
    rw [comparisonLayer] at hcond
    omega
  rw [comparisonLayer]
  rw [Nat.cast_sub hsub]
  rw [cast_ambientEdgeCount_div_two (by omega)]
  have he := cast_cubeEdgeCount (d := d) (by omega)
  push_cast
  simp only [Nat.cast_pow, Nat.cast_ofNat] at he ⊢
  rw [he]
  ring

theorem comparison_rational_identity (x y : ℝ) (hx : x ≠ 0)
    (hy : x - 1 - 8 * y ≠ 0) :
    (x * (x - 1) / 2 - 2 * (y * x / 2)) /
          (x * (x - 1 - 4 * y) / 4 - 2 * (y * x / 2)) - 1 =
      (x - 1 + 4 * y) / (x - 1 - 8 * y) := by
  have hnum : x * (x - 1) / 2 - 2 * (y * x / 2) =
      x * (x - 1 - 2 * y) / 2 := by ring
  have hden : x * (x - 1 - 4 * y) / 4 - 2 * (y * x / 2) =
      x * (x - 1 - 8 * y) / 4 := by ring
  have hy' : -1 + x - y * 8 ≠ 0 := by
    intro h
    apply hy
    linarith
  have hquot :
      (x * (x - 1) / 2 - 2 * (y * x / 2)) /
          (x * (x - 1 - 4 * y) / 4 - 2 * (y * x / 2)) =
        2 * (x - 1 - 2 * y) / (x - 1 - 8 * y) := by
    rw [hnum, hden]
    field_simp [hx, hy]
    norm_num
    ring
  rw [hquot]
  ring_nf
  have hcancel := inv_mul_cancel₀ hy'
  ring_nf at hcancel
  linarith only [hcancel]

theorem comparisonExcess_formula {d : ℕ} (hd : 8 ≤ d) :
    comparisonExcess d =
      ((((2 ^ d : ℕ) : ℝ) - 1 + 4 * d) /
        (((2 ^ d : ℕ) : ℝ) - 1 - 8 * d)) := by
  let X : ℝ := ((2 ^ d : ℕ) : ℝ)
  have hcond := comparisonLayer_conditions hd
  have hN := cast_ambientEdgeCount (by omega : 1 ≤ d)
  have hM := cast_comparisonLayer hd
  have he := cast_cubeEdgeCount (by omega : 1 ≤ d)
  have hdenNat : 2 * cubeEdgeCount d ≤ comparisonLayer d := hcond.1.le
  have hnumNat : 2 * cubeEdgeCount d ≤ ambientEdgeCount d :=
    hdenNat.trans hcond.2
  have hden : 0 < X - 1 - 8 * d := by
    have hpos : 0 < (comparisonLayer d - 2 * cubeEdgeCount d : ℕ) := by omega
    have hposR : (0 : ℝ) < (comparisonLayer d - 2 * cubeEdgeCount d : ℕ) :=
      by exact_mod_cast hpos
    rw [Nat.cast_sub hdenNat, Nat.cast_mul, hM, he] at hposR
    dsimp [X] at hposR ⊢
    nlinarith [show (0 : ℝ) < ((2 ^ d : ℕ) : ℝ) by positivity]
  unfold comparisonExcess
  rw [Nat.cast_sub hnumNat, Nat.cast_sub hdenNat, Nat.cast_mul, hN, hM, he]
  dsimp [X] at hden ⊢
  exact comparison_rational_identity _ _ (by positivity) (ne_of_gt hden)

theorem comparisonBackgroundExponent_formula {d : ℕ} (hd : 8 ≤ d) :
    comparisonBackgroundExponent d =
      (d : ℝ) ^ 2 / 2 *
        ((((2 ^ d : ℕ) : ℝ) *
            (((2 ^ d : ℕ) : ℝ) - 1 + 4 * d)) /
          ((((2 ^ d : ℕ) : ℝ) - 1) *
            (((2 ^ d : ℕ) : ℝ) - 1 - 4 * d))) := by
  let X : ℝ := ((2 ^ d : ℕ) : ℝ)
  have hcond := comparisonLayer_conditions hd
  have hN := cast_ambientEdgeCount (by omega : 1 ≤ d)
  have hM := cast_comparisonLayer hd
  have he := cast_cubeEdgeCount (by omega : 1 ≤ d)
  have hMN : comparisonLayer d ≤ ambientEdgeCount d := hcond.2
  have hMpos : (0 : ℝ) < comparisonLayer d := by
    exact_mod_cast (show 0 < comparisonLayer d by omega)
  have hNpos : (0 : ℝ) < ambientEdgeCount d := by
    exact_mod_cast (show 0 < ambientEdgeCount d by omega)
  have hden1 : 0 < X - 1 := by
    dsimp [X]
    have hxNat : 1 < 2 ^ d := by
      have := eight_mul_add_one_lt_two_pow (by omega : 6 ≤ d)
      omega
    have hx : (1 : ℝ) < ((2 ^ d : ℕ) : ℝ) := by exact_mod_cast hxNat
    linarith
  have hden2 : 0 < X - 1 - 4 * d := by
    rw [hM] at hMpos
    dsimp [X] at hMpos ⊢
    nlinarith [show (0 : ℝ) < ((2 ^ d : ℕ) : ℝ) by positivity]
  unfold comparisonBackgroundExponent
  rw [Nat.cast_sub hMN, hN, hM, he]
  dsimp [X] at hden1 hden2 ⊢
  field_simp [ne_of_gt hden1, ne_of_gt hden2]
  ring

theorem normalize_linear_ratio (x a b : ℝ) (hx : x ≠ 0) :
    (x + a) / (x + b) = (1 + a / x) / (1 + b / x) := by
  have ha : 1 + a / x = (x + a) / x := by
    field_simp [hx]
  have hb : 1 + b / x = (x + b) / x := by
    field_simp [hx]
  rw [ha, hb, div_div_div_cancel_right₀ hx]

theorem comparisonExcess_tendsto_one :
    Tendsto comparisonExcess atTop (nhds 1) := by
  let z0 : ℕ → ℝ := fun d => 1 / (((2 ^ d : ℕ) : ℝ))
  let z1 : ℕ → ℝ := fun d => (d : ℝ) / (((2 ^ d : ℕ) : ℝ))
  have hz0 : Tendsto z0 atTop (nhds 0) := by
    simpa [z0] using polynomial_div_two_pow_tendsto_zero 0
  have hz1 : Tendsto z1 atTop (nhds 0) := by
    simpa [z1] using polynomial_div_two_pow_tendsto_zero 1
  have hnum : Tendsto (fun d => 1 - z0 d + 4 * z1 d)
      atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub hz0).add (tendsto_const_nhds.mul hz1) using 1 <;>
      ring
  have hden : Tendsto (fun d => 1 - z0 d - 8 * z1 d)
      atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub hz0).sub (tendsto_const_nhds.mul hz1) using 1 <;>
      ring
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      ((fun d => 1 - z0 d + 4 * z1 d) /
        (fun d => 1 - z0 d - 8 * z1 d)) =ᶠ[atTop] comparisonExcess := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    rw [comparisonExcess_formula hd]
    let X : ℝ := ((2 ^ d : ℕ) : ℝ)
    have hx : X ≠ 0 := by dsimp [X]; positivity
    rw [show X - 1 + 4 * d = X + (-1 + 4 * d) by ring,
      show X - 1 - 8 * d = X + (-1 - 8 * d) by ring,
      normalize_linear_ratio X (-1 + 4 * d) (-1 - 8 * d) hx]
    simp only [z0, z1]
    dsimp [X]
    field_simp
    ring
  simpa using hquot.congr' heq

theorem comparisonExcess_nonneg_eventually :
    ∀ᶠ d : ℕ in atTop, 0 ≤ comparisonExcess d := by
  have h := comparisonExcess_tendsto_one
  exact h.eventually (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1))

theorem comparisonExcess_le_two_eventually :
    ∀ᶠ d : ℕ in atTop, 1 + comparisonExcess d ≤ 3 := by
  have h := comparisonExcess_tendsto_one
  have he : ∀ᶠ x : ℝ in nhds 1, x < 2 :=
    eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)
  filter_upwards [h.eventually he] with d hd
  linarith

noncomputable def backgroundCorrectionNumerator (d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 *
    (1 / (((2 ^ d : ℕ) : ℝ)) -
      (1 / (((2 ^ d : ℕ) : ℝ))) ^ 2 +
      8 * ((d : ℝ) / (((2 ^ d : ℕ) : ℝ))) -
      4 * (1 / (((2 ^ d : ℕ) : ℝ))) *
        ((d : ℝ) / (((2 ^ d : ℕ) : ℝ))))

noncomputable def backgroundCorrectionDenominator (d : ℕ) : ℝ :=
  (1 - 1 / (((2 ^ d : ℕ) : ℝ))) *
    (1 - 1 / (((2 ^ d : ℕ) : ℝ)) -
      4 * ((d : ℝ) / (((2 ^ d : ℕ) : ℝ))))

theorem backgroundCorrectionNumerator_tendsto_zero :
    Tendsto backgroundCorrectionNumerator atTop (nhds 0) := by
  have h0 := polynomial_div_two_pow_tendsto_zero 0
  have h2 := polynomial_div_two_pow_tendsto_zero 2
  have h3 := polynomial_div_two_pow_tendsto_zero 3
  have hsmall2 : Tendsto
      (fun d : ℕ => ((d : ℝ) ^ 2 / ((2 ^ d : ℕ) : ℝ)) *
        (1 / ((2 ^ d : ℕ) : ℝ))) atTop (nhds 0) := by
    convert h2.mul h0 using 1 <;> ring
  have hsmall3 : Tendsto
      (fun d : ℕ => ((d : ℝ) ^ 3 / ((2 ^ d : ℕ) : ℝ)) *
        (1 / ((2 ^ d : ℕ) : ℝ))) atTop (nhds 0) := by
    convert h3.mul h0 using 1 <;> ring
  unfold backgroundCorrectionNumerator
  convert ((h2.sub hsmall2).add (h3.const_mul 8)).sub
      (hsmall3.const_mul 4) using 1 <;> ring

theorem backgroundCorrectionDenominator_tendsto_one :
    Tendsto backgroundCorrectionDenominator atTop (nhds 1) := by
  have h0 := polynomial_div_two_pow_tendsto_zero 0
  have h1 := polynomial_div_two_pow_tendsto_zero 1
  have hone : Tendsto (fun _d : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  unfold backgroundCorrectionDenominator
  convert (hone.sub h0).mul ((hone.sub h0).sub (h1.const_mul 4)) using 1
  · funext d
    ring
  · ring

theorem normalize_background_factor (x y : ℝ) (hx : x ≠ 0) :
    x * (x - 1 + 4 * y) / ((x - 1) * (x - 1 - 4 * y)) =
      (1 - 1 / x + 4 * (y / x)) /
        ((1 - 1 / x) * (1 - 1 / x - 4 * (y / x))) := by
  have hn : x * (x - 1 + 4 * y) / x ^ 2 =
      1 - 1 / x + 4 * (y / x) := by
    field_simp [hx]
  have hd : (x - 1) * (x - 1 - 4 * y) / x ^ 2 =
      (1 - 1 / x) * (1 - 1 / x - 4 * (y / x)) := by
    field_simp [hx]
  calc
    x * (x - 1 + 4 * y) / ((x - 1) * (x - 1 - 4 * y)) =
        (x * (x - 1 + 4 * y) / x ^ 2) /
          ((x - 1) * (x - 1 - 4 * y) / x ^ 2) :=
      (div_div_div_cancel_right₀ (pow_ne_zero 2 hx)
        (x * (x - 1 + 4 * y)) ((x - 1) * (x - 1 - 4 * y))).symm
    _ = _ := by rw [hn, hd]

theorem comparisonBackgroundExponent_sub_main_tendsto_zero :
    Tendsto (fun d => comparisonBackgroundExponent d - (d : ℝ) ^ 2 / 2)
      atTop (nhds 0) := by
  have hquot := backgroundCorrectionNumerator_tendsto_zero.div
    backgroundCorrectionDenominator_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  have hhalf := hquot.const_mul ((1 : ℝ) / 2)
  have heq : (fun d => (1 : ℝ) / 2 *
      (backgroundCorrectionNumerator / backgroundCorrectionDenominator) d) =ᶠ[atTop]
      (fun d => comparisonBackgroundExponent d - (d : ℝ) ^ 2 / 2) := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    rw [comparisonBackgroundExponent_formula hd]
    let X : ℝ := ((2 ^ d : ℕ) : ℝ)
    have hx : X ≠ 0 := by dsimp [X]; positivity
    rw [normalize_background_factor X d hx]
    let N : ℝ := 1 - 1 / X + 4 * ((d : ℝ) / X)
    let D : ℝ := (1 - 1 / X) *
      (1 - 1 / X - 4 * ((d : ℝ) / X))
    have hD : backgroundCorrectionDenominator d ≠ 0 := by
      have hX1 : (1 : ℝ) < X := by
        dsimp [X]
        exact_mod_cast (show 1 < 2 ^ d by
          have := eight_mul_add_one_lt_two_pow (by omega : 6 ≤ d)
          omega)
      have hX4 : (4 : ℝ) * d + 1 < X := by
        dsimp [X]
        exact_mod_cast (show 4 * d + 1 < 2 ^ d by
          have := eight_mul_add_one_lt_two_pow (by omega : 6 ≤ d)
          omega)
      have hXpos : 0 < X := lt_trans (by norm_num) hX1
      have hfirst : 0 < 1 - 1 / X := by
        rw [sub_pos, div_lt_one hXpos]
        exact hX1
      have hsecond : 0 < 1 - 1 / X - 4 * ((d : ℝ) / X) := by
        have hfrac : 1 / X + 4 * ((d : ℝ) / X) < 1 := by
          rw [show 1 / X + 4 * ((d : ℝ) / X) =
            (1 + 4 * (d : ℝ)) / X by field_simp]
          rw [div_lt_one hXpos]
          linarith
        linarith
      unfold backgroundCorrectionDenominator
      dsimp [X] at hfirst hsecond ⊢
      exact mul_ne_zero (ne_of_gt hfirst) (ne_of_gt hsecond)
    have hDEq : backgroundCorrectionDenominator d = D := by
      unfold backgroundCorrectionDenominator
      rfl
    have hNEq : backgroundCorrectionNumerator d =
        (d : ℝ) ^ 2 * (N - D) := by
      unfold backgroundCorrectionNumerator
      dsimp [N, D, X]
      ring
    change (1 : ℝ) / 2 *
        (backgroundCorrectionNumerator d / backgroundCorrectionDenominator d) =
      (d : ℝ) ^ 2 / 2 * (N / D) - (d : ℝ) ^ 2 / 2
    rw [hNEq, hDEq]
    have hD' : D ≠ 0 := hDEq ▸ hD
    field_simp [hD']
  simpa using hhalf.congr' heq

theorem comparisonExcess_rate_tendsto_zero :
    Tendsto (fun d : ℕ => (comparisonExcess d - 1) * (d : ℝ) ^ 2)
      atTop (nhds 0) := by
  let D : ℕ → ℝ := fun d =>
    1 - 1 / (((2 ^ d : ℕ) : ℝ)) -
      8 * ((d : ℝ) / (((2 ^ d : ℕ) : ℝ)))
  have h0 := polynomial_div_two_pow_tendsto_zero 0
  have h1 := polynomial_div_two_pow_tendsto_zero 1
  have h3 := polynomial_div_two_pow_tendsto_zero 3
  have hD : Tendsto D atTop (nhds 1) := by
    have hone : Tendsto (fun _d : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    unfold D
    convert (hone.sub h0).sub (h1.const_mul 8) using 1
    · funext d
      ring
    · ring
  have hlim := (h3.const_mul 12).div hD (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun d : ℕ => 12 *
      ((d : ℝ) ^ 3 / (((2 ^ d : ℕ) : ℝ))) / D d) =ᶠ[atTop]
      (fun d : ℕ => (comparisonExcess d - 1) * (d : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    rw [comparisonExcess_formula hd]
    let X : ℝ := ((2 ^ d : ℕ) : ℝ)
    have hX : X ≠ 0 := by dsimp [X]; positivity
    have hden : X - 1 - 8 * (d : ℝ) ≠ 0 := by
      have hnat := sixteen_mul_add_one_lt_two_pow hd
      have hr : (16 : ℝ) * d + 1 < X := by
        dsimp [X]
        exact_mod_cast hnat
      nlinarith
    have hsub :
        (X - 1 + 4 * (d : ℝ)) / (X - 1 - 8 * (d : ℝ)) - 1 =
          12 * (d : ℝ) / (X - 1 - 8 * (d : ℝ)) := by
      rw [div_sub_one hden]
      congr 1
      ring
    have hDEq : D d = (X - 1 - 8 * (d : ℝ)) / X := by
      dsimp [D]
      field_simp [hX]
      ring
    rw [hsub, hDEq]
    rw [show 12 * ((d : ℝ) ^ 3 / X) =
      (12 * (d : ℝ) ^ 3) / X by ring]
    rw [div_div_div_cancel_right₀ hX]
    field_simp [hden]
  simpa using hlim.congr' heq

noncomputable def cutoffFactor (d : ℕ) : ℝ :=
  ((((2 ^ d : ℕ) : ℝ) / ((2 ^ d - d ^ 4 : ℕ) : ℝ)) ^ 2)

theorem cutoffFactor_tendsto_one :
    Tendsto cutoffFactor atTop (nhds 1) := by
  have h4 := polynomial_div_two_pow_tendsto_zero 4
  have hden : Tendsto
      (fun d : ℕ => 1 - (d : ℝ) ^ 4 / (((2 ^ d : ℕ) : ℝ)))
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub h4 using 1 <;> ring
  have hone : Tendsto (fun _d : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  let R : ℕ → ℝ := fun d =>
    1 / (1 - (d : ℝ) ^ 4 / (((2 ^ d : ℕ) : ℝ)))
  have hratio : Tendsto R atTop (nhds 1) := by
    unfold R
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hpow := hratio.pow 2
  have heq : (fun d : ℕ => (R d) ^ 2) =ᶠ[atTop]
      cutoffFactor := by
    filter_upwards [cutoff_lt_two_pow_eventually] with d hd
    unfold cutoffFactor
    rw [Nat.cast_sub hd.le]
    dsimp [R]
    simp only [Nat.cast_pow]
    have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
    have hdiff : (2 : ℝ) ^ d - (d : ℝ) ^ 4 ≠ 0 := by
      have hr : (d : ℝ) ^ 4 < (2 : ℝ) ^ d := by
        exact_mod_cast hd
      linarith
    field_simp [h2, hdiff]
  simpa using hpow.congr' heq

noncomputable def cutoffCorrectionNumerator (d : ℕ) : ℝ :=
  2 * ((d : ℝ) ^ 6 / (((2 ^ d : ℕ) : ℝ))) -
    ((d : ℝ) ^ 10 / (((2 ^ d : ℕ) : ℝ))) *
      (1 / (((2 ^ d : ℕ) : ℝ)))

noncomputable def cutoffCorrectionDenominator (d : ℕ) : ℝ :=
  (1 - (d : ℝ) ^ 4 / (((2 ^ d : ℕ) : ℝ))) ^ 2

theorem cutoffCorrectionNumerator_tendsto_zero :
    Tendsto cutoffCorrectionNumerator atTop (nhds 0) := by
  have h0 := polynomial_div_two_pow_tendsto_zero 0
  have h6 := polynomial_div_two_pow_tendsto_zero 6
  have h10 := polynomial_div_two_pow_tendsto_zero 10
  unfold cutoffCorrectionNumerator
  convert (h6.const_mul 2).sub (h10.mul h0) using 1 <;> ring

theorem cutoffCorrectionDenominator_tendsto_one :
    Tendsto cutoffCorrectionDenominator atTop (nhds 1) := by
  have h4 := polynomial_div_two_pow_tendsto_zero 4
  have hone : Tendsto (fun _d : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  unfold cutoffCorrectionDenominator
  convert (hone.sub h4).pow 2 using 1 <;> ring

theorem cutoffFactor_rate_tendsto_zero :
    Tendsto (fun d : ℕ => (d : ℝ) ^ 2 * (cutoffFactor d - 1))
      atTop (nhds 0) := by
  have hquot := cutoffCorrectionNumerator_tendsto_zero.div
    cutoffCorrectionDenominator_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (cutoffCorrectionNumerator / cutoffCorrectionDenominator) =ᶠ[atTop]
      (fun d : ℕ => (d : ℝ) ^ 2 * (cutoffFactor d - 1)) := by
    filter_upwards [cutoff_lt_two_pow_eventually] with d hd
    let X : ℝ := ((2 ^ d : ℕ) : ℝ)
    have hX : X ≠ 0 := by dsimp [X]; positivity
    let y : ℝ := (d : ℝ) ^ 4 / X
    have hden : 1 - y ≠ 0 := by
      have hr : (d : ℝ) ^ 4 < X := by
        dsimp [X]
        exact_mod_cast hd
      have hXpos : 0 < X := by positivity
      rw [sub_ne_zero]
      exact ne_of_gt (by simpa [y] using (div_lt_one hXpos |>.2 hr))
    have hfac : cutoffFactor d = (1 / (1 - y)) ^ 2 := by
      unfold cutoffFactor
      rw [Nat.cast_sub hd.le]
      dsimp [y, X]
      simp only [Nat.cast_pow]
      have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
      have hdiff : (2 : ℝ) ^ d - (d : ℝ) ^ 4 ≠ 0 := by
        have hr : (d : ℝ) ^ 4 < (2 : ℝ) ^ d := by
          exact_mod_cast hd
        linarith
      field_simp [h2, hdiff]
    have hnum : cutoffCorrectionNumerator d =
        (d : ℝ) ^ 2 * (2 * y - y ^ 2) := by
      unfold cutoffCorrectionNumerator
      dsimp [y, X]
      field_simp [hX]
    have hdenEq : cutoffCorrectionDenominator d = (1 - y) ^ 2 := by
      unfold cutoffCorrectionDenominator
      rfl
    change cutoffCorrectionNumerator d / cutoffCorrectionDenominator d =
      (d : ℝ) ^ 2 * (cutoffFactor d - 1)
    rw [hnum, hdenEq, hfac]
    field_simp [hden]
    ring
  simpa using hquot.congr' heq

theorem isolatedSmallLambda_sub_main_tendsto_zero :
    Tendsto (fun d : ℕ =>
      isolatedSmallLambda d (comparisonExcess d) (d ^ 4) -
        (d : ℝ) ^ 2 / 2) atTop (nhds 0) := by
  have hA := comparisonExcess_rate_tendsto_zero.const_mul ((1 : ℝ) / 2)
  have hAR := hA.mul cutoffFactor_tendsto_one
  have hR := cutoffFactor_rate_tendsto_zero.const_mul ((1 : ℝ) / 2)
  have hsum := hAR.add hR
  convert hsum using 1
  · funext d
    unfold isolatedSmallLambda cutoffFactor
    ring
  · ring

theorem isolatedSmallLambda_sub_background_tendsto_zero :
    Tendsto (fun d : ℕ =>
      isolatedSmallLambda d (comparisonExcess d) (d ^ 4) -
        comparisonBackgroundExponent d) atTop (nhds 0) := by
  have h := isolatedSmallLambda_sub_main_tendsto_zero.sub
    comparisonBackgroundExponent_sub_main_tendsto_zero
  convert h using 1 <;> ring

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph

theorem geometric_cubic_mul_exp_quadratic_tendsto_zero
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (C : ℝ) :
    Tendsto (fun d : ℕ => q ^ (d ^ 3) * Real.exp (C * (d : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hd : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hd2 : Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop :=
    by
      convert hd.atTop_mul_atTop₀ hd using 1
      funext d
      ring
  have hlinear : Tendsto
      (fun d : ℕ => (d : ℝ) * Real.log q + C) atTop atBot :=
    tendsto_atBot_add_const_right atTop C
      (hd.atTop_mul_const_of_neg (Real.log_neg hq0 hq1))
  have harg : Tendsto
      (fun d : ℕ => (d : ℝ) ^ 2 * ((d : ℝ) * Real.log q + C))
      atTop atBot := hd2.atTop_mul_atBot₀ hlinear
  have hexp := Real.tendsto_exp_atBot.comp harg
  convert hexp using 1
  funext d
  dsimp only [Function.comp_apply]
  symm
  rw [show (d : ℝ) ^ 2 * ((d : ℝ) * Real.log q + C) =
      ((d ^ 3 : ℕ) : ℝ) * Real.log q + C * (d : ℝ) ^ 2 by
        push_cast
        ring]
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hq0]

theorem cube_le_fourth_div {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    d ^ 3 ≤ d ^ 4 / k := by
  rw [Nat.le_div_iff_mul_le hk]
  calc
    d ^ 3 * k ≤ d ^ 3 * d := Nat.mul_le_mul_left _ hkd
    _ = d ^ 4 := by ring

theorem universalIsolatedLambda_comparison_le_eventually :
    ∀ᶠ d : ℕ in atTop,
      universalIsolatedLambda d (comparisonExcess d) ≤ 81 * (d : ℝ) ^ 2 := by
  filter_upwards [comparisonExcess_le_two_eventually] with d hd
  unfold universalIsolatedLambda
  have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  nlinarith

theorem largeCoreTail_tendsto_zero :
    Tendsto (fun d : ℕ =>
      4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
        Real.exp (universalIsolatedLambda d (comparisonExcess d)))
      atTop (nhds 0) := by
  let g : ℕ → ℝ := fun d =>
    4 * ((2 : ℝ) / 3) ^ (d ^ 3) * Real.exp (81 * (d : ℝ) ^ 2)
  have hg0 : Tendsto g atTop (nhds 0) := by
    have h := (geometric_cubic_mul_exp_quadratic_tendsto_zero
      (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 : ℝ) / 3 < 1) 81).const_mul 4
    convert h using 1
    · funext d
      dsimp [g]
      ring
    · norm_num
  have hlower : ∀ᶠ d : ℕ in atTop,
      0 ≤ 4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
        Real.exp (universalIsolatedLambda d (comparisonExcess d)) :=
    Filter.Eventually.of_forall fun d => by positivity
  have hupper : ∀ᶠ d : ℕ in atTop,
      4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
          Real.exp (universalIsolatedLambda d (comparisonExcess d)) ≤ g d := by
    filter_upwards [eventually_ge_atTop 6,
      universalIsolatedLambda_comparison_le_eventually] with d hd hlam
    dsimp [g]
    have hpow : ((2 : ℝ) / 3) ^ (d ^ 4 / 6) ≤
        ((2 : ℝ) / 3) ^ (d ^ 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (cube_le_fourth_div (by norm_num) hd)
    have hexp : Real.exp (universalIsolatedLambda d (comparisonExcess d)) ≤
        Real.exp (81 * (d : ℝ) ^ 2) := Real.exp_le_exp.mpr hlam
    calc
      4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
          Real.exp (universalIsolatedLambda d (comparisonExcess d)) ≤
        4 * ((2 : ℝ) / 3) ^ (d ^ 3) *
          Real.exp (universalIsolatedLambda d (comparisonExcess d)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Real.exp_pos _).le
      _ ≤ 4 * ((2 : ℝ) / 3) ^ (d ^ 3) *
          Real.exp (81 * (d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hg0 hlower hupper

theorem isolatedTail_tendsto_zero :
    Tendsto (fun d : ℕ =>
      2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
        Real.exp (2 * universalIsolatedLambda d (comparisonExcess d))))
      atTop (nhds 0) := by
  let g : ℕ → ℝ := fun d =>
    2 * (((1 : ℝ) / 2) ^ (d ^ 3) * Real.exp (162 * (d : ℝ) ^ 2))
  have hg0 : Tendsto g atTop (nhds 0) := by
    have h := (geometric_cubic_mul_exp_quadratic_tendsto_zero
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) 162).const_mul 2
    simpa [g] using h
  have hlower : ∀ᶠ d : ℕ in atTop,
      0 ≤ 2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
        Real.exp (2 * universalIsolatedLambda d (comparisonExcess d))) :=
    Filter.Eventually.of_forall fun d => by positivity
  have hupper : ∀ᶠ d : ℕ in atTop,
      2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
          Real.exp (2 * universalIsolatedLambda d (comparisonExcess d))) ≤ g d := by
    filter_upwards [eventually_ge_atTop 4,
      universalIsolatedLambda_comparison_le_eventually] with d hd hlam
    dsimp [g]
    have hpow : ((1 : ℝ) / 2) ^ (d ^ 4 / 4) ≤
        ((1 : ℝ) / 2) ^ (d ^ 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (cube_le_fourth_div (by norm_num) hd)
    have hexp : Real.exp (2 * universalIsolatedLambda d (comparisonExcess d)) ≤
        Real.exp (162 * (d : ℝ) ^ 2) := by
      rw [Real.exp_le_exp]
      linarith
    calc
      2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
          Real.exp (2 * universalIsolatedLambda d (comparisonExcess d))) ≤
        2 * (((1 : ℝ) / 2) ^ (d ^ 3) *
          Real.exp (2 * universalIsolatedLambda d (comparisonExcess d))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (by norm_num)
      _ ≤ 2 * (((1 : ℝ) / 2) ^ (d ^ 3) *
          Real.exp (162 * (d : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (by positivity)) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hg0 hlower hupper

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph Topology

noncomputable def leadingOverlapTerm (d : ℕ) : ℝ :=
  (1 + 4 * coreDecay d) *
    Real.exp (isolatedSmallLambda d (comparisonExcess d) (d ^ 4) -
      comparisonBackgroundExponent d)

noncomputable def momentUpperBound (d : ℕ) : ℝ :=
  4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
      Real.exp (universalIsolatedLambda d (comparisonExcess d)) +
    leadingOverlapTerm d +
    2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
      Real.exp (2 * universalIsolatedLambda d (comparisonExcess d)))

theorem coreDecay_le_quarter_eventually :
    ∀ᶠ d : ℕ in atTop, coreDecay d ≤ 1 / 4 := by
  have h := coreDecay_tendsto_zero
  exact h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))

theorem leadingOverlapTerm_tendsto_one :
    Tendsto leadingOverlapTerm atTop (nhds 1) := by
  have hcore : Tendsto (fun d : ℕ => 1 + 4 * coreDecay d)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.add (coreDecay_tendsto_zero.const_mul 4) using 1 <;>
      ring
  have hexp : Tendsto (fun d : ℕ =>
      Real.exp (isolatedSmallLambda d (comparisonExcess d) (d ^ 4) -
        comparisonBackgroundExponent d)) atTop (nhds 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp
      isolatedSmallLambda_sub_background_tendsto_zero
    convert h using 1
    · funext d
      rfl
    · norm_num
  unfold leadingOverlapTerm
  convert hcore.mul hexp using 1 <;> ring

theorem momentUpperBound_tendsto_one :
    Tendsto momentUpperBound atTop (nhds 1) := by
  have h := largeCoreTail_tendsto_zero.add leadingOverlapTerm_tendsto_one |>.add
    isolatedTail_tendsto_zero
  unfold momentUpperBound
  convert h using 1
  norm_num

theorem comparisonBackgroundExponent_nonneg (d : ℕ) :
    0 ≤ comparisonBackgroundExponent d := by
  unfold comparisonBackgroundExponent
  positivity

theorem backgroundProbability_nonneg (N M e : ℕ) :
    0 ≤ backgroundProbability N M e := by
  unfold backgroundProbability fallingProbability
  positivity

theorem overlapAverage_nonneg {d : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ overlapAverage d c := by
  unfold overlapAverage
  positivity

theorem fixedMomentRatio_le_momentUpperBound_eventually :
    ∀ᶠ d : ℕ in atTop,
      fixedMomentRatio d (comparisonLayer d) ≤ momentUpperBound d := by
  filter_upwards [eventually_ge_atTop 8,
      comparisonExcess_nonneg_eventually,
      comparisonExcess_le_two_eventually,
      cutoff_lt_two_pow_eventually,
      coreDecay_le_quarter_eventually] with d hd ha hc hcut hdecay
  let N := ambientEdgeCount d
  let M := comparisonLayer d
  let e := cubeEdgeCount d
  let a := comparisonExcess d
  let B := comparisonBackgroundExponent d
  have hcond := comparisonLayer_conditions hd
  have he : 0 < e := cubeEdgeCount_pos (by omega)
  have h2eM : 2 * e < M := hcond.1
  have hMN : M ≤ N := hcond.2
  have hratio : fixedMomentRatio d M ≤
      backgroundProbability N M e * overlapAverage d (1 + a) := by
    have h := fixedMomentRatio_le_background_mul_overlapAverage d M he h2eM hMN
    have hcEq :
        ((((2 ^ d).choose 2 - 2 * (d * 2 ^ (d - 1)) : ℕ) : ℝ) /
            (M - 2 * (d * 2 ^ (d - 1)) : ℕ)) = 1 + a := by
      dsimp [a, M, N, e]
      unfold comparisonExcess ambientEdgeCount cubeEdgeCount
      ring
    simpa [N, M, e, hcEq, ambientEdgeCount, cubeEdgeCount] using h
  have hoverlap := overlapAverage_le_three_terms d (d ^ 4)
    (by omega : 1 ≤ d) ha hc hcut hdecay
  have hbg : backgroundProbability N M e ≤ Real.exp (-B) := by
    rw [backgroundProbability_eq_product h2eM.le hMN]
    have h := backgroundProduct_le_exp he h2eM.le hMN
    simpa [N, M, e, B, comparisonBackgroundExponent,
      ambientEdgeCount, cubeEdgeCount] using h
  have hoverlap0 : 0 ≤ overlapAverage d (1 + a) :=
    overlapAverage_nonneg (by linarith)
  have hbg0 : 0 ≤ backgroundProbability N M e :=
    backgroundProbability_nonneg N M e
  have hsum0 : 0 ≤
      (4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6)) *
          Real.exp (universalIsolatedLambda d a) +
        ((1 + 4 * coreDecay d) * Real.exp (isolatedSmallLambda d a (d ^ 4)) +
          2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
            Real.exp (2 * universalIsolatedLambda d a))) := by
    have hcore0 : 0 ≤ 1 + 4 * coreDecay d := by
      unfold coreDecay
      positivity
    positivity
  calc
    fixedMomentRatio d M ≤
        backgroundProbability N M e * overlapAverage d (1 + a) := hratio
    _ ≤ Real.exp (-B) * overlapAverage d (1 + a) :=
      mul_le_mul_of_nonneg_right hbg hoverlap0
    _ ≤ Real.exp (-B) *
        ((4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6)) *
            Real.exp (universalIsolatedLambda d a) +
          ((1 + 4 * coreDecay d) * Real.exp (isolatedSmallLambda d a (d ^ 4)) +
            2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
              Real.exp (2 * universalIsolatedLambda d a)))) :=
      mul_le_mul_of_nonneg_left hoverlap (Real.exp_pos _).le
    _ ≤ momentUpperBound d := by
      have hB : Real.exp (-B) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (comparisonBackgroundExponent_nonneg d)
      have hlarge0 : 0 ≤ 4 * ((2 : ℝ) / 3) ^ (d ^ 4 / 6) *
          Real.exp (universalIsolatedLambda d a) := by positivity
      have hiso0 : 0 ≤ 2 * (((1 : ℝ) / 2) ^ (d ^ 4 / 4) *
          Real.exp (2 * universalIsolatedLambda d a)) := by positivity
      have hlead : Real.exp (-B) *
          ((1 + 4 * coreDecay d) * Real.exp (isolatedSmallLambda d a (d ^ 4))) =
          leadingOverlapTerm d := by
        unfold leadingOverlapTerm
        dsimp [a, B]
        calc
          Real.exp (-comparisonBackgroundExponent d) *
              ((1 + 4 * coreDecay d) *
                Real.exp (isolatedSmallLambda d (comparisonExcess d) (d ^ 4))) =
            (1 + 4 * coreDecay d) *
              (Real.exp (-comparisonBackgroundExponent d) *
                Real.exp (isolatedSmallLambda d (comparisonExcess d) (d ^ 4))) := by ring
          _ = (1 + 4 * coreDecay d) *
              Real.exp (-comparisonBackgroundExponent d +
                isolatedSmallLambda d (comparisonExcess d) (d ^ 4)) := by
            rw [Real.exp_add]
          _ = _ := by congr 2; ring
      dsimp [momentUpperBound]
      rw [mul_add, mul_add, hlead]
      have hlarge := mul_le_of_le_one_left hlarge0 hB
      have hiso := mul_le_of_le_one_left hiso0 hB
      linarith

end Erdos578

namespace Erdos578

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph Topology

theorem comparison_fixedSamples_pos {d : ℕ} (hd : 8 ≤ d) :
    0 < (fixedEdgeSamples d (comparisonLayer d)).card := by
  rw [card_fixedEdgeSamples]
  exact Nat.choose_pos (comparisonLayer_conditions hd).2

theorem comparison_firstMoment_pos {d : ℕ} (hd : 8 ≤ d) :
    0 < ∑ S ∈ fixedEdgeSamples d (comparisonLayer d),
      (copyMultiplicity d S : ℝ) := by
  let N := ambientEdgeCount d
  let M := comparisonLayer d
  let e := cubeEdgeCount d
  have hcond := comparisonLayer_conditions hd
  have heM : e ≤ M := by dsimp [e, M]; omega
  have hMN : M ≤ N := by simpa [M, N] using hcond.2
  have hsub : M - e ≤ N - e := Nat.sub_le_sub_right hMN e
  have hnat := sum_copyMultiplicity d M heM
  have hposNat : 0 < ∑ S ∈ fixedEdgeSamples d M, copyMultiplicity d S := by
    rw [hnat]
    exact Nat.mul_pos Fintype.card_pos (Nat.choose_pos hsub)
  exact_mod_cast hposNat

theorem comparison_secondMoment_pos {d : ℕ} (hd : 8 ≤ d) :
    0 < ∑ S ∈ fixedEdgeSamples d (comparisonLayer d),
      (copyMultiplicity d S : ℝ) ^ 2 := by
  have hfirst := comparison_firstMoment_pos hd
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := fixedEdgeSamples d (comparisonLayer d))
    (f := fun S => (copyMultiplicity d S : ℝ))
  have hsecond0 : 0 ≤ ∑ S ∈ fixedEdgeSamples d (comparisonLayer d),
      (copyMultiplicity d S : ℝ) ^ 2 := by positivity
  have hcard0 : 0 ≤ ((fixedEdgeSamples d (comparisonLayer d)).card : ℝ) :=
    Nat.cast_nonneg _
  nlinarith [sq_pos_of_pos hfirst]

theorem fixedMomentRatio_comparison_tendsto_one :
    Tendsto (fun d : ℕ => fixedMomentRatio d (comparisonLayer d))
      atTop (nhds 1) := by
  have hlower : ∀ᶠ d : ℕ in atTop,
      1 ≤ fixedMomentRatio d (comparisonLayer d) := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    exact one_le_fixedMomentRatio d (comparisonLayer d)
      (comparison_firstMoment_pos hd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds momentUpperBound_tendsto_one hlower
      fixedMomentRatio_le_momentUpperBound_eventually

theorem fixedSuccessProbability_comparison_tendsto_one :
    Tendsto (fun d : ℕ => fixedSuccessProbability d (comparisonLayer d))
      atTop (nhds 1) := by
  have hratio := fixedMomentRatio_comparison_tendsto_one
  have hinv : Tendsto
      (fun d : ℕ => 1 / fixedMomentRatio d (comparisonLayer d))
      atTop (nhds 1) := by
    have h := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [one_div] using h
  have hlower : ∀ᶠ d : ℕ in atTop,
      1 / fixedMomentRatio d (comparisonLayer d) ≤
        fixedSuccessProbability d (comparisonLayer d) := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    exact one_div_fixedMomentRatio_le_fixedSuccessProbability
      d (comparisonLayer d) (comparison_fixedSamples_pos hd)
        (comparison_firstMoment_pos hd) (comparison_secondMoment_pos hd)
  have hupper : ∀ᶠ d : ℕ in atTop,
      fixedSuccessProbability d (comparisonLayer d) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 8] with d hd
    exact fixedSuccessProbability_le_one d (comparisonLayer d)
      (comparison_fixedSamples_pos hd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hinv tendsto_const_nhds hlower hupper

/-- **Erdős Problem 578 (Bollobás--Erdős conjecture, resolved by Riordan).**

For the independent random graph on `2^d` labelled vertices in which every
edge is present with probability `1/2`, the probability of containing the
spanning `d`-dimensional hypercube tends to `1` as `d → ∞`.

Here `successProbability d` is the exact finite probability: the number of
labelled simple graphs on `CubeVertex d` which contain `cubeGraph d`, divided
by the total number `2^(choose (2^d) 2)` of labelled graphs. -/
theorem erdos_578 : Tendsto successProbability atTop (nhds 1) := by
  have honeMinusLow : Tendsto (fun d : ℕ => 1 - lowEdgeProbability d)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub lowEdgeProbability_tendsto_zero using 1 <;>
      ring
  have hlowerLimit := fixedSuccessProbability_comparison_tendsto_one.mul
    honeMinusLow
  have hlower : ∀ᶠ d : ℕ in atTop,
      fixedSuccessProbability d (comparisonLayer d) *
          (1 - lowEdgeProbability d) ≤ successProbability d :=
    Filter.Eventually.of_forall fixed_mul_one_sub_low_le_successProbability
  have hupper : ∀ᶠ d : ℕ in atTop, successProbability d ≤ 1 :=
    Filter.Eventually.of_forall successProbability_le_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlowerLimit) tendsto_const_nhds hlower hupper

#print axioms erdos_578

end Erdos578
