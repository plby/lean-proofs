/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547EC2

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- The number of neighbors of `v` which lie in the finite set `S`. -/
def degreeInto (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) : ℕ :=
  (S.filter fun w ↦ G.Adj v w).card

@[simp] theorem degreeInto_empty (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v ∅ = 0 := by simp [degreeInto]

theorem degreeInto_le_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (S : Finset V) : degreeInto G v S ≤ S.card := by
  exact Finset.card_filter_le _ _

theorem degreeInto_eq_card_interedges_singleton (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (S : Finset V) :
    degreeInto G v S = (G.interedges {v} S).card := by
  classical
  rw [degreeInto, SimpleGraph.interedges_def]
  apply Finset.card_bij (fun w _ ↦ (v, w))
  · intro w hw
    simp only [Finset.mem_filter] at hw
    simp [Rel.mem_interedges_iff, hw]
  · intro a ha b hb hab
    exact congrArg Prod.snd hab
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
    refine ⟨p.2, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hp.1.2, by simpa [hp.1.1] using hp.2⟩
    · apply Prod.ext
      · exact hp.1.1.symm
      · rfl

/-- Counting cross-edges by their first endpoint. -/
theorem sum_degreeInto_eq_card_interedges (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T : Finset V) :
    ∑ v ∈ S, degreeInto G v T = (G.interedges S T).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [degreeInto]
  | @insert v S hv ih =>
      have hd : Disjoint (G.interedges {v} T) (G.interedges S T) :=
        G.interedges_disjoint_left (by simp [hv]) T
      calc
        ∑ x ∈ insert v S, degreeInto G x T
            = degreeInto G v T + ∑ x ∈ S, degreeInto G x T := by simp [hv]
        _ = (G.interedges {v} T).card + (G.interedges S T).card := by
          rw [degreeInto_eq_card_interedges_singleton, ih]
        _ = (G.interedges (insert v S) T).card := by
          rw [← Finset.card_union_of_disjoint hd]
          congr 1
          ext p
          simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_insert]
          aesop

/-- A discrete Markov bound: if every vertex in `B` has at least `k`
neighbors in `T`, then `|B| k` is at most the number of `S`--`T` edges. -/
theorem card_mul_le_card_interedges_of_subset_of_degreeInto
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B S T : Finset V} {k : ℕ} (hBS : B ⊆ S)
    (hdeg : ∀ v ∈ B, k ≤ degreeInto G v T) :
    B.card * k ≤ (G.interedges S T).card := by
  rw [← sum_degreeInto_eq_card_interedges]
  calc
    B.card * k = ∑ _ ∈ B, k := by simp
    _ ≤ ∑ v ∈ B, degreeInto G v T := by
      exact Finset.sum_le_sum fun v hv ↦ hdeg v hv
    _ ≤ ∑ v ∈ S, degreeInto G v T := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hBS (fun _ _ _ ↦ Nat.zero_le _)

/-- The set of vertices in `S` with at least `k` neighbors in `T`. -/
def crossHeavy (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (k : ℕ) : Finset V :=
  S.filter fun v ↦ k ≤ degreeInto G v T

theorem crossHeavy_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (k : ℕ) : crossHeavy G S T k ⊆ S := by
  exact Finset.filter_subset _ _

theorem crossHeavy_card_mul_le_interedges (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T : Finset V) (k : ℕ) :
    (crossHeavy G S T k).card * k ≤ (G.interedges S T).card := by
  apply card_mul_le_card_interedges_of_subset_of_degreeInto G
  · exact crossHeavy_subset G S T k
  · intro v hv
    simpa [crossHeavy] using (Finset.mem_filter.mp hv).2

/-- Rebalance a candidate side `C` to exactly `n` vertices while keeping
the already classified large vertices `L₁` on that side and `L₂` off it.
If `C` was within `b` vertices of size `n`, the correction changes at most
`b` vertices in either direction.  This is the finite-set core of Zhao's
repartitioning step in the proof of Lemma 7.5. -/
theorem exists_balanced_near
    {L₁ L₂ C : Finset V} {n b : ℕ}
    (hV : Fintype.card V = 2 * n)
    (hLcard : L₁.card + L₂.card = n)
    (hL₁C : L₁ ⊆ C) (hCL₂ : Disjoint C L₂)
    (hupper : C.card ≤ n + b) (hlower : n ≤ C.card + b) :
    ∃ W : Finset V,
      W.card = n ∧ L₁ ⊆ W ∧ Disjoint W L₂ ∧
        (C \ W).card ≤ b ∧ (W \ C).card ≤ b := by
  classical
  have hL₁n : L₁.card ≤ n := by omega
  have hCcompl : C ⊆ L₂ᶜ := by
    intro x hx
    simp only [Finset.mem_compl]
    exact fun hx₂ ↦ Finset.disjoint_left.mp hCL₂ hx hx₂
  have hncompl : n ≤ (L₂ᶜ : Finset V).card := by
    rw [Finset.card_compl, hV]
    omega
  rcases le_total C.card n with hCn | hnC
  · obtain ⟨W, hCW, hWcompl, hWcard⟩ :=
      Finset.exists_subsuperset_card_eq hCcompl hCn hncompl
    refine ⟨W, hWcard, hL₁C.trans hCW, ?_, ?_, ?_⟩
    · exact Finset.disjoint_left.mpr fun x hxW hxL₂ ↦
        (Finset.mem_compl.mp (hWcompl hxW)) hxL₂
    · simp [Finset.sdiff_eq_empty_iff_subset.mpr hCW]
    · rw [Finset.card_sdiff_of_subset hCW, hWcard]
      omega
  · obtain ⟨W, hL₁W, hWC, hWcard⟩ :=
      Finset.exists_subsuperset_card_eq hL₁C hL₁n hnC
    refine ⟨W, hWcard, hL₁W, hCL₂.mono_left hWC, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset hWC, hWcard]
      omega
    · simp [Finset.sdiff_eq_empty_iff_subset.mpr hWC]

/-- Deleting at most `b` vertices from a target set can lower the number of
available neighbors by at most `b`. -/
theorem degreeInto_le_add_removed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C W : Finset V) :
    degreeInto G v C ≤ degreeInto G v W + (C \ W).card := by
  classical
  unfold degreeInto
  calc
    (C.filter fun w ↦ G.Adj v w).card
        ≤ ((W.filter fun w ↦ G.Adj v w) ∪ (C \ W)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
          by_cases hxW : x ∈ W
          · exact Or.inl ⟨hxW, hx.2⟩
          · exact Or.inr ⟨hx.1, hxW⟩
    _ ≤ (W.filter fun w ↦ G.Adj v w).card + (C \ W).card :=
      Finset.card_union_le _ _

theorem degreeInto_sub_le_of_removed_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {C W : Finset V} {b : ℕ} (hremoved : (C \ W).card ≤ b) :
    degreeInto G v C - b ≤ degreeInto G v W := by
  have h := degreeInto_le_add_removed G v C W
  omega

theorem degreeInto_union_of_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : Disjoint S T) :
    degreeInto G v S + degreeInto G v T = degreeInto G v (S ∪ T) := by
  classical
  unfold degreeInto
  rw [Finset.filter_union]
  exact (Finset.card_union_of_disjoint
    (hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))).symm

theorem degreeInto_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : Disjoint S T)
    (hcover : S ∪ T = Finset.univ) :
    degreeInto G v S + degreeInto G v T = degreeInto G v Finset.univ := by
  rw [degreeInto_union_of_disjoint G v hST, hcover]

/-- Large vertices classified by the side into which they have more than
`k` neighbors. -/
def classified (G : SimpleGraph V) [DecidableRel G.Adj]
    (L S : Finset V) (k : ℕ) : Finset V :=
  L.filter fun v ↦ k < degreeInto G v S

theorem classified_subset_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (L S : Finset V) (k : ℕ) : classified G L S k ⊆ L :=
  Finset.filter_subset _ _

theorem classified_mem_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    {L S : Finset V} {k : ℕ} {v : V} (hv : v ∈ classified G L S k) :
    k < degreeInto G v S := by
  exact (Finset.mem_filter.mp hv).2

/-- Under the high-total-degree hypothesis and Claim 7.12's conclusion
(no large vertex is cross-heavy into both sides), the two side classes
partition the chosen `n` large vertices. -/
theorem classified_partition_large
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {V₁ V₂ L : Finset V} {n k : ℕ}
    (hdisj : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = Finset.univ)
    (hLcard : L.card = n)
    (hlarge : ∀ v ∈ L, n ≤ degreeInto G v Finset.univ)
    (hk : 2 * k < n)
    (hnoBoth : ∀ v ∈ L,
      ¬(k < degreeInto G v V₁ ∧ k < degreeInto G v V₂)) :
    let L₁ := classified G L V₁ k
    let L₂ := classified G L V₂ k
    Disjoint L₁ L₂ ∧ L₁ ∪ L₂ = L ∧ L₁.card + L₂.card = n := by
  dsimp only
  have hdisjClass :
      Disjoint (classified G L V₁ k) (classified G L V₂ k) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hnoBoth v (classified_subset_left G L V₁ k hv₁)
      ⟨classified_mem_degree G hv₁, classified_mem_degree G hv₂⟩
  have hunion : classified G L V₁ k ∪ classified G L V₂ k = L := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset
        (classified_subset_left G L V₁ k) (classified_subset_left G L V₂ k)
    · intro v hvL
      by_contra hv
      simp only [classified, Finset.mem_union, Finset.mem_filter, hvL, true_and,
        not_or, not_lt] at hv
      have hsum := degreeInto_partition G v hdisj hcover
      have := hlarge v hvL
      omega
  refine ⟨hdisjClass, hunion, ?_⟩
  rw [← Finset.card_union_of_disjoint hdisjClass, hunion, hLcard]

/-- The discrete EC2-to-EC3 core after Claim 7.12 has ruled out a large
vertex which is heavy into both sides.  Here `b` is the bound on the number
of misclassified vertices, and the conclusion loses at most `b` neighbors
when swapping misclassified vertices and another `b` when balancing the
side back to exactly `n` vertices. -/
theorem exists_dense_balanced_side_of_classification
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {V₁ V₂ L₁ L₂ : Finset V} {n k b : ℕ}
    (hV : Fintype.card V = 2 * n)
    (hV₁card : V₁.card = n)
    (hdisjV : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = Finset.univ)
    (hdisjL : Disjoint L₁ L₂) (hLcard : L₁.card + L₂.card = n)
    (hlarge₁ : ∀ v ∈ L₁, n ≤ degreeInto G v Finset.univ)
    (hclass₁ : ∀ v ∈ L₁, k < degreeInto G v V₁)
    (hclass₂ : ∀ v ∈ L₂, k < degreeInto G v V₂)
    (hnot₂ : ∀ v ∈ L₁, degreeInto G v V₂ ≤ k)
    (hcross : (G.interedges V₁ V₂).card < (b + 1) * (k + 1)) :
    ∃ W : Finset V,
      W.card = n ∧ L₁ ⊆ W ∧
        ∀ v ∈ L₁, n - k - 2 * b ≤ degreeInto G v W := by
  classical
  let M₁₂ : Finset V := L₁ ∩ V₂
  let M₂₁ : Finset V := L₂ ∩ V₁
  have hM₁₂V₂ : M₁₂ ⊆ V₂ := Finset.inter_subset_right
  have hM₂₁V₁ : M₂₁ ⊆ V₁ := Finset.inter_subset_right
  have hM₁₂mul : M₁₂.card * (k + 1) ≤ (G.interedges V₂ V₁).card := by
    apply card_mul_le_card_interedges_of_subset_of_degreeInto G hM₁₂V₂
    intro v hv
    have hvL₁ : v ∈ L₁ := Finset.mem_inter.mp hv |>.1
    exact Nat.succ_le_iff.mpr (hclass₁ v hvL₁)
  have hcross' : (G.interedges V₂ V₁).card < (b + 1) * (k + 1) := by
    rw [show (G.interedges V₂ V₁).card = (G.interedges V₁ V₂).card by
      have := G.symm
      exact Rel.card_interedges_comm V₂ V₁]
    exact hcross
  have hM₁₂card : M₁₂.card ≤ b := by
    have hmul : M₁₂.card * (k + 1) < (b + 1) * (k + 1) :=
      lt_of_le_of_lt hM₁₂mul hcross'
    have := Nat.lt_of_mul_lt_mul_right hmul
    omega
  have hM₂₁mul : M₂₁.card * (k + 1) ≤ (G.interedges V₁ V₂).card := by
    apply card_mul_le_card_interedges_of_subset_of_degreeInto G hM₂₁V₁
    intro v hv
    have hvL₂ : v ∈ L₂ := Finset.mem_inter.mp hv |>.1
    exact Nat.succ_le_iff.mpr (hclass₂ v hvL₂)
  have hM₂₁card : M₂₁.card ≤ b := by
    have hmul : M₂₁.card * (k + 1) < (b + 1) * (k + 1) :=
      lt_of_le_of_lt hM₂₁mul hcross
    have := Nat.lt_of_mul_lt_mul_right hmul
    omega
  let C : Finset V := (V₁ \ M₂₁) ∪ M₁₂
  have hparts : Disjoint (V₁ \ M₂₁) M₁₂ :=
    hdisjV.mono Finset.sdiff_subset hM₁₂V₂
  have hCcard : C.card = n - M₂₁.card + M₁₂.card := by
    dsimp only [C]
    rw [Finset.card_union_of_disjoint hparts,
      Finset.card_sdiff_of_subset hM₂₁V₁, hV₁card]
  have hCupper : C.card ≤ n + b := by omega
  have hClower : n ≤ C.card + b := by
    have hM₂₁n : M₂₁.card ≤ n := by
      exact (Finset.card_le_card hM₂₁V₁).trans_eq hV₁card
    omega
  have hL₁C : L₁ ⊆ C := by
    intro v hvL₁
    have hvV : v ∈ V₁ ∪ V₂ := by simpa [hcover]
    rcases Finset.mem_union.mp hvV with hvV₁ | hvV₂
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hvV₁, fun hvM₂₁ ↦
        Finset.disjoint_left.mp hdisjL hvL₁ (Finset.mem_inter.mp hvM₂₁).1⟩
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvL₁, hvV₂⟩)
  have hCL₂ : Disjoint C L₂ := by
    rw [Finset.disjoint_left]
    intro v hvC hvL₂
    rcases Finset.mem_union.mp hvC with hvleft | hvright
    · have hxsd := Finset.mem_sdiff.mp hvleft
      exact hxsd.2 (Finset.mem_inter.mpr ⟨hvL₂, hxsd.1⟩)
    · exact Finset.disjoint_left.mp hdisjL (Finset.mem_inter.mp hvright).1 hvL₂
  obtain ⟨W, hWcard, hL₁W, -, hremoved, -⟩ :=
    exists_balanced_near hV hLcard hL₁C hCL₂ hCupper hClower
  refine ⟨W, hWcard, hL₁W, ?_⟩
  intro v hvL₁
  have hsum := degreeInto_partition G v hdisjV hcover
  have hV₁lower : n - k ≤ degreeInto G v V₁ := by
    have := hlarge₁ v hvL₁
    have := hnot₂ v hvL₁
    omega
  have hV₁diff : V₁ \ C ⊆ M₂₁ := by
    intro x hx
    simp only [C, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
    exact Classical.byContradiction fun hnot ↦ hx.2.1 ⟨hx.1, hnot⟩
  have hV₁removed : (V₁ \ C).card ≤ b :=
    (Finset.card_le_card hV₁diff).trans hM₂₁card
  have hClowerDeg : n - k - b ≤ degreeInto G v C := by
    have h := degreeInto_sub_le_of_removed_le G v hV₁removed
    omega
  have hWlowerDeg := degreeInto_sub_le_of_removed_le G v hremoved
  omega

/-- A precise discrete form of Zhao's EC2-to-EC3 reduction, conditional only
on Claim 7.12's conclusion (`hnoBoth`).  It selects exactly `n` of the large
vertices, classifies them, controls the two misclassified sets by cross-edge
counting, chooses the larger class, and produces an exactly balanced side on
which every vertex of that class has internal degree at least
`n - k - 2*b`. -/
theorem ec2_to_dense_side_of_no_vertex_heavy_both
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {V₁ V₂ L : Finset V} {n k b : ℕ}
    (hV : Fintype.card V = 2 * n)
    (hV₁card : V₁.card = n)
    (hdisjV : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = Finset.univ)
    (hLcard : L.card = n)
    (hlarge : ∀ v ∈ L, n ≤ degreeInto G v Finset.univ)
    (hk : 2 * k < n)
    (hnoBoth : ∀ v ∈ L,
      ¬(k < degreeInto G v V₁ ∧ k < degreeInto G v V₂))
    (hcross : (G.interedges V₁ V₂).card < (b + 1) * (k + 1)) :
    ∃ (A W : Finset V),
      W.card = n ∧ n ≤ 2 * A.card ∧ A ⊆ W ∧
        ∀ v ∈ A, n - k - 2 * b ≤ degreeInto G v W := by
  classical
  let L₁ := classified G L V₁ k
  let L₂ := classified G L V₂ k
  obtain ⟨hdisjL, hunionL, hclasses⟩ :=
    classified_partition_large G hdisjV hcover hLcard hlarge hk hnoBoth
  have hclassSum : L₁.card + L₂.card = n := by
    simpa [L₁, L₂] using hclasses
  have hV₂card : V₂.card = n := by
    have hcards := Finset.card_union_of_disjoint hdisjV
    rw [hcover, Finset.card_univ, hV, hV₁card] at hcards
    omega
  have hcross' : (G.interedges V₂ V₁).card < (b + 1) * (k + 1) := by
    rw [show (G.interedges V₂ V₁).card = (G.interedges V₁ V₂).card by
      have := G.symm
      exact Rel.card_interedges_comm V₂ V₁]
    exact hcross
  have hlarge₁ : ∀ v ∈ L₁, n ≤ degreeInto G v Finset.univ := by
    intro v hv
    exact hlarge v (classified_subset_left G L V₁ k hv)
  have hlarge₂ : ∀ v ∈ L₂, n ≤ degreeInto G v Finset.univ := by
    intro v hv
    exact hlarge v (classified_subset_left G L V₂ k hv)
  have hclass₁ : ∀ v ∈ L₁, k < degreeInto G v V₁ := by
    intro v hv
    exact classified_mem_degree G hv
  have hclass₂ : ∀ v ∈ L₂, k < degreeInto G v V₂ := by
    intro v hv
    exact classified_mem_degree G hv
  have hnot₂ : ∀ v ∈ L₁, degreeInto G v V₂ ≤ k := by
    intro v hv
    apply Nat.le_of_not_gt
    intro hv₂
    exact hnoBoth v (classified_subset_left G L V₁ k hv) ⟨hclass₁ v hv, hv₂⟩
  have hnot₁ : ∀ v ∈ L₂, degreeInto G v V₁ ≤ k := by
    intro v hv
    apply Nat.le_of_not_gt
    intro hv₁
    exact hnoBoth v (classified_subset_left G L V₂ k hv) ⟨hv₁, hclass₂ v hv⟩
  rcases le_total L₁.card L₂.card with h₁₂ | h₂₁
  · obtain ⟨W, hWcard, hL₂W, hdeg⟩ :=
      exists_dense_balanced_side_of_classification G hV hV₂card hdisjV.symm
        (by simpa [Finset.union_comm] using hcover) hdisjL.symm (by omega)
        hlarge₂ hclass₂ hclass₁ hnot₁ hcross'
    refine ⟨L₂, W, hWcard, ?_, hL₂W, hdeg⟩
    omega
  · obtain ⟨W, hWcard, hL₁W, hdeg⟩ :=
      exists_dense_balanced_side_of_classification G hV hV₁card hdisjV hcover
        hdisjL hclassSum hlarge₁ hclass₁ hclass₂ hnot₂ hcross
    refine ⟨L₁, W, hWcard, ?_, hL₁W, hdeg⟩
    omega

end Erdos547EC2

#print axioms Erdos547EC2.ec2_to_dense_side_of_no_vertex_heavy_both

#print axioms Erdos547EC2.ec2_to_dense_side_of_no_vertex_heavy_both

namespace Erdos547EC2

/-! ### Zhao's Proposition 7.11(1)--(2)

These are the unconditional tree-counting inputs used in the few-leaf branch
of Lemma 7.4.  `leafVertices` is Zhao's set of leaves and `branchVertices` is
the set of vertices of degree at least three. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

def leafVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

def branchVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 <= G.degree v

lemma tree_one_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) (v : V) : 1 <= G.degree v := by
  rw [<- hT.minDegree_eq_one_of_nontrivial]
  exact G.minDegree_le_degree v

lemma sum_degree_sub_two_eq_neg_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.IsTree) :
    (∑ v : V, ((G.degree v : Int) - 2)) = -2 := by
  calc
    (∑ v : V, ((G.degree v : Int) - 2)) =
        (∑ v : V, (G.degree v : Int)) - 2 * Fintype.card V := by
      rw [Finset.sum_sub_distrib]
      simp [mul_comm]
    _ = 2 * (G.edgeFinset.card : Int) - 2 * (Fintype.card V : Int) := by
      have hdegZ : (∑ v : V, (G.degree v : Int)) =
          2 * (G.edgeFinset.card : Int) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      rw [hdegZ]
    _ = -2 := by
      have hedge := hT.card_edgeFinset
      omega

lemma sum_degree_sub_two_decomposition
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) :
    (∑ v : V, ((G.degree v : Int) - 2)) =
      - (leafVertices G).card +
        ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
  rw [show (∑ v : V, ((G.degree v : Int) - 2)) =
      ∑ v : V, ((if G.degree v = 1 then (-1 : Int) else 0) +
        if 3 <= G.degree v then (G.degree v : Int) - 2 else 0) by
    apply Finset.sum_congr rfl
    intro v hv
    have hpos := tree_one_le_degree G hT v
    by_cases h1 : G.degree v = 1
    · simp [h1]
    · have htwo : 2 <= G.degree v := by omega
      by_cases h3 : 3 <= G.degree v
      · simp [h1, h3]
      · have heq : G.degree v = 2 := by omega
        simp [h1, h3, heq]]
  rw [Finset.sum_add_distrib]
  simp only [leafVertices, branchVertices, Finset.sum_ite, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp

/-- Zhao Proposition 7.11(1), in its exact degree-excess form. -/
theorem branch_excess_eq_leaf_card_sub_two
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) :
    (∑ v ∈ branchVertices G, ((G.degree v : Int) - 2)) =
      (leafVertices G).card - 2 := by
  have hsum := sum_degree_sub_two_eq_neg_two G hT
  rw [sum_degree_sub_two_decomposition G hT] at hsum
  omega

/-- Zhao Proposition 7.11(1): the number of vertices of degree at least three
is at most the number of leaves minus two. -/
theorem zhao_prop_7_11_part_one
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) :
    (branchVertices G).card <= (leafVertices G).card - 2 := by
  have hterm : ∀ v ∈ branchVertices G,
      (1 : Int) <= (G.degree v : Int) - 2 := by
    intro v hv
    simp only [branchVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    omega
  have hcardZ : ((branchVertices G).card : Int) <=
      ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
    calc
      ((branchVertices G).card : Int) =
          ∑ v ∈ branchVertices G, (1 : Int) := by simp
      _ <= ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
        exact Finset.sum_le_sum fun v hv => hterm v hv
  have hexcess := branch_excess_eq_leaf_card_sub_two G hT
  have hleaves : 2 <= (leafVertices G).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    have hsubset : {u, v} ⊆ leafVertices G := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [leafVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    have := Finset.card_le_card hsubset
    simpa [huv] using this
  rw [hexcess] at hcardZ
  omega

def openNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  S.biUnion fun v => G.neighborFinset v

lemma card_openNeighborFinset_le_sum_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (openNeighborFinset G S).card <= ∑ v ∈ S, G.degree v := by
  simpa [openNeighborFinset] using
    (Finset.card_biUnion_le (s := S) (t := fun v => G.neighborFinset v))

def branchExcess (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Int :=
  if 3 <= G.degree v then (G.degree v : Int) - 2 else 0

lemma branchExcess_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    0 <= branchExcess G v := by
  simp only [branchExcess]
  split_ifs with h <;> omega

lemma sum_branchExcess_eq_sum_branchVertices
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, branchExcess G v) =
      ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
  change (∑ v : V,
      if 3 <= G.degree v then (G.degree v : Int) - 2 else 0) =
    ∑ v ∈ Finset.univ.filter (fun v => 3 <= G.degree v),
      ((G.degree v : Int) - 2)
  rw [Finset.sum_filter]

lemma sum_degree_le_two_mul_card_add_branch_excess
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (∑ v ∈ S, (G.degree v : Int)) <=
      2 * S.card +
        ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
  have hpoint : ∀ v : V, (G.degree v : Int) <=
      2 + branchExcess G v := by
    intro v
    by_cases h : 3 <= G.degree v
    · simp [branchExcess, h]
    · simp [branchExcess, h]
      omega
  calc
    (∑ v ∈ S, (G.degree v : Int)) <=
        ∑ v ∈ S, (2 + branchExcess G v) := by
      exact Finset.sum_le_sum fun v hv => hpoint v
    _ = 2 * S.card +
        ∑ v ∈ S, branchExcess G v := by
      simp [Finset.sum_add_distrib, mul_comm]
    _ <= 2 * S.card +
        ∑ v : V, branchExcess G v := by
      apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        exact Finset.mem_univ v
      · intro v hvS hvuniv
        exact branchExcess_nonneg G v
    _ = 2 * S.card +
        ∑ v ∈ branchVertices G, ((G.degree v : Int) - 2) := by
      rw [sum_branchExcess_eq_sum_branchVertices G]

/-- The subtraction-free form of Zhao Proposition 7.11(2). -/
theorem zhao_prop_7_11_part_two
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) (S : Finset V) :
    (openNeighborFinset G S).card + 2 <=
      2 * S.card + (leafVertices G).card := by
  have hcard := card_openNeighborFinset_le_sum_degree G S
  have hcardZ : ((openNeighborFinset G S).card : Int) <=
      ∑ v ∈ S, (G.degree v : Int) := by
    exact_mod_cast hcard
  have hsum := sum_degree_le_two_mul_card_add_branch_excess G S
  have hexcess := branch_excess_eq_leaf_card_sub_two G hT
  rw [hexcess] at hsum
  exact_mod_cast (show ((openNeighborFinset G S).card : Int) + 2 <=
      2 * (S.card : Int) + (leafVertices G).card by omega)

/-- Zhao Proposition 7.11(2), literally `|N_T(S)| <= 2|S| + ell - 2`. -/
theorem zhao_prop_7_11_part_two_sub
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) (S : Finset V) :
    (openNeighborFinset G S).card <=
      2 * S.card + (leafVertices G).card - 2 := by
  have hmain := zhao_prop_7_11_part_two G hT S
  have hleaves : 2 <= (leafVertices G).card := by
    obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
    have hsubset : {u, v} ⊆ leafVertices G := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [leafVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    have := Finset.card_le_card hsubset
    simpa [huv] using this
  omega

end Erdos547EC2

#print axioms Erdos547EC2.zhao_prop_7_11_part_one
#print axioms Erdos547EC2.zhao_prop_7_11_part_two_sub
