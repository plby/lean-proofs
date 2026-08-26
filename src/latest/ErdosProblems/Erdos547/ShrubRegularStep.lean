import ErdosProblems.Erdos547.PartitionShrubEmbedding
import ErdosProblems.Erdos547.ShrubStateInsert
import ErdosProblems.Erdos547.ShrubReservoirCount

/-!
# One actual shrub insertion with reservation and reservoir accounting
-/

namespace Erdos547.ShrubState

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj] {C : I → Finset V}
  {head : ↥P.shrubs → I} {seed : (T.induce (P.seeds : Set U)).Copy G}

theorem exists_regular_insert (E : ShrubState P G C head seed)
    (S : ↥P.shrubs) (hS : S ∉ E.placed) (j : I)
    (D : ShrubRootData T P.seeds S.val)
    (Q : I → Finset V) (hQ : ∀ i, Q i ⊆ C i)
    (hC : ∀ i k, i ≠ k → Disjoint (C i) (C k))
    (future A B R : Finset V) (hfuture : Disjoint E.occupied future)
    {ε d η : ℝ}
    (hreg : G.IsUniform ε (C (head S)) (C j))
    (hdis : Disjoint (C (head S)) (C j)) (heq : (C (head S)).card = (C j).card)
    (hd : d ≤ (G.edgeDensity (C (head S)) (C j) : ℝ)) (hη : 0 ≤ η)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (hA : A ⊆ C (head S)) (hB : B ⊆ C j) (hR : R ⊆ C (head S))
    (hRA : Disjoint R A)
    (hAsize : η * ((C (head S)).card : ℝ) ≤ A.card)
    (hBsize : η * ((C (head S)).card : ℝ) ≤ B.card)
    (hRsize : 2 * ε * ((C (head S)).card : ℝ) ≤ R.card)
    (hsmall : (S.val.card : ℝ) ≤ ε * (C (head S)).card)
    (v : V) (hvX : v ∈ C (head S)) (hvR : v ∉ R)
    (hroot : 2 * ε * (C (head S)).card ≤ (degreeIn G B v : ℝ))
    (hvbad : v ∉ E.occupied ∪ future)
    (hAbad : Disjoint A (E.occupied ∪ future)) (hBbad : Disjoint B (E.occupied ∪ future))
    (hRbad : Disjoint R (E.occupied ∪ future))
    (hAQ : ∀ i, Disjoint A (Q i)) (hBQ : ∀ i, Disjoint B (Q i))
    (hprimary : G.Adj (seed D.seed) v)
    (hsecondary : ∀ z, D.second = some z → ∀ w ∈ R, G.Adj (seed z.1) w)
    (p : Prop) [Decidable p] (hprimaryQ : v ∈ Q (head S) → p) :
    ∃ E' : ShrubState P G C head seed,
      E'.placed = insert S E.placed ∧ E'.tail = Function.update E.tail S j ∧
      E.occupied ⊆ E'.occupied ∧ Disjoint E'.occupied future ∧
      ∀ i, (Q i ∩ E'.occupied).card ≤ (Q i ∩ E.occupied).card +
        (if head S = i ∧ p then 1 else 0) + (if D.second.isSome then 1 else 0) := by
  classical
  let allQ := Finset.univ.biUnion Q
  have hAall : Disjoint A allQ := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwQ
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwQ
    exact Finset.disjoint_left.mp (hAQ i) hwA hwi
  have hBall : Disjoint B allQ := by
    apply Finset.disjoint_left.mpr
    intro w hwB hwQ
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwQ
    exact Finset.disjoint_left.mp (hBQ i) hwB hwi
  obtain ⟨f, hfroot, hfavoid, hfprimary, hfsecondary, hfnear, hffar, hfQ⟩ :=
    P.exists_partition_shrub_copy S D G seed hreg hdis heq hd hη hde hmargin
      hA hB hR hRA hAsize hBsize hRsize hsmall v hvX hvR hroot hvbad
      hAbad hBbad hRbad hAall hBall hprimary hsecondary
  have hfresh : ∀ u, f u ∉ E.occupied :=
    fun u hu ↦ hfavoid u (Finset.mem_union_left _ hu)
  obtain ⟨E', hplaced, htail, hmono, hused⟩ :=
    E.exists_insert S hS j D f hfresh hfprimary hfsecondary hfnear hffar
  have hfuture' : Disjoint E'.occupied future := by
    rw [hused]
    apply Finset.disjoint_union_left.mpr
    refine ⟨hfuture, Finset.disjoint_left.mpr ?_⟩
    intro w hw hwfuture
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
    exact hfavoid u (Finset.mem_union_right _ hwfuture)
  refine ⟨E', hplaced, htail, hmono, hfuture', ?_⟩
  intro i
  have hqi : Q i ⊆ allQ := fun w hw ↦ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩
  have hp : f D.root ∈ Q i → head S = i ∧ p := by
    intro hv
    rw [hfroot] at hv
    have he : head S = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (hC (head S) i hne) hvX (hQ i hv)
    exact ⟨he, hprimaryQ (he.symm ▸ hv)⟩
  have hcount := card_reservoir_image_le (fun u ↦ f u) D.root (D.second.map Prod.snd)
    (Q i) (head S = i ∧ p) (fun u hu ↦ hfQ u (hqi hu)) hp
  have hsome : (D.second.map Prod.snd).isSome = D.second.isSome := by
    cases D.second <;> rfl
  have hcount' : (Q i ∩ Finset.univ.image f).card ≤
      (if head S = i ∧ p then 1 else 0) + (if D.second.isSome then 1 else 0) := by
    cases hs : D.second <;> simpa only [hs, Option.map_none, Option.map_some,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true] using hcount
  rw [hused]
  have hh := reservoir_count_after_union (Q i) E.occupied (Finset.univ.image f)
    (Q i ∩ E.occupied).card
    ((if head S = i ∧ p then 1 else 0) + (if D.second.isSome then 1 else 0)) le_rfl hcount'
  omega

end Erdos547.ShrubState

#print axioms Erdos547.ShrubState.exists_regular_insert
