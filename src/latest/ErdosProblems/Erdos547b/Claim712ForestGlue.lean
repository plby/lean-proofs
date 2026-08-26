/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Fact72
import ErdosProblems.Erdos547b.Lemma59
import Mathlib.Data.Fintype.EquivFin
import ErdosProblems.Erdos547b.RootFixedPeeling
import ErdosProblems.Erdos547b.Claim712ExternalRoot

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim712

open Finset Fintype SimpleGraph

/-- Images used by two already constructed, vertex-disjoint pieces of a
target tree. -/
def splitCoreImages
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {T : SimpleGraph α} {G : SimpleGraph β}
    (C₁ C₂ : Finset α)
    (f₁ : (T.induce (C₁ : Set α)).Copy G)
    (f₂ : (T.induce (C₂ : Set α)).Copy G) : Finset β :=
  (Finset.univ.image f₁) ∪ (Finset.univ.image f₂)

/-- Unused neighbours of the image of the distinguished attachment root. -/
def rootLeafChoices
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {T : SimpleGraph α} (G : SimpleGraph β) [DecidableRel G.Adj]
    (C₁ C₂ : Finset α)
    (f₁ : (T.induce (C₁ : Set α)).Copy G)
    (f₂ : (T.induce (C₂ : Set α)).Copy G)
    (root : α) (hroot : root ∈ C₂) : Finset β :=
  G.neighborFinset (f₂ ⟨root, hroot⟩) \ splitCoreImages C₁ C₂ f₁ f₂

/-- The cardinality calculation behind the last sentence of Zhao's Claim
7.12.  The two embedded pieces use `|C₁|+|C₂|` vertices.  The image of the
root itself is used but is not its own neighbour, so degree `|T|-1` leaves
at least `|L|` unused neighbours for the deleted root-leaves. -/
theorem card_rootLeafChoices_ge
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (root : α) (C₁ C₂ L : Finset α)
    (hdisj₁₂ : Disjoint C₁ C₂)
    (hdisj₁L : Disjoint C₁ L) (hdisj₂L : Disjoint C₂ L)
    (hcover : (C₁ ∪ C₂) ∪ L = Finset.univ)
    (hroot : root ∈ C₂)
    (H₁ H₂ : Finset β) (hH : Disjoint H₁ H₂)
    (f₁ : (T.induce (C₁ : Set α)).Copy G)
    (f₂ : (T.induce (C₂ : Set α)).Copy G)
    (hf₁ : ∀ x, f₁ x ∈ H₁) (hf₂ : ∀ x, f₂ x ∈ H₂)
    (hdegree : Fintype.card α - 1 ≤ G.degree (f₂ ⟨root, hroot⟩)) :
    L.card ≤ (rootLeafChoices G C₁ C₂ f₁ f₂ root hroot).card := by
  classical
  let U₁ : Finset β := Finset.univ.image f₁
  let U₂ : Finset β := Finset.univ.image f₂
  let U : Finset β := U₁ ∪ U₂
  let p : β := f₂ ⟨root, hroot⟩
  let N : Finset β := G.neighborFinset p
  have hU₁card : U₁.card = C₁.card := by
    rw [show U₁.card = Fintype.card {x // x ∈ C₁} by
      exact Finset.card_image_iff.mpr fun _ _ _ _ h => f₁.injective h]
    exact Fintype.card_coe C₁
  have hU₂card : U₂.card = C₂.card := by
    rw [show U₂.card = Fintype.card {x // x ∈ C₂} by
      exact Finset.card_image_iff.mpr fun _ _ _ _ h => f₂.injective h]
    exact Fintype.card_coe C₂
  have hUdisj : Disjoint U₁ U₂ := by
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hw₁
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hw₂
    have hxH₁ : f₁ x ∈ H₁ := hf₁ x
    have hyH₂ : f₂ y ∈ H₂ := hf₂ y
    rw [hx] at hxH₁
    rw [hy] at hyH₂
    exact Finset.disjoint_left.mp hH hxH₁ hyH₂
  have hUcard : U.card = C₁.card + C₂.card := by
    rw [Finset.card_union_of_disjoint hUdisj, hU₁card, hU₂card]
  have hpU : p ∈ U := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨root, hroot⟩, Finset.mem_univ _, rfl⟩
  have hpN : p ∉ N := by simp [N, p]
  have hproper : N ∩ U ⊂ U := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro heq
    apply hpN
    exact (Finset.mem_inter.mp (heq ▸ hpU)).1
  have hinter : (N ∩ U).card + 1 ≤ U.card := by
    have := Finset.card_lt_card hproper
    omega
  have htargetCard : C₁.card + C₂.card + L.card = Fintype.card α := by
    have hdisjCoreL : Disjoint (C₁ ∪ C₂) L :=
      Finset.disjoint_union_left.mpr ⟨hdisj₁L, hdisj₂L⟩
    rw [← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hdisjCoreL,
      Finset.card_union_of_disjoint hdisj₁₂]
  have hN : Fintype.card α - 1 ≤ N.card := by
    simpa [N, p] using hdegree
  unfold rootLeafChoices
  change L.card ≤ (N \ U).card
  rw [Finset.card_sdiff]
  rw [Finset.inter_comm] at hinter
  omega

/-- Glue the two pieces occurring in Claim 7.12 and restore the components
which are single leaves at the distinguished root.

`C₂` is the selected natural subtree and contains `root`; `C₁` is the union
of the remaining nontrivial rooted components.  `hboundary` is the defining
single-boundary property of a natural subtree: every edge between the two
pieces has its `C₂` endpoint at `root`.  The component roots in `C₁` are
already mapped to neighbours of the root image (`hattach`).  Finally `L`
consists precisely of the omitted one-vertex components at `root`.

The conclusion is a genuine `SimpleGraph.Copy`.  It also records that the
copy agrees with both prescribed piece embeddings and maps the restored
leaves to previously unused neighbours of the root image. -/
theorem exists_copy_of_natural_split_and_root_leaves
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (root : α) (C₁ C₂ L : Finset α)
    (hdisj₁₂ : Disjoint C₁ C₂)
    (hdisj₁L : Disjoint C₁ L) (hdisj₂L : Disjoint C₂ L)
    (hcover : (C₁ ∪ C₂) ∪ L = Finset.univ)
    (hroot : root ∈ C₂)
    (hleafUnique : ∀ x ∈ L, ∀ ⦃y⦄, T.Adj x y → y = root)
    (hboundary : ∀ ⦃x y⦄, x ∈ C₁ → y ∈ C₂ → T.Adj x y → y = root)
    (H₁ H₂ : Finset β) (hH : Disjoint H₁ H₂)
    (f₁ : (T.induce (C₁ : Set α)).Copy G)
    (f₂ : (T.induce (C₂ : Set α)).Copy G)
    (hf₁ : ∀ x, f₁ x ∈ H₁) (hf₂ : ∀ x, f₂ x ∈ H₂)
    (hattach : ∀ x : {x // x ∈ C₁}, T.Adj x root →
      G.Adj (f₁ x) (f₂ ⟨root, hroot⟩))
    (hdegree : Fintype.card α - 1 ≤ G.degree (f₂ ⟨root, hroot⟩)) :
    ∃ f : T.Copy G,
      (∀ x : {x // x ∈ C₁}, f x = f₁ x) ∧
      (∀ x : {x // x ∈ C₂}, f x = f₂ x) ∧
      (∀ x : {x // x ∈ L},
        f x ∈ rootLeafChoices G C₁ C₂ f₁ f₂ root hroot) := by
  classical
  let U : Finset β := splitCoreImages C₁ C₂ f₁ f₂
  let p : β := f₂ ⟨root, hroot⟩
  let A : Finset β := rootLeafChoices G C₁ C₂ f₁ f₂ root hroot
  have hLcard : Fintype.card {x // x ∈ L} ≤ A.card := by
    rw [Fintype.card_coe]
    exact card_rootLeafChoices_ge T G root C₁ C₂ L hdisj₁₂ hdisj₁L hdisj₂L
      hcover hroot H₁ H₂ hH f₁ f₂ hf₁ hf₂ hdegree
  obtain ⟨g, hgA⟩ := Function.Embedding.exists_of_card_le_finset hLcard
  have hrootNotL : root ∉ L := by
    intro hrL
    exact Finset.disjoint_left.mp hdisj₂L hroot hrL
  let F : α → β := fun x =>
    if hx₁ : x ∈ C₁ then f₁ ⟨x, hx₁⟩
    else if hx₂ : x ∈ C₂ then f₂ ⟨x, hx₂⟩
    else g ⟨x, by
      have hxall : x ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
      exact (Finset.mem_union.mp hxall).resolve_left
        (fun hxcore => (Finset.mem_union.mp hxcore).elim hx₁ hx₂)⟩
  have hF₁ (x : {x // x ∈ C₁}) : F x = f₁ x := by
    simp [F, x.property]
  have hF₂ (x : {x // x ∈ C₂}) : F x = f₂ x := by
    have hx₁ : (x : α) ∉ C₁ :=
      fun hx => Finset.disjoint_left.mp hdisj₁₂ hx x.property
    simp [F, hx₁, x.property]
  have hFL (x : {x // x ∈ L}) : F x = g x := by
    have hx₁ : (x : α) ∉ C₁ :=
      fun hx => Finset.disjoint_left.mp hdisj₁L hx x.property
    have hx₂ : (x : α) ∉ C₂ :=
      fun hx => Finset.disjoint_left.mp hdisj₂L hx x.property
    simp [F, hx₁, hx₂]
  have hgFresh (x : {x // x ∈ L}) : g x ∉ U := by
    have hx : g x ∈ A := hgA ⟨x, rfl⟩
    exact (Finset.mem_sdiff.mp hx).2
  have hF_inj : Function.Injective F := by
    intro x y hxy
    by_cases hx₁ : x ∈ C₁
    · by_cases hy₁ : y ∈ C₁
      · have hsub : (⟨x, hx₁⟩ : {x // x ∈ C₁}) = ⟨y, hy₁⟩ := by
          apply f₁.injective
          simpa [F, hx₁, hy₁] using hxy
        exact Subtype.ext_iff.mp hsub
      · by_cases hy₂ : y ∈ C₂
        · have hxH := hf₁ ⟨x, hx₁⟩
          have hyH := hf₂ ⟨y, hy₂⟩
          have heq : f₁ ⟨x, hx₁⟩ = f₂ ⟨y, hy₂⟩ := by
            simpa [F, hx₁, hy₁, hy₂] using hxy
          rw [← heq] at hyH
          exact False.elim (Finset.disjoint_left.mp hH hxH hyH)
        · have hyL : y ∈ L := by
            have hyall : y ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
            exact (Finset.mem_union.mp hyall).resolve_left
              (fun hycore => (Finset.mem_union.mp hycore).elim hy₁ hy₂)
          exfalso
          apply hgFresh ⟨y, hyL⟩
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          exact ⟨⟨x, hx₁⟩, Finset.mem_univ _, by simpa [F, hx₁, hy₁, hy₂] using hxy⟩
    · by_cases hx₂ : x ∈ C₂
      · by_cases hy₁ : y ∈ C₁
        · have hxH := hf₂ ⟨x, hx₂⟩
          have hyH := hf₁ ⟨y, hy₁⟩
          have heq : f₂ ⟨x, hx₂⟩ = f₁ ⟨y, hy₁⟩ := by
            simpa [F, hx₁, hx₂, hy₁] using hxy
          rw [heq] at hxH
          exact False.elim (Finset.disjoint_left.mp hH hyH hxH)
        · by_cases hy₂ : y ∈ C₂
          · have hsub : (⟨x, hx₂⟩ : {x // x ∈ C₂}) = ⟨y, hy₂⟩ := by
              apply f₂.injective
              simpa [F, hx₁, hx₂, hy₁, hy₂] using hxy
            exact Subtype.ext_iff.mp hsub
          · have hyL : y ∈ L := by
              have hyall : y ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
              exact (Finset.mem_union.mp hyall).resolve_left
                (fun hycore => (Finset.mem_union.mp hycore).elim hy₁ hy₂)
            exfalso
            apply hgFresh ⟨y, hyL⟩
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨⟨x, hx₂⟩, Finset.mem_univ _, by
              simpa [F, hx₁, hx₂, hy₁, hy₂] using hxy⟩
      · have hxL : x ∈ L := by
          have hxall : x ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
          exact (Finset.mem_union.mp hxall).resolve_left
            (fun hxcore => (Finset.mem_union.mp hxcore).elim hx₁ hx₂)
        by_cases hy₁ : y ∈ C₁
        · exfalso
          apply hgFresh ⟨x, hxL⟩
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          exact ⟨⟨y, hy₁⟩, Finset.mem_univ _, by
            simpa [F, hx₁, hx₂, hy₁] using hxy.symm⟩
        · by_cases hy₂ : y ∈ C₂
          · exfalso
            apply hgFresh ⟨x, hxL⟩
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨⟨y, hy₂⟩, Finset.mem_univ _, by
              simpa [F, hx₁, hx₂, hy₁, hy₂] using hxy.symm⟩
          · have hyL : y ∈ L := by
              have hyall : y ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
              exact (Finset.mem_union.mp hyall).resolve_left
                (fun hycore => (Finset.mem_union.mp hycore).elim hy₁ hy₂)
            have hsub : (⟨x, hxL⟩ : {x // x ∈ L}) = ⟨y, hyL⟩ := by
              apply g.injective
              simpa [F, hx₁, hx₂, hy₁, hy₂] using hxy
            exact Subtype.ext_iff.mp hsub
  have hF_adj : ∀ ⦃x y⦄, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hxL : x ∈ L
    · have hyr : y = root := hleafUnique x hxL hxy
      subst y
      have hg : g ⟨x, hxL⟩ ∈ A := hgA ⟨⟨x, hxL⟩, rfl⟩
      have hadj : G.Adj p (g ⟨x, hxL⟩) :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hg).1
      have hx₁ : x ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁L h hxL
      have hx₂ : x ∉ C₂ := fun h => Finset.disjoint_left.mp hdisj₂L h hxL
      have hr₁ : root ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hroot
      simpa [F, p, hx₁, hx₂, hr₁, hroot] using hadj.symm
    · by_cases hyL : y ∈ L
      · have hxr : x = root := hleafUnique y hyL hxy.symm
        subst x
        have hg : g ⟨y, hyL⟩ ∈ A := hgA ⟨⟨y, hyL⟩, rfl⟩
        have hadj : G.Adj p (g ⟨y, hyL⟩) :=
          (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hg).1
        have hy₁ : y ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁L h hyL
        have hy₂ : y ∉ C₂ := fun h => Finset.disjoint_left.mp hdisj₂L h hyL
        have hr₁ : root ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hroot
        simpa [F, p, hy₁, hy₂, hr₁, hroot] using hadj
      · have hxcore : x ∈ C₁ ∪ C₂ := by
          have hxall : x ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
          exact (Finset.mem_union.mp hxall).resolve_right hxL
        have hycore : y ∈ C₁ ∪ C₂ := by
          have hyall : y ∈ (C₁ ∪ C₂) ∪ L := by simpa [hcover]
          exact (Finset.mem_union.mp hyall).resolve_right hyL
        rcases Finset.mem_union.mp hxcore with hx₁ | hx₂ <;>
          rcases Finset.mem_union.mp hycore with hy₁ | hy₂
        · have hm := f₁.toHom.map_rel
            (show (T.induce (C₁ : Set α)).Adj ⟨x, hx₁⟩ ⟨y, hy₁⟩ by simpa using hxy)
          simpa [F, hx₁, hy₁] using hm
        · have hyr : y = root := hboundary hx₁ hy₂ hxy
          subst y
          have hadj := hattach ⟨x, hx₁⟩ hxy
          have hr₁ : root ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hroot
          simpa [F, hx₁, hr₁, hroot] using hadj
        · have hxr : x = root := hboundary hy₁ hx₂ hxy.symm
          subst x
          have hadj := hattach ⟨y, hy₁⟩ hxy.symm
          have hr₁ : root ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hroot
          simpa [F, hy₁, hr₁, hroot] using hadj.symm
        · have hm := f₂.toHom.map_rel
            (show (T.induce (C₂ : Set α)).Adj ⟨x, hx₂⟩ ⟨y, hy₂⟩ by simpa using hxy)
          have hx₁ : x ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hx₂
          have hy₁ : y ∉ C₁ := fun h => Finset.disjoint_left.mp hdisj₁₂ h hy₂
          simpa [F, hx₁, hx₂, hy₁, hy₂] using hm
  let f : T.Copy G := ⟨⟨F, fun {_ _} h => hF_adj h⟩, hF_inj⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    simpa [f] using hF₁ x
  · intro x
    simpa [f] using hF₂ x
  · intro x
    have hx : g x ∈ A := hgA ⟨x, rfl⟩
    simpa [f, hFL x] using hx

/-! ## Claim 7.12-shaped construction of the two core copies -/

/-- The two host sets used for one semibipartite embedding. -/
def twoParts {β : Type*} (A B : Finset β) (i : Fin 2) : Finset β :=
  if i = 0 then A else B

@[simp] theorem twoParts_zero {β : Type*} (A B : Finset β) :
    twoParts A B 0 = A := by simp [twoParts]

@[simp] theorem twoParts_one {β : Type*} (A B : Finset β) :
    twoParts A B 1 = B := by simp [twoParts]

theorem twoParts_pairwiseDisjoint {β : Type*} [DecidableEq β]
    {A B : Finset β} (hAB : Disjoint A B) :
    Set.PairwiseDisjoint Set.univ (twoParts A B) := by
  intro i _ j _ hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change Disjoint A B
    exact hAB
  · change Disjoint B A
    exact hAB.symm
  · exact (hij rfl).elim

private theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- Embed a rooted forest so that every component root is adjacent to one
prescribed host vertex.  This is the source-shaped use of the artificial
root in Zhao's Claim 7.12: adjoining a cone vertex to the forest makes a
tree, and the root-preserving candidate lemma sends that cone vertex to
`rootImage`.

The single integer `q` exposes the two estimates used in this coarse auxiliary.  It is
at least the order of the cone, every component root has at least `q`
candidate neighbours of `rootImage`, and every oriented forest edge has at
least `q` candidates at its far endpoint. -/
theorem exists_forest_copy_attached_at
    {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ] [DecidableEq β]
    (F : SimpleGraph γ) (G : SimpleGraph β) [DecidableRel G.Adj]
    (roots : Finset γ)
    (hforest : (Erdos547b.ZhaoLemma59.rootedForestCone F roots).IsTree)
    (candidate : γ → Finset β) (rootImage : β) (q : ℕ)
    (horder : Fintype.card γ + 1 ≤ q)
    (hroot : ∀ x ∈ roots,
      q ≤ #{w ∈ candidate x | G.Adj rootImage w})
    (hcross : ∀ ⦃x y⦄, F.Adj x y → ∀ v ∈ candidate x,
      q ≤ #{w ∈ candidate y | G.Adj v w}) :
    ∃ f : F.Copy G,
      (∀ x, f x ∈ candidate x) ∧
      (∀ x ∈ roots, G.Adj rootImage (f x)) := by
  classical
  let cone := Erdos547b.ZhaoLemma59.rootedForestCone F roots
  let coneCandidate : Option γ → Finset β
    | none => ∅
    | some x => candidate x
  have hconeCard : Fintype.card (Option γ) = Fintype.card γ + 1 := by simp
  obtain ⟨fc, hfcRoot, hfcMem⟩ :=
    Erdos547b.ZhaoLemma59.exists_rooted_candidate_copy cone G hforest none
      coneCandidate rootImage (by
        intro a ha
        cases a with
        | none => simp [cone, Erdos547b.ZhaoLemma59.rootedForestCone] at ha
        | some x =>
            have hxRoot : x ∈ roots := by
              simpa [cone, Erdos547b.ZhaoLemma59.rootedForestCone] using ha
            rw [hconeCard]
            simpa [coneCandidate] using horder.trans (hroot x hxRoot)) (by
        intro a b hab hb v hv
        cases a with
        | none => simp [coneCandidate] at hv
        | some x =>
            cases b with
            | none => exact False.elim (hb rfl)
            | some y =>
                have hxy : F.Adj x y := by
                  simpa [cone, Erdos547b.ZhaoLemma59.rootedForestCone] using hab
                rw [hconeCard]
                simpa [coneCandidate] using horder.trans (hcross hxy v hv))
  let fMap : γ → β := fun x => fc (some x)
  have hfMapInj : Function.Injective fMap := by
    intro x y hxy
    exact Option.some.inj (fc.injective hxy)
  have hfMapAdj : ∀ ⦃x y⦄, F.Adj x y → G.Adj (fMap x) (fMap y) := by
    intro x y hxy
    exact fc.toHom.map_rel (by
      simpa [cone, Erdos547b.ZhaoLemma59.rootedForestCone] using hxy)
  let f : F.Copy G := ⟨⟨fMap, fun {_ _} h => hfMapAdj h⟩, hfMapInj⟩
  refine ⟨f, ?_, ?_⟩
  · intro x
    have := hfcMem (some x) (by simp)
    simpa [f, fMap, coneCandidate] using this
  · intro x hx
    have hconeAdj : cone.Adj none (some x) := by
      simpa [cone, Erdos547b.ZhaoLemma59.rootedForestCone] using hx
    have hm := fc.toHom.map_rel hconeAdj
    change G.Adj (fc none) (fc (some x)) at hm
    rw [hfcRoot] at hm
    simpa [f, fMap] using hm

/-- A coarse cone-order variant of the middle embedding step of Zhao's Claim 7.12.

`C₂` is the natural subtree containing `root`; `C₁` is the complementary
forest after its one-vertex components have been put aside.  The four host
regions are the source's `A₁,B₁,A₂,B₂`.  The first piece is embedded through
the cone construction, which forces all component roots to be adjacent to
`v₀`.  The second piece is embedded by Fact 7.2's prescribed-root
semibipartite lemma and sends `root` exactly to `v₀`.

The hypotheses headed by `q` are the exact discrete three-way minimum-degree
bounds: the `(0,0)`, `(0,1)`, and `(1,0)` directions are required, while the
independent second side never requires `(1,1)`. -/
theorem exists_claim712_piece_copies
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (root : α) (C₁ C₂ : Finset α) (hroot : root ∈ C₂)
    (roots₁ : Finset {x // x ∈ C₁})
    (hforest₁ :
      (Erdos547b.ZhaoLemma59.rootedForestCone
        (T.induce (C₁ : Set α)) roots₁).IsTree)
    (hboundaryRoots : ∀ x : {x // x ∈ C₁}, T.Adj x root → x ∈ roots₁)
    (side₁ : {x // x ∈ C₁} → Fin 2)
    (hTree₂ : (T.induce (C₂ : Set α)).IsTree)
    (side₂ : {x // x ∈ C₂} → Fin 2)
    (hindep₂ : ∀ ⦃x y⦄, (T.induce (C₂ : Set α)).Adj x y →
      side₂ x = 1 → side₂ y ≠ 1)
    (A₁ B₁ A₂ B₂ : Finset β)
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hhost12 : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (v₀ : β) (q : ℕ)
    (horder₁ : Fintype.card {x // x ∈ C₁} + 1 ≤ q)
    (hrootNbr₁ : ∀ x ∈ roots₁,
      q ≤ #{w ∈ twoParts A₁ B₁ (side₁ x) | G.Adj v₀ w})
    (hcross₁ : ∀ ⦃x y⦄, (T.induce (C₁ : Set α)).Adj x y →
      ∀ v ∈ twoParts A₁ B₁ (side₁ x),
        q ≤ #{w ∈ twoParts A₁ B₁ (side₁ y) | G.Adj v w})
    (hpartCard₂ : ∀ i, Erdos547b.ZhaoFact72.partCount side₂ i ≤ q)
    (hdegree₂ : ∀ i j, ¬(i = 1 ∧ j = 1) →
      ∀ v ∈ twoParts A₂ B₂ i,
        q ≤ #((G.neighborFinset v) ∩ twoParts A₂ B₂ j))
    (hv₀ : v₀ ∈ twoParts A₂ B₂ (side₂ ⟨root, hroot⟩)) :
    ∃ (f₁ : (T.induce (C₁ : Set α)).Copy G)
      (f₂ : (T.induce (C₂ : Set α)).Copy G),
      (∀ x, f₁ x ∈ A₁ ∪ B₁) ∧
      (∀ x, f₂ x ∈ A₂ ∪ B₂) ∧
      f₂ ⟨root, hroot⟩ = v₀ ∧
      (∀ x : {x // x ∈ C₁}, T.Adj x root →
        G.Adj (f₁ x) (f₂ ⟨root, hroot⟩)) := by
  classical
  let candidate₁ : {x // x ∈ C₁} → Finset β := fun x =>
    twoParts A₁ B₁ (side₁ x)
  obtain ⟨f₁, hf₁mem, hf₁root⟩ :=
    exists_forest_copy_attached_at (T.induce (C₁ : Set α)) G roots₁
      hforest₁ candidate₁ v₀ q horder₁ (by
        intro x hx
        simpa [candidate₁] using hrootNbr₁ x hx) (by
        intro x y hxy v hv
        simpa [candidate₁] using hcross₁ hxy v hv)
  have hparts₂ : Set.PairwiseDisjoint Set.univ (twoParts A₂ B₂) :=
    twoParts_pairwiseDisjoint hAB₂
  have hdeg₂ : ∀ i j, ¬(i = 1 ∧ j = 1) →
      ∀ v ∈ twoParts A₂ B₂ i,
        Erdos547b.ZhaoFact72.partCount side₂ j ≤
          #((G.neighborFinset v) ∩ twoParts A₂ B₂ j) := by
    intro i j hij v hv
    exact (hpartCard₂ j).trans (hdegree₂ i j hij v hv)
  obtain ⟨f₂, hf₂root, hf₂mem⟩ :=
    Erdos547b.ZhaoFact72.exists_rooted_semibipartite_copy
      (T.induce (C₂ : Set α)) G hTree₂ side₂ hindep₂
      (twoParts A₂ B₂) hparts₂ hdeg₂ ⟨root, hroot⟩ v₀ hv₀
  refine ⟨f₁, f₂, ?_, ?_, hf₂root, ?_⟩
  · intro x
    have hx := hf₁mem x
    rcases fin2_eq_zero_or_one (side₁ x) with hside | hside
    · exact Finset.mem_union_left _ (by simpa [candidate₁, hside] using hx)
    · exact Finset.mem_union_right _ (by simpa [candidate₁, hside] using hx)
  · intro x
    have hx := hf₂mem x
    rcases fin2_eq_zero_or_one (side₂ x) with hside | hside
    · exact Finset.mem_union_left _ (by simpa [hside] using hx)
    · exact Finset.mem_union_right _ (by simpa [hside] using hx)
  · intro x hx
    have h := hf₁root x (hboundaryRoots x hx)
    rw [hf₂root]
    exact h.symm

/-- Completion corresponding to the preceding coarse cone-order variant.  The target
tree is split into the complementary nontrivial forest `C₁`, the natural
subtree `C₂`, and the discarded one-vertex components `L`.  The preceding
theorem embeds the first two pieces in the disjoint host regions
`A₁ ∪ B₁` and `A₂ ∪ B₂`; `exists_copy_of_natural_split_and_root_leaves`
then restores `L` using only the heavy total degree of `v₀`.

This theorem deliberately concludes with the actual copy rather than only
containment, so it can be reused by the surrounding EC2 argument. -/
theorem exists_claim712_full_copy
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree)
    (root : α) (C₁ C₂ L : Finset α)
    (hdisj₁₂ : Disjoint C₁ C₂)
    (hdisj₁L : Disjoint C₁ L) (hdisj₂L : Disjoint C₂ L)
    (hcover : (C₁ ∪ C₂) ∪ L = Finset.univ)
    (hroot : root ∈ C₂)
    (hleafUnique : ∀ x ∈ L, ∀ ⦃y⦄, T.Adj x y → y = root)
    (hboundary : ∀ ⦃x y⦄, x ∈ C₁ → y ∈ C₂ → T.Adj x y → y = root)
    (roots₁ : Finset {x // x ∈ C₁})
    (hforest₁ :
      (Erdos547b.ZhaoLemma59.rootedForestCone
        (T.induce (C₁ : Set α)) roots₁).IsTree)
    (hboundaryRoots : ∀ x : {x // x ∈ C₁}, T.Adj x root → x ∈ roots₁)
    (side₁ : {x // x ∈ C₁} → Fin 2)
    (hconnected₂ : (T.induce (C₂ : Set α)).Connected)
    (side₂ : {x // x ∈ C₂} → Fin 2)
    (hindep₂ : ∀ ⦃x y⦄, (T.induce (C₂ : Set α)).Adj x y →
      side₂ x = 1 → side₂ y ≠ 1)
    (A₁ B₁ A₂ B₂ : Finset β)
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hhost12 : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (v₀ : β) (q : ℕ)
    (horder₁ : Fintype.card {x // x ∈ C₁} + 1 ≤ q)
    (hrootNbr₁ : ∀ x ∈ roots₁,
      q ≤ #{w ∈ twoParts A₁ B₁ (side₁ x) | G.Adj v₀ w})
    (hcross₁ : ∀ ⦃x y⦄, (T.induce (C₁ : Set α)).Adj x y →
      ∀ v ∈ twoParts A₁ B₁ (side₁ x),
        q ≤ #{w ∈ twoParts A₁ B₁ (side₁ y) | G.Adj v w})
    (hpartCard₂ : ∀ i, Erdos547b.ZhaoFact72.partCount side₂ i ≤ q)
    (hdegree₂ : ∀ i j, ¬(i = 1 ∧ j = 1) →
      ∀ v ∈ twoParts A₂ B₂ i,
        q ≤ #((G.neighborFinset v) ∩ twoParts A₂ B₂ j))
    (hv₀ : v₀ ∈ twoParts A₂ B₂ (side₂ ⟨root, hroot⟩))
    (hheavy : Fintype.card α - 1 ≤ G.degree v₀) :
    Nonempty (T.Copy G) := by
  have hTree₂ : (T.induce (C₂ : Set α)).IsTree :=
    ⟨hconnected₂, hT.isAcyclic.induce (C₂ : Set α)⟩
  obtain ⟨f₁, f₂, hf₁, hf₂, hf₂root, hattach⟩ :=
    exists_claim712_piece_copies T G root C₁ C₂ hroot roots₁ hforest₁
      hboundaryRoots side₁ hTree₂ side₂ hindep₂ A₁ B₁ A₂ B₂
      hAB₁ hAB₂ hhost12 v₀ q horder₁ hrootNbr₁ hcross₁ hpartCard₂
      hdegree₂ hv₀
  have hrootDegree : Fintype.card α - 1 ≤ G.degree (f₂ ⟨root, hroot⟩) := by
    rw [hf₂root]
    exact hheavy
  obtain ⟨f, -, -, -⟩ :=
    exists_copy_of_natural_split_and_root_leaves T G root C₁ C₂ L
      hdisj₁₂ hdisj₁L hdisj₂L hcover hroot hleafUnique hboundary
      (A₁ ∪ B₁) (A₂ ∪ B₂) hhost12 f₁ f₂ hf₁ hf₂ hattach hrootDegree
  exact ⟨f⟩

/-! ## Class-sharp, external-root form used by Zhao's Claim 7.12 -/

/-- Reserve distinct images of the roots of all complementary-forest
components using only the *total* supply of neighbours of `v₀` in
`A₁ ∪ B₁`.  The later choice of component orientation records, for each
reserved image, whether it lies in `A₁` or `B₁`. -/
theorem exists_injective_root_images_in_neighborhood
    {γ β : Type*} [Fintype γ] [Fintype β]
    [DecidableEq γ] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (roots : Finset γ) (v₀ : β) (A₁ B₁ : Finset β)
    (hcard : roots.card ≤
      ((G.neighborFinset v₀) ∩ (A₁ ∪ B₁)).card) :
    ∃ e : {x // x ∈ roots} ↪ β,
      ∀ x, G.Adj v₀ (e x) ∧ e x ∈ A₁ ∪ B₁ := by
  classical
  have hcard' : Fintype.card {x // x ∈ roots} ≤
      ((G.neighborFinset v₀) ∩ (A₁ ∪ B₁)).card := by
    simpa only [Fintype.card_coe] using hcard
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hcard'
  refine ⟨e, fun x => ?_⟩
  have hx := he ⟨x, rfl⟩
  exact ⟨by simpa using (Finset.mem_inter.mp hx).1,
    (Finset.mem_inter.mp hx).2⟩

/-- The nontrivial permutation of the two colour classes. -/
def flipTwo (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem flipTwo_zero : flipTwo 0 = 1 := by simp [flipTwo]

@[simp] theorem flipTwo_one : flipTwo 1 = 0 := by simp [flipTwo]

theorem flipTwo_injective : Function.Injective flipTwo := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

theorem flipTwo_ne_of_ne {i j : Fin 2} (hij : i ≠ j) :
    flipTwo i ≠ flipTwo j := by
  exact fun h => hij (flipTwo_injective h)

/-- Orient every connected component of a bipartite forest independently.
`componentRoot x` names the component containing `x`; `rootVertex` realizes
that name as its distinguished target root.  The component is flipped
exactly when needed to give its root the prescribed `rootSide`.

The only structural fact used here is that adjacent vertices have the same
component name. -/
def orientComponents
    {γ ρ : Type*} {F : SimpleGraph γ}
    (c : F.Coloring (Fin 2))
    (componentRoot : γ → ρ) (rootVertex : ρ → γ)
    (rootSide : ρ → Fin 2)
    (hadjRoot : ∀ ⦃x y⦄, F.Adj x y → componentRoot x = componentRoot y) :
    F.Coloring (Fin 2) where
  toFun x := if rootSide (componentRoot x) = c (rootVertex (componentRoot x))
    then c x else flipTwo (c x)
  map_rel' := by
    intro x y hxy
    have hcy : c x ≠ c y := c.valid hxy
    have hr := hadjRoot hxy
    rw [hr]
    by_cases hsame : rootSide (componentRoot y) = c (rootVertex (componentRoot y))
    · simpa [hsame] using hcy
    · simpa [hsame] using flipTwo_ne_of_ne hcy

/-- The independently oriented colouring has the requested colour at every
distinguished root. -/
theorem orientComponents_root
    {γ ρ : Type*} {F : SimpleGraph γ}
    (c : F.Coloring (Fin 2))
    (componentRoot : γ → ρ) (rootVertex : ρ → γ)
    (rootSide : ρ → Fin 2)
    (hadjRoot : ∀ ⦃x y⦄, F.Adj x y → componentRoot x = componentRoot y)
    (hroot : ∀ r, componentRoot (rootVertex r) = r) (r : ρ) :
    orientComponents c componentRoot rootVertex rootSide hadjRoot (rootVertex r) =
      rootSide r := by
  change (if rootSide (componentRoot (rootVertex r)) =
      c (rootVertex (componentRoot (rootVertex r)))
    then c (rootVertex r) else flipTwo (c (rootVertex r))) = rootSide r
  rw [hroot r]
  by_cases hsame : rootSide r = c (rootVertex r)
  · simpa [orientComponents, hsame] using hsame.symm
  · have hne : c (rootVertex r) ≠ rootSide r := Ne.symm hsame
    rcases fin2_eq_zero_or_one (c (rootVertex r)) with hc | hc <;>
      rcases fin2_eq_zero_or_one (rootSide r) with hs | hs <;>
      simp_all [orientComponents, flipTwo]

/-- Choose the host side containing a reserved root image.  Disjointness is
not needed for existence; if an image lies in both sides, side zero is used. -/
def rootImageSide {ρ β : Type*} [DecidableEq β]
    (A₁ : Finset β) (rootImage : ρ → β) (r : ρ) : Fin 2 :=
  if rootImage r ∈ A₁ then 0 else 1

/-- A reserved image from `A₁ ∪ B₁` lies in the side selected by
`rootImageSide`. -/
theorem rootImage_mem_selected_side
    {ρ β : Type*} [DecidableEq β]
    (A₁ B₁ : Finset β) (rootImage : ρ → β)
    (hmem : ∀ r, rootImage r ∈ A₁ ∪ B₁) (r : ρ) :
    rootImage r ∈ twoParts A₁ B₁ (rootImageSide A₁ rootImage r) := by
  by_cases hA : rootImage r ∈ A₁
  · simpa [rootImageSide, hA] using hA
  · have hB : rootImage r ∈ B₁ :=
      (Finset.mem_union.mp (hmem r)).resolve_left hA
    simpa [rootImageSide, hA] using hB

/-- The source-faithful middle embedding step of Zhao's Claim 7.12.

The complementary forest is embedded with a prescribed image for every
component root.  Its capacity and minimum-degree assumptions are sharp in
the two colour-class cardinalities; there is no hypothesis bounding the
total forest order by one class size.  The selected natural subtree is
embedded with its root sent to the external vertex `v₀`; all of its other
vertices lie in `A₂ ∪ B₂`, so `v₀` need not belong to either set. -/
theorem exists_claim712_piece_copies_sharp
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (root : α) (C₁ C₂ : Finset α) (hroot : root ∈ C₂)
    (roots₁ : Finset {x // x ∈ C₁})
    (hrootIndependent₁ :
      (T.induce (C₁ : Set α)).IsIndepSet (roots₁ : Set {x // x ∈ C₁}))
    (hpeel₁ : Erdos547b.RootFixedPeeling.HasRootedLeafPeeling
      (T.induce (C₁ : Set α)) roots₁)
    (hboundaryRoots : ∀ x : {x // x ∈ C₁},
      T.Adj x root → x ∈ roots₁)
    (side₁ : (T.induce (C₁ : Set α)).Coloring (Fin 2))
    (hTree₂ : (T.induce (C₂ : Set α)).IsTree)
    (A₁ B₁ A₂ B₂ : Finset β)
    (hAB₁ : Disjoint A₁ B₁)
    (v₀ : β)
    (rootImage₁ : {x // x ∈ roots₁} → β)
    (hrootImageInj₁ : Function.Injective rootImage₁)
    (hrootImageAdj₁ : ∀ x : {x // x ∈ roots₁}, G.Adj v₀ (rootImage₁ x))
    (hrootImageMem₁ : ∀ x : {x // x ∈ roots₁},
      rootImage₁ x ∈ twoParts A₁ B₁ (side₁ x))
    (hcap₁ : ∀ i, Coloring.partCard side₁ i ≤
      (twoParts A₁ B₁ i).card)
    (hdegree₁ : ∀ i j, i ≠ j → ∀ v ∈ twoParts A₁ B₁ i,
      Coloring.partCard side₁ j ≤
        ((G.neighborFinset v) ∩ twoParts A₁ B₁ j).card)
    (hrootDegree₂ : Fintype.card {x // x ∈ C₂} ≤
      ((G.neighborFinset v₀) ∩ (A₂ ∪ B₂)).card)
    (hminDegree₂ : ∀ v ∈ A₂ ∪ B₂,
      Fintype.card {x // x ∈ C₂} ≤
        ((G.neighborFinset v) ∩ (A₂ ∪ B₂)).card) :
    ∃ f₁ : (T.induce (C₁ : Set α)).Copy G,
      ∃ f₂ : (T.induce (C₂ : Set α)).Copy G,
        (∀ x, f₁ x ∈ A₁ ∪ B₁) ∧
        (∀ x, x ≠ (⟨root, hroot⟩ : {x // x ∈ C₂}) →
          f₂ x ∈ A₂ ∪ B₂) ∧
        f₂ ⟨root, hroot⟩ = v₀ ∧
        (∀ x : {x // x ∈ C₁}, T.Adj x root →
          G.Adj (f₁ x) (f₂ ⟨root, hroot⟩)) := by
  have hparts₁ : Set.PairwiseDisjoint Set.univ (twoParts A₁ B₁) :=
    twoParts_pairwiseDisjoint hAB₁
  obtain ⟨f₁, hf₁parts, hf₁roots⟩ :=
    Erdos547b.RootFixedPeeling.rooted_forest_embedding_respecting_parts
      (T.induce (C₁ : Set α)) G roots₁ hrootIndependent₁ hpeel₁ side₁
      (twoParts A₁ B₁) hparts₁ rootImage₁ hrootImageInj₁
      hrootImageMem₁ hcap₁ hdegree₁
  obtain ⟨f₂, hf₂root, hf₂mem⟩ :=
    exists_external_root_tree_copy (T.induce (C₂ : Set α)) G hTree₂
      ⟨root, hroot⟩ v₀ (A₂ ∪ B₂) hrootDegree₂ hminDegree₂
  refine ⟨f₁, f₂, ?_, hf₂mem, hf₂root, ?_⟩
  · intro x
    have hx := hf₁parts x
    rcases fin2_eq_zero_or_one (side₁ x) with hside | hside
    · exact Finset.mem_union_left _ (by simpa [hside] using hx)
    · exact Finset.mem_union_right _ (by simpa [hside] using hx)
  · intro x hx
    have hxroot : x ∈ roots₁ := hboundaryRoots x hx
    let xr : {x // x ∈ roots₁} := ⟨x, hxroot⟩
    have himage : f₁ x = rootImage₁ xr := hf₁roots xr
    rw [hf₂root, himage]
    exact (hrootImageAdj₁ xr).symm

/-- A convenient oriented form of the sharp middle step.  The caller gives
one ordinary bipartite colouring of the forest and a component-root map.
Each component is then flipped automatically according to whether its
reserved root image lies in `A₁` or `B₁`. -/
theorem exists_claim712_piece_copies_oriented
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (root : α) (C₁ C₂ : Finset α) (hroot : root ∈ C₂)
    (roots₁ : Finset {x // x ∈ C₁})
    (hrootIndependent₁ :
      (T.induce (C₁ : Set α)).IsIndepSet (roots₁ : Set {x // x ∈ C₁}))
    (hpeel₁ : Erdos547b.RootFixedPeeling.HasRootedLeafPeeling
      (T.induce (C₁ : Set α)) roots₁)
    (hboundaryRoots : ∀ x : {x // x ∈ C₁},
      T.Adj x root → x ∈ roots₁)
    (baseColor₁ : (T.induce (C₁ : Set α)).Coloring (Fin 2))
    (componentRoot : {x // x ∈ C₁} → {x // x ∈ roots₁})
    (hcomponentRoot : ∀ r : {x // x ∈ roots₁},
      componentRoot (r : {x // x ∈ C₁}) = r)
    (hadjComponent : ∀ ⦃x y : {x // x ∈ C₁}⦄,
      (T.induce (C₁ : Set α)).Adj x y → componentRoot x = componentRoot y)
    (hTree₂ : (T.induce (C₂ : Set α)).IsTree)
    (A₁ B₁ A₂ B₂ : Finset β) (hAB₁ : Disjoint A₁ B₁)
    (v₀ : β)
    (rootImage₁ : {x // x ∈ roots₁} → β)
    (hrootImageInj₁ : Function.Injective rootImage₁)
    (hrootImageAdj₁ : ∀ r, G.Adj v₀ (rootImage₁ r))
    (hrootImageUnion₁ : ∀ r, rootImage₁ r ∈ A₁ ∪ B₁)
    (hcap₁ : ∀ i, Coloring.partCard
      (orientComponents baseColor₁ componentRoot
        (fun r : {x // x ∈ roots₁} => (r : {x // x ∈ C₁}))
        (rootImageSide A₁ rootImage₁) hadjComponent) i ≤
      (twoParts A₁ B₁ i).card)
    (hdegree₁ : ∀ i j, i ≠ j → ∀ v ∈ twoParts A₁ B₁ i,
      Coloring.partCard
        (orientComponents baseColor₁ componentRoot
          (fun r : {x // x ∈ roots₁} => (r : {x // x ∈ C₁}))
          (rootImageSide A₁ rootImage₁) hadjComponent) j ≤
        ((G.neighborFinset v) ∩ twoParts A₁ B₁ j).card)
    (hrootDegree₂ : Fintype.card {x // x ∈ C₂} ≤
      ((G.neighborFinset v₀) ∩ (A₂ ∪ B₂)).card)
    (hminDegree₂ : ∀ v ∈ A₂ ∪ B₂,
      Fintype.card {x // x ∈ C₂} ≤
        ((G.neighborFinset v) ∩ (A₂ ∪ B₂)).card) :
    ∃ f₁ : (T.induce (C₁ : Set α)).Copy G,
      ∃ f₂ : (T.induce (C₂ : Set α)).Copy G,
        (∀ x, f₁ x ∈ A₁ ∪ B₁) ∧
        (∀ x, x ≠ (⟨root, hroot⟩ : {x // x ∈ C₂}) →
          f₂ x ∈ A₂ ∪ B₂) ∧
        f₂ ⟨root, hroot⟩ = v₀ ∧
        (∀ x : {x // x ∈ C₁}, T.Adj x root →
          G.Adj (f₁ x) (f₂ ⟨root, hroot⟩)) := by
  let rootVertex : {x // x ∈ roots₁} → {x // x ∈ C₁} := fun r => r
  let side₁ := orientComponents baseColor₁ componentRoot rootVertex
    (rootImageSide A₁ rootImage₁) hadjComponent
  have hsideRoot : ∀ r : {x // x ∈ roots₁},
      side₁ (r : {x // x ∈ C₁}) = rootImageSide A₁ rootImage₁ r := by
    intro r
    exact orientComponents_root baseColor₁ componentRoot rootVertex
      (rootImageSide A₁ rootImage₁) hadjComponent hcomponentRoot r
  have hrootImageMem₁ : ∀ r : {x // x ∈ roots₁},
      rootImage₁ r ∈ twoParts A₁ B₁ (side₁ r) := by
    intro r
    rw [hsideRoot]
    exact rootImage_mem_selected_side A₁ B₁ rootImage₁ hrootImageUnion₁ r
  apply exists_claim712_piece_copies_sharp T G root C₁ C₂ hroot roots₁
    hrootIndependent₁ hpeel₁ hboundaryRoots side₁ hTree₂
    A₁ B₁ A₂ B₂ hAB₁ v₀ rootImage₁ hrootImageInj₁
    hrootImageAdj₁ hrootImageMem₁
  · simpa [side₁, rootVertex] using hcap₁
  · simpa [side₁, rootVertex] using hdegree₁
  · exact hrootDegree₂
  · exact hminDegree₂

/-- Full sharp Claim 7.12 glue.  No membership of `v₀` in the second host
region is required; the source's stronger fact is that it is external to
all four regions.  The `C₂` copy is regarded as lying in
`insert v₀ (A₂ ∪ B₂)` solely for the disjointness bookkeeping, and the
deleted one-vertex components are restored from the total degree of `v₀`. -/
theorem exists_claim712_full_copy_sharp
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (root : α) (C₁ C₂ L : Finset α)
    (hdisj₁₂ : Disjoint C₁ C₂)
    (hdisj₁L : Disjoint C₁ L) (hdisj₂L : Disjoint C₂ L)
    (hcover : (C₁ ∪ C₂) ∪ L = Finset.univ)
    (hroot : root ∈ C₂)
    (hleafUnique : ∀ x ∈ L, ∀ ⦃y⦄, T.Adj x y → y = root)
    (hboundary : ∀ ⦃x y⦄, x ∈ C₁ → y ∈ C₂ → T.Adj x y → y = root)
    (roots₁ : Finset {x // x ∈ C₁})
    (hrootIndependent₁ :
      (T.induce (C₁ : Set α)).IsIndepSet (roots₁ : Set {x // x ∈ C₁}))
    (hpeel₁ : Erdos547b.RootFixedPeeling.HasRootedLeafPeeling
      (T.induce (C₁ : Set α)) roots₁)
    (hboundaryRoots : ∀ x : {x // x ∈ C₁},
      T.Adj x root → x ∈ roots₁)
    (side₁ : (T.induce (C₁ : Set α)).Coloring (Fin 2))
    (hTree₂ : (T.induce (C₂ : Set α)).IsTree)
    (A₁ B₁ A₂ B₂ : Finset β)
    (hAB₁ : Disjoint A₁ B₁)
    (hhost12 : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (v₀ : β) (hv₀outside₁ : v₀ ∉ A₁ ∪ B₁)
    (rootImage₁ : {x // x ∈ roots₁} → β)
    (hrootImageInj₁ : Function.Injective rootImage₁)
    (hrootImageAdj₁ : ∀ x : {x // x ∈ roots₁}, G.Adj v₀ (rootImage₁ x))
    (hrootImageMem₁ : ∀ x : {x // x ∈ roots₁},
      rootImage₁ x ∈ twoParts A₁ B₁ (side₁ x))
    (hcap₁ : ∀ i, Coloring.partCard side₁ i ≤
      (twoParts A₁ B₁ i).card)
    (hdegree₁ : ∀ i j, i ≠ j → ∀ v ∈ twoParts A₁ B₁ i,
      Coloring.partCard side₁ j ≤
        ((G.neighborFinset v) ∩ twoParts A₁ B₁ j).card)
    (hrootDegree₂ : Fintype.card {x // x ∈ C₂} ≤
      ((G.neighborFinset v₀) ∩ (A₂ ∪ B₂)).card)
    (hminDegree₂ : ∀ v ∈ A₂ ∪ B₂,
      Fintype.card {x // x ∈ C₂} ≤
        ((G.neighborFinset v) ∩ (A₂ ∪ B₂)).card)
    (hheavy : Fintype.card α - 1 ≤ G.degree v₀) :
    Nonempty (T.Copy G) := by
  obtain ⟨f₁, f₂, hf₁, hf₂away, hf₂root, hattach⟩ :=
    exists_claim712_piece_copies_sharp T G root C₁ C₂ hroot roots₁
      hrootIndependent₁ hpeel₁ hboundaryRoots side₁ hTree₂
      A₁ B₁ A₂ B₂ hAB₁ v₀ rootImage₁ hrootImageInj₁
      hrootImageAdj₁ hrootImageMem₁ hcap₁ hdegree₁
      hrootDegree₂ hminDegree₂
  have hhost : Disjoint (A₁ ∪ B₁) (insert v₀ (A₂ ∪ B₂)) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Finset.mem_insert] at hx₂
    rcases hx₂ with rfl | hx₂
    · exact hv₀outside₁ hx₁
    · exact Finset.disjoint_left.mp hhost12 hx₁ hx₂
  have hf₂ : ∀ x, f₂ x ∈ insert v₀ (A₂ ∪ B₂) := by
    intro x
    by_cases hx : x = (⟨root, hroot⟩ : {x // x ∈ C₂})
    · subst x
      simp [hf₂root]
    · exact Finset.mem_insert_of_mem (hf₂away x hx)
  have hrootDegree :
      Fintype.card α - 1 ≤ G.degree (f₂ ⟨root, hroot⟩) := by
    rw [hf₂root]
    exact hheavy
  obtain ⟨f, -, -, -⟩ :=
    exists_copy_of_natural_split_and_root_leaves T G root C₁ C₂ L
      hdisj₁₂ hdisj₁L hdisj₂L hcover hroot hleafUnique hboundary
      (A₁ ∪ B₁) (insert v₀ (A₂ ∪ B₂)) hhost f₁ f₂ hf₁ hf₂
      hattach hrootDegree
  exact ⟨f⟩

end Erdos547b.ZhaoClaim712

#print axioms Erdos547b.ZhaoClaim712.card_rootLeafChoices_ge
#print axioms Erdos547b.ZhaoClaim712.exists_copy_of_natural_split_and_root_leaves
#print axioms Erdos547b.ZhaoClaim712.exists_forest_copy_attached_at
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_piece_copies
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_full_copy
#print axioms Erdos547b.ZhaoClaim712.exists_injective_root_images_in_neighborhood
#print axioms Erdos547b.ZhaoClaim712.orientComponents
#print axioms Erdos547b.ZhaoClaim712.orientComponents_root
#print axioms Erdos547b.ZhaoClaim712.rootImage_mem_selected_side
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_piece_copies_sharp
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_piece_copies_oriented
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_full_copy_sharp
