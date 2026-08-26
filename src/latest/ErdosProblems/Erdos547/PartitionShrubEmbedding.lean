import ErdosProblems.Erdos547.PlacedShrub

/-!
# A regular-pair copy with all seed edges and forbidden-set conditions
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V : Type*} [Fintype U] [DecidableEq U]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

theorem exists_partition_shrub_copy (S : ↥P.shrubs)
    (D : ShrubRootData T P.seeds S.val) (G : SimpleGraph V) [DecidableRel G.Adj]
    (seed : ↥P.seeds → V) {ε d η : ℝ} {X Y A B R bad Q : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y) (heq : X.card = Y.card)
    (hd : d ≤ (G.edgeDensity X Y : ℝ)) (hη : 0 ≤ η)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (hA : A ⊆ X) (hB : B ⊆ Y) (hR : R ⊆ X) (hRA : Disjoint R A)
    (hAsize : η * (X.card : ℝ) ≤ A.card) (hBsize : η * (X.card : ℝ) ≤ B.card)
    (hRsize : 2 * ε * (X.card : ℝ) ≤ R.card)
    (hsmall : (S.val.card : ℝ) ≤ ε * X.card)
    (v : V) (hvX : v ∈ X) (hvR : v ∉ R)
    (hroot : 2 * ε * X.card ≤ (degreeIn G B v : ℝ))
    (hvbad : v ∉ bad) (hAbad : Disjoint A bad) (hBbad : Disjoint B bad)
    (hRbad : Disjoint R bad) (hAQ : Disjoint A Q) (hBQ : Disjoint B Q)
    (hprimary : G.Adj (seed D.seed) v)
    (hsecondary : ∀ z, D.second = some z → ∀ w ∈ R, G.Adj (seed z.1) w) :
    ∃ f : (T.induce (S.val : Set U)).Copy G,
      f D.root = v ∧
      (∀ u, f u ∉ bad) ∧
      G.Adj (seed D.seed) (f D.root) ∧
      (∀ z, D.second = some z → G.Adj (seed z.1) (f z.2)) ∧
      (∀ u, col u.val ≠ P.shrubColour S → f u ∈ X) ∧
      (∀ u, col u.val = P.shrubColour S → f u ∈ Y) ∧
      (∀ u, f u ∈ Q → u = D.root ∨ D.second.map Prod.snd = some u) := by
  have hn : (Fintype.card ↥S.val : ℝ) ≤ ε * X.card := by
    simpa only [Fintype.card_coe] using hsmall
  obtain ⟨f, hf, hsecond, hrest⟩ := exists_shrub_copy_in_regular_pair
    (T.induce (S.val : Set U)) G D.root (D.second.map Prod.snd) D.rooted
    hreg hdis heq hd hη hde hmargin hA hB hR hRA hAsize hBsize hRsize hn v hvX hvR hroot
  have hordinary (u : ↥S.val) (hur : u ≠ D.root) (hus : D.second.map Prod.snd ≠ some u) :
      f u ∈ A ∨ f u ∈ B := by
    by_cases he : (T.induce (S.val : Set U)).dist D.root u % 2 = 0
    · exact Or.inl ((hrest u hur hus).1 he)
    · exact Or.inr ((hrest u hur hus).2 he)
  have hparts := P.shrub_copy_near_far S D f X Y (hf.symm ▸ hvX)
    (fun u hu ↦ hR (hsecond u hu))
    (fun u hur hus ↦ ⟨fun h ↦ hA ((hrest u hur hus).1 h),
      fun h ↦ hB ((hrest u hur hus).2 h)⟩)
  refine ⟨f, hf, ?_, hf.symm ▸ hprimary, ?_, hparts.1, hparts.2, ?_⟩
  · exact shrub_copy_avoids f D.root (D.second.map Prod.snd) A B R bad
      (hf.symm ▸ hvbad) hAbad hBbad hRbad hsecond hordinary
  · intro z hz
    apply hsecondary z hz
    apply hsecond z.2
    rw [hz]
    rfl
  · exact shrub_reservoir_only_roots f D.root (D.second.map Prod.snd) A B Q hAQ hBQ hordinary

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_partition_shrub_copy
