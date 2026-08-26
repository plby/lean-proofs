import ErdosProblems.Erdos547.TwoRootRegularMargins

/-!
# The regular-pair shrub embedding lemma
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*}

/-- A tree with a root and an optional second root at even distance at least four. -/
structure IsRootedShrub (T : SimpleGraph U) (r : U) (x : Option U) : Prop where
  isTree : T.IsTree
  even_distance : ∀ u, x = some u → T.dist r u % 2 = 0
  distance_lower : ∀ u, x = some u → 4 ≤ T.dist r u

theorem exists_shrub_copy_in_regular_pair [Fintype U] (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : U) (x : Option U) (hT : IsRootedShrub T r x)
    {ε d η : ℝ} {X Y A B P : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y) (heq : X.card = Y.card)
    (hd : d ≤ (G.edgeDensity X Y : ℝ)) (hη : 0 ≤ η)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (hA : A ⊆ X) (hB : B ⊆ Y) (hP : P ⊆ X) (hPA : Disjoint P A)
    (hAsize : η * (X.card : ℝ) ≤ A.card) (hBsize : η * (X.card : ℝ) ≤ B.card)
    (hPsize : 2 * ε * (X.card : ℝ) ≤ P.card)
    (hsmall : (Fintype.card U : ℝ) ≤ ε * X.card)
    (v : V) (hvX : v ∈ X) (hvP : v ∉ P)
    (hroot : 2 * ε * X.card ≤ (degreeIn G B v : ℝ)) :
    ∃ f : T.Copy G, f r = v ∧ (∀ u, x = some u → f u ∈ P) ∧
      ∀ u, u ≠ r → x ≠ some u →
        (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  cases x with
  | none =>
      have hε := hreg.pos.le
      have hd0 : 0 ≤ d := by linarith
      have hdone : d ≤ 1 := hd.trans (by exact_mod_cast G.edgeDensity_le_one X Y)
      have hweak : 4 * ε ≤ d * η := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd0 hdone) hη
        nlinarith only [hh, hmargin, hε]
      obtain ⟨f, hf, hpart⟩ := exists_small_rooted_copy_in_regular_pair T G hT.isTree
        hreg hdis heq hd hη hde hweak hA hB hAsize hBsize hsmall r v hvX hroot
      refine ⟨f, hf, ?_, fun u hur _ ↦ hpart u hur⟩
      intro u h
      cases h
  | some x =>
      obtain ⟨f, hf, hfx, hpart⟩ := exists_small_two_rooted_copy_in_regular_pair T G hT.isTree
        r x (hT.even_distance x rfl) (hT.distance_lower x rfl) hreg hdis heq hd hη hde
        hmargin hA hB hP hPA hAsize hBsize hPsize hsmall v hvP hroot
      refine ⟨f, hf, ?_, ?_⟩
      · intro u hu
        exact (Option.some.inj hu) ▸ hfx
      · intro u hur hux
        exact hpart u hur (fun hh ↦ hux (congrArg some hh.symm))

end Erdos547

#print axioms Erdos547.exists_shrub_copy_in_regular_pair
