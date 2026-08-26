import ErdosProblems.Erdos591.MacroRed
import ErdosProblems.Erdos591.MacroType
import ErdosProblems.Erdos591.LocalAssembly

/-!
# The all-builder-wins branch of the exact height-two game

The constructed root fibers have unbounded finite powers of `omega^omega`
and all cross-fiber pairs are non-blue. The checked local Erdős--Milner
relation supplies red pieces of cofinal types inside selected fibers.
Their union is a red set of the exact endpoint type.
-/

open Cardinal Ordinal

namespace Erdos591.Positive.Game

theorem no_cardinal_clique_of_cliqueFree {X : Type} (blue : SimpleGraph X) (n : ℕ)
    (hfree : blue.CliqueFree n) : ¬ ∃ S : Set X, blue.IsClique S ∧ #S = n := by
  classical
  rintro ⟨S, hS, hcard⟩
  obtain ⟨hfin, hfinCard⟩ := Cardinal.mk_eq_nat_iff_fintype.mp hcard
  let := hfin
  let e : S ↪ X := Function.Embedding.subtype S
  let t : Finset X := Finset.univ.map e
  apply hfree t
  constructor
  · intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
    exact hS a.property b.property hxy
  · simpa [t] using hfinCard

theorem local_red_piece (blue : SimpleGraph Erdos591.Negative.Exact.G)
    (htri : blue.CliqueFree 3) (n : ℕ) (S : Set Erdos591.Negative.Exact.G)
    (hS : LocalAssembly.source n ≤ typeLT S) :
    ∃ T : Set Erdos591.Negative.Exact.G, T ⊆ S ∧ blueᶜ.IsClique T ∧
      typeLT T = LocalAssembly.target n := by
  classical
  let er : ((· < ·) : (LocalAssembly.source n).ToType →
      (LocalAssembly.source n).ToType → Prop) ↪r ((· < ·) : S → S → Prop) :=
    Classical.choice (Ordinal.type_le_iff'.mp (by simpa only [Ordinal.type_toType] using hS))
  let F : (LocalAssembly.source n).ToType ↪o Erdos591.Negative.Exact.G :=
    (OrderEmbedding.ofStrictMono er (fun _ _ h => er.map_rel_iff.mpr h)).trans
      (OrderEmbedding.subtype S)
  let B := blue.comap F
  have hB : B.CliqueFree 4 :=
    SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap F.toEmbedding blue).isContained
      (SimpleGraph.CliqueFree.mono (by decide : 3 ≤ 4) htri)
  have hram := LocalAssembly.local_four_of_em_inputs n Erdos590.erdos_590
  rcases hram Bᶜ B isCompl_compl.symm with ⟨R, hR, htype⟩ | hblue
  · let e : R ↪o Erdos591.Negative.Exact.G := (OrderEmbedding.subtype R).trans F
    refine ⟨Set.range e, ?_, ?_, ?_⟩
    · rintro x ⟨a, rfl⟩
      exact (er a.val).property
    · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hxy
      have hab : a.val ≠ b.val := fun h => hxy (congrArg F h)
      have hc := hR a.property b.property hab
      apply (blue.compl_adj _ _).mpr
      exact ⟨hxy, (B.compl_adj _ _).mp hc |>.2⟩
    · exact (OrderIso.ordinalType_congr e.orderIso).symm.trans htype
  · exact (no_cardinal_clique_of_cliqueFree B 4 hB hblue).elim

theorem local_source_theta_power (n : ℕ) :
    LocalAssembly.source n = (ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2) := by
  rw [← Ordinal.opow_natCast, ← Ordinal.opow_mul]
  simp only [LocalAssembly.source, LocalAssembly.exp, Ordinal.natCast_mul,
    Nat.cast_ofNat, mul_assoc]

theorem local_target_theta_power (n : ℕ) :
    LocalAssembly.target n = (ω ^ ω : Ordinal.{0}) ^ (n + 1) := by
  rw [← Ordinal.opow_natCast, ← Ordinal.opow_mul]

namespace Macro.Forest

open Erdos591.Negative.Exact Erdos591.Negative.LexPrefix

/-- The builder side of the exact conservative-game dichotomy supplies
a red copy of `omega^(omega^2)` whenever the blue graph has no triangle. -/
theorem builder_red_set {N H : Set ℕ} (hH : H.Infinite) (hHN : H ⊆ N)
    (b : Concrete.Hist N → ℕ) (blue : SimpleGraph G)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H b
      (History.initial (Position.Next N) Position.initial))
    (htri : blue.CliqueFree 3) :
    ∃ S : Set G, blueᶜ.IsClique S ∧ typeLT S = (ω ^ (ω ^ 2) : Ordinal.{0}) := by
  classical
  have hpieces (n : ℕ) : ∃ T : Set G, T ⊆ vertices hH b (child 0 ((n + 1) * 2)) ∧
      blueᶜ.IsClique T ∧ typeLT T = LocalAssembly.target n := by
    apply local_red_piece blue htri n
    rw [local_source_theta_power]
    exact root_type_lower hH b _
  choose T hsub hclique htype using hpieces
  let S : Set G := ⋃ n, T n
  refine ⟨S, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hclique i hi hj hxy
    · apply (blue.compl_adj x y).mpr
      refine ⟨hxy, ?_⟩
      apply different_root_fibers_nonadjacent hH b hHN blue hbuilder
        (show (i + 1) * 2 ≠ (j + 1) * 2 by omega) (hsub i hi) (hsub j hj)
  · apply le_antisymm
    · exact (Ordinal.type_set_le S).trans_eq Erdos591.Negative.Exact.type_G
    · rw [← Erdos591.Negative.thetaOmega_eq,
        ← Ordinal.iSup_pow_natCast (Ordinal.opow_pos _ Ordinal.omega0_pos)]
      apply Ordinal.iSup_le
      intro n
      have hn : typeLT (T n) ≤ typeLT S :=
        typeLT_mono_set (Set.subset_iUnion T n)
      rw [htype n, local_target_theta_power] at hn
      calc
        (ω ^ ω : Ordinal.{0}) ^ n ≤ (ω ^ ω) ^ n * (ω ^ ω) :=
          Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
        _ = (ω ^ ω) ^ (n + 1) := (pow_succ _ _).symm
        _ ≤ typeLT S := hn

#print axioms builder_red_set

end Macro.Forest

end Erdos591.Positive.Game
