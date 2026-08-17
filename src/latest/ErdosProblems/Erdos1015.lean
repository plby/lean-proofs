/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.Ramsey
import ErdosProblems.Erdos1037

/-!
# Erdős Problem 1015

Burr, Erdős, and Spencer proved that, for fixed t ≥ 3 and all sufficiently
large host orders n, the largest unavoidable number of uncovered vertices
in a packing by vertex-disjoint monochromatic K_t's is

R(t,t-1) - 1 + (n - (R(t,t-1) - 1)) % t.

The Erdős Problems page states an answer one larger.  That is the corresponding
strict threshold (remaining < b), whereas this file follows the problem's
inclusive convention (remaining ≤ b).

Reference: S. A. Burr, P. Erdős, and J. H. Spencer,
*Ramsey theorems for multiple copies of graphs*, Trans. AMS 209 (1975),
87--99, Theorem 6.
-/

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos1015

open Ramsey SimpleGraph

/-- A red or blue clique of order t, with red encoded by G and blue by
independence in G. -/
def MonoClique {V : Type*} (G : SimpleGraph V) (t : ℕ) (K : Finset V) : Prop :=
  G.IsNClique t K ∨ G.IsNIndepSet t K

/-- TilesTo G t S R means that S minus R is partitioned into pairwise
vertex-disjoint monochromatic K_t's and R is the remainder. -/
inductive TilesTo {V : Type*} [DecidableEq V] (G : SimpleGraph V) (t : ℕ) :
    Finset V → Finset V → Prop
  | refl (R : Finset V) : TilesTo G t R R
  | add {K S R : Finset V} (hK : MonoClique G t K)
      (hdisj : Disjoint K S) (hrest : TilesTo G t S R) :
      TilesTo G t (K ∪ S) R

namespace TilesTo

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

theorem subset {S R : Finset V} (h : TilesTo G t S R) : R ⊆ S := by
  induction h with
  | refl => exact Subset.rfl
  | add hK hdisj hrest ih =>
      exact ih.trans subset_union_right

theorem trans {A B C : Finset V}
    (hAB : TilesTo G t A B) (hBC : TilesTo G t B C) :
    TilesTo G t A C := by
  induction hAB with
  | refl => exact hBC
  | add hK hdisj hrest ih =>
      exact .add hK hdisj (ih hBC)

theorem card_eq_add_mul {S R : Finset V} (h : TilesTo G t S R) :
    ∃ m : ℕ, S.card = R.card + m * t := by
  induction h with
  | refl =>
      exact ⟨0, by simp⟩
  | @add K S R hK hdisj hrest ih =>
      rcases ih with ⟨m, hm⟩
      refine ⟨m + 1, ?_⟩
      have hcardK : K.card = t := by
        rcases hK with hK | hK
        · exact hK.card_eq
        · exact hK.card_eq
      rw [card_union_of_disjoint hdisj, hcardK, hm]
      simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]

theorem card_mod_eq {S R : Finset V} (h : TilesTo G t S R) :
    S.card % t = R.card % t := by
  rcases h.card_eq_add_mul with ⟨m, hm⟩
  simp [hm, Nat.add_mod]

theorem card_le {S R : Finset V} (h : TilesTo G t S R) :
    R.card ≤ S.card := by
  rcases h.card_eq_add_mul with ⟨m, hm⟩
  omega

theorem extend {A B T : Finset V}
    (h : TilesTo G t A B) (hd : Disjoint T A) :
    TilesTo G t (T ∪ A) (T ∪ B) := by
  induction h with
  | refl => exact .refl _
  | @add K S R hK hKS hrest ih =>
      have hTK : Disjoint T K := by
        exact Finset.disjoint_left.2 fun x hxT hxK =>
          Finset.disjoint_left.1 hd hxT (mem_union_left S hxK)
      have hT_S : Disjoint T S := by
        exact hd.mono_right subset_union_right
      have hK_TS : Disjoint K (T ∪ S) := by
        rw [Finset.disjoint_left]
        intro x hxK hx
        rcases mem_union.1 hx with hxT | hxS
        · exact Finset.disjoint_left.1 hTK hxT hxK
        · exact Finset.disjoint_left.1 hKS hxK hxS
      simpa [union_assoc, union_left_comm, union_comm] using
        TilesTo.add hK hK_TS (ih hT_S)

theorem compl {S R : Finset V} (h : TilesTo G t S R) :
    TilesTo Gᶜ t S R := by
  induction h with
  | refl => exact .refl _
  | add hK hdisj hrest ih =>
      apply TilesTo.add _ hdisj ih
      rcases hK with hred | hblue
      · exact Or.inr (by simpa using hred)
      · exact Or.inl (by simpa using hblue)

end TilesTo

/-- Every red/blue graph on a finite n-vertex type has a packing leaving at
most b vertices.  Quantifying over all finite types makes the lower-bound
sum construction transparent; it is equivalent to using Fin n. -/
def RemainderBound (t n b : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = n →
    ∀ G : SimpleGraph V, ∃ R : Finset V,
      TilesTo G t univ R ∧ R.card ≤ b

theorem remainderBound_exists (t n : ℕ) : ∃ b, RemainderBound t n b := by
  refine ⟨n, ?_⟩
  intro V _ _ hcard G
  refine ⟨univ, .refl _, ?_⟩
  simp [hcard]

/-- The exact worst-case minimum uncovered count. -/
def packingRemainder (t n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (remainderBound_exists t n)

theorem packingRemainder_spec (t n : ℕ) :
    RemainderBound t n (packingRemainder t n) :=
  by
    classical
    exact Nat.find_spec (remainderBound_exists t n)

theorem packingRemainder_le_of_bound {t n b : ℕ}
    (h : RemainderBound t n b) :
    packingRemainder t n ≤ b :=
  by
    classical
    exact Nat.find_min' (remainderBound_exists t n) h

/-- The inclusive Burr--Erdős--Spencer remainder. -/
def besRemainder (t n : ℕ) : ℕ :=
  let R := ramseyNumber t (t - 1)
  R - 1 + (n - (R - 1)) % t

/-- The reservoir size in the Burr--Erdős--Spencer proof. -/
def besReservoir (t : ℕ) : ℕ :=
  (t - 1) * (ramseyNumber t t - ramseyNumber t (t - 1)) +
    (t - 1) * (t - 2) + 1

/-- An explicit sufficient host threshold for the exact formula. -/
def besThreshold (t : ℕ) : ℕ :=
  ramseyNumber (besReservoir t) (besReservoir t)

/-- Target-size monotonicity of the Ramsey property. -/
theorem ramseyProperty_mono_targets {a b a' b' N : ℕ}
    (haa : a ≤ a') (hbb : b ≤ b')
    (h : RamseyProperty a' b' N) :
    RamseyProperty a b N := by
  intro G hbad
  apply h G
  constructor
  · intro K hK
    obtain ⟨K', hsub, hcard⟩ :=
      exists_subset_card_eq (s := K) (show a ≤ K.card by simpa [hK.card_eq] using haa)
    exact hbad.1 K' ⟨hK.isClique.subset (by simpa using hsub), hcard⟩
  · intro K hK
    obtain ⟨K', hsub, hcard⟩ :=
      exists_subset_card_eq (s := K) (show b ≤ K.card by simpa [hK.card_eq] using hbb)
    exact hbad.2 K' ⟨hK.isIndepSet.mono (by simpa using hsub), hcard⟩

/-- Target-size monotonicity of Ramsey numbers. -/
theorem ramseyNumber_mono {a b a' b' : ℕ}
    (haa : a ≤ a') (hbb : b ≤ b') :
    ramseyNumber a b ≤ ramseyNumber a' b' := by
  apply ramseyNumber_le_of_property
  exact ramseyProperty_mono_targets haa hbb (ramseyNumber_spec a' b')

/-- A graph witnessing failure one vertex below its Ramsey number. -/
theorem exists_ramseyCriticalGraph {a b : ℕ}
    (hpos : 0 < ramseyNumber a b) :
    ∃ G : SimpleGraph (Fin (ramseyNumber a b - 1)),
      G.CliqueFree a ∧ G.IndepSetFree b := by
  classical
  have hnot :
      ¬ RamseyProperty a b (ramseyNumber a b - 1) := by
    exact Nat.find_min (ramseyProperty_exists a b)
      (Nat.pred_lt (Nat.ne_of_gt hpos))
  unfold RamseyProperty at hnot
  push Not at hnot
  exact hnot

/-- Ramsey extraction from an arbitrary finite vertex set. -/
theorem monoClique_exists_of_ramsey_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {a b : ℕ} {S : Finset V}
    (hcard : ramseyNumber a b ≤ S.card) :
    (∃ K : Finset V, K ⊆ S ∧ G.IsNClique a K) ∨
      (∃ K : Finset V, K ⊆ S ∧ G.IsNIndepSet b K) := by
  let H : SimpleGraph {x // x ∈ S} := G.induce S
  have hprop : RamseyProperty a b S.card :=
    ramseyProperty_of_ramseyNumber_le hcard
  have hram := ramseyProperty_of_card (by simp) hprop H
  by_cases hcf : H.CliqueFree a
  · have hif : ¬ H.IndepSetFree b := fun hi => hram ⟨hcf, hi⟩
    unfold IndepSetFree at hif
    push Not at hif
    rcases hif with ⟨K, hK⟩
    refine Or.inr ⟨K.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_⟩
    · intro x hx
      rcases mem_map.1 hx with ⟨y, hy, rfl⟩
      exact y.property
    · have hK' : (G.induce (S : Set V)).IsNIndepSet b K := by
        simpa [H] using hK
      have htop :
          (((⊤ : SimpleGraph.Subgraph G).induce (S : Set V)).coe).IsNIndepSet b K := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hK'
      exact (isNIndepSet_induce (G := G)).1 htop
  · unfold CliqueFree at hcf
    push Not at hcf
    rcases hcf with ⟨K, hK⟩
    refine Or.inl ⟨K.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_⟩
    · intro x hx
      rcases mem_map.1 hx with ⟨y, hy, rfl⟩
      exact y.property
    · have hK' : (G.induce (S : Set V)).IsNClique a K := by
        simpa [H] using hK
      exact (isNClique_induce_iff (G := G) (S : Set V) K a).1 hK'

/-- A useful single-parameter form of Ramsey extraction. -/
theorem monoClique_exists_of_card_ge_ramsey {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {t : ℕ} {S : Finset V}
    (hcard : ramseyNumber t t ≤ S.card) :
    ∃ K : Finset V, K ⊆ S ∧ MonoClique G t K := by
  rcases monoClique_exists_of_ramsey_le G hcard with h | h
  · rcases h with ⟨K, hKS, hK⟩
    exact ⟨K, hKS, Or.inl hK⟩
  · rcases h with ⟨K, hKS, hK⟩
    exact ⟨K, hKS, Or.inr hK⟩

/-- Greedily tile a finite set until its remainder contains no monochromatic
K_t.  Ramsey's theorem then bounds that remainder by R(t,t)-1. -/
theorem greedyTiles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t : ℕ} (ht : 0 < t) (S : Finset V) :
    ∃ D : Finset V, TilesTo G t S D ∧
      (∀ K : Finset V, K ⊆ D → ¬ MonoClique G t K) ∧
      D.card < ramseyNumber t t := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      by_cases hex : ∃ K : Finset V, K ⊆ S ∧ MonoClique G t K
      · rcases hex with ⟨K, hKS, hK⟩
        have hcardK : K.card = t := by
          rcases hK with hK | hK
          · exact hK.card_eq
          · exact hK.card_eq
        have hKne : K.Nonempty := card_pos.mp (hcardK.trans_gt ht)
        have hlt : (S \ K).card < n := by
          rw [← hcard]
          rw [card_sdiff_of_subset hKS]
          exact Nat.sub_lt_of_pos_le (card_pos.mpr hKne) (card_le_card hKS)
        rcases ih (S \ K).card hlt (S \ K) rfl with
          ⟨D, htile, hfree, hDcard⟩
        refine ⟨D, ?_, hfree, hDcard⟩
        have hdisj : Disjoint K (S \ K) := by
          rw [Finset.disjoint_left]
          intro x hxK hxSK
          exact (mem_sdiff.1 hxSK).2 hxK
        have hunion : K ∪ (S \ K) = S := by
          exact union_sdiff_of_subset hKS
        rw [← hunion]
        exact TilesTo.add hK hdisj htile
      · refine ⟨S, .refl _, ?_, ?_⟩
        · intro K hKS hK
          exact hex ⟨K, hKS, hK⟩
        · by_contra hnot
          have hge : ramseyNumber t t ≤ S.card := Nat.le_of_not_gt hnot
          rcases monoClique_exists_of_card_ge_ramsey G hge with ⟨K, hKS, hK⟩
          exact hex ⟨K, hKS, hK⟩

/-- A red clique can be tiled down to exactly its cardinal remainder modulo t. -/
theorem tilesTo_remainder_of_isClique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {t : ℕ} (ht : 0 < t) {C : Finset V}
    (hC : G.IsClique C) :
    ∃ R : Finset V, TilesTo G t C R ∧ R ⊆ C ∧ R.card = C.card % t := by
  classical
  induction hcard : C.card using Nat.strong_induction_on generalizing C with
  | h n ih =>
      by_cases hlt : C.card < t
      · refine ⟨C, .refl _, Subset.rfl, ?_⟩
        rw [← hcard]
        exact (Nat.mod_eq_of_lt hlt).symm
      · have htle : t ≤ C.card := Nat.le_of_not_gt hlt
        obtain ⟨K, hKC, hcardK⟩ := exists_subset_card_eq (s := C) htle
        have hKne : K.Nonempty := card_pos.mp (hcardK.trans_gt ht)
        have hsmall : (C \ K).card < n := by
          rw [← hcard]
          rw [card_sdiff_of_subset hKC]
          exact Nat.sub_lt_of_pos_le (card_pos.mpr hKne) (card_le_card hKC)
        have hCsmall : G.IsClique (↑(C \ K) : Set V) := by
          exact hC.subset (by simp)
        rcases ih (C \ K).card hsmall hCsmall rfl with
          ⟨R, htile, hRC, hRcard⟩
        refine ⟨R, ?_, hRC.trans sdiff_subset, ?_⟩
        · have hKmono : MonoClique G t K :=
            Or.inl ⟨hC.subset (by simpa using hKC), hcardK⟩
          have hdisj : Disjoint K (C \ K) := by
            rw [Finset.disjoint_left]
            intro x hxK hxCK
            exact (mem_sdiff.1 hxCK).2 hxK
          rw [← union_sdiff_of_subset hKC]
          exact TilesTo.add hKmono hdisj htile
        · rw [hRcard]
          rw [← hcard]
          have hcards : C.card = K.card + (C \ K).card := by
            rw [card_sdiff_of_subset hKC, hcardK]
            omega
          rw [hcards, hcardK, Nat.add_mod]
          simp

theorem tilesTo_remainder_of_isIndepSet {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {t : ℕ} (ht : 0 < t) {C : Finset V}
    (hC : G.IsIndepSet C) :
    ∃ R : Finset V, TilesTo G t C R ∧ R ⊆ C ∧ R.card = C.card % t := by
  have hc' : Gᶜ.IsClique C := by simpa using hC
  rcases tilesTo_remainder_of_isClique Gᶜ ht hc' with ⟨R, htile, hsub, hcard⟩
  exact ⟨R, by simpa using htile.compl, hsub, hcard⟩

/-- The reservoir exchange lemma of Burr--Erdős--Spencer.  The natural number
e is a bound on the number of exchanges still needed. -/
theorem absorbBlueCliques {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t e : ℕ} (ht : 3 ≤ t)
    {C D : Finset V}
    (hCD : Disjoint C D) (hC : G.IsClique C)
    (hDfree : ∀ K : Finset V, K ⊆ D → ¬ MonoClique G t K)
    (hDcard : D.card ≤ ramseyNumber t (t - 1) - 1 + e)
    (hCcard :
      (t - 1) * e + (t - 1) * (t - 2) + 1 ≤ C.card) :
    ∃ C' D' : Finset V,
      C' ⊆ C ∧ D' ⊆ D ∧ Disjoint C' D' ∧ G.IsClique C' ∧
      D'.card ≤ ramseyNumber t (t - 1) - 1 ∧
      TilesTo G t (C ∪ D) (C' ∪ D') := by
  classical
  induction e generalizing C D with
  | zero =>
      refine ⟨C, D, Subset.rfl, Subset.rfl, hCD, hC, ?_, .refl _⟩
      simpa using hDcard
  | succ e ih =>
      let R := ramseyNumber t (t - 1)
      let B := (t - 1) * (t - 2) + 1
      have hRpos : 0 < R :=
        ramseyNumber_pos (by omega) (by omega)
      by_cases hsmall : D.card ≤ R - 1
      · exact ⟨C, D, Subset.rfl, Subset.rfl, hCD, hC, hsmall, .refl _⟩
      have hRle : R ≤ D.card := by omega
      rcases monoClique_exists_of_ramsey_le (a := t) (b := t - 1) G hRle with
        hred | hblue
      · rcases hred with ⟨K, hKD, hKred⟩
        exact False.elim (hDfree K hKD (Or.inl hKred))
      · rcases hblue with ⟨E, hED, hEblue⟩
        let N : V → Finset V := fun x => C.filter (G.Adj x)
        by_cases hlarge : ∃ x ∈ E, t - 1 ≤ (N x).card
        · rcases hlarge with ⟨x, hxE, hxlarge⟩
          obtain ⟨F, hFN, hFcard⟩ :=
            exists_subset_card_eq (s := N x) hxlarge
          have hFD : F ⊆ C := by
            intro y hy
            exact (mem_filter.1 (hFN hy)).1
          have hxD : x ∈ D := hED hxE
          have hxC : x ∉ C := by
            intro hxC
            exact Finset.disjoint_left.1 hCD hxC hxD
          have hxF : x ∉ F := fun hx => hxC (hFD hx)
          let K := insert x F
          have hFclique : G.IsClique (↑F : Set V) :=
            hC.subset (by simpa using hFD)
          have hFred : G.IsNClique (t - 1) F := ⟨hFclique, hFcard⟩
          have hxadj : ∀ y ∈ F, G.Adj x y := by
            intro y hy
            exact (mem_filter.1 (hFN hy)).2
          have hKred : G.IsNClique t K := by
            have hi := hFred.insert hxadj
            simpa [K, Nat.sub_add_cancel (by omega : 1 ≤ t)] using hi
          let C₀ := C \ F
          let D₀ := D.erase x
          have hC₀C : C₀ ⊆ C := by
            exact sdiff_subset
          have hD₀D : D₀ ⊆ D := erase_subset _ _
          have hC₀D₀ : Disjoint C₀ D₀ :=
            hCD.mono hC₀C hD₀D
          have hC₀ : G.IsClique (↑C₀ : Set V) :=
            hC.subset (by simpa using hC₀C)
          have hD₀free : ∀ L : Finset V, L ⊆ D₀ → ¬ MonoClique G t L := by
            intro L hL
            exact hDfree L (hL.trans hD₀D)
          have hD₀card : D₀.card ≤ R - 1 + e := by
            have herase : D₀.card = D.card - 1 := by
              simp [D₀, card_erase_of_mem hxD]
            dsimp [R] at hDcard ⊢
            rw [herase]
            omega
          have hC₀card :
              (t - 1) * e + (t - 1) * (t - 2) + 1 ≤ C₀.card := by
            have hdiff : C₀.card = C.card - (t - 1) := by
              simp [C₀, card_sdiff_of_subset hFD, hFcard]
            have hbudget :
                (t - 1) * e + (t - 1) * (t - 2) + 1 + (t - 1) ≤ C.card := by
              simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hCcard
            rw [hdiff]
            exact Nat.le_sub_of_add_le hbudget
          rcases ih hC₀D₀ hC₀ hD₀free hD₀card hC₀card with
            ⟨C', D', hC'C₀, hD'D₀, hC'D', hC'clique, hD'card, htile⟩
          refine ⟨C', D', hC'C₀.trans hC₀C, hD'D₀.trans hD₀D,
            hC'D', hC'clique, hD'card, ?_⟩
          have hKdisj : Disjoint K (C₀ ∪ D₀) := by
            rw [Finset.disjoint_left]
            intro z hzK hzrest
            rcases mem_insert.1 hzK with rfl | hzF
            · rcases mem_union.1 hzrest with hzC₀ | hzD₀
              · exact hxC (hC₀C hzC₀)
              · exact (mem_erase.1 hzD₀).1 rfl
            · rcases mem_union.1 hzrest with hzC₀ | hzD₀
              · exact (mem_sdiff.1 hzC₀).2 hzF
              · exact Finset.disjoint_left.1 hCD (hFD hzF) (hD₀D hzD₀)
          have hstep : TilesTo G t (K ∪ (C₀ ∪ D₀)) (C' ∪ D') :=
            TilesTo.add (Or.inl hKred) hKdisj htile
          have hunion : K ∪ (C₀ ∪ D₀) = C ∪ D := by
            ext z
            simp only [K, C₀, D₀, mem_union, mem_insert, mem_sdiff, mem_erase]
            constructor
            · intro hz
              rcases hz with hzK | hzrest
              · rcases hzK with hzx | hzF
                · subst z
                  exact Or.inr hxD
                · exact Or.inl (hFD hzF)
              · rcases hzrest with hzC₀ | hzD₀
                · exact Or.inl hzC₀.1
                · exact Or.inr hzD₀.2
            · intro hz
              rcases hz with hzC | hzD
              · by_cases hzF : z ∈ F
                · exact Or.inl (Or.inr hzF)
                · exact Or.inr (Or.inl ⟨hzC, hzF⟩)
              · by_cases hzx : z = x
                · exact Or.inl (Or.inl hzx)
                · exact Or.inr (Or.inr ⟨hzx, hzD⟩)
          rw [hunion] at hstep
          exact hstep
        · have hNsmall : ∀ x ∈ E, (N x).card ≤ t - 2 := by
            intro x hx
            have hnle : ¬t - 1 ≤ (N x).card := by
              intro hle
              exact hlarge ⟨x, hx, hle⟩
            have := not_le.mp hnle
            omega
          let U : Finset V := E.biUnion N
          have hUcard : U.card ≤ (t - 1) * (t - 2) := by
            calc
              U.card ≤ ∑ x ∈ E, (N x).card := card_biUnion_le
              _ ≤ ∑ _x ∈ E, (t - 2) := by
                exact sum_le_sum fun x hx => hNsmall x hx
              _ = E.card * (t - 2) := by simp
              _ = (t - 1) * (t - 2) := by rw [hEblue.card_eq]
          have hU_lt_C : U.card < C.card := by
            omega
          obtain ⟨y, hy⟩ := sdiff_nonempty_of_card_lt_card hU_lt_C
          have hyC : y ∈ C := (mem_sdiff.1 hy).1
          have hyU : y ∉ U := (mem_sdiff.1 hy).2
          have hyD : y ∉ D := by
            intro hyD
            exact Finset.disjoint_left.1 hCD hyC hyD
          have hyE : y ∉ E := fun hyE => hyD (hED hyE)
          have hy_not_red : ∀ x ∈ E, ¬ G.Adj y x := by
            intro x hxE hred
            apply hyU
            apply mem_biUnion.2
            refine ⟨x, hxE, ?_⟩
            exact mem_filter.2 ⟨hyC, hred.symm⟩
          let K := insert y E
          have hEcompl : Gᶜ.IsNClique (t - 1) E := by
            simpa using hEblue
          have hyblue : ∀ x ∈ E, Gᶜ.Adj y x := by
            intro x hxE
            rw [compl_adj]
            exact ⟨fun hxy => hyE (hxy ▸ hxE), hy_not_red x hxE⟩
          have hKblue : G.IsNIndepSet t K := by
            have hi := hEcompl.insert hyblue
            have hi' : Gᶜ.IsNClique t K := by
              simpa [K, Nat.sub_add_cancel (by omega : 1 ≤ t)] using hi
            simpa using hi'
          let C₀ := C.erase y
          let D₀ := D \ E
          have hC₀C : C₀ ⊆ C := erase_subset _ _
          have hD₀D : D₀ ⊆ D := sdiff_subset
          have hC₀D₀ : Disjoint C₀ D₀ := hCD.mono hC₀C hD₀D
          have hC₀ : G.IsClique (↑C₀ : Set V) :=
            hC.subset (by simpa using hC₀C)
          have hD₀free : ∀ L : Finset V, L ⊆ D₀ → ¬ MonoClique G t L := by
            intro L hL
            exact hDfree L (hL.trans hD₀D)
          have hD₀card : D₀.card ≤ R - 1 + e := by
            have hEne : E.Nonempty := card_pos.mp (hEblue.card_eq.trans_gt (by omega))
            have hdiff : D₀.card < D.card := by
              dsimp [D₀]
              rw [card_sdiff_of_subset hED]
              exact Nat.sub_lt_of_pos_le (card_pos.mpr hEne) (card_le_card hED)
            dsimp [R] at hDcard ⊢
            omega
          have hC₀card :
              (t - 1) * e + (t - 1) * (t - 2) + 1 ≤ C₀.card := by
            have herase : C₀.card = C.card - 1 := by
              simp [C₀, card_erase_of_mem hyC]
            have hbudget :
                (t - 1) * e + (t - 1) * (t - 2) + 1 + (t - 1) ≤ C.card := by
              simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hCcard
            have hone :
                (t - 1) * e + (t - 1) * (t - 2) + 1 + 1 ≤ C.card := by
              omega
            rw [herase]
            exact Nat.le_sub_of_add_le hone
          rcases ih hC₀D₀ hC₀ hD₀free hD₀card hC₀card with
            ⟨C', D', hC'C₀, hD'D₀, hC'D', hC'clique, hD'card, htile⟩
          refine ⟨C', D', hC'C₀.trans hC₀C, hD'D₀.trans hD₀D,
            hC'D', hC'clique, hD'card, ?_⟩
          have hKdisj : Disjoint K (C₀ ∪ D₀) := by
            rw [Finset.disjoint_left]
            intro z hzK hzrest
            rcases mem_insert.1 hzK with rfl | hzE
            · rcases mem_union.1 hzrest with hzC₀ | hzD₀
              · exact (mem_erase.1 hzC₀).1 rfl
              · exact hyD (hD₀D hzD₀)
            · rcases mem_union.1 hzrest with hzC₀ | hzD₀
              · exact Finset.disjoint_left.1 hCD (hC₀C hzC₀) (hED hzE)
              · exact (mem_sdiff.1 hzD₀).2 hzE
          have hstep : TilesTo G t (K ∪ (C₀ ∪ D₀)) (C' ∪ D') :=
            TilesTo.add (Or.inr hKblue) hKdisj htile
          have hunion : K ∪ (C₀ ∪ D₀) = C ∪ D := by
            ext z
            simp only [K, C₀, D₀, mem_union, mem_insert, mem_erase, mem_sdiff]
            constructor
            · intro hz
              rcases hz with hzK | hzrest
              · rcases hzK with hzy | hzE
                · subst z
                  exact Or.inl hyC
                · exact Or.inr (hED hzE)
              · rcases hzrest with hzC₀ | hzD₀
                · exact Or.inl hzC₀.2
                · exact Or.inr hzD₀.1
            · intro hz
              rcases hz with hzC | hzD
              · by_cases hzy : z = y
                · exact Or.inl (Or.inl hzy)
                · exact Or.inr (Or.inl ⟨hzy, hzC⟩)
              · by_cases hzE : z ∈ E
                · exact Or.inl (Or.inr hzE)
                · exact Or.inr (Or.inr ⟨hzD, hzE⟩)
          rw [hunion] at hstep
          exact hstep

/-- Among natural numbers at least `a` and congruent to `n` modulo `t`,
`a + (n-a) % t` is the least one. -/
theorem residueCeil_le {a n t m : ℕ} (_ht : 0 < t) (ha : a ≤ n)
    (ham : a ≤ m) (hmod : m % t = n % t) :
    a + (n - a) % t ≤ m := by
  have hmn : m ≡ n [MOD t] := hmod
  have haa : a ≡ a [MOD t] := Nat.ModEq.refl a
  have hsub : (m - a) % t = (n - a) % t :=
    hmn.sub ham ha haa
  calc
    a + (n - a) % t = a + (m - a) % t := by rw [hsub]
    _ ≤ a + (m - a) := Nat.add_le_add_left (Nat.mod_le _ _) _
    _ = m := Nat.add_sub_of_le ham

/-- The residue-adjusted ceiling is monotone in its lower endpoint. -/
theorem residueEnvelope {a q n t : ℕ} (ht : 0 < t)
    (haq : a ≤ q) (hqn : q ≤ n) :
    a + (n - a) % t ≤ q + (n - q) % t := by
  apply residueCeil_le ht (haq.trans hqn)
  · exact le_add_right haq
  · rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_sub_of_le hqn]

/-- The unique number in `[a,a+t)` congruent to `n` is the
residue-adjusted ceiling of `a`. -/
theorem eq_residueCeil {a n t m : ℕ} (_ht : 0 < t) (ha : a ≤ n)
    (ham : a ≤ m) (hmt : m < a + t) (hmod : m % t = n % t) :
    m = a + (n - a) % t := by
  have hmn : m ≡ n [MOD t] := hmod
  have hsub : (m - a) % t = (n - a) % t :=
    hmn.sub ham ha (Nat.ModEq.refl a)
  have hdiff : m - a < t := by omega
  calc
    m = a + (m - a) := (Nat.add_sub_of_le ham).symm
    _ = a + (m - a) % t := by rw [Nat.mod_eq_of_lt hdiff]
    _ = a + (n - a) % t := by rw [hsub]

/-- The BES reservoir is at least the clique order. -/
theorem le_besReservoir {t : ℕ} (ht : 3 ≤ t) : t ≤ besReservoir t := by
  have hbase : t ≤ (t - 1) * (t - 2) + 1 := by
    calc
      t = (t - 1) * 1 + 1 := by omega
      _ ≤ (t - 1) * (t - 2) + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
  unfold besReservoir
  omega

/-- The off-diagonal Ramsey number fits below the explicit BES threshold. -/
theorem ramseyOffdiag_le_besThreshold {t : ℕ} (ht : 3 ≤ t) :
    ramseyNumber t (t - 1) ≤ besThreshold t := by
  unfold besThreshold
  apply ramseyNumber_mono (le_besReservoir ht)
  exact (Nat.sub_le t 1).trans (le_besReservoir ht)

/-- The upper-bound construction once a red reservoir has been selected. -/
theorem tilesTo_besRemainder_of_reservoir {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {t n : ℕ} (ht : 3 ≤ t)
    (hV : Fintype.card V = n)
    {C : Finset V} (hC : G.IsNClique (besReservoir t) C)
    (hqn : ramseyNumber t (t - 1) - 1 ≤ n) :
    ∃ L : Finset V, TilesTo G t univ L ∧ L.card ≤ besRemainder t n := by
  classical
  have htpos : 0 < t := by omega
  let O : Finset V := univ \ C
  rcases greedyTiles G htpos O with ⟨D, hOD, hDfree, hDsmall⟩
  have hDO : D ⊆ O := hOD.subset
  have hCO : Disjoint C O := by
    rw [Finset.disjoint_left]
    intro x hxC hxO
    exact (mem_sdiff.1 hxO).2 hxC
  have hCD : Disjoint C D := hCO.mono_right hDO
  have hRS : ramseyNumber t (t - 1) ≤ ramseyNumber t t :=
    ramseyNumber_mono le_rfl (by omega)
  have hDcard :
      D.card ≤ ramseyNumber t (t - 1) - 1 +
        (ramseyNumber t t - ramseyNumber t (t - 1)) := by
    omega
  have hCbudget :
      (t - 1) * (ramseyNumber t t - ramseyNumber t (t - 1)) +
          (t - 1) * (t - 2) + 1 ≤ C.card := by
    rw [hC.card_eq]
    exact le_rfl
  rcases absorbBlueCliques G ht hCD hC.isClique hDfree hDcard hCbudget with
    ⟨C', D', hC'C, hD'D, hC'D', hC'clique, hD'card, hAbsorb⟩
  rcases tilesTo_remainder_of_isClique G htpos hC'clique with
    ⟨C₂, hC'tile, hC₂C', hC₂card⟩
  have hpre : TilesTo G t univ (C ∪ D) := by
    have hext := hOD.extend hCO
    have hCuniv : C ⊆ (univ : Finset V) := subset_univ _
    simpa [O, union_sdiff_of_subset hCuniv] using hext
  have hD'C' : Disjoint D' C' := hC'D'.symm
  have hpost : TilesTo G t (C' ∪ D') (C₂ ∪ D') := by
    have hext := hC'tile.extend hD'C'
    simpa [union_comm] using hext
  let L : Finset V := C₂ ∪ D'
  have hwhole : TilesTo G t univ L := by
    exact (hpre.trans hAbsorb).trans (by simpa [L] using hpost)
  refine ⟨L, hwhole, ?_⟩
  have hC₂D' : Disjoint C₂ D' := hC'D'.mono_left hC₂C'
  have hLcard : L.card = D'.card + C₂.card := by
    change (C₂ ∪ D').card = D'.card + C₂.card
    rw [card_union_of_disjoint hC₂D']
    omega
  have hC₂lt : C₂.card < t := by
    rw [hC₂card]
    exact Nat.mod_lt _ htpos
  have hD'L : D'.card ≤ L.card := by omega
  have hLn : L.card ≤ n := by
    have := hwhole.card_le
    simpa [hV] using this
  have hLlt : L.card < D'.card + t := by omega
  have hLmod : L.card % t = n % t := by
    have := hwhole.card_mod_eq
    simpa [hV] using this.symm
  have hLeq : L.card = D'.card + (n - D'.card) % t :=
    eq_residueCeil htpos (hD'L.trans hLn) hD'L hLlt hLmod
  rw [hLeq]
  unfold besRemainder
  exact residueEnvelope htpos hD'card hqn

/-- Burr--Erdős--Spencer upper bound, with the inclusive convention. -/
theorem remainderBound_besUpper {t n : ℕ} (ht : 3 ≤ t)
    (hn : besThreshold t ≤ n) :
    RemainderBound t n (besRemainder t n) := by
  intro V _ _ hV G
  have hqn : ramseyNumber t (t - 1) - 1 ≤ n :=
    (Nat.pred_le (ramseyNumber t (t - 1))).trans
      ((ramseyOffdiag_le_besThreshold ht).trans hn)
  have hram : ramseyNumber (besReservoir t) (besReservoir t) ≤
      (univ : Finset V).card := by
    simpa [besThreshold, hV] using hn
  rcases monoClique_exists_of_card_ge_ramsey G hram with ⟨C, hCuniv, hC⟩
  rcases hC with hCred | hCblue
  · exact tilesTo_besRemainder_of_reservoir G ht hV hCred hqn
  · have hCcomp : Gᶜ.IsNClique (besReservoir t) C := by simpa using hCblue
    rcases tilesTo_besRemainder_of_reservoir Gᶜ ht hV hCcomp hqn with
      ⟨L, htile, hcard⟩
    exact ⟨L, by simpa using htile.compl, hcard⟩

/-- In the Ramsey-critical lower-bound coloring, every monochromatic tile
lies entirely in the red-complete left summand. -/
theorem monoClique_subset_left_of_critical {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (H : SimpleGraph B) {t : ℕ} (ht : 3 ≤ t)
    (hcrit : H.CliqueFree t ∧ H.IndepSetFree (t - 1))
    {K : Finset (A ⊕ B)} (hK : MonoClique ((⊤ : SimpleGraph A) ⊕g H) t K) :
    K ⊆ (univ : Finset A).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  intro z hzK
  cases z with
  | inl a => simp
  | inr b =>
      exfalso
      rcases hK with hred | hblue
      · have hleft0 : K.toLeft = ∅ := by
          ext a
          simp only [mem_toLeft]
          constructor
          · intro ha
            have hadj := hred.isClique ha hzK (by simp)
            simp at hadj
          · intro ha
            simp at ha
        have hrightClique : H.IsClique (↑K.toRight : Set B) := by
          intro x hx y hy hxy
          have hadj := hred.isClique (mem_toRight.1 hx) (mem_toRight.1 hy)
            (by simpa using hxy)
          simpa using hadj
        have hrightcard : K.toRight.card = t := by
          have hsum := card_toLeft_add_card_toRight (u := K)
          rw [hleft0] at hsum
          simpa [hred.card_eq] using hsum
        exact hcrit.1 K.toRight ⟨hrightClique, hrightcard⟩
      · have hleftle : K.toLeft.card ≤ 1 := by
          rw [card_le_one_iff]
          intro x y hx hy
          by_contra hxy
          have hnot := hblue.isIndepSet (mem_toLeft.1 hx) (mem_toLeft.1 hy)
            (by simpa using hxy)
          exact hnot (by simp [hxy])
        have hrightlarge : t - 1 ≤ K.toRight.card := by
          have hsum := card_toLeft_add_card_toRight (u := K)
          rw [hblue.card_eq] at hsum
          omega
        obtain ⟨E, hEright, hEcard⟩ :=
          exists_subset_card_eq (s := K.toRight) hrightlarge
        have hEindep : H.IsIndepSet (↑E : Set B) := by
          intro x hx y hy hxy
          have hnot := hblue.isIndepSet
            (mem_toRight.1 (hEright hx)) (mem_toRight.1 (hEright hy))
            (by simpa using hxy)
          simpa using hnot
        exact hcrit.2 E ⟨hEindep, hEcard⟩

/-- If every tile lies in the left summand, a tiling cannot remove any
vertex from the right summand. -/
theorem TilesTo.right_subset_remainder {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {G : SimpleGraph (A ⊕ B)} {t : ℕ}
    {S R : Finset (A ⊕ B)}
    (h : TilesTo G t S R)
    (hSright : (univ : Finset B).map ⟨Sum.inr, Sum.inr_injective⟩ ⊆ S)
    (hleft : ∀ K : Finset (A ⊕ B), MonoClique G t K →
      K ⊆ (univ : Finset A).map ⟨Sum.inl, Sum.inl_injective⟩) :
    (univ : Finset B).map ⟨Sum.inr, Sum.inr_injective⟩ ⊆ R := by
  induction h with
  | refl => exact hSright
  | @add K S R hK hdisj hrest ih =>
      apply ih
      intro z hz
      have hz' := hSright hz
      rcases mem_union.1 hz' with hzK | hzS
      · have hzleft := hleft K hK hzK
        rcases mem_map.1 hz with ⟨b, hb, rfl⟩
        simp at hzleft
      · exact hzS

/-- The Ramsey-critical coloring gives the matching inclusive lower bound. -/
theorem besLower_le_packingRemainder {t n : ℕ} (ht : 3 ≤ t)
    (hqn : ramseyNumber t (t - 1) - 1 ≤ n) :
    besRemainder t n ≤ packingRemainder t n := by
  classical
  let q := ramseyNumber t (t - 1) - 1
  have hRpos : 0 < ramseyNumber t (t - 1) :=
    ramseyNumber_pos (by omega) (by omega)
  obtain ⟨H, hcrit⟩ := exists_ramseyCriticalGraph hRpos
  let G : SimpleGraph (Fin (n - q) ⊕ Fin q) := (⊤ : SimpleGraph (Fin (n - q))) ⊕g H
  have hVcard : Fintype.card (Fin (n - q) ⊕ Fin q) = n := by
    simp [q]
    omega
  rcases packingRemainder_spec t n (Fin (n - q) ⊕ Fin q) hVcard G with
    ⟨L, htile, hLbound⟩
  have hright :
      (univ : Finset (Fin q)).map ⟨Sum.inr, Sum.inr_injective⟩ ⊆ L := by
    apply htile.right_subset_remainder (by simp)
    intro K hK
    exact monoClique_subset_left_of_critical H ht hcrit hK
  have hqL : q ≤ L.card := by
    have hc := card_le_card hright
    simpa using hc
  have hLn : L.card ≤ n := by
    have hc := htile.card_le
    simpa [hVcard] using hc
  have hLmod : L.card % t = n % t := by
    have hm := htile.card_mod_eq
    simpa [hVcard] using hm.symm
  have hceil : q + (n - q) % t ≤ L.card :=
    residueCeil_le (by omega) hqn hqL hLmod
  unfold besRemainder
  change q + (n - q) % t ≤ packingRemainder t n
  exact hceil.trans hLbound

/-- The exact pointwise resolution of Erdős Problem 1015.  This is the
inclusive (`at most`) version of Burr--Erdős--Spencer, Theorem 6. -/
theorem erdos1015_exact {t n : ℕ} (ht : 3 ≤ t)
    (hn : besThreshold t ≤ n) :
    packingRemainder t n = besRemainder t n := by
  apply le_antisymm
  · exact packingRemainder_le_of_bound (remainderBound_besUpper ht hn)
  · apply besLower_le_packingRemainder ht
    exact (Nat.pred_le _).trans ((ramseyOffdiag_le_besThreshold ht).trans hn)

/-- The least strict threshold (`remaining < b`) is one more than the
inclusive optimum. -/
def strictPackingThreshold (t n : ℕ) : ℕ := packingRemainder t n + 1

/-- This is the formula printed on the Erdős Problems page: it is correct
for a strict bound, rather than for the stated inclusive convention. -/
theorem erdos1015_strict_exact {t n : ℕ} (ht : 3 ≤ t)
    (hn : besThreshold t ≤ n) :
    strictPackingThreshold t n =
      ramseyNumber t (t - 1) +
        (n - (ramseyNumber t (t - 1) - 1)) % t := by
  rw [strictPackingThreshold, erdos1015_exact ht hn]
  dsimp [besRemainder]
  have hRpos : 0 < ramseyNumber t (t - 1) :=
    ramseyNumber_pos (by omega) (by omega)
  omega

/-- The optimal eventual bound independent of the host residue. -/
def besUniformRemainder (t : ℕ) : ℕ :=
  ramseyNumber t (t - 1) + t - 2

theorem besRemainder_le_uniform {t n : ℕ} (ht : 3 ≤ t) :
    besRemainder t n ≤ besUniformRemainder t := by
  dsimp [besRemainder, besUniformRemainder]
  have hRpos : 0 < ramseyNumber t (t - 1) :=
    ramseyNumber_pos (by omega) (by omega)
  have hmod := Nat.mod_lt (n - (ramseyNumber t (t - 1) - 1))
    (by omega : 0 < t)
  omega

theorem RemainderBound.mono {t n a b : ℕ} (h : RemainderBound t n a)
    (hab : a ≤ b) : RemainderBound t n b := by
  intro V _ _ hV G
  rcases h V hV G with ⟨L, htile, hcard⟩
  exact ⟨L, htile, hcard.trans hab⟩

/-- For every lower cutoff there is a larger host order attaining the worst
residue class. -/
theorem exists_large_host_attaining_uniform {t N : ℕ} (ht : 3 ≤ t) :
    ∃ n : ℕ, N ≤ n ∧ besThreshold t ≤ n ∧
      packingRemainder t n = besUniformRemainder t := by
  let q := ramseyNumber t (t - 1) - 1
  let n := q + (N + besThreshold t) * t + (t - 1)
  have htpos : 0 < t := by omega
  have hmul : N + besThreshold t ≤ (N + besThreshold t) * t :=
    Nat.le_mul_of_pos_right _ htpos
  have hNn : N ≤ n := by
    dsimp [n]
    omega
  have hthreshold : besThreshold t ≤ n := by
    dsimp [n]
    omega
  have hnsub : n - q = (N + besThreshold t) * t + (t - 1) := by
    dsimp [n]
    omega
  have hrem : (n - q) % t = t - 1 := by
    rw [hnsub, Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt (by omega : t - 1 < t)]
  refine ⟨n, hNn, hthreshold, ?_⟩
  rw [erdos1015_exact ht hthreshold]
  unfold besRemainder besUniformRemainder
  change q + (n - q) % t = ramseyNumber t (t - 1) + t - 2
  rw [hrem]
  have hRpos : 0 < ramseyNumber t (t - 1) :=
    ramseyNumber_pos (by omega) (by omega)
  dsimp [q]
  omega

/-- A host-order-independent bound is eventually valid. -/
def EventualRemainderBound (t b : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RemainderBound t n b

/-- The exact uniform interpretation of Moon's/Erdős's `f(t)`: the BES
quantity is eventually valid, and every eventual uniform bound is at least
this large. -/
theorem erdos1015_eventual_uniform {t : ℕ} (ht : 3 ≤ t) :
    EventualRemainderBound t (besUniformRemainder t) ∧
      ∀ b : ℕ, EventualRemainderBound t b → besUniformRemainder t ≤ b := by
  constructor
  · refine ⟨besThreshold t, ?_⟩
    intro n hn
    exact (remainderBound_besUpper ht hn).mono (besRemainder_le_uniform ht)
  · intro b hb
    rcases hb with ⟨N, hN⟩
    rcases exists_large_host_attaining_uniform (t := t) (N := N) ht with
      ⟨n, hNn, hnthreshold, heq⟩
    have hp : packingRemainder t n ≤ b :=
      packingRemainder_le_of_bound (hN n hNn)
    omega

/-- A deterministic Ramsey-critical graph sufficient for a quadratic lower
bound: vertices with the same first coordinate form red cliques, and all
edges between different first coordinates are blue. -/
def blockGraph (a b : ℕ) : SimpleGraph (Fin a × Fin b) :=
  SimpleGraph.fromRel fun x y => x.1 = y.1

@[simp] theorem blockGraph_adj {a b : ℕ} {x y : Fin a × Fin b} :
    (blockGraph a b).Adj x y ↔ x ≠ y ∧ x.1 = y.1 := by
  simp [blockGraph, SimpleGraph.fromRel_adj, eq_comm]

/-- The elementary complete-multipartite construction gives the lower bound
`(t-1)(t-2) < R(t,t-1)`. -/
theorem quadratic_lt_ramseyOffdiag {t : ℕ} (ht : 3 ≤ t) :
    (t - 1) * (t - 2) < ramseyNumber t (t - 1) := by
  let G := blockGraph (t - 2) (t - 1)
  have hcf : G.CliqueFree t := by
    intro K hK
    have hinj : Set.InjOn Prod.snd
        (↑K : Set (Fin (t - 2) × Fin (t - 1))) := by
      intro x hx y hy hsnd
      by_cases hxy : x = y
      · exact hxy
      · have hadj := hK.isClique hx hy hxy
        exact Prod.ext (blockGraph_adj.1 hadj).2 hsnd
    have himage : (image Prod.snd K).card = K.card :=
      card_image_of_injOn hinj
    have himagele : (image Prod.snd K).card ≤ t - 1 := by
      have := card_le_card (subset_univ (image Prod.snd K))
      simpa using this
    rw [himage, hK.card_eq] at himagele
    omega
  have hif : G.IndepSetFree (t - 1) := by
    intro K hK
    have hinj : Set.InjOn Prod.fst (↑K : Set (Fin (t - 2) × Fin (t - 1))) := by
      intro x hx y hy hxy
      by_contra hne
      have hnot := hK.isIndepSet hx hy hne
      exact hnot (blockGraph_adj.2 ⟨hne, hxy⟩)
    have himage : (image Prod.fst K).card = K.card :=
      card_image_of_injOn hinj
    have himagele : (image Prod.fst K).card ≤ t - 2 := by
      have := card_le_card (subset_univ (image Prod.fst K))
      simpa using this
    rw [himage, hK.card_eq] at himagele
    omega
  by_contra hnot
  have hRle : ramseyNumber t (t - 1) ≤ (t - 1) * (t - 2) :=
    Nat.le_of_not_gt hnot
  have hprop : RamseyProperty t (t - 1) ((t - 1) * (t - 2)) :=
    ramseyProperty_of_ramseyNumber_le hRle
  have hcard : Fintype.card (Fin (t - 2) × Fin (t - 1)) =
      (t - 1) * (t - 2) := by
    simp [Nat.mul_comm]
  exact ramseyProperty_of_card hcard hprop G ⟨hcf, hif⟩

/-- In particular the eventual uniform remainder is not eventually bounded
by any fixed natural multiple of `t`; this formalizes the negative answer to
`f(t) ≪ t`. -/
theorem uniform_not_eventually_linear :
    ∀ C N : ℕ, ∃ t : ℕ, N ≤ t ∧ C * t < besUniformRemainder t := by
  intro C N
  let t := C + N + 3
  have ht : 3 ≤ t := by dsimp [t]; omega
  have hquad := quadratic_lt_ramseyOffdiag ht
  have hRle : ramseyNumber t (t - 1) ≤ besUniformRemainder t := by
    dsimp [besUniformRemainder]
    omega
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    omega
  · have hCt : C * t < (t - 1) * (t - 2) := by
      have ht1 : t - 1 = C + N + 2 := by dsimp [t]
      have ht2 : t - 2 = C + N + 1 := by dsimp [t]; omega
      rw [ht1, ht2]
      dsimp [t]
      nlinarith
    exact hCt.trans (hquad.trans_le hRle)

/-- The standard asymptotic-notation form of the second negative answer. -/
theorem uniformRemainder_not_isBigO_id :
    ¬ Asymptotics.IsBigO Filter.atTop
      (fun t : ℕ => (besUniformRemainder t : ℝ))
      (fun t : ℕ => (t : ℝ)) := by
  intro hO
  rcases hO.bound with ⟨c, hc⟩
  rcases Filter.eventually_atTop.1 hc with ⟨N, hN⟩
  let C := ⌈c⌉₊
  rcases uniform_not_eventually_linear C N with ⟨t, hNt, hCt⟩
  have hbound := hN t hNt
  have hcC : c ≤ (C : ℝ) := by
    dsimp [C]
    exact Nat.le_ceil c
  have hCtReal : (C : ℝ) * (t : ℝ) < (besUniformRemainder t : ℝ) := by
    exact_mod_cast hCt
  have hFnonneg : (0 : ℝ) ≤ (besUniformRemainder t : ℝ) := Nat.cast_nonneg _
  have htnonneg : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hbound' : (besUniformRemainder t : ℝ) ≤ c * (t : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hFnonneg,
      abs_of_nonneg htnonneg] using hbound
  nlinarith

/-- Elementary arithmetic used to feed powers of two into the probabilistic
Ramsey graph supplied by `Erdos1037.Lemma_Base`. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

/-- A convenient exponential subsequence of the classical random-graph
Ramsey lower bound.  The existing formally verified first-moment/random-graph
construction in `Erdos1037` supplies graphs with clique and independence
numbers at most `3 log₂ m`; setting `m=2^k` gives this statement. -/
theorem exponential_ramsey_subsequence :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 ^ k < ramseyNumber (3 * k + 2) (3 * k + 1) := by
  rcases Erdos1037.Lemma_Base with ⟨m₀, hm₀⟩
  refine ⟨m₀, ?_⟩
  intro k hk
  have hm : m₀ ≤ 2 ^ k := hk.trans (nat_le_two_pow k)
  rcases hm₀ (2 ^ k) hm with ⟨G, hclique, hindep, hdegree⟩
  have hlog : Real.logb 2 (2 ^ k : ℕ) = k := by
    rw [Nat.cast_pow, Real.logb_pow]
    norm_num [Real.logb]
  rw [hlog] at hclique hindep
  have hcliqueNat : G.cliqueNum ≤ 3 * k := by
    exact_mod_cast hclique
  have hindepNat : G.indepNum ≤ 3 * k := by
    exact_mod_cast hindep
  have hcf : G.CliqueFree (3 * k + 2) := by
    intro K hK
    have hle := hK.isClique.card_le_cliqueNum
    rw [hK.card_eq] at hle
    omega
  have hif : G.IndepSetFree (3 * k + 1) := by
    intro K hK
    have hle := hK.isIndepSet.card_le_indepNum
    rw [hK.card_eq] at hle
    omega
  by_contra hnot
  have hRle : ramseyNumber (3 * k + 2) (3 * k + 1) ≤ 2 ^ k :=
    Nat.le_of_not_gt hnot
  have hprop : RamseyProperty (3 * k + 2) (3 * k + 1) (2 ^ k) :=
    ramseyProperty_of_ramseyNumber_le hRle
  have hcard : Fintype.card (Fin (2 ^ k)) = 2 ^ k := by simp
  exact ramseyProperty_of_card hcard hprop G ⟨hcf, hif⟩

/-- Consequently the exact eventual packing remainder is exponentially large
along `t=3k+2`. -/
theorem exponential_uniform_subsequence :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 ^ k < besUniformRemainder (3 * k + 2) := by
  rcases exponential_ramsey_subsequence with ⟨k₀, hk₀⟩
  refine ⟨k₀, ?_⟩
  intro k hk
  have hram := hk₀ k hk
  have hle : ramseyNumber (3 * k + 2) (3 * k + 1) ≤
      besUniformRemainder (3 * k + 2) := by
    dsimp [besUniformRemainder]
    omega
  exact hram.trans_le hle

/-- The real `t`-th root of the optimal eventual uniform remainder. -/
def uniformRoot (t : ℕ) : ℝ :=
  (besUniformRemainder t : ℝ) ^ (1 / (t : ℝ))

/-- A power-of-two lower bound at `t=3k+2` forces the corresponding root to
stay above the fourth root of two once `k≥2`. -/
theorem fourthRootTwo_le_uniformRoot {k : ℕ} (hk : 2 ≤ k)
    (hpow : 2 ^ k ≤ besUniformRemainder (3 * k + 2)) :
    (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ uniformRoot (3 * k + 2) := by
  let t := 3 * k + 2
  have htpos : (0 : ℝ) < (t : ℝ) := by
    positivity
  have hexp : (1 : ℝ) / 4 ≤ (k : ℝ) / (t : ℝ) := by
    dsimp [t]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)]
    norm_num
    norm_cast
    omega
  have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤
      (besUniformRemainder t : ℝ) := by
    dsimp [t]
    exact_mod_cast hpow
  have heq :
      (((2 ^ k : ℕ) : ℝ) ^ (1 / (t : ℝ))) =
        (2 : ℝ) ^ ((k : ℝ) / (t : ℝ)) := by
    calc
      (((2 ^ k : ℕ) : ℝ) ^ (1 / (t : ℝ))) =
          (((2 : ℝ) ^ (k : ℝ)) ^ (1 / (t : ℝ))) := by
            norm_num only [Nat.cast_ofNat, Nat.cast_pow]
            rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((k : ℝ) * (1 / (t : ℝ))) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          (k : ℝ) (1 / (t : ℝ))).symm
      _ = (2 : ℝ) ^ ((k : ℝ) / (t : ℝ)) := by congr 1; ring
  calc
    (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ (2 : ℝ) ^ ((k : ℝ) / (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (((2 ^ k : ℕ) : ℝ) ^ (1 / (t : ℝ))) := heq.symm
    _ ≤ (besUniformRemainder t : ℝ) ^ (1 / (t : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hpowReal (by positivity)
    _ = uniformRoot (3 * k + 2) := by rfl

/-- The first question in Problem 1015 has a negative answer: the `t`-th
roots of the optimal eventual remainder do not converge to one. -/
theorem uniformRoot_not_tendsto_one :
    ¬ Filter.Tendsto uniformRoot Filter.atTop (nhds 1) := by
  intro hlim
  let c : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)
  have hc : 1 < c := by
    dsimp [c]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have heps : 0 < (c - 1) / 2 := by linarith
  rcases (Metric.tendsto_atTop.1 hlim) ((c - 1) / 2) heps with ⟨N, hN⟩
  rcases exponential_uniform_subsequence with ⟨k₀, hk₀⟩
  let k := max k₀ (max N 2)
  have hk₀k : k₀ ≤ k := le_max_left _ _
  have hNk : N ≤ k := (le_max_left N 2).trans (le_max_right k₀ (max N 2))
  have h2k : 2 ≤ k := (le_max_right N 2).trans (le_max_right k₀ (max N 2))
  have hpow : 2 ^ k ≤ besUniformRemainder (3 * k + 2) :=
    (hk₀ k hk₀k).le
  have hroot : c ≤ uniformRoot (3 * k + 2) := by
    simpa [c] using fourthRootTwo_le_uniformRoot h2k hpow
  have hNt : N ≤ 3 * k + 2 := by omega
  have hnear := hN (3 * k + 2) hNt
  have hroot_one : 1 ≤ uniformRoot (3 * k + 2) := hc.le.trans hroot
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hroot_one)] at hnear
  linarith

#print axioms erdos1015_exact
#print axioms erdos1015_eventual_uniform
#print axioms uniform_not_eventually_linear
#print axioms uniformRemainder_not_isBigO_id
#print axioms exponential_uniform_subsequence
#print axioms uniformRoot_not_tendsto_one

end Erdos1015
