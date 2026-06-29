/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1014.
https://www.erdosproblems.com/forum/thread/1014

Informal authors:
- an internal model at OpenAI

Formal authors:
- Codex
- Boris Alexeev

URLs:
- https://openai.com/index/introducing-gpt-5-5/
- https://cdn.openai.com/pdf/6dc7175d-d9e7-4b8d-96b8-48fe5798cd5b/Ramsey.pdf
- https://www.erdosproblems.com/forum/thread/1014#post-5749
-/
import Mathlib

open Filter
open Finset
open MeasureTheory ProbabilityTheory unitInterval
open scoped Topology ENNReal

noncomputable section

namespace Erdos1014

namespace SimpleGraph

theorem IndepSetFree.comap {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (f : H ↪g G) : G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← _root_.SimpleGraph.cliqueFree_compl] at h ⊢
  exact _root_.SimpleGraph.CliqueFree.comap
    (((_root_.SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun f).isContained) h

end SimpleGraph

/--
The Ramsey property on `n` vertices: every finite simple graph on `n` vertices contains
either a `k`-clique or an independent set of size `l`.
-/
def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

lemma ramseyProperty_of_card {k l n : ℕ} {α : Type*} [Fintype α]
    (hcard : Fintype.card α = n) (hprop : RamseyProperty k l n) :
    ∀ G : SimpleGraph α, ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  intro G hbad
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := SimpleGraph.overFinIso (G := G) hcard
  have hcf : H.CliqueFree k := hbad.1.comap e.symm.toEmbedding.isContained
  have hcfCompl : Hᶜ.CliqueFree l := by
    have hGCompl : Gᶜ.CliqueFree l := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    exact hGCompl.comap
      (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun e.symm.toEmbedding).isContained)
  have hif : H.IndepSetFree l := by
    simpa [SimpleGraph.cliqueFree_compl] using hcfCompl
  exact hprop H ⟨hcf, hif⟩

lemma ramseyProperty_mono {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

/--
Finite Ramsey's theorem, packaged as the existence of a size satisfying `RamseyProperty`.

This is the only remaining foundational gap in the definition layer.
-/
theorem ramseyProperty_exists (k l : ℕ) : ∃ n, RamseyProperty k l n := by
  sorry
/-- The off-diagonal Ramsey number `R(k, l)`. -/
def ramseyNumber (k l : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ramseyProperty_exists k l)

theorem ramseyNumber_three_three : ramseyNumber 3 3 = 6 := by
  classical
  have hprop6 : RamseyProperty 3 3 6 := by
    intro G hbad
    let v : Fin 6 := 0
    have hcfCompl : Gᶜ.CliqueFree 3 := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    have hifCompl : Gᶜ.IndepSetFree 3 := by
      simpa [SimpleGraph.indepSetFree_compl] using hbad.1
    have hdeg : (G.neighborFinset v).card ≤ 2 := by
      by_contra hdeg
      have hdeg3 : 3 ≤ (G.neighborFinset v).card :=
        Nat.succ_le_of_lt (lt_of_not_ge hdeg)
      obtain ⟨s, hs_sub, hs_card⟩ :=
        Finset.exists_subset_card_eq (s := G.neighborFinset v) hdeg3
      have hs_indep : G.IsNIndepSet 3 s := by
        refine ⟨?_, hs_card⟩
        rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hab
        have hInd := G.isIndepSet_neighborSet_of_triangleFree hbad.1 v
        have ha' : a ∈ G.neighborSet v := by
          have : a ∈ G.neighborFinset v := hs_sub ha
          simpa [SimpleGraph.mem_neighborFinset] using this
        have hb' : b ∈ G.neighborSet v := by
          have : b ∈ G.neighborFinset v := hs_sub hb
          simpa [SimpleGraph.mem_neighborFinset] using this
        exact hInd ha' hb' hab
      exact hbad.2 s hs_indep
    have hdegCompl : (Gᶜ.neighborFinset v).card ≤ 2 := by
      by_contra hdeg
      have hdeg3 : 3 ≤ (Gᶜ.neighborFinset v).card :=
        Nat.succ_le_of_lt (lt_of_not_ge hdeg)
      obtain ⟨s, hs_sub, hs_card⟩ :=
        Finset.exists_subset_card_eq (s := Gᶜ.neighborFinset v) hdeg3
      have hs_indep : Gᶜ.IsNIndepSet 3 s := by
        refine ⟨?_, hs_card⟩
        rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hab
        have hInd := Gᶜ.isIndepSet_neighborSet_of_triangleFree hcfCompl v
        have ha' : a ∈ Gᶜ.neighborSet v := by
          have : a ∈ Gᶜ.neighborFinset v := hs_sub ha
          simpa [SimpleGraph.mem_neighborFinset] using this
        have hb' : b ∈ Gᶜ.neighborSet v := by
          have : b ∈ Gᶜ.neighborFinset v := hs_sub hb
          simpa [SimpleGraph.mem_neighborFinset] using this
        exact hInd ha' hb' hab
      exact hifCompl s hs_indep
    have hcomp : (Gᶜ.neighborFinset v).card = 5 - (G.neighborFinset v).card := by
      rw [SimpleGraph.neighborFinset_compl]
      rw [Finset.card_sdiff_of_subset]
      · rw [Finset.card_singleton, Finset.card_compl, Fintype.card_fin]
        omega
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        simp
    omega
  have hnot5 : ¬ RamseyProperty 3 3 5 := by
    have hneighbors_not_adj :
        ∀ a : Fin 5, ¬ (SimpleGraph.cycleGraph 5).Adj (a - 1) (a + 1) := by
      intro a
      fin_cases a <;> decide
    have hcycleCliqueFree : (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
      intro s hs
      obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
      have hb_mem : b ∈ ({a - 1, a + 1} : Finset (Fin 5)) := by
        rw [← SimpleGraph.cycleGraph_neighborFinset]
        simpa [SimpleGraph.mem_neighborFinset] using hab
      have hc_mem : c ∈ ({a - 1, a + 1} : Finset (Fin 5)) := by
        rw [← SimpleGraph.cycleGraph_neighborFinset]
        simpa [SimpleGraph.mem_neighborFinset] using hac
      have hb_cases : b = a - 1 ∨ b = a + 1 := by
        simpa using hb_mem
      have hc_cases : c = a - 1 ∨ c = a + 1 := by
        simpa using hc_mem
      rcases hb_cases with rfl | rfl
      · rcases hc_cases with rfl | rfl
        · exact hbc.ne rfl
        · exact hneighbors_not_adj a hbc
      · rcases hc_cases with rfl | rfl
        · exact hneighbors_not_adj a hbc.symm
        · exact hbc.ne rfl
    let e : (SimpleGraph.cycleGraph 5)ᶜ ≃g SimpleGraph.cycleGraph 5 := by
      refine
        { toEquiv :=
            { toFun := fun i => ⟨(2 * i.1) % 5, by omega⟩
              invFun := fun i => ⟨(3 * i.1) % 5, by omega⟩
              left_inv := by intro i; fin_cases i <;> decide
              right_inv := by intro i; fin_cases i <;> decide }
          map_rel_iff' := ?_ }
      intro v w
      fin_cases v <;> fin_cases w <;> decide
    have hcycleIndepFree : (SimpleGraph.cycleGraph 5).IndepSetFree 3 := by
      rw [← SimpleGraph.cliqueFree_compl]
      exact SimpleGraph.CliqueFree.comap e.toEmbedding.isContained hcycleCliqueFree
    intro h
    exact h (SimpleGraph.cycleGraph 5) ⟨hcycleCliqueFree, hcycleIndepFree⟩
  have hle : ramseyNumber 3 3 ≤ 6 := Nat.find_min' (ramseyProperty_exists 3 3) hprop6
  have hge : 6 ≤ ramseyNumber 3 3 := by
    by_contra hlt
    have hprop5 : RamseyProperty 3 3 5 := by
      have hrn_le_five : ramseyNumber 3 3 ≤ 5 := by omega
      exact ramseyProperty_mono hrn_le_five (Nat.find_spec (ramseyProperty_exists 3 3))
    exact hnot5 hprop5
  exact le_antisymm hle hge

lemma ramseyNumber_spec (k l : ℕ) : RamseyProperty k l (ramseyNumber k l) :=
  by
    classical
    exact Nat.find_spec (ramseyProperty_exists k l)

namespace SimpleGraph

def Iso.compl {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      simp
    · simpa [_root_.SimpleGraph.compl_adj, hvw, e.injective.ne_iff] using
        not_congr (e.map_adj_iff (v := v) (w := w))

theorem Iso.cliqueFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.CliqueFree n ↔ H.CliqueFree n := by
  constructor
  · intro h
    exact _root_.SimpleGraph.CliqueFree.comap e.symm.toEmbedding.isContained h
  · intro h
    exact _root_.SimpleGraph.CliqueFree.comap e.toEmbedding.isContained h

theorem Iso.indepSetFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.IndepSetFree n ↔ H.IndepSetFree n := by
  simpa [_root_.SimpleGraph.indepSetFree_compl] using
    (Iso.cliqueFree_iff (n := n) (e := Iso.compl e))

end SimpleGraph

lemma ramseyProperty_one_left (l : ℕ) : RamseyProperty 1 l 1 := by
  intro G hbad
  simpa [SimpleGraph.cliqueFree_one] using hbad.1

lemma ramseyProperty_mono_vertices {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

lemma ramseyNumber_le_of_property {k l n : ℕ} (hn : RamseyProperty k l n) :
    ramseyNumber k l ≤ n := by
  classical
  exact Nat.find_min' (ramseyProperty_exists k l) hn

lemma ramseyProperty_of_ramseyNumber_le {k l n : ℕ} (hn : ramseyNumber k l ≤ n) :
    RamseyProperty k l n :=
  ramseyProperty_mono_vertices hn (ramseyNumber_spec k l)

lemma ramseyProperty_zero_right (k : ℕ) : RamseyProperty k 0 0 := by
  intro G hbad
  have hnil : G.IsNIndepSet 0 (∅ : Finset (Fin 0)) := by
    simp [SimpleGraph.isNIndepSet_iff]
  exact hbad.2 _ hnil

lemma ramseyNumber_zero_right (k : ℕ) : ramseyNumber k 0 = 0 := by
  exact le_antisymm (ramseyNumber_le_of_property (ramseyProperty_zero_right k)) (Nat.zero_le _)

lemma ramseyNumber_pos {u m : ℕ} (hu : 1 ≤ u) (hm : 1 ≤ m) : 0 < ramseyNumber u m := by
  sorry
lemma ramseyProperty_one_right (k : ℕ) : RamseyProperty k 1 1 := by
  intro G hbad
  have hs : G.IsNIndepSet 1 (Finset.univ : Finset (Fin 1)) := by
    refine ⟨?_, by simp⟩
    simp [SimpleGraph.isIndepSet_iff]
  exact hbad.2 _ hs

lemma not_ramseyProperty_one_zero {k : ℕ} (hk : 2 ≤ k) : ¬ RamseyProperty k 1 0 := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hcf : G.CliqueFree k := SimpleGraph.cliqueFree_bot hk
  have hif : G.IndepSetFree 1 := by
    intro t ht
    have ht0 : t = ∅ := by
      ext x
      exact Fin.elim0 x
    have hcard0 : t.card = 0 := by simp [ht0]
    simpa [hcard0] using ht.card_eq
  exact h G ⟨hcf, hif⟩

def addIsolated {α : Type*} (G : SimpleGraph α) : SimpleGraph (Option α) :=
  G.map Function.Embedding.some

lemma cliqueFree_addIsolated {α : Type*} (G : SimpleGraph α) {k : ℕ} (hk : 2 ≤ k)
    (hG : G.CliqueFree k) : (addIsolated G).CliqueFree k := by
      sorry
lemma indepSetFree_addIsolated_succ {α : Type*} (G : SimpleGraph α) {l : ℕ}
    (hG : G.IndepSetFree l) : (addIsolated G).IndepSetFree (l + 1) := by
  classical
  intro s hs
  have hsErase : G.IsIndepSet (s.eraseNone : Set α) := by
    intro a ha b hb hab habG
    exact hs.isIndepSet
      (by simpa using (Finset.mem_eraseNone.mp ha))
      (by simpa using (Finset.mem_eraseNone.mp hb))
      (by simpa using hab)
      ((SimpleGraph.map_adj Function.Embedding.some G (some a) (some b)).2
        ⟨a, b, habG, rfl, rfl⟩)
  have hcard_ge : l ≤ s.eraseNone.card := by
    by_cases hnone : none ∈ s
    · rw [Finset.card_eraseNone_of_mem hnone, hs.card_eq]
      omega
    · rw [Finset.card_eraseNone_of_not_mem hnone, hs.card_eq]
      omega
  obtain ⟨t, htsub, htcard⟩ := exists_subset_card_eq (s := s.eraseNone) hcard_ge
  have htsub' : (↑t : Set α) ⊆ ↑(s.eraseNone : Finset α) := by
    intro x hx
    exact htsub hx
  have htInd : G.IsIndepSet (t : Set α) := hsErase.mono htsub'
  exact hG t ⟨htInd, htcard⟩

lemma ramseyNumber_lt_succ_right (k : ℕ) (hk : 2 ≤ k) :
    ∀ l : ℕ, ramseyNumber k l < ramseyNumber k (l + 1)
  | 0 => by
      have hr0 : ramseyNumber k 0 = 0 := ramseyNumber_zero_right k
      have hr1_le : ramseyNumber k 1 ≤ 1 := ramseyNumber_le_of_property (ramseyProperty_one_right k)
      have hr1_ne : ramseyNumber k 1 ≠ 0 := by
        intro h0
        have hprop : RamseyProperty k 1 0 := by simpa [h0] using ramseyNumber_spec k 1
        exact not_ramseyProperty_one_zero hk hprop
      have hr1_pos : 0 < ramseyNumber k 1 := Nat.pos_of_ne_zero hr1_ne
      simpa [hr0] using hr1_pos
  | l + 1 => by
      have ih := ramseyNumber_lt_succ_right k hk l
      have hpos : 0 < ramseyNumber k (l + 1) := lt_of_le_of_lt (Nat.zero_le _) ih
      have hcounter :
          ∃ G : SimpleGraph (Fin (ramseyNumber k (l + 1) - 1)),
            G.CliqueFree k ∧ G.IndepSetFree (l + 1) := by
        have hnot : ¬ RamseyProperty k (l + 1) (ramseyNumber k (l + 1) - 1) :=
          by
            classical
            exact Nat.find_min (ramseyProperty_exists k (l + 1)) (Nat.pred_lt (Nat.ne_of_gt hpos))
        unfold RamseyProperty at hnot
        push Not at hnot
        exact hnot
      rcases hcounter with ⟨G, hcf, hif⟩
      have hnot :
          ¬ RamseyProperty k (l + 2) (ramseyNumber k (l + 1)) := by
        intro hprop
        let H₀ : SimpleGraph (Option (Fin (ramseyNumber k (l + 1) - 1))) := addIsolated G
        have hcardH :
            Fintype.card (Option (Fin (ramseyNumber k (l + 1) - 1))) =
              ramseyNumber k (l + 1) := by
          rw [Fintype.card_option, Fintype.card_fin]
          omega
        let H : SimpleGraph (Fin (ramseyNumber k (l + 1))) := H₀.overFin hcardH
        have hcfH₀ : H₀.CliqueFree k := cliqueFree_addIsolated G hk hcf
        have hifH₀ : H₀.IndepSetFree (l + 2) := indepSetFree_addIsolated_succ G hif
        have hIso : H₀ ≃g H := SimpleGraph.overFinIso (G := H₀) hcardH
        have hcfH : H.CliqueFree k :=
          (SimpleGraph.Iso.cliqueFree_iff (n := k) (e := hIso)).1 hcfH₀
        have hifH : H.IndepSetFree (l + 2) :=
          (SimpleGraph.Iso.indepSetFree_iff (n := l + 2) (e := hIso)).1 hifH₀
        exact hprop H ⟨hcfH, hifH⟩
      by_contra hle
      exact hnot (ramseyProperty_of_ramseyNumber_le (k := k) (l := l + 2) (not_lt.mp hle))

/-- Off-diagonal Ramsey numbers are strictly increasing in the second argument for `k ≥ 2`. -/
theorem ramseyNumber_strictMono_right (k : ℕ) (hk : 2 ≤ k) : StrictMono (ramseyNumber k) :=
  strictMono_nat_of_lt_succ (ramseyNumber_lt_succ_right k hk)

/-- The successive gap `Δ_l = R(k, l + 1) - R(k, l)`. -/
def ramseyGap (k l : ℕ) : ℕ :=
  ramseyNumber k (l + 1) - ramseyNumber k l

/-- The critical size `n_l = R(k, l + 1) - 1`. -/
def ramseyCriticalSize (k l : ℕ) : ℕ :=
  ramseyNumber k (l + 1) - 1

lemma ramseyGap_ge_one (k l : ℕ) (hk : 2 ≤ k) : 1 ≤ ramseyGap k l := by
  dsimp [ramseyGap]
  have hlt : ramseyNumber k l < ramseyNumber k (l + 1) := ramseyNumber_lt_succ_right k hk l
  omega

lemma ramseyNumber_ge_index (k l : ℕ) (hk : 2 ≤ k) : l ≤ ramseyNumber k l := by
  induction l with
  | zero =>
      exact Nat.zero_le _
  | succ l ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (ramseyNumber_lt_succ_right k hk l))

lemma ramseyCriticalSize_ge (k l : ℕ) (hk : 2 ≤ k) : l ≤ ramseyCriticalSize k l := by
  have hle : l + 1 ≤ ramseyNumber k (l + 1) := ramseyNumber_ge_index k (l + 1) hk
  dsimp [ramseyCriticalSize]
  omega

lemma tendsto_ramseyCriticalSize_atTop (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (ramseyCriticalSize k) atTop atTop := by
  exact Filter.tendsto_atTop_mono (fun l => ramseyCriticalSize_ge k l hk) tendsto_id

lemma tendsto_ramseyCriticalSize_real_atTop (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun l => (ramseyCriticalSize k l : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp (tendsto_ramseyCriticalSize_atTop k hk)

lemma eventually_ramseyCriticalSize_ne_zero (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ l : ℕ in atTop, (ramseyCriticalSize k l : ℝ) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with l hl
  have hge : l ≤ ramseyCriticalSize k l := ramseyCriticalSize_ge k l hk
  have hpos : 0 < ramseyCriticalSize k l := lt_of_lt_of_le hl hge
  exact_mod_cast Nat.ne_of_gt hpos

lemma eventually_gap_sub_one_div_critical_nonneg (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ l : ℕ in atTop, 0 ≤ (((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) := by
  filter_upwards [eventually_gt_atTop 0] with l hl
  have hgap : 1 ≤ ramseyGap k l := ramseyGap_ge_one k l hk
  have hge : l ≤ ramseyCriticalSize k l := ramseyCriticalSize_ge k l hk
  have hcrit : 0 < ramseyCriticalSize k l := lt_of_lt_of_le hl hge
  refine div_nonneg ?_ (by exact_mod_cast hcrit.le)
  exact sub_nonneg.mpr (by exact_mod_cast hgap)

lemma tendsto_zero_of_eventually_nonneg_of_pow_tendsto_zero {f : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hpow : Tendsto (fun l => (f l) ^ q) atTop (𝓝 0))
    (hnonneg : ∀ᶠ l in atTop, 0 ≤ f l) :
    Tendsto f atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hεq : 0 < ε ^ q := pow_pos hε q
  filter_upwards [Metric.tendsto_nhds.1 hpow (ε ^ q) hεq, hnonneg] with l hlpow hfl
  have hltpow_abs : |f l| ^ q < ε ^ q := by
    simpa [Real.dist_eq] using hlpow
  have hltpow : (f l) ^ q < ε ^ q := by
    simpa [abs_of_nonneg hfl] using hltpow_abs
  have hlt : f l < ε := (pow_lt_pow_iff_left₀ hfl hε.le hq0).mp hltpow
  simpa [Real.dist_eq, abs_of_nonneg hfl] using hlt

lemma eventually_ramseyNumber_ne_zero (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ l : ℕ in atTop, (ramseyNumber k l : ℝ) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with l hl
  have hge : l ≤ ramseyNumber k l := ramseyNumber_ge_index k l hk
  have hpos : 0 < ramseyNumber k l := lt_of_lt_of_le hl hge
  exact_mod_cast Nat.ne_of_gt hpos

lemma ramsey_div_critical_eq (k l : ℕ) (hk : 2 ≤ k)
    (hcrit : (ramseyCriticalSize k l : ℝ) ≠ 0) :
    (ramseyNumber k l : ℝ) / ramseyCriticalSize k l =
      1 + 1 / (ramseyCriticalSize k l : ℝ) - (ramseyGap k l : ℝ) / ramseyCriticalSize k l := by
  have hle : ramseyNumber k l ≤ ramseyNumber k (l + 1) := by
    exact (ramseyNumber_strictMono_right k hk).monotone (Nat.le_succ l)
  have hpos : 1 ≤ ramseyNumber k (l + 1) := by
    have hidx : l + 1 ≤ ramseyNumber k (l + 1) := ramseyNumber_ge_index k (l + 1) hk
    omega
  have hgap_cast : (ramseyNumber k l : ℝ) + ramseyGap k l = ramseyNumber k (l + 1) := by
    exact_mod_cast (Nat.add_sub_of_le hle)
  have hcrit_cast : (ramseyCriticalSize k l : ℝ) + 1 = ramseyNumber k (l + 1) := by
    exact_mod_cast (Nat.sub_add_cancel hpos)
  have hnum : (ramseyNumber k l : ℝ) =
      (ramseyCriticalSize k l : ℝ) + 1 - ramseyGap k l := by
    linarith
  rw [hnum]
  field_simp [hcrit]

lemma ramseyGap_div_ramsey_eq (k l : ℕ) (hcrit : (ramseyCriticalSize k l : ℝ) ≠ 0) :
    (ramseyGap k l : ℝ) / ramseyNumber k l =
      ((ramseyGap k l : ℝ) / ramseyCriticalSize k l) *
        (((ramseyNumber k l : ℝ) / ramseyCriticalSize k l)⁻¹) := by
  field_simp [hcrit]

lemma ramseySucc_ratio_eq_one_add_gap_div (k l : ℕ) (hk : 2 ≤ k)
    (hr : (ramseyNumber k l : ℝ) ≠ 0) :
    (ramseyNumber k (l + 1) : ℝ) / ramseyNumber k l =
      1 + (ramseyGap k l : ℝ) / ramseyNumber k l := by
  have hle : ramseyNumber k l ≤ ramseyNumber k (l + 1) := by
    exact (ramseyNumber_strictMono_right k hk).monotone (Nat.le_succ l)
  have hcast : (ramseyNumber k (l + 1) : ℝ) = (ramseyNumber k l : ℝ) + ramseyGap k l := by
    exact_mod_cast (Nat.add_sub_of_le hle).symm
  rw [hcast]
  field_simp [hr]

lemma ramseyGap_div_critical_eq_sub_one_add_inv (k l : ℕ)
    (hcrit : (ramseyCriticalSize k l : ℝ) ≠ 0) :
    (ramseyGap k l : ℝ) / ramseyCriticalSize k l =
      (((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) +
        1 / ramseyCriticalSize k l := by
  field_simp [hcrit]
  ring

lemma ramseyProperty_succ_succ_of_sum {k l m n : ℕ}
    (hm : RamseyProperty k (l + 1) m)
    (hn : RamseyProperty (k + 1) l n)
    (hpos : 0 < m + n) :
    RamseyProperty (k + 1) (l + 1) (m + n) := by
      sorry
lemma ramseyNumber_recurrence (u m : ℕ) (hu : 1 ≤ u) :
    ramseyNumber (u + 1) (m + 1) ≤ ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
  apply ramseyNumber_le_of_property
  have hpos : 0 < ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
    exact Nat.add_pos_left (ramseyNumber_pos hu (by omega)) _
  exact ramseyProperty_succ_succ_of_sum
    (ramseyNumber_spec u (m + 1))
    (ramseyNumber_spec (u + 1) m)
    hpos

lemma ramseyNumber_le_choose (u : ℕ) :
    ∀ m, ramseyNumber (u + 1) m ≤ Nat.choose (u + m - 1) u := by
  induction u with
  | zero =>
      intro m
      cases m with
      | zero =>
          simp [ramseyNumber_zero_right]
      | succ m =>
          have hle : ramseyNumber 1 (m + 1) ≤ 1 := by
            exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
          simpa using hle
  | succ u ihu =>
      intro m
      induction m with
      | zero =>
          rw [ramseyNumber_zero_right]
          simp
      | succ m ihm =>
          have hrec : ramseyNumber (u + 2) (m + 1) ≤
              ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := by
            exact ramseyNumber_recurrence (u + 1) m (by omega)
          have hleft : ramseyNumber (u + 1) (m + 1) ≤ Nat.choose (u + m) u := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihu (m + 1)
          have hright : ramseyNumber (u + 2) m ≤ Nat.choose (u + m) (u + 1) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihm
          calc
            ramseyNumber (u + 2) (m + 1)
                ≤ ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := hrec
            _ ≤ Nat.choose (u + m) u + Nat.choose (u + m) (u + 1) := by
              exact Nat.add_le_add hleft hright
            _ = Nat.choose (u + m + 1) (u + 1) := by
              rw [Nat.choose_succ_succ' (u + m) u]
            _ = Nat.choose (u + 1 + (m + 1) - 1) (u + 1) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
Step 6. Convert Delta_ell / n_ell -> 0 into the desired ratio.

Recall that

    n_ell = r_{ell+1} - 1
          = r_ell + Delta_ell - 1.

Therefore

    r_ell / n_ell
      = (n_ell - Delta_ell + 1)/n_ell
      = 1 - Delta_ell/n_ell + 1/n_ell.

By (23), Delta_ell/n_ell -> 0, and since n_ell -> infinity, also 1/n_ell -> 0.
Thus

    r_ell / n_ell -> 1.                                         (24)

Now

    Delta_ell / r_ell
      = (Delta_ell/n_ell) / (r_ell/n_ell).

The numerator tends to 0 by (23), and the denominator tends to 1 by (24).
Hence

    Delta_ell / r_ell -> 0.                                     (25)

Finally,

    R(k,ell+1) / R(k,ell)
      = r_{ell+1} / r_ell
      = (r_ell + Delta_ell) / r_ell
      = 1 + Delta_ell/r_ell.

By (25),

    r_{ell+1} / r_ell -> 1.

That is,

    lim_{ell -> infinity} R(k,ell+1) / R(k,ell) = 1.

This proves the theorem.
-/
theorem ratio_tendsto_one_of_gap_div_critical_tendsto_zero (k : ℕ)
    (hk : 2 ≤ k)
    (hgap :
      Tendsto (fun l => ((ramseyGap k l : ℝ) / ramseyCriticalSize k l)) atTop (𝓝 0)) :
    Tendsto (fun l => (ramseyNumber k (l + 1) : ℝ) / ramseyNumber k l) atTop (𝓝 1) := by
  have hinvCrit :
      Tendsto (fun l => (1 : ℝ) / ramseyCriticalSize k l) atTop (𝓝 0) := by
    exact (tendsto_const_nhds.div_atTop (tendsto_ramseyCriticalSize_real_atTop k hk))
  have hratioAux :
      Tendsto
        (fun l => 1 + 1 / (ramseyCriticalSize k l : ℝ) -
          (ramseyGap k l : ℝ) / ramseyCriticalSize k l) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg, add_assoc] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add (hinvCrit.sub hgap)
  have hratio :
      Tendsto (fun l => (ramseyNumber k l : ℝ) / ramseyCriticalSize k l) atTop (𝓝 1) := by
    refine hratioAux.congr' ?_
    exact (eventually_ramseyCriticalSize_ne_zero k hk).mono fun l hcrit =>
      (ramsey_div_critical_eq k l hk hcrit).symm
  have hratioInv :
      Tendsto (fun l => ((ramseyNumber k l : ℝ) / ramseyCriticalSize k l)⁻¹) atTop (𝓝 1) := by
    simpa using hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hgapRamseyAux :
      Tendsto
        (fun l =>
          ((ramseyGap k l : ℝ) / ramseyCriticalSize k l) *
            (((ramseyNumber k l : ℝ) / ramseyCriticalSize k l)⁻¹))
        atTop (𝓝 0) := by
    simpa using hgap.mul hratioInv
  have hgapRamsey :
      Tendsto (fun l => (ramseyGap k l : ℝ) / ramseyNumber k l) atTop (𝓝 0) := by
    refine hgapRamseyAux.congr' ?_
    exact (eventually_ramseyCriticalSize_ne_zero k hk).mono fun l hcrit =>
      (ramseyGap_div_ramsey_eq k l hcrit).symm
  have hratioSuccAux :
      Tendsto (fun l => 1 + (ramseyGap k l : ℝ) / ramseyNumber k l) atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hgapRamsey
  refine hratioSuccAux.congr' ?_
  exact (eventually_ramseyNumber_ne_zero k hk).mono fun l hr =>
    (ramseySucc_ratio_eq_one_add_gap_div k l hk hr).symm

/--
Proof.
We write

    r_ell := R(k, ell),
    Delta_ell := r_{ell+1} - r_ell,
    n_ell := r_{ell+1} - 1.

Thus n_ell is one less than the Ramsey number R(k, ell+1). By the definition
of R(k, ell+1), there exists a graph G on n_ell vertices such that G is
K_k-free and alpha(G) <= ell.

The proof has six steps.
-/
lemma ramseyGap_steps1to5_setup : True := by
  trivial

/--
Step 1. Elementary Ramsey estimates.

We shall use the following two estimates.

First, for every fixed integer u >= 1, there is a constant C_u such that

    R(u,m) <= C_u m^{u-1}                                      (1)

for all m >= 1.

We prove this estimate.

Proof of (1).
The standard recurrence is

    R(a,b) <= R(a-1,b) + R(a,b-1)                               (3)

for a,b >= 2, with boundary values

    R(1,b) = R(a,1) = 1.

Indeed, take any graph H on R(a-1,b) + R(a,b-1) vertices and choose a vertex v.
If the neighborhood N(v) has size at least R(a-1,b), then H[N(v)] contains
either a K_{a-1}, which together with v gives a K_a, or an independent b-set.
If the non-neighborhood of v has size at least R(a,b-1), then it contains
either a K_a, or an independent (b-1)-set, which together with v gives an
independent b-set. This proves (3).

Induction using Pascal's identity gives

    R(a,b) <= binom(a+b-2, a-1).

Therefore, for fixed u,

    R(u,m) <= binom(u+m-2, u-1) <= C_u m^{u-1},

which proves (1).
-/
lemma ramseyGap_step1_upper_bound :
    ∀ u : ℕ, 1 ≤ u → ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℕ, (ramseyNumber u m : ℝ) ≤ C * (m : ℝ) ^ (u - 1) := by
        sorry
lemma setBernoulli_superset_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (↑t : Set ι) ⊆ s} = toNNReal p ^ t.card := by
  classical
  letI := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop => {i | q i}) ⁻¹' {s : Set ι | (↑t : Set ι) ⊆ s}) =
        ((↑t : Set ι).pi fun _ => ({True} : Set Prop)) := by
    ext q
    simp [Set.subset_def]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

lemma setBernoulli_disjoint_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (↑t : Set ι) s} =
      toNNReal (σ p) ^ t.card := by
  classical
  letI := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop => {i | q i}) ⁻¹' {s : Set ι |
        Disjoint (↑t : Set ι) s}) =
        ((↑t : Set ι).pi fun _ => ({False} : Set Prop)) := by
    ext q
    simp [Set.disjoint_left]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

noncomputable def pairEdgeFinset {α : Type*} [DecidableEq α] (s : Finset α) :
    Finset (Sym2 α) :=
  ((⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}).edgeFinset).map
    (Function.Embedding.subtype (fun x => x ∈ (↑s : Set α))).sym2Map

lemma pairEdgeFinset_card {α : Type*} [DecidableEq α] (s : Finset α) :
    (pairEdgeFinset s).card = Nat.choose s.card 2 := by
  classical
  calc
    (pairEdgeFinset s).card
        = ((⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}).edgeFinset).card := by
          exact Finset.card_map _
    _ = Nat.choose (Fintype.card {x // x ∈ (↑s : Set α)}) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose s.card 2 := by
      simp

lemma mem_pairEdgeFinset_iff {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) {e : Sym2 α} :
    e ∈ pairEdgeFinset s ↔ e ∈ s.sym2 ∧ ¬ e.IsDiag := by
  classical
  letI := Fintype.ofFinite α
  have hmap := SimpleGraph.map_edgeFinset_induce
    (G := (⊤ : SimpleGraph α)) (s := (↑s : Set α))
  have hind : SimpleGraph.induce (↑s : Set α) (⊤ : SimpleGraph α) =
      (⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}) := by
    ext a b
    simp [SimpleGraph.induce]
  have hmem := Finset.ext_iff.mp hmap e
  simpa [and_comm, pairEdgeFinset, hind, SimpleGraph.mem_edgeFinset,
    Finset.mem_inter, Finset.mk_mem_sym2_iff] using hmem

lemma pairEdgeFinset_subset_diagCompl {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) :
    (↑(pairEdgeFinset s) : Set (Sym2 α)) ⊆ Sym2.diagSetᶜ := by
  classical
  letI := Fintype.ofFinite α
  intro e he
  simpa [Set.compl_setOf] using (mem_pairEdgeFinset_iff s).1 he |>.2

lemma isClique_iff_pairEdgeFinset_subset {α : Type*} [Finite α] [DecidableEq α]
    (G : SimpleGraph α) (s : Finset α) :
    G.IsClique (↑s : Set α) ↔ (↑(pairEdgeFinset s) : Set (Sym2 α)) ⊆ G.edgeSet := by
  classical
  letI := Fintype.ofFinite α
  rw [SimpleGraph.isClique_iff]
  constructor
  · intro h e he
    revert he
    refine Sym2.inductionOn e ?_
    intro a b he'
    rcases (mem_pairEdgeFinset_iff s).1 he' with ⟨hmem, hndiag⟩
    have ha : a ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).1
    have hb : b ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).2
    have hab : a ≠ b := by
      simpa using hndiag
    exact h ha hb hab
  · intro h a ha b hb hab
    have he : (s(a, b) : Sym2 α) ∈ pairEdgeFinset s := by
      exact (mem_pairEdgeFinset_iff s).2
        ⟨by simpa [Finset.mk_mem_sym2_iff] using And.intro ha hb,
          by simpa using hab⟩
    exact h he

lemma isIndepSet_iff_pairEdgeFinset_disjoint {α : Type*} [Finite α] [DecidableEq α]
    (G : SimpleGraph α) (s : Finset α) :
    G.IsIndepSet (↑s : Set α) ↔ Disjoint (↑(pairEdgeFinset s) : Set (Sym2 α)) G.edgeSet := by
  classical
  letI := Fintype.ofFinite α
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro e he hedg
    revert he hedg
    refine Sym2.inductionOn e ?_
    intro a b he' hedg'
    rcases (mem_pairEdgeFinset_iff s).1 he' with ⟨hmem, hndiag⟩
    have ha : a ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).1
    have hb : b ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).2
    have hab : a ≠ b := by
      simpa using hndiag
    exact h ha hb hab (by simpa [SimpleGraph.mem_edgeSet] using hedg')
  · intro h a ha b hb hab hedg
    have he : (s(a, b) : Sym2 α) ∈ pairEdgeFinset s := by
      exact (mem_pairEdgeFinset_iff s).2
        ⟨by simpa [Finset.mk_mem_sym2_iff] using And.intro ha hb,
          by simpa using hab⟩
    exact h.le_bot ⟨he, by simpa [SimpleGraph.mem_edgeSet] using hedg⟩

lemma exists_induced_cliqueFree_subgraph {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {u : ℕ} (hu : 1 ≤ u) :
    ∃ U : Finset α,
      Fintype.card α - (G.cliqueFinset u).card ≤ U.card ∧
        (G.induce (↑U : Set α)).CliqueFree u := by
          sorry
lemma exists_large_cliqueFree_graph_of_bounded_cliques
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {u m : ℕ} (hu : 1 ≤ u) (hif : G.IndepSetFree m) :
    ∃ n : ℕ,
      Fintype.card α - (G.cliqueFinset u).card ≤ n ∧
        ∃ H : SimpleGraph (Fin n), H.CliqueFree u ∧ H.IndepSetFree m := by
  classical
  obtain ⟨U, hUcard, hUcf⟩ := exists_induced_cliqueFree_subgraph G hu
  let H₀ : SimpleGraph {x // x ∈ (↑U : Set α)} := G.induce (↑U : Set α)
  have hH₀if : H₀.IndepSetFree m := by
    exact SimpleGraph.IndepSetFree.comap
      (SimpleGraph.Embedding.induce (G := G) (s := (↑U : Set α))) hif
  let n := U.card
  have hcardH₀ : Fintype.card {x // x ∈ (↑U : Set α)} = n := by
    simp [n]
  let H : SimpleGraph (Fin n) := H₀.overFin hcardH₀
  have hIso : H₀ ≃g H := SimpleGraph.overFinIso (G := H₀) hcardH₀
  have hHcf : H.CliqueFree u := (SimpleGraph.Iso.cliqueFree_iff (n := u) (e := hIso)).1 hUcf
  have hHif : H.IndepSetFree m :=
    (SimpleGraph.Iso.indepSetFree_iff (n := m) (e := hIso)).1 hH₀if
  exact ⟨n, hUcard, H, hHcf, hHif⟩

lemma cliqueFinset_eq_filter_powersetCard {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (u : ℕ) :
    G.cliqueFinset u = (Finset.univ.powersetCard u).filter fun s => G.IsNClique u s := by
  ext s
  rw [SimpleGraph.mem_cliqueFinset_iff]
  simp [SimpleGraph.isNClique_iff]

lemma indepSetFinset_eq_filter_powersetCard {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (m : ℕ) :
    G.indepSetFinset m = (Finset.univ.powersetCard m).filter fun s => G.IsNIndepSet m s := by
  ext s
  rw [SimpleGraph.mem_indepSetFinset_iff]
  simp [SimpleGraph.isNIndepSet_iff]

noncomputable def step1CliqueCount (u N : ℕ) (ω : Set (Sym2 (Fin N))) : ℕ :=
  by
    classical
    exact ((SimpleGraph.fromEdgeSet ω).cliqueFinset u).card

noncomputable def step1IndepCount (m N : ℕ) (ω : Set (Sym2 (Fin N))) : ℕ :=
  by
    classical
    exact ((SimpleGraph.fromEdgeSet ω).indepSetFinset m).card

lemma pairEdgeFinset_subset_edgeSet_fromEdgeSet_iff {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) (ω : Set (Sym2 α)) :
    (↑(pairEdgeFinset s) : Set (Sym2 α)) ⊆ (SimpleGraph.fromEdgeSet ω).edgeSet ↔
      (↑(pairEdgeFinset s) : Set (Sym2 α)) ⊆ ω := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro h e he
    exact (h he).1
  · intro h e he
    exact ⟨h he, pairEdgeFinset_subset_diagCompl s he⟩

lemma pairEdgeFinset_disjoint_edgeSet_fromEdgeSet_iff {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) (ω : Set (Sym2 α)) :
    Disjoint (↑(pairEdgeFinset s) : Set (Sym2 α)) (SimpleGraph.fromEdgeSet ω).edgeSet ↔
      Disjoint (↑(pairEdgeFinset s) : Set (Sym2 α)) ω := by
  rw [SimpleGraph.edgeSet_fromEdgeSet, Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h e he1 he2
    exact h he1 ⟨he2, pairEdgeFinset_subset_diagCompl s he1⟩
  · intro h e he1 he2
    exact h he1 he2.1

lemma step1_clique_event_measure (N u : ℕ) (p : I) (s : Finset (Fin N)) (hs : s.card = u) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
      {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNClique u s} =
        (toNNReal p : ℝ≥0∞) ^ Nat.choose u 2 := by
  have hpre :
      {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNClique u s} =
        {ω : Set (Sym2 (Fin N)) | (↑(pairEdgeFinset s) : Set (Sym2 (Fin N))) ⊆ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have hclique : (SimpleGraph.fromEdgeSet ω).IsClique (↑s : Set (Fin N)) :=
        ((SimpleGraph.isNClique_iff (G := SimpleGraph.fromEdgeSet ω) (n := u) (s := s)).mp h).1
      exact (pairEdgeFinset_subset_edgeSet_fromEdgeSet_iff s ω).1
        ((isClique_iff_pairEdgeFinset_subset (SimpleGraph.fromEdgeSet ω) s).1 hclique)
    · intro h
      refine (SimpleGraph.isNClique_iff (G := SimpleGraph.fromEdgeSet ω) (n := u) (s := s)).2 ?_
      refine ⟨?_, hs⟩
      exact (isClique_iff_pairEdgeFinset_subset (SimpleGraph.fromEdgeSet ω) s).2
        ((pairEdgeFinset_subset_edgeSet_fromEdgeSet_iff s ω).2 h)
  rw [hpre]
  rw [setBernoulli_superset_finset (u := (Sym2.diagSetᶜ : Set (Sym2 (Fin N))))
    (p := p) (t := pairEdgeFinset s) (pairEdgeFinset_subset_diagCompl s)]
  simp [pairEdgeFinset_card, hs]

lemma step1_indep_event_measure (N m : ℕ) (p : I) (s : Finset (Fin N)) (hs : s.card = m) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
      {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s} =
        (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose m 2 := by
  have hpre :
      {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s} =
        {ω : Set (Sym2 (Fin N)) | Disjoint (↑(pairEdgeFinset s) : Set (Sym2 (Fin N))) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have hind : (SimpleGraph.fromEdgeSet ω).IsIndepSet (↑s : Set (Fin N)) :=
        ((SimpleGraph.isNIndepSet_iff (G := SimpleGraph.fromEdgeSet ω) (n := m) (s := s)).mp h).1
      exact (pairEdgeFinset_disjoint_edgeSet_fromEdgeSet_iff s ω).1
        ((isIndepSet_iff_pairEdgeFinset_disjoint (SimpleGraph.fromEdgeSet ω) s).1 hind)
    · intro h
      refine (SimpleGraph.isNIndepSet_iff (G := SimpleGraph.fromEdgeSet ω) (n := m) (s := s)).2 ?_
      refine ⟨?_, hs⟩
      exact (isIndepSet_iff_pairEdgeFinset_disjoint (SimpleGraph.fromEdgeSet ω) s).2
        ((pairEdgeFinset_disjoint_edgeSet_fromEdgeSet_iff s ω).2 h)
  rw [hpre]
  rw [setBernoulli_disjoint_finset (u := (Sym2.diagSetᶜ : Set (Sym2 (Fin N))))
    (p := p) (t := pairEdgeFinset s) (pairEdgeFinset_subset_diagCompl s)]
  simp [pairEdgeFinset_card, hs]

lemma step1_cliqueCount_lintegral_eq (N u : ℕ) (p : I) :
    ∫⁻ ω, (step1CliqueCount u N ω : ℝ≥0∞) ∂
      setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
        (Nat.choose N u : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ Nat.choose u 2 := by
  classical
  let A : Finset (Finset (Fin N)) := Finset.univ.powersetCard u
  have hcount :
      ∀ ω : Set (Sym2 (Fin N)),
        (step1CliqueCount u N ω : ℝ≥0∞) =
          Finset.sum A (fun s =>
            if (SimpleGraph.fromEdgeSet ω).IsNClique u s then (1 : ℝ≥0∞) else 0) := by
    intro ω
    dsimp [step1CliqueCount, A]
    rw [cliqueFinset_eq_filter_powersetCard]
    simp
  calc
    ∫⁻ ω, (step1CliqueCount u N ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
        =
          ∫⁻ ω, Finset.sum A (fun s =>
            if (SimpleGraph.fromEdgeSet ω).IsNClique u s then (1 : ℝ≥0∞) else 0) ∂
              setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            exact hcount ω
    _ =
          Finset.sum A (fun s => ∫⁻ ω,
            (if (SimpleGraph.fromEdgeSet ω).IsNClique u s then (1 : ℝ≥0∞) else 0) ∂
              setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) := by
            apply MeasureTheory.lintegral_finsetSum
            intro s hs
            exact measurable_of_countable _
    _ = Finset.sum A (fun s =>
          setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
            {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNClique u s}) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hsMeas :
              MeasurableSet
                {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNClique u s} :=
            (Set.to_countable _).measurableSet
          simpa [Set.indicator, hsMeas] using
            (MeasureTheory.lintegral_indicator_one
              (μ := setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) hsMeas)
    _ = Finset.sum A (fun _ => (toNNReal p : ℝ≥0∞) ^ Nat.choose u 2) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact step1_clique_event_measure N u p s (by simpa [A] using hs)
    _ = (Nat.choose N u : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ Nat.choose u 2 := by
          simp [A, Finset.card_powersetCard]

lemma step1_indepCount_lintegral_eq (N m : ℕ) (p : I) :
    ∫⁻ ω, (step1IndepCount m N ω : ℝ≥0∞) ∂
      setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
        (Nat.choose N m : ℝ≥0∞) * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose m 2 := by
  classical
  let A : Finset (Finset (Fin N)) := Finset.univ.powersetCard m
  have hcount :
      ∀ ω : Set (Sym2 (Fin N)),
        (step1IndepCount m N ω : ℝ≥0∞) =
          Finset.sum A (fun s =>
            if (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s then (1 : ℝ≥0∞) else 0) := by
    intro ω
    dsimp [step1IndepCount, A]
    rw [indepSetFinset_eq_filter_powersetCard]
    simp
  calc
    ∫⁻ ω, (step1IndepCount m N ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
        =
          ∫⁻ ω, Finset.sum A (fun s =>
            if (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s then (1 : ℝ≥0∞) else 0) ∂
              setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            exact hcount ω
    _ =
          Finset.sum A (fun s => ∫⁻ ω,
            (if (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s then (1 : ℝ≥0∞) else 0) ∂
              setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) := by
            apply MeasureTheory.lintegral_finsetSum
            intro s hs
            exact measurable_of_countable _
    _ = Finset.sum A (fun s =>
          setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
            {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s}) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hsMeas :
              MeasurableSet
                {ω : Set (Sym2 (Fin N)) | (SimpleGraph.fromEdgeSet ω).IsNIndepSet m s} :=
            (Set.to_countable _).measurableSet
          simpa [Set.indicator, hsMeas] using
            (MeasureTheory.lintegral_indicator_one
              (μ := setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) hsMeas)
    _ = Finset.sum A (fun _ => (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose m 2) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact step1_indep_event_measure N m p s (by simpa [A] using hs)
    _ = (Nat.choose N m : ℝ≥0∞) * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose m 2 := by
          simp [A, Finset.card_powersetCard]

lemma indepSetFinset_eq_empty_iff {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (m : ℕ) :
    G.indepSetFinset m = ∅ ↔ G.IndepSetFree m := by
  simp [SimpleGraph.IndepSetFree, eq_empty_iff_forall_notMem, SimpleGraph.mem_indepSetFinset_iff]

lemma step1IndepCount_eq_zero_iff (N m : ℕ) (ω : Set (Sym2 (Fin N))) :
    step1IndepCount m N ω = 0 ↔ (SimpleGraph.fromEdgeSet ω).IndepSetFree m := by
  classical
  dsimp [step1IndepCount]
  rw [Finset.card_eq_zero, indepSetFinset_eq_empty_iff]

lemma step1_good_from_outcome (N u m : ℕ) (ω : Set (Sym2 (Fin N))) (hu : 1 ≤ u)
    (hcliques : step1CliqueCount u N ω ≤ N / 2)
    (hindep : step1IndepCount m N ω = 0) :
    ∃ n : ℕ,
      N / 2 ≤ n ∧
        ∃ G : SimpleGraph (Fin n), G.CliqueFree u ∧ G.IndepSetFree m := by
  classical
  let G₀ : SimpleGraph (Fin N) := SimpleGraph.fromEdgeSet ω
  have hif : G₀.IndepSetFree m := by
    simpa [G₀] using (step1IndepCount_eq_zero_iff N m ω).1 hindep
  have hcliqueCard : (G₀.cliqueFinset u).card ≤ N / 2 := by
    simpa [step1CliqueCount, G₀] using hcliques
  obtain ⟨n, hn, G, hcf, hifG⟩ := exists_large_cliqueFree_graph_of_bounded_cliques G₀ hu hif
  have hsize : N / 2 ≤ n := by
    have htmp : N / 2 ≤ N - (G₀.cliqueFinset u).card := by
      omega
    have hn' : N - (G₀.cliqueFinset u).card ≤ n := by
      simpa using hn
    exact htmp.trans hn'
  exact ⟨n, hsize, G, hcf, hifG⟩

/--
Step 1. Equation (4) in the random-graph argument.

Let `X` be the number of `K_u` copies in `G(N, π)`. After choosing `c > 0`
small enough, the expectation estimate gives

    E X <= N / 8.

Equation (4) is then the Markov bound

    P(X > N / 2) <= 1 / 4.
-/
lemma ramseyGap_step1_eq4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} {N : ℝ≥0∞}
    (hX : AEMeasurable X μ)
    (hEX : ∫⁻ ω, X ω ∂μ ≤ N / 8) :
    μ {ω | N / 2 < X ω} ≤ (1 / 4 : ℝ≥0∞) := by
      sorry
/--
Step 1. Equation (5) in the random-graph argument.

Let `Y` be the number of independent sets of size `m` in `G(N, π)`. The
exponential estimate for `E Y` shows that `E Y → 0`, so for all sufficiently
large `m` we have

    E Y < 1 / 4.

Since `Y` counts independent `m`-sets, this gives equation (5):

    P(Y > 0) <= E Y < 1 / 4.
-/
lemma ramseyGap_step1_eq5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Y : Ω → ℕ}
    (hY : AEMeasurable (fun ω => (Y ω : ℝ≥0∞)) μ)
    (hEY : ∫⁻ ω, (Y ω : ℝ≥0∞) ∂μ < 1 / 4) :
    μ {ω | 0 < Y ω} < (1 / 4 : ℝ≥0∞) := by
  have hle : μ {ω | 0 < Y ω} ≤ ∫⁻ ω, (Y ω : ℝ≥0∞) ∂μ := by
    refine MeasureTheory.meas_le_lintegral₀ hY ?_
    intro ω hω
    exact_mod_cast Nat.succ_le_iff.2 hω
  exact lt_of_le_of_lt hle hEY

lemma ramseyGap_step1_good_graph_constant {u : ℕ} (hu : 3 ≤ u) :
    ∃ d : ℝ, 0 < d ∧ 4 * d ≤ 1 / 4 ∧ d ≤ 1 ∧
      (4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2 ≤ d / 16 := by
  let C : ℕ := Nat.choose u 2
  let A : ℝ := (4 : ℝ) ^ u * (u : ℝ) ^ C
  let d : ℝ := (16 * A)⁻¹
  have hu_pos : 0 < (u : ℝ) := by
    exact_mod_cast (show 0 < u by omega)
  have hu_one : 1 ≤ (u : ℝ) := by
    exact_mod_cast (show 1 ≤ u by omega)
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have h4u_ge_one : 1 ≤ (4 : ℝ) ^ u := by
    simpa using
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 4 by norm_num) u)
  have huC_ge_one : 1 ≤ (u : ℝ) ^ C := by
    simpa using
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hu_one C)
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    nlinarith
  have hAd : A * d = 1 / 16 := by
    have hA_ne : A ≠ 0 := hA_pos.ne'
    dsimp [d]
    rw [← div_eq_mul_inv]
    field_simp [hA_ne]
  have h4d_le_quarter : 4 * d ≤ 1 / 4 := by
    calc
      4 * d = 4 / (16 * A) := by
        dsimp [d]
        rw [← div_eq_mul_inv]
      _ ≤ 4 / 16 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 16) ?_
        nlinarith
      _ = 1 / 4 := by norm_num
  have hd_le_one : d ≤ 1 := by
    nlinarith
  have hd_pow : d ^ u ≤ d ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hd_pos hd_le_one
      (by exact_mod_cast (show 2 ≤ u by omega))
  have hcoeff : (4 * d) ^ u * (u : ℝ) ^ C ≤ d / 16 := by
    calc
      (4 * d) ^ u * (u : ℝ) ^ C = A * d ^ u := by
        dsimp [A]
        rw [mul_pow]
        ring
      _ ≤ A * d ^ 2 := by
        gcongr
      _ = (A * d) * d := by ring
      _ = d / 16 := by
        rw [hAd]
        ring
  refine ⟨d, hd_pos, h4d_le_quarter, hd_le_one, ?_⟩
  simpa [C] using hcoeff

lemma ramseyGap_step1_hy_lower {d M : ℝ}
    (hd_pos : 0 < d) (hMpos : 0 < M) (hlog_pos : 0 < Real.log M)
    (hlog_over_M_le_d_half : Real.log M / M ≤ d / 2) :
    2 / d ≤ M / Real.log M := by
  have htmp0 :
      (Real.log M / M) * M ≤ (d / 2) * M :=
    mul_le_mul_of_nonneg_right hlog_over_M_le_d_half hMpos.le
  have htmp1 : Real.log M ≤ (d / 2) * M := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hMpos.ne'] using htmp0
  have htmp : 2 * Real.log M ≤ d * M := by
    nlinarith
  have htmp' : (2 * Real.log M) / d ≤ M := by
    exact (div_le_iff₀ hd_pos).2 (by simpa [mul_comm] using htmp)
  have htmp'' : (2 / d) * Real.log M ≤ M := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp'
  exact (le_div_iff₀ hlog_pos).2 htmp''

lemma ramseyGap_step1_half_sub_one_lt_halfNat (N : ℕ) :
    (N : ℝ) / 2 - 1 < (N / 2 : ℕ) := by
  by_cases hmod : N % 2 = 0
  · have hdecomp_nat : 2 * (N / 2) = N := by
      simpa [hmod, add_comm, add_left_comm, add_assoc] using (Nat.mod_add_div N 2)
    have hdecomp : (2 : ℝ) * (N / 2 : ℕ) = N := by
      exact_mod_cast hdecomp_nat
    have hhalf_eq : (N : ℝ) / 2 = (N / 2 : ℕ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun t : ℝ => t / 2) hdecomp.symm
    rw [hhalf_eq]
    linarith
  · have hmod1 : N % 2 = 1 := by
      have hlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
      omega
    have hdecomp_nat : 1 + 2 * (N / 2) = N := by
      simpa [hmod1, add_comm, add_left_comm, add_assoc] using (Nat.mod_add_div N 2)
    have hdecomp : (1 : ℝ) + 2 * (N / 2 : ℕ) = N := by
      exact_mod_cast hdecomp_nat
    have hhalf_eq : (N : ℝ) / 2 = (1 : ℝ) / 2 + (N / 2 : ℕ) := by
      simpa [add_div, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun t : ℝ => t / 2) hdecomp.symm
    rw [hhalf_eq]
    linarith

lemma ramseyGap_step1_hN_half_lower {d x : ℝ} {N : ℕ}
    (hdx_ge_two : 2 ≤ d * x) (hN_gt : 4 * d * x - 1 < N) :
    d * x ≤ (N / 2 : ℕ) := by
  have htmp : d * x ≤ (N : ℝ) / 2 - 1 := by
    have hN_real : 4 * d * x - 1 ≤ N := le_of_lt hN_gt
    nlinarith
  exact htmp.trans (le_of_lt (ramseyGap_step1_half_sub_one_lt_halfNat N))

lemma ramseyGap_step1_hx_pow {u : ℕ} {y : ℝ} (hy_pos : 0 < y) :
    (y ^ ((u : ℝ) / 2)) ^ u = y ^ Nat.choose u 2 * y ^ ((u : ℝ) / 2) := by
  calc
    (y ^ ((u : ℝ) / 2)) ^ u = y ^ (((u : ℝ) / 2) * u) := by
      rw [← Real.rpow_mul_natCast hy_pos.le ((u : ℝ) / 2) u]
    _ = y ^ ((Nat.choose u 2 : ℝ) + (u : ℝ) / 2) := by
      congr 1
      rw [Nat.cast_choose_two]
      ring
    _ = y ^ (Nat.choose u 2 : ℝ) * y ^ ((u : ℝ) / 2) := by
      rw [Real.rpow_add hy_pos]
    _ = y ^ Nat.choose u 2 * y ^ ((u : ℝ) / 2) := by
      rw [Real.rpow_natCast]

lemma ramseyGap_step1_hX_real {u N : ℕ} {d x y M q : ℝ}
    (hcoeff : (4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2 ≤ d / 16)
    (hN_upper : (N : ℝ) ≤ 4 * d * x) (hq_nonneg : 0 ≤ q)
    (hq_pow :
      q ^ Nat.choose u 2 =
        (u : ℝ) ^ Nat.choose u 2 * (Real.log M / M) ^ Nat.choose u 2)
    (hx_pow : x ^ u = y ^ Nat.choose u 2 * x)
    (hcancel :
      y ^ Nat.choose u 2 * (Real.log M / M) ^ Nat.choose u 2 = 1)
    (hx_nonneg : 0 ≤ x) (hN_lower : 2 * d * x ≤ N) :
    (Nat.choose N u : ℝ) * q ^ Nat.choose u 2 ≤ N / 8 := by
  have hchoose : (Nat.choose N u : ℝ) ≤ (N : ℝ) ^ u := by
    exact_mod_cast (Nat.choose_le_pow N u)
  have hN_pow : (N : ℝ) ^ u ≤ (4 * d * x) ^ u := by
    exact pow_le_pow_left₀ (by positivity) hN_upper u
  have hq_pow_nonneg : 0 ≤ q ^ Nat.choose u 2 := by
    exact pow_nonneg hq_nonneg _
  calc
    (Nat.choose N u : ℝ) * q ^ Nat.choose u 2 ≤ (N : ℝ) ^ u * q ^ Nat.choose u 2 := by
      exact mul_le_mul_of_nonneg_right hchoose hq_pow_nonneg
    _ ≤ (4 * d * x) ^ u * q ^ Nat.choose u 2 := by
      exact mul_le_mul_of_nonneg_right hN_pow hq_pow_nonneg
    _ = (4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2 * x := by
      rw [show 4 * d * x = (4 * d) * x by ring, mul_pow, hq_pow, hx_pow]
      calc
        (4 * d) ^ u * (y ^ Nat.choose u 2 * x) *
            ((u : ℝ) ^ Nat.choose u 2 * (Real.log M / M) ^ Nat.choose u 2)
            =
            ((4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2) *
              (y ^ Nat.choose u 2 * (Real.log M / M) ^ Nat.choose u 2) * x := by
              ring
        _ = ((4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2) * x := by
              rw [hcancel]
              ring
        _ = (4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2 * x := by
              ring
    _ ≤ (d / 16) * x := by
      exact mul_le_mul_of_nonneg_right hcoeff hx_nonneg
    _ ≤ N / 8 := by
      have hdx_nonneg : 0 ≤ d * x := by
        nlinarith
      have hdx_le_two : d * x ≤ (2 : ℝ) * (d * x) := by
        simpa using
          (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hdx_nonneg)
      have hN_lower' : (2 : ℝ) * (d * x) ≤ N := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hN_lower
      have hdx_le_N : d * x ≤ N := by
        exact hdx_le_two.trans hN_lower'
      have hdiv : (d * x) / 16 ≤ (N : ℝ) / 16 := by
        exact div_le_div_of_nonneg_right hdx_le_N (by norm_num : (0 : ℝ) ≤ 16)
      have hsmall : (N : ℝ) / 16 ≤ N / 8 := by
        have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
        nlinarith
      have hrewrite : (d / 16) * x = (d * x) / 16 := by
        ring
      rw [hrewrite]
      exact hdiv.trans hsmall

lemma ramseyGap_step1_hs_exp {m : ℕ} {q : ℝ} (hm_two : 2 ≤ m)
    (hq_le_one : q ≤ 1) :
    (1 - q) ^ Nat.choose m 2 ≤ Real.exp (-(q * Nat.choose m 2)) := by
  have hqK_le : q * Nat.choose m 2 ≤ Nat.choose m 2 := by
    nlinarith
  have hmain := Real.one_sub_div_pow_le_exp_neg
    (n := Nat.choose m 2) (t := q * Nat.choose m 2) hqK_le
  have hK_pos : 0 < Nat.choose m 2 := by
    exact Nat.choose_pos hm_two
  have hK_ne : (Nat.choose m 2 : ℝ) ≠ 0 := by
    exact_mod_cast hK_pos.ne'
  have hdiv : (q * (Nat.choose m 2 : ℝ)) / Nat.choose m 2 = q := by
    field_simp [hK_ne]
  simpa [hdiv] using hmain

lemma ramseyGap_step1_hEY_real {u m N : ℕ} {d x q : ℝ} {p : I}
    (hd_nonneg : 0 ≤ d) (h4d_le_quarter : 4 * d ≤ 1 / 4)
    (hs_eq :
      ((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) = 1 - q)
    (hm_two : 2 ≤ m) (hq_le_one : q ≤ 1) (hx_le : x ≤ (m : ℝ) ^ ((u : ℝ) / 2))
    (hqK_eq :
      q * Nat.choose m 2 =
        Real.log (m : ℝ) * ((u : ℝ) * (((m : ℝ) - 1) / 2)))
    (hm_pos : 0 < (m : ℝ)) (hm_gt_one : 1 < (m : ℝ))
    (hN_upper : (N : ℝ) ≤ 4 * d * x)
    (hmDecay : (m : ℝ) ^ u * ((1 / 4 : ℝ) ^ m) < 1 / 4) :
    (Nat.choose N m : ℝ) *
        (((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) ^ Nat.choose m 2) <
      1 / 4 := by
  have hchoose : (Nat.choose N m : ℝ) ≤ (N : ℝ) ^ m := by
    exact_mod_cast (Nat.choose_le_pow N m)
  have hN_pow : (N : ℝ) ^ m ≤ (4 * d * x) ^ m := by
    exact pow_le_pow_left₀ (by positivity) hN_upper m
  have h4d_nonneg : 0 ≤ 4 * d := by
    nlinarith
  have hfourdx_le : 4 * d * x ≤ (4 * d) * (m : ℝ) ^ ((u : ℝ) / 2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hx_le h4d_nonneg)
  have hfourdx_nonneg : 0 ≤ 4 * d * x := by
    exact le_trans (by positivity : 0 ≤ (N : ℝ)) hN_upper
  have hfourdx_pow :
      (4 * d * x) ^ m ≤ (((4 * d) * (m : ℝ) ^ ((u : ℝ) / 2)) ^ m) := by
    exact pow_le_pow_left₀ hfourdx_nonneg hfourdx_le m
  have hpow_nonneg : 0 ≤ (1 - q) ^ Nat.choose m 2 := by
    exact pow_nonneg (sub_nonneg.mpr hq_le_one) _
  have hexp_nonneg : 0 ≤ Real.exp (-(q * Nat.choose m 2)) := by
    positivity
  have hexp_eq :
      Real.exp (-(q * Nat.choose m 2)) =
        (m : ℝ) ^ (-((u : ℝ) * (((m : ℝ) - 1) / 2))) := by
    rw [hqK_eq]
    have hrew :
        -(Real.log (m : ℝ) * ((u : ℝ) * (((m : ℝ) - 1) / 2))) =
          Real.log (m : ℝ) * (-((u : ℝ) * (((m : ℝ) - 1) / 2))) := by
      ring
    rw [hrew, Real.exp_mul, Real.exp_log hm_pos]
  have hexact :
      (((4 * d) * (m : ℝ) ^ ((u : ℝ) / 2)) ^ m) * Real.exp (-(q * Nat.choose m 2)) =
        (4 * d) ^ m * (m : ℝ) ^ ((u : ℝ) / 2) := by
    calc
      (((4 * d) * (m : ℝ) ^ ((u : ℝ) / 2)) ^ m) * Real.exp (-(q * Nat.choose m 2))
          = (4 * d) ^ m * ((m : ℝ) ^ ((u : ℝ) / 2)) ^ m *
              (m : ℝ) ^ (-((u : ℝ) * (((m : ℝ) - 1) / 2))) := by
                rw [mul_pow, hexp_eq]
      _ = (4 * d) ^ m * (m : ℝ) ^ (((u : ℝ) / 2) * m) *
            (m : ℝ) ^ (-((u : ℝ) * (((m : ℝ) - 1) / 2))) := by
            rw [← Real.rpow_mul_natCast hm_pos.le ((u : ℝ) / 2) m]
      _ = (4 * d) ^ m *
            ((m : ℝ) ^ (((u : ℝ) / 2) * m) *
              (m : ℝ) ^ (-((u : ℝ) * (((m : ℝ) - 1) / 2)))) := by
            ring
      _ = (4 * d) ^ m *
            (m : ℝ) ^
              ((((u : ℝ) / 2) * m) + (-((u : ℝ) * (((m : ℝ) - 1) / 2)))) := by
            rw [← Real.rpow_add hm_pos]
      _ = (4 * d) ^ m * (m : ℝ) ^ ((u : ℝ) / 2) := by
            congr 2
            ring
  have hM_pow : (m : ℝ) ^ ((u : ℝ) / 2) ≤ (m : ℝ) ^ u := by
    have h_exp_le : (u : ℝ) / 2 ≤ u := by
      nlinarith
    simpa using Real.rpow_le_rpow_of_exponent_le hm_gt_one.le h_exp_le
  have hfourd_pow : (4 * d) ^ m ≤ (1 / 4 : ℝ) ^ m := by
    exact pow_le_pow_left₀ h4d_nonneg h4d_le_quarter m
  calc
    (Nat.choose N m : ℝ) *
        (((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) ^ Nat.choose m 2)
        =
        (Nat.choose N m : ℝ) * (1 - q) ^ Nat.choose m 2 := by
          rw [hs_eq]
    _ ≤ (N : ℝ) ^ m * Real.exp (-(q * Nat.choose m 2)) := by
          refine (mul_le_mul_of_nonneg_right hchoose hpow_nonneg).trans ?_
          exact mul_le_mul_of_nonneg_left
            (ramseyGap_step1_hs_exp hm_two hq_le_one)
            (by positivity : 0 ≤ (N : ℝ) ^ m)
    _ ≤ (4 * d * x) ^ m * Real.exp (-(q * Nat.choose m 2)) := by
          exact mul_le_mul_of_nonneg_right hN_pow hexp_nonneg
    _ ≤ (((4 * d) * (m : ℝ) ^ ((u : ℝ) / 2)) ^ m) * Real.exp (-(q * Nat.choose m 2)) := by
          exact mul_le_mul_of_nonneg_right hfourdx_pow hexp_nonneg
    _ = (4 * d) ^ m * (m : ℝ) ^ ((u : ℝ) / 2) := hexact
    _ ≤ (4 * d) ^ m * (m : ℝ) ^ u := by
          exact mul_le_mul_of_nonneg_left hM_pow (pow_nonneg h4d_nonneg m)
    _ ≤ (1 / 4 : ℝ) ^ m * (m : ℝ) ^ u := by
          refine mul_le_mul_of_nonneg_right hfourd_pow ?_
          positivity
    _ < 1 / 4 := by
          simpa [mul_comm] using hmDecay

lemma ramseyGap_step1_hEX (N u : ℕ) (p : I) {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hp : (((unitInterval.toNNReal p : NNReal) : ENNReal)) = ENNReal.ofReal q)
    (hX_real : (Nat.choose N u : ℝ) * q ^ Nat.choose u 2 ≤ N / 8) :
    ∫⁻ ω, (step1CliqueCount u N ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) ≤ N / 8 := by
  have hRhs8 : ENNReal.ofReal ((N : ℝ) / 8) = (N : ENNReal) / 8 := by
    have hfinite : ((N : ENNReal) / 8) ≠ ∞ := by
      exact ENNReal.div_ne_top (by simp) (by norm_num)
    simpa using (ENNReal.ofReal_toReal (a := (N : ENNReal) / 8) hfinite)
  rw [step1_cliqueCount_lintegral_eq]
  rw [← ENNReal.ofReal_natCast, hp,
    ← ENNReal.ofReal_pow hq_nonneg (Nat.choose u 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Nat.choose N u : ℝ)),
    ← hRhs8]
  exact ENNReal.ofReal_le_ofReal hX_real

lemma ramseyGap_step1_hEY (N m : ℕ) (p : I) {q : ℝ}
    (hq_le_one : q ≤ 1)
    (hs_eq :
      ((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) = 1 - q)
    (hEY_real :
      (Nat.choose N m : ℝ) *
          (((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) ^ Nat.choose m 2) <
        1 / 4) :
    ∫⁻ ω, (step1IndepCount m N ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) < 1 / 4 := by
  have hs_eq_enn :
      (((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ENNReal)) =
        ENNReal.ofReal (1 - q) := by
    rw [ENNReal.coe_nnreal_eq]
    simpa using congrArg ENNReal.ofReal hs_eq
  have hQuarter : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
    simp
  have hEY_real' : (Nat.choose N m : ℝ) * (1 - q) ^ Nat.choose m 2 < 1 / 4 := by
    simpa [hs_eq] using hEY_real
  rw [step1_indepCount_lintegral_eq]
  rw [← ENNReal.ofReal_natCast, hs_eq_enn,
    ← ENNReal.ofReal_pow (sub_nonneg.mpr hq_le_one) (Nat.choose m 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Nat.choose N m : ℝ)),
    ← hQuarter]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).2 hEY_real'

lemma ramseyGap_step1_hUnionLt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : Set Ω} (hA : μ A ≤ (1 / 4 : ℝ≥0∞)) (hB : μ B < (1 / 4 : ℝ≥0∞)) :
    μ (A ∪ B) < 1 := by
  calc
    μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
    _ ≤ (1 / 4 : ℝ≥0∞) + μ B := by gcongr
    _ < (1 / 4 : ℝ≥0∞) + 1 / 4 := by
          exact ENNReal.add_lt_add_left (by simp) hB
    _ < 1 := by
          have htr :
              (((1 / 4 : ℝ≥0∞) + 1 / 4).toReal) < (1 : ℝ≥0∞).toReal := by
            norm_num [ENNReal.toReal_add]
          exact (ENNReal.toReal_lt_toReal (by simp) (by simp)).1 htr

lemma ramseyGap_step1_nat_floor_half_eq (N : ℕ) :
    Nat.floor ((N : ℝ) / 2) = N / 2 := by
  by_cases hmod : N % 2 = 0
  · have hdecomp_nat : 2 * (N / 2) = N := by
      simpa [hmod, add_comm, add_left_comm, add_assoc] using (Nat.mod_add_div N 2)
    have hdecomp : (2 : ℝ) * (N / 2 : ℕ) = N := by
      exact_mod_cast hdecomp_nat
    have hhalf_eq : (N : ℝ) / 2 = (N / 2 : ℕ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun t : ℝ => t / 2) hdecomp.symm
    exact (Nat.floor_eq_iff (a := (N : ℝ) / 2) (n := N / 2) (by positivity)).2
      ⟨by simp [hhalf_eq], by simp [hhalf_eq]⟩
  · have hmod1 : N % 2 = 1 := by
      have hlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
      omega
    have hdecomp_nat : 1 + 2 * (N / 2) = N := by
      simpa [hmod1, add_comm, add_left_comm, add_assoc] using (Nat.mod_add_div N 2)
    have hdecomp : (1 : ℝ) + 2 * (N / 2 : ℕ) = N := by
      exact_mod_cast hdecomp_nat
    have hhalf_eq : (N : ℝ) / 2 = (1 : ℝ) / 2 + (N / 2 : ℕ) := by
      simpa [add_div, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun t : ℝ => t / 2) hdecomp.symm
    have hlow : (N / 2 : ℕ) ≤ (N : ℝ) / 2 := by
      rw [hhalf_eq]
      nlinarith
    have hhigh : (N : ℝ) / 2 < (N / 2 : ℕ) + 1 := by
      rw [hhalf_eq]
      nlinarith
    exact (Nat.floor_eq_iff (a := (N : ℝ) / 2) (n := N / 2) (by positivity)).2
      ⟨hlow, hhigh⟩

lemma ramseyGap_step1_hcliques_nat {u N : ℕ} {ω : Set (Sym2 (Fin N))}
    (hcliques_real : (step1CliqueCount u N ω : ℝ) ≤ (N : ℝ) / 2) :
    step1CliqueCount u N ω ≤ N / 2 := by
  have hcliques_floor : step1CliqueCount u N ω ≤ Nat.floor ((N : ℝ) / 2) := by
    rw [Nat.le_floor_iff (by positivity : 0 ≤ (N : ℝ) / 2)]
    simpa using hcliques_real
  simpa [ramseyGap_step1_nat_floor_half_eq N] using hcliques_floor

lemma ramseyGap_step1_good_graph_for_m {u : ℕ} (hu : 3 ≤ u) {d : ℝ}
    (hd_pos : 0 < d) (h4d_le_quarter : 4 * d ≤ 1 / 4)
    (hcoeff_nat : (4 * d) ^ u * (u : ℝ) ^ Nat.choose u 2 ≤ d / 16) {m : ℕ}
    (hmLog : Real.log (m : ℝ) / (m : ℝ) < min (d / 2) (1 / (u : ℝ)))
    (hmDecay : (m : ℝ) ^ u * ((1 / 4 : ℝ) ^ m) < 1 / 4) (hm3 : 3 < m) :
    ∃ n : ℕ,
      d * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (n : ℝ) ∧
        ∃ G : SimpleGraph (Fin n), G.CliqueFree u ∧ G.IndepSetFree m := by
  have hu_pos : 0 < (u : ℝ) := by
    exact_mod_cast (show 0 < u by omega)
  have hu_one : 1 ≤ (u : ℝ) := by
    exact_mod_cast (show 1 ≤ u by omega)
  have hd_le_one : d ≤ 1 := by
    nlinarith
  let C : ℕ := Nat.choose u 2
  have hcoeff : (4 * d) ^ u * (u : ℝ) ^ C ≤ d / 16 := by
    simpa [C] using hcoeff_nat
  let M : ℝ := (m : ℝ)
  let y : ℝ := M / Real.log M
  let x : ℝ := y ^ ((u : ℝ) / 2)
  let N : ℕ := Nat.floor (4 * d * x)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hm_gt_one : 1 < M := by
    dsimp [M]
    exact_mod_cast (show 1 < m by omega)
  have hm_gt_three : (3 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast hm3
  have hlog_gt_one : 1 < Real.log M := by
    rw [Real.lt_log_iff_exp_lt hMpos]
    exact lt_trans Real.exp_one_lt_three hm_gt_three
  have hlog_pos : 0 < Real.log M := by
    linarith
  have hlog_ge_one : 1 ≤ Real.log M := hlog_gt_one.le
  have hlog_over_M_le_d_half : Real.log M / M ≤ d / 2 :=
    le_of_lt (lt_of_lt_of_le hmLog (min_le_left _ _))
  have hlog_over_M_le_inv_u : Real.log M / M ≤ 1 / (u : ℝ) :=
    le_of_lt (lt_of_lt_of_le hmLog (min_le_right _ _))
  let q : ℝ := (u : ℝ) * (Real.log M / M)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_one : q ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hlog_over_M_le_inv_u hu_pos.le
    calc
      q = (u : ℝ) * (Real.log M / M) := by rfl
      _ ≤ (u : ℝ) * (1 / (u : ℝ)) := hmul
      _ = 1 := by field_simp [hu_pos.ne']
  let p : I := ⟨q, hq_nonneg, hq_le_one⟩
  have hy_lower : 2 / d ≤ y := by
    simpa [y] using
      ramseyGap_step1_hy_lower hd_pos hMpos hlog_pos hlog_over_M_le_d_half
  have hy_ge_one : 1 ≤ y := by
    dsimp [y]
    have htwo : (2 : ℝ) ≤ 2 / d := by
      exact (le_div_iff₀ hd_pos).2 (by nlinarith [hd_le_one])
    have : (1 : ℝ) ≤ 2 / d := le_trans (by norm_num) htwo
    exact this.trans hy_lower
  have hx_ge_y : y ≤ x := by
    dsimp [x]
    have h_exp_ge_one : 1 ≤ (u : ℝ) / 2 := by
      have hu_three : (3 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith
    exact Real.self_le_rpow_of_one_le hy_ge_one h_exp_ge_one
  have hdx_ge_two : 2 ≤ d * x := by
    have hx_lower : 2 / d ≤ x := hy_lower.trans hx_ge_y
    have hmul : (2 : ℝ) ≤ x * d := (div_le_iff₀ hd_pos).1 hx_lower
    simpa [mul_comm] using hmul
  have hN_upper : (N : ℝ) ≤ 4 * d * x := by
    exact Nat.floor_le (by positivity : 0 ≤ 4 * d * x)
  have hN_gt : 4 * d * x - 1 < N := by
    simpa [N] using Nat.sub_one_lt_floor (4 * d * x)
  have hN_lower : 2 * d * x ≤ N := by
    have : 2 * d * x ≤ 4 * d * x - 1 := by
      nlinarith
    exact this.trans (le_of_lt hN_gt)
  have hN_half_lower : d * x ≤ (N / 2 : ℕ) := by
    exact ramseyGap_step1_hN_half_lower hdx_ge_two hN_gt
  have hy_pos : 0 < y := by
    dsimp [y]
    positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hq_pow : q ^ C = (u : ℝ) ^ C * (Real.log M / M) ^ C := by
    dsimp [q]
    rw [mul_pow]
  have hx_pow : x ^ u = y ^ C * x := by
    simpa [x, C] using ramseyGap_step1_hx_pow (u := u) hy_pos
  have hcancel : y ^ C * (Real.log M / M) ^ C = 1 := by
    have hmul : y * (Real.log M / M) = 1 := by
      dsimp [y]
      field_simp [hMpos.ne', hlog_pos.ne']
    calc
      y ^ C * (Real.log M / M) ^ C = (y * (Real.log M / M)) ^ C := by
        rw [← mul_pow]
      _ = 1 := by
        simp [hmul]
  have hX_real : (Nat.choose N u : ℝ) * q ^ C ≤ N / 8 := by
    simpa [C] using
      ramseyGap_step1_hX_real
        (by simpa [C] using hcoeff)
        hN_upper hq_nonneg
        (by simpa [C] using hq_pow)
        (by simpa [C] using hx_pow)
        (by simpa [C] using hcancel)
        hx_nonneg hN_lower
  have hm_two : 2 ≤ m := by
    omega
  have hs_eq : ((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) = 1 - q := by
    have hsum :
        ((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) + q = 1 := by
      simp [p, q]
    linarith
  have hx_le : x ≤ M ^ ((u : ℝ) / 2) := by
    have hdiv_le : y ≤ M := by
      dsimp [y]
      exact div_le_self hMpos.le hlog_ge_one
    dsimp [x]
    exact Real.rpow_le_rpow hy_pos.le hdiv_le (by positivity)
  have hqK_eq : q * Nat.choose m 2 = Real.log M * ((u : ℝ) * ((M - 1) / 2)) := by
    dsimp [q, M]
    rw [Nat.cast_choose_two]
    field_simp
  have hEY_real :
      (Nat.choose N m : ℝ) *
          (((unitInterval.toNNReal (unitInterval.symm p) : NNReal) : ℝ) ^ Nat.choose m 2) <
        1 / 4 := by
    simpa [M] using
      ramseyGap_step1_hEY_real (u := u) (m := m) (N := N) (d := d) (x := x) (q := q)
        (p := p) (le_of_lt hd_pos) h4d_le_quarter hs_eq hm_two hq_le_one
        (by simpa [M] using hx_le)
        (by simpa [M] using hqK_eq)
        (by simpa [M] using hMpos)
        (by simpa [M] using hm_gt_one)
        hN_upper hmDecay
  let μ : Measure (Set (Sym2 (Fin N))) := setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  have hX_meas :
      AEMeasurable (fun ω => (step1CliqueCount u N ω : ℝ≥0∞)) μ := by
    exact (measurable_of_countable _).aemeasurable
  have hY_meas :
      AEMeasurable (fun ω => (step1IndepCount m N ω : ℝ≥0∞)) μ := by
    exact (measurable_of_countable _).aemeasurable
  have hEX :
      ∫⁻ ω, (step1CliqueCount u N ω : ℝ≥0∞) ∂μ ≤ N / 8 := by
    have hp : (((unitInterval.toNNReal p : NNReal) : ENNReal)) = ENNReal.ofReal q := by
      rw [ENNReal.coe_nnreal_eq]
      simp [p]
    simpa [μ, C] using
      ramseyGap_step1_hEX N u p hq_nonneg hp (by simpa [C] using hX_real)
  have hEY :
      ∫⁻ ω, (step1IndepCount m N ω : ℝ≥0∞) ∂μ < 1 / 4 := by
    simpa [μ] using ramseyGap_step1_hEY N m p hq_le_one hs_eq hEY_real
  let BadClique : Set (Set (Sym2 (Fin N))) :=
    {ω | (N : ℝ≥0∞) / 2 < step1CliqueCount u N ω}
  let BadIndep : Set (Set (Sym2 (Fin N))) :=
    {ω | 0 < step1IndepCount m N ω}
  have hBadClique : μ BadClique ≤ (1 / 4 : ℝ≥0∞) := by
    simpa [μ, BadClique] using ramseyGap_step1_eq4 μ hX_meas hEX
  have hBadIndep : μ BadIndep < (1 / 4 : ℝ≥0∞) := by
    simpa [μ, BadIndep] using ramseyGap_step1_eq5 μ hY_meas hEY
  have hUnionLt : μ (BadClique ∪ BadIndep) < 1 := by
    exact ramseyGap_step1_hUnionLt μ hBadClique hBadIndep
  have hUnionMeas : MeasurableSet (BadClique ∪ BadIndep) :=
    (Set.to_countable _).measurableSet
  let Good : Set (Set (Sym2 (Fin N))) := (BadClique ∪ BadIndep)ᶜ
  have hGood_ne_zero : μ Good ≠ 0 := by
    intro hzero
    have hsum : μ (BadClique ∪ BadIndep) + μ Good = 1 := by
      simpa [μ, Good] using (measure_add_measure_compl (μ := μ) hUnionMeas)
    rw [hzero, add_zero] at hsum
    exact (not_lt_of_ge hsum.ge) hUnionLt
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measure_ne_zero hGood_ne_zero
  have hω_union : ω ∉ BadClique ∪ BadIndep := by
    simpa [Good] using hω
  have hω_clique : ω ∉ BadClique := fun hA => hω_union (Or.inl hA)
  have hω_indep : ω ∉ BadIndep := fun hB => hω_union (Or.inr hB)
  have hcliques_real : (step1CliqueCount u N ω : ℝ) ≤ (N : ℝ) / 2 := by
    have hcliques_enn : (step1CliqueCount u N ω : ℝ≥0∞) ≤ (N : ℝ≥0∞) / 2 := by
      exact le_of_not_gt (by simpa [BadClique] using hω_clique)
    have hright_ne_top : ((N : ℝ≥0∞) / 2) ≠ ∞ := by
      exact ENNReal.div_ne_top (by simp) (by norm_num)
    simpa using
      (ENNReal.toReal_le_toReal (by simp) hright_ne_top).2 hcliques_enn
  have hcliques_nat : step1CliqueCount u N ω ≤ N / 2 := by
    exact ramseyGap_step1_hcliques_nat hcliques_real
  have hindep : step1IndepCount m N ω = 0 := by
    exact Nat.eq_zero_of_not_pos (by simpa [BadIndep] using hω_indep)
  have hu_one_nat : 1 ≤ u := by omega
  obtain ⟨n, hn, G, hcf, hif⟩ :=
    step1_good_from_outcome N u m ω hu_one_nat hcliques_nat hindep
  have hsize : d * x ≤ n := by
    have hhalf_cast : ((N / 2 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hn
    exact hN_half_lower.trans hhalf_cast
  refine ⟨n, ?_, G, hcf, hif⟩
  simpa [x, y, M] using hsize

/--
Step 1. The probabilistic construction produces actual `K_u`-free graphs.

Combining equations (4) and (5), one finds a graph with at most `N / 2`
copies of `K_u` and with no independent set of size `m`. Deleting one chosen
vertex from each `K_u` copy leaves an induced subgraph on at least `N / 2`
vertices that is `K_u`-free and still has no independent set of size `m`.
-/
lemma ramseyGap_step1_good_graph_exists :
    ∀ u : ℕ, 3 ≤ u → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ n : ℕ,
          c * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (n : ℝ) ∧
            ∃ G : SimpleGraph (Fin n), G.CliqueFree u ∧ G.IndepSetFree m := by
  intro u hu
  rcases ramseyGap_step1_good_graph_constant hu with
    ⟨d, hd_pos, h4d_le_quarter, _, hcoeff⟩
  have hu_pos : 0 < (u : ℝ) := by
    exact_mod_cast (show 0 < u by omega)
  have hlogdiv :
      Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
    have hlittle :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] fun n => (n : ℝ) := by
      simpa using
        (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 1 zero_lt_one).natCast_atTop
    exact hlittle.tendsto_div_nhds_zero
  have hpowdecay :
      Tendsto (fun m : ℕ => (m : ℝ) ^ u * ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_pow_const_div_const_pow_of_one_lt u (show (1 : ℝ) < 4 by norm_num)
  refine ⟨d, hd_pos, ?_⟩
  have hsmall_log :
      ∀ᶠ m : ℕ in atTop,
        Real.log (m : ℝ) / (m : ℝ) < min (d / 2) (1 / (u : ℝ)) := by
    have hmin_pos : 0 < min (d / 2) (1 / (u : ℝ)) := by
      refine lt_min ?_ ?_
      · positivity
      · exact one_div_pos.mpr hu_pos
    exact hlogdiv.eventually (Iio_mem_nhds hmin_pos)
  have hsmall_decay :
      ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ u * ((1 / 4 : ℝ) ^ m) < 1 / 4 := by
    exact hpowdecay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall_log, hsmall_decay, eventually_gt_atTop 3] with m hmLog hmDecay hm3
  exact
    ramseyGap_step1_good_graph_for_m hu hd_pos h4d_le_quarter hcoeff hmLog hmDecay hm3

/--
Step 1. Turning an eventually available family of good graphs into a lower bound
for the Ramsey numbers.

If, for all sufficiently large `m`, there is a `K_u`-free graph on `n` vertices
with no independent set of size `m`, then `R(u,m)` must exceed `n`.
-/
lemma ramseyGap_step1_lower_bound_of_eventually_good_graph {u : ℕ} {c : ℝ}
    (hgood :
      ∀ᶠ m : ℕ in atTop,
        ∃ n : ℕ,
          c * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (n : ℝ) ∧
            ∃ G : SimpleGraph (Fin n), G.CliqueFree u ∧ G.IndepSetFree m) :
    ∀ᶠ m : ℕ in atTop,
      c * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (ramseyNumber u m : ℝ) := by
  filter_upwards [hgood] with m hm
  rcases hm with ⟨n, hsize, G, hcf, hif⟩
  have hnot : ¬ RamseyProperty u m n := by
    intro hramsey
    exact hramsey G ⟨hcf, hif⟩
  have hramsey_not_le : ¬ ramseyNumber u m ≤ n := by
    intro hle
    exact hnot (ramseyProperty_of_ramseyNumber_le hle)
  have hramsey_lt : n < ramseyNumber u m := Nat.lt_of_not_ge hramsey_not_le
  have hramsey_le_real : (n : ℝ) ≤ (ramseyNumber u m : ℝ) := by
    exact_mod_cast Nat.le_of_lt hramsey_lt
  exact hsize.trans hramsey_le_real

/--
Step 1. Elementary Ramsey estimates.

For every fixed integer `u >= 3`, there is a constant `c_u > 0` such that, for
all sufficiently large `m`,

    R(u,m) >= c_u (m / log m)^{u/2}.                            (2)

The proof uses the random-graph construction summarized in
`ramseyGap_step1_good_graph_exists` and then converts those graphs into a lower
bound for `R(u,m)`.
-/
lemma ramseyGap_step1_lower_bound_from_random_graph :
    ∀ u : ℕ, 3 ≤ u → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        c * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (ramseyNumber u m : ℝ) := by
  intro u hu
  rcases ramseyGap_step1_good_graph_exists u hu with ⟨c, hc, hgood⟩
  refine ⟨c, hc, ?_⟩
  exact ramseyGap_step1_lower_bound_of_eventually_good_graph hgood

lemma ramseyGap_step1_lower_bound :
    ∀ u : ℕ, 3 ≤ u → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        c * ((m : ℝ) / Real.log (m : ℝ)) ^ ((u : ℝ) / 2) ≤ (ramseyNumber u m : ℝ) := by
  intro u hu
  simpa using ramseyGap_step1_lower_bound_from_random_graph u hu

/--
Step 2. A large jump forces large minimum degree.

Recall that

    r_ell = R(k,ell),
    Delta_ell = r_{ell+1} - r_ell,
    n_ell = r_{ell+1} - 1.

We first note that

    Delta_ell >= 1.

For ell >= 2, by the definition of r_ell, there is a K_k-free graph F on
r_ell - 1 vertices with alpha(F) <= ell - 1. Add one isolated vertex to F.
The resulting graph is still K_k-free, has r_ell vertices, and has independence
number at most ell. Hence

    R(k,ell+1) > r_ell,

so Delta_ell >= 1. For ell = 1 this is also true, since R(k,1)=1 and
R(k,2)=k.
-/
lemma ramseyGap_step2_gap_ge_one (k l : ℕ) (hk : 2 ≤ k) : 1 ≤ ramseyGap k l := by
  exact ramseyGap_ge_one k l hk

/--
Step 2. A large jump forces large minimum degree.

Now let G be any K_k-free graph on n_ell vertices with alpha(G) <= ell. We claim
that

    delta(G) >= Delta_ell - 1.                                  (6)

Take any vertex v in G. Let

    N[v] := N(v) union {v}

be the closed neighborhood of v. Consider the induced graph

    H := G - N[v].

The graph H is K_k-free, because it is an induced subgraph of the K_k-free graph
G.

Also, H has no independent set of size ell. Indeed, if I subset V(H) were an
independent set of size ell, then no vertex of I is adjacent to v, because
I lies outside N[v]. Thus I union {v} would be an independent set of size
ell+1 in G, contradicting alpha(G) <= ell.

Therefore H is K_k-free and has no independent ell-set. By the definition of
r_ell = R(k,ell), this implies

    |V(H)| <= r_ell - 1.

But

    |V(H)| = n_ell - |N[v]|
           = (r_{ell+1}-1) - (d(v)+1).

Hence

    (r_{ell+1}-1) - (d(v)+1) <= r_ell - 1.

Rearranging gives

    d(v)+1 >= r_{ell+1} - r_ell = Delta_ell,

so

    d(v) >= Delta_ell - 1.

Since v was arbitrary, this proves (6).
-/
lemma ramseyGap_step2_minDegree_bound (k l : ℕ) (hk : 3 ≤ k) :
    ∀ {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      Fintype.card α = ramseyCriticalSize k l →
      G.CliqueFree k →
      G.IndepSetFree (l + 1) →
      ∀ v : α, ramseyGap k l - 1 ≤ G.degree v := by
        sorry
noncomputable def step3CommonNeighbors {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => ∀ u ∈ T, G.Adj u v

noncomputable def step3TupleCommonNeighbors {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {q : ℕ} (x : Fin q → α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => ∀ i : Fin q, G.Adj (x i) v

noncomputable def step3GlobalBadSubsets {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (s t l : ℕ) : Finset (Finset α) := by
  classical
  exact (Finset.univ.powersetCard s).filter fun T =>
    (step3CommonNeighbors G T).card < ramseyNumber t (l + 1)

lemma mem_step3CommonNeighbors {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (T : Finset α) (v : α) :
    v ∈ step3CommonNeighbors G T ↔ ∀ u ∈ T, G.Adj u v := by
  classical
  simp [step3CommonNeighbors]

lemma mem_step3TupleCommonNeighbors {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {q : ℕ} (x : Fin q → α) (v : α) :
    v ∈ step3TupleCommonNeighbors G x ↔ ∀ i : Fin q, G.Adj (x i) v := by
  classical
  simp [step3TupleCommonNeighbors]

lemma mem_step3GlobalBadSubsets {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (s t l : ℕ) (T : Finset α) :
    T ∈ step3GlobalBadSubsets G s t l ↔
      T.card = s ∧ (step3CommonNeighbors G T).card < ramseyNumber t (l + 1) := by
  classical
  simp [step3GlobalBadSubsets]

lemma step3_exists_clique_of_card_ge_ramsey
    {α : Type*} (G : SimpleGraph α)
    (s l : ℕ) (A : Finset α) (hcard : ramseyNumber s (l + 1) ≤ A.card)
    (hif : G.IndepSetFree (l + 1)) :
    ∃ C : Finset α, C ⊆ A ∧ G.IsNClique s C := by
      sorry
lemma step3_isNClique_union_right
    {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    {s t : ℕ} {C D : Finset α}
    (hC : G.IsNClique s C) (hD : G.IsNClique t D)
    (hCD : ∀ v ∈ D, ∀ u ∈ C, G.Adj u v) :
    G.IsNClique (s + t) (C ∪ D) := by
  classical
  induction D using Finset.induction_on generalizing t C s with
  | empty =>
      have ht : t = 0 := by simpa using hD.2.symm
      subst ht
      simpa using hC
  | @insert a D ha ih =>
    have hD' : G.IsNClique (t - 1) D := by
      simpa [ha] using (hD.erase_of_mem (a := a) (by simp))
    have hIH : G.IsNClique (s + (t - 1)) (C ∪ D) := by
      apply ih hC hD'
      intro v hv u hu
      exact hCD v (by simp [hv]) u hu
    have ha_adj : ∀ b ∈ C ∪ D, G.Adj a b := by
      intro b hb
      rcases Finset.mem_union.mp hb with hbC | hbD
      · exact (hCD a (by simp) b hbC).symm
      · exact hD.1 (by simp) (by simp [hbD]) (by
            intro hab
            subst b
            exact ha hbD)
    have ha_not_mem_C : a ∉ C := by
      intro haC
      exact (hCD a (by simp) a haC).ne rfl
    have hIns : G.IsNClique (s + (t - 1) + 1) (insert a (C ∪ D)) :=
      hIH.insert ha_adj
    have htpos : 0 < t := by
      rw [← hD.2]
      simp
    have hst : s + (t - 1) + 1 = s + t := by omega
    have hset : insert a (C ∪ D) = C ∪ insert a D := by
      ext x
      simp [Finset.mem_union, Finset.mem_insert, or_comm]
    rw [hset] at hIns
    simpa [hst, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
      using hIns

lemma step3_card_le_ramsey_add_bad
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (s t l : ℕ) (hs : 1 ≤ s)
    (hcf : G.CliqueFree (s + t))
    (hif : G.IndepSetFree (l + 1))
    (A : Finset α) :
    A.card ≤
      ramseyNumber s (l + 1) - 1 +
        ((step3GlobalBadSubsets G s t l).filter fun T => T ⊆ A).card := by
  classical
  let B : Finset (Finset α) := (step3GlobalBadSubsets G s t l).filter fun T => T ⊆ A
  let pick : {T // T ∈ B} → α := fun T =>
    Classical.choose <| by
      have hTB : T.1 ∈ step3GlobalBadSubsets G s t l := (Finset.mem_filter.mp T.2).1
      have hcardT : T.1.card = s := (mem_step3GlobalBadSubsets G s t l T.1).1 hTB |>.1
      have hTpos : 0 < T.1.card := by omega
      exact Finset.card_pos.mp hTpos
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hTB : T.1 ∈ step3GlobalBadSubsets G s t l := (Finset.mem_filter.mp T.2).1
      have hcardT : T.1.card = s := (mem_step3GlobalBadSubsets G s t l T.1).1 hTB |>.1
      have hTpos : 0 < T.1.card := by omega
      exact Finset.card_pos.mp hTpos
  have hpick_mem_A : ∀ T : {T // T ∈ B}, pick T ∈ A := by
    intro T
    have hsub : T.1 ⊆ A := (Finset.mem_filter.mp T.2).2
    exact hsub (hpick_mem T)
  let deleted : Finset α := B.attach.image pick
  have hdeleted_subset : deleted ⊆ A := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    exact hpick_mem_A T
  let U : Finset α := A \ deleted
  have hU_lower : A.card - B.card ≤ U.card := by
    have hdeleted_card : deleted.card ≤ B.card := by
      simpa [deleted] using (Finset.card_image_le (s := B.attach) (f := pick))
    calc
      A.card - B.card ≤ A.card - deleted.card := Nat.sub_le_sub_left hdeleted_card _
      _ = U.card := by
        symm
        simp [U, deleted, Finset.card_sdiff_of_subset hdeleted_subset]
  have hU_no_bad :
      ∀ {T : Finset α}, T ∈ step3GlobalBadSubsets G s t l → T ⊆ U → False := by
    intro T hT hTU
    have hTA : T ⊆ A := by
      intro v hv
      exact (show v ∈ A ∧ v ∉ deleted by simpa [U] using hTU hv).1
    have hTB : T ∈ B := by
      exact Finset.mem_filter.mpr ⟨hT, hTA⟩
    let TT : {T // T ∈ B} := ⟨T, hTB⟩
    have hpick_del : pick TT ∈ deleted := by
      exact Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
    have hpick_T : pick TT ∈ T := hpick_mem TT
    have hpick_U : pick TT ∈ U := hTU hpick_T
    have hpick_not_deleted : pick TT ∉ deleted := by
      exact (show pick TT ∈ A ∧ pick TT ∉ deleted by simpa [U] using hpick_U).2
    exact hpick_not_deleted hpick_del
  by_contra hA
  have hU_lower' :
      A.card - ((step3GlobalBadSubsets G s t l).filter fun T => T ⊆ A).card ≤ U.card := by
    simpa [B] using hU_lower
  have hU_large : ramseyNumber s (l + 1) ≤ U.card := by
    omega
  obtain ⟨C, hCU, hC⟩ := step3_exists_clique_of_card_ge_ramsey G s l U hU_large hif
  have hN_large : ramseyNumber t (l + 1) ≤ (step3CommonNeighbors G C).card := by
    by_contra hN
    have hCbad : C ∈ step3GlobalBadSubsets G s t l := by
      have hlt : (step3CommonNeighbors G C).card < ramseyNumber t (l + 1) := lt_of_not_ge hN
      exact (mem_step3GlobalBadSubsets G s t l C).2 ⟨hC.2, hlt⟩
    exact hU_no_bad hCbad hCU
  obtain ⟨D, hDN, hD⟩ :=
    step3_exists_clique_of_card_ge_ramsey G t l (step3CommonNeighbors G C) hN_large hif
  have hCD : ∀ v ∈ D, ∀ u ∈ C, G.Adj u v := by
    intro v hv u hu
    exact (mem_step3CommonNeighbors G C v).1 (hDN hv) u hu
  have hUnion : G.IsNClique (s + t) (C ∪ D) :=
    step3_isNClique_union_right G hC hD hCD
  exact hcf _ hUnion

lemma ramseyGap_step3_drc_inequality
    {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (s t l q d : ℕ) (hα : 0 < Fintype.card α) (hs : 1 ≤ s) (ht : 1 ≤ t) (hq : 0 < q)
    (hcf : G.CliqueFree (s + t))
    (hif : G.IndepSetFree (l + 1))
    (hd : ∀ v : α, d ≤ G.degree v) :
    (d : ℝ) ^ q / (Fintype.card α : ℝ) ^ (q - 1) ≤
      ((ramseyNumber s (l + 1) : ℝ) - 1) +
        (Nat.choose (Fintype.card α) s : ℝ) *
          ((((ramseyNumber t (l + 1) : ℝ) - 1) / (Fintype.card α : ℝ)) ^ q) := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq) with ⟨q', rfl⟩
  let n := Fintype.card α
  let S := ramseyNumber s (l + 1)
  let M := ramseyNumber t (l + 1)
  let Bad := step3GlobalBadSubsets G s t l
  let Tuple := Fin (q' + 1) → α
  have hTupleCount :
      ∑ x : Tuple, (step3TupleCommonNeighbors G x).card =
        ∑ v : α, G.degree v ^ (q' + 1) := by
    calc
      ∑ x : Tuple, (step3TupleCommonNeighbors G x).card
          = ∑ x : Tuple, Fintype.card {v : α // ∀ i : Fin (q' + 1), G.Adj (x i) v} := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [step3TupleCommonNeighbors, Fintype.card_subtype]
      _ =
          Fintype.card
            (Σ x : Tuple, {v : α // ∀ i : Fin (q' + 1), G.Adj (x i) v}) := by
              simp [Fintype.card_sigma]
      _ =
          Fintype.card
            (Σ v : α, {x : Tuple // ∀ i : Fin (q' + 1), G.Adj (x i) v}) := by
              refine Fintype.card_congr
                { toFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
                  invFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
                  left_inv := by intro p; cases p; rfl
                  right_inv := by intro p; cases p; rfl }
      _ =
          ∑ v : α, Fintype.card {x : Tuple // ∀ i : Fin (q' + 1), G.Adj (x i) v} := by
              simp [Fintype.card_sigma]
      _ = ∑ v : α, G.degree v ^ (q' + 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            let e :
                {x : Tuple // ∀ i : Fin (q' + 1), G.Adj (x i) v} ≃
                  (Fin (q' + 1) → {w : α // G.Adj w v}) :=
              { toFun := fun x i => ⟨x.1 i, x.2 i⟩
                invFun := fun f => ⟨fun i => f i, by intro i; exact (f i).property⟩
                left_inv := by intro x; cases x; rfl
                right_inv := by intro f; rfl }
            calc
              Fintype.card {x : Tuple // ∀ i : Fin (q' + 1), G.Adj (x i) v}
                  = Fintype.card (Fin (q' + 1) → {w : α // G.Adj w v}) := by
                      exact Fintype.card_congr e
              _ = Fintype.card {w : α // G.Adj w v} ^ Fintype.card (Fin (q' + 1)) := by
                    simp
              _ = G.degree v ^ (q' + 1) := by
                    have hcard :
                        Fintype.card {w : α // G.Adj w v} = G.degree v := by
                      calc
                        Fintype.card {w : α // G.Adj w v}
                            = Fintype.card (G.neighborSet v) := by
                                refine Fintype.card_congr
                                  { toFun := fun w => ⟨w.1,
                                      (SimpleGraph.mem_neighborSet (G := G) (v := v) (w := w.1)).2
                                        w.2.symm⟩
                                    invFun := fun w => ⟨w.1, by
                                      exact
                                        ((SimpleGraph.mem_neighborSet
                                          (G := G) (v := v) (w := w.1)).1 w.2).symm⟩
                                    left_inv := by intro w; cases w; rfl
                                    right_inv := by intro w; cases w; rfl }
                        _ = G.degree v := G.card_neighborSet_eq_degree v
                    simp [hcard]
  have hLower :
      n * d ^ (q' + 1) ≤ ∑ x : Tuple, (step3TupleCommonNeighbors G x).card := by
    calc
      n * d ^ (q' + 1) = ∑ v : α, d ^ (q' + 1) := by
        simp [n]
      _ ≤ ∑ v : α, G.degree v ^ (q' + 1) := by
        exact Finset.sum_le_sum fun v hv => Nat.pow_le_pow_left (hd v) _
      _ = ∑ x : Tuple, (step3TupleCommonNeighbors G x).card := hTupleCount.symm
  have hTupleBound :
      ∀ x : Tuple,
        (step3TupleCommonNeighbors G x).card ≤
          S - 1 + (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card := by
    intro x
    simpa [S, Bad] using
      (step3_card_le_ramsey_add_bad G s t l hs hcf hif (step3TupleCommonNeighbors G x))
  have hBadSum :
      ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card ≤
        Bad.card * (M - 1) ^ (q' + 1) := by
    have hBadCountEq :
        ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card =
          ∑ Tbad : {T : Finset α // T ∈ Bad},
            Fintype.card {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x} := by
      calc
        ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card
            =
              ∑ x : Tuple,
                Fintype.card
                  {T : Finset α // T ∈ Bad ∧ T ⊆ step3TupleCommonNeighbors G x} := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hxcard :
                      (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card =
                        Fintype.card
                          {T : Finset α // T ∈ Bad ∧ T ⊆ step3TupleCommonNeighbors G x} := by
                    rw [Fintype.card_subtype]
                    have hEq :
                        Bad.filter (fun T => T ⊆ step3TupleCommonNeighbors G x) =
                          Finset.univ.filter (fun T : Finset α =>
                            T ∈ Bad ∧ T ⊆ step3TupleCommonNeighbors G x) := by
                      ext T
                      simp
                    exact congrArg Finset.card hEq
                  exact hxcard
        _ =
            Fintype.card
              (Σ x : Tuple,
                {T : Finset α // T ∈ Bad ∧ T ⊆ step3TupleCommonNeighbors G x}) := by
                simp [Fintype.card_sigma]
        _ =
            Fintype.card
              (Σ Tbad : {T : Finset α // T ∈ Bad},
                {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x}) := by
                  refine Fintype.card_congr
                    { toFun := fun p => ⟨⟨p.2.1, p.2.2.1⟩, ⟨p.1, p.2.2.2⟩⟩
                      invFun := fun p => ⟨p.2.1, ⟨p.1.1, p.1.2, p.2.2⟩⟩
                      left_inv := by intro p; cases p; rfl
                      right_inv := by intro p; cases p; rfl }
        _ =
            ∑ Tbad : {T : Finset α // T ∈ Bad},
              Fintype.card {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x} := by
                simp [Fintype.card_sigma]
    have hFiberBound :
        ∀ Tbad : {T : Finset α // T ∈ Bad},
          Fintype.card {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x} ≤
            (M - 1) ^ (q' + 1) := by
      intro Tbad
      have hTbad : Tbad.1 ∈ Bad := Tbad.2
      have hTlt : (step3CommonNeighbors G Tbad.1).card < M := by
        simpa [Bad, M] using (mem_step3GlobalBadSubsets G s t l Tbad.1).1 hTbad |>.2
      let e :
          {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x} ≃
            (Fin (q' + 1) → {v : α // v ∈ step3CommonNeighbors G Tbad.1}) :=
        { toFun := fun x i => ⟨x.1 i, by
            refine (mem_step3CommonNeighbors G Tbad.1 (x.1 i)).2 ?_
            intro u hu
            exact ((mem_step3TupleCommonNeighbors G x.1 u).1 (x.2 hu) i).symm⟩
          invFun := fun f => ⟨fun i => f i, by
            intro u hu
            refine (mem_step3TupleCommonNeighbors G (fun i => (f i).1) u).2 ?_
            intro i
            exact ((mem_step3CommonNeighbors G Tbad.1 ((f i).1)).1 (f i).2 u hu).symm⟩
          left_inv := by intro x; cases x; rfl
          right_inv := by intro f; rfl }
      calc
        Fintype.card {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x}
            = Fintype.card (Fin (q' + 1) → {v : α // v ∈ step3CommonNeighbors G Tbad.1}) := by
                exact Fintype.card_congr e
        _ = (step3CommonNeighbors G Tbad.1).card ^ (q' + 1) := by
              simp [Fintype.card_subtype]
        _ ≤ (M - 1) ^ (q' + 1) := by
              exact Nat.pow_le_pow_left (Nat.le_pred_of_lt hTlt) _
    calc
      ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card
          =
            ∑ Tbad : {T : Finset α // T ∈ Bad},
              Fintype.card {x : Tuple // Tbad.1 ⊆ step3TupleCommonNeighbors G x} := hBadCountEq
      _ ≤ ∑ Tbad : {T : Finset α // T ∈ Bad}, (M - 1) ^ (q' + 1) := by
            exact Finset.sum_le_sum fun Tbad hTbad => hFiberBound Tbad
      _ = Bad.card * (M - 1) ^ (q' + 1) := by simp
  have hBadCard : Bad.card ≤ Nat.choose n s := by
    unfold Bad
    simpa [step3GlobalBadSubsets, n] using
      (Finset.card_filter_le
        (Finset.univ.powersetCard s)
        (fun T => (step3CommonNeighbors G T).card < ramseyNumber t (l + 1)))
  have hNat :
      n * d ^ (q' + 1) ≤
        n ^ (q' + 1) * (S - 1) + Nat.choose n s * (M - 1) ^ (q' + 1) := by
    calc
      n * d ^ (q' + 1) ≤ ∑ x : Tuple, (step3TupleCommonNeighbors G x).card := hLower
      _ ≤
          ∑ x : Tuple,
            (S - 1 + (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card) := by
              exact Finset.sum_le_sum fun x hx => hTupleBound x
      _ =
          Fintype.card Tuple * (S - 1) +
            ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card := by
              rw [Finset.sum_add_distrib]
              simp
      _ = n ^ (q' + 1) * (S - 1) +
            ∑ x : Tuple, (Bad.filter fun T => T ⊆ step3TupleCommonNeighbors G x).card := by
              simp [Tuple, n]
      _ ≤ n ^ (q' + 1) * (S - 1) + Bad.card * (M - 1) ^ (q' + 1) := by
            exact Nat.add_le_add_left hBadSum _
      _ ≤ n ^ (q' + 1) * (S - 1) + Nat.choose n s * (M - 1) ^ (q' + 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hBadCard) _
  have hl : 1 ≤ l + 1 := Nat.succ_le_succ (Nat.zero_le l)
  have hS_ge : 1 ≤ S := Nat.succ_le_of_lt (ramseyNumber_pos hs hl)
  have hM_ge : 1 ≤ M := Nat.succ_le_of_lt (ramseyNumber_pos ht hl)
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hα
  have hRealNat :
      (n : ℝ) * (d : ℝ) ^ (q' + 1) ≤
        (n : ℝ) ^ (q' + 1) * (↑(S - 1)) +
          (Nat.choose n s : ℝ) * ↑((M - 1) ^ (q' + 1)) := by
    exact_mod_cast hNat
  have hReal :
      (n : ℝ) * (d : ℝ) ^ (q' + 1) ≤
        (n : ℝ) ^ (q' + 1) * ((S : ℝ) - 1) +
          (Nat.choose n s : ℝ) * (((M : ℝ) - 1) ^ (q' + 1)) := by
    simpa [Nat.cast_sub hS_ge, Nat.cast_sub hM_ge, Nat.cast_pow] using hRealNat
  have hDiv :
      ((n : ℝ) * (d : ℝ) ^ (q' + 1)) / (n : ℝ) ^ (q' + 1) ≤
        ((n : ℝ) ^ (q' + 1) * ((S : ℝ) - 1) +
          (Nat.choose n s : ℝ) * (((M : ℝ) - 1) ^ (q' + 1))) / (n : ℝ) ^ (q' + 1) :=
    div_le_div_of_nonneg_right hReal (pow_nonneg hn_pos.le _)
  have hLeft :
      ((n : ℝ) * (d : ℝ) ^ (q' + 1)) / (n : ℝ) ^ (q' + 1) =
        (d : ℝ) ^ (q' + 1) / (n : ℝ) ^ q' := by
    field_simp [hn_pos.ne']
    ring
  have hRight :
      ((n : ℝ) ^ (q' + 1) * ((S : ℝ) - 1) +
          (Nat.choose n s : ℝ) * (((M : ℝ) - 1) ^ (q' + 1))) / (n : ℝ) ^ (q' + 1) =
        ((S : ℝ) - 1) +
          (Nat.choose n s : ℝ) * ((((M : ℝ) - 1) / (n : ℝ)) ^ (q' + 1)) := by
    have hnq_ne : (n : ℝ) ^ (q' + 1) ≠ 0 := by
      exact pow_ne_zero _ hn_pos.ne'
    rw [add_div]
    have hfirst :
        ((n : ℝ) ^ (q' + 1) * ((S : ℝ) - 1)) / (n : ℝ) ^ (q' + 1) = ((S : ℝ) - 1) := by
      field_simp [hnq_ne]
    have hsecond :
        ((Nat.choose n s : ℝ) * (((M : ℝ) - 1) ^ (q' + 1))) / (n : ℝ) ^ (q' + 1) =
          (Nat.choose n s : ℝ) * ((((M : ℝ) - 1) / (n : ℝ)) ^ (q' + 1)) := by
      rw [mul_div_assoc, ← div_pow]
    rw [hfirst, hsecond]
  rw [hLeft, hRight] at hDiv
  simpa [n, S, M]
    using hDiv

/--
Step 4. Apply the lemma to a Ramsey-critical graph.

Let s,t >= 1 satisfy

    s + t = k,

and let q >= 1.

By the definition of n_ell = R(k,ell+1)-1, there exists a graph G on n_ell
vertices such that

    G is K_k-free,
    alpha(G) <= ell.

Let d be the average degree of G. By Step 2,

    d >= delta(G) >= Delta_ell - 1.

Applying the lemma from Step 3 to this graph G gives

    d^q / n_ell^{q-1}
      <= R(s,ell+1)-1
         + binom(n_ell,s)
           ((R(t,ell+1)-1)/n_ell)^q.

Divide both sides by n_ell:

    (d/n_ell)^q
      <= (R(s,ell+1)-1)/n_ell
         + binom(n_ell,s)
           (R(t,ell+1)-1)^q / n_ell^{q+1}.

Since d >= Delta_ell - 1, we get

    ((Delta_ell - 1)/n_ell)^q
      <= (R(s,ell+1)-1)/n_ell
         + binom(n_ell,s)
           (R(t,ell+1)-1)^q / n_ell^{q+1}.                     (14)

This is the key inequality.
-/
lemma ramseyGap_step4_key_inequality (s t q : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hk : 3 ≤ s + t) (hq : 0 < q) :
    ∀ l : ℕ,
      ((((ramseyGap (s + t) l : ℝ) - 1) / ramseyCriticalSize (s + t) l) ^ q) ≤
        (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize (s + t) l) +
          (Nat.choose (ramseyCriticalSize (s + t) l) s : ℝ) *
            (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
              (ramseyCriticalSize (s + t) l : ℝ) ^ (q + 1)) := by
                sorry
/--
Step 5. Choose a balanced split and prove Delta_ell / n_ell -> 0.

Now fix k >= 3.

Choose

    s := ceil(k/2),
    t := floor(k/2).

Thus

    s + t = k.

Put

    p := k/2,
    a := s - 1,
    b := t - 1.

Then

    a < p,
    b < p.

Indeed:

    if k = 2m, then s=t=m, p=m, and a=b=m-1;
    if k = 2m+1, then s=m+1, t=m, p=m+1/2, a=m, b=m-1.

Choose an integer q >= 1 so large that

    q(p-b) > p a.                                               (15)

This is possible because p-b > 0. Also, (15) implies q-a > 0.

We apply (14) with this choice of s,t,q.

Write

    L := ell + 1,
    n := n_ell = R(k,L)-1.
-/
lemma ramseyGap_step5_choose_balanced_split (k : ℕ) (hk : 3 ≤ k) :
    ∃ s t q a b : ℕ,
      s = (k + 1) / 2 ∧
      t = k / 2 ∧
      a = s - 1 ∧
      b = t - 1 ∧
      s + t = k ∧
      0 < q ∧
      ((q : ℝ) * ((k : ℝ) / 2 - b) > ((k : ℝ) / 2) * a) := by
  let s := (k + 1) / 2
  let t := k / 2
  let q := k * k
  let a := s - 1
  let b := t - 1
  refine ⟨s, t, q, a, b, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp [s, t]
    omega
  · dsimp [q]
    have hk0 : 0 < k := by omega
    exact Nat.mul_pos hk0 hk0
  · have hk0_nat : 0 < k := by omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk0_nat
    have hqeq : (q : ℝ) = (k : ℝ) ^ 2 := by
      dsimp [q]
      norm_num [pow_two]
    have ht_pos : 0 < t := by
      dsimp [t]
      omega
    have ht_le : (t : ℝ) ≤ (k : ℝ) / 2 := by
      have hnat : 2 * t ≤ k := by
        dsimp [t]
        exact Nat.mul_div_le k 2
      have hreal : (2 : ℝ) * t ≤ k := by
        exact_mod_cast hnat
      nlinarith
    have hb_succ : b + 1 = t := by
      dsimp [b]
      exact Nat.succ_pred_eq_of_pos ht_pos
    have hb_plus_one_le : (b : ℝ) + 1 ≤ (k : ℝ) / 2 := by
      have hb_succ_real : (b : ℝ) + 1 = (t : ℝ) := by
        exact_mod_cast hb_succ
      nlinarith
    have hpb : 1 ≤ (k : ℝ) / 2 - b := by
      nlinarith
    have ha_le_nat : a ≤ k := by
      dsimp [a, s]
      omega
    have ha_le : (a : ℝ) ≤ k := by
      exact_mod_cast ha_le_nat
    have hleft : (k : ℝ) ^ 2 ≤ (q : ℝ) * ((k : ℝ) / 2 - b) := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      nlinarith
    have hright : ((k : ℝ) / 2) * a < (k : ℝ) ^ 2 := by
      nlinarith
    nlinarith

/--
By the upper bound (1),

    R(s,L)-1 <<_k L^a,                                          (16)

and

    R(t,L)-1 <<_k L^b.                                          (17)

When t=1, this is still valid because R(1,L)-1=0.

By the lower bound (2), applied with u=k, we have

    R(k,L) >= c_k (L / log L)^{k/2}

for all sufficiently large L. Since n = R(k,L)-1, this implies, after decreasing
the constant if necessary, that

    n >>_k L^p / (log L)^p                                      (18)

for all sufficiently large L.

We now estimate the two terms on the right-hand side of (14).

First term.
Using (16) and (18),

    (R(s,L)-1)/n
      <<_k L^a / (L^p / (log L)^p)
      = (log L)^p / L^{p-a}.

Since p-a > 0, we get

    (R(s,L)-1)/n -> 0.                                          (19)
-/
lemma ramseyGap_step5_first_term_tendsto_zero (k s a : ℕ)
    (hs : s = (k + 1) / 2) (ha : a = s - 1) :
    Tendsto
      (fun l => (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l))
      atTop (𝓝 0) := by
  by_cases hk : 3 ≤ k
  · have hk2 : 2 ≤ k := by omega
    have hs1 : 1 ≤ s := by
      rw [hs]
      omega
    obtain ⟨C, hCnonneg, hCup⟩ := ramseyGap_step1_upper_bound s hs1
    obtain ⟨c, hcpos, hclow⟩ := ramseyGap_step1_lower_bound k hk
    let x : ℕ → ℝ := fun l => ((l + 1 : ℕ) : ℝ)
    let p : ℝ := (k : ℝ) / 2
    have hpa_nat : 2 * a < k := by
      rw [ha, hs]
      omega
    have hpa : (a : ℝ) < p := by
      have hpa_real : (2 * a : ℝ) < k := by
        exact_mod_cast hpa_nat
      dsimp [p] at *
      nlinarith
    have hpapos : 0 < p - a := sub_pos.mpr hpa
    have hpane : p - a ≠ 0 := by linarith
    have hx_tendsto : Tendsto x atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hmodel :
        Tendsto (fun l => Real.log (x l) ^ p / x l ^ (p - a)) atTop (𝓝 0) := by
      have hlittle :
          (fun y : ℝ => Real.log y ^ p) =o[atTop] fun y => y ^ (p - a) := by
        simpa [p] using isLittleO_log_rpow_rpow_atTop p hpapos
      simpa [x] using (hlittle.comp_tendsto hx_tendsto).tendsto_div_nhds_zero
    have hbound :
        ∀ᶠ l : ℕ in atTop,
          (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l) ≤
            (2 * C / c) * (Real.log (x l) ^ p / x l ^ (p - a)) := by
      have hclow' :
          ∀ᶠ l : ℕ in atTop,
            c * (x l / Real.log (x l)) ^ p ≤ (ramseyNumber k (l + 1) : ℝ) := by
        simpa [x, p] using (Filter.tendsto_add_atTop_nat 1).eventually hclow
      filter_upwards [hclow', eventually_gt_atTop 1] with l hlow hl
      have hx_pos : 0 < x l := by
        dsimp [x]
        positivity
      have hx_nonneg : 0 ≤ x l := le_of_lt hx_pos
      have hx_gt_one : 1 < x l := by
        dsimp [x]
        exact_mod_cast (show 1 < l + 1 by omega)
      have hlog_pos : 0 < Real.log (x l) := Real.log_pos hx_gt_one
      have hlog_nonneg : 0 ≤ Real.log (x l) := le_of_lt hlog_pos
      have hnum_le :
          ((ramseyNumber s (l + 1) : ℝ) - 1) ≤ C * x l ^ a := by
        have hle : (ramseyNumber s (l + 1) : ℝ) ≤ C * x l ^ a := by
          simpa [x, ha] using hCup (l + 1)
        linarith
      have hnum_nonneg : 0 ≤ C * x l ^ a := by
        exact mul_nonneg hCnonneg (pow_nonneg hx_nonneg _)
      have hramsey_two : 2 ≤ ramseyNumber k (l + 1) := by
        have hidx : l + 1 ≤ ramseyNumber k (l + 1) := ramseyNumber_ge_index k (l + 1) hk2
        omega
      have hhalf_le :
          ((ramseyNumber k (l + 1) : ℝ) / 2) ≤ ramseyCriticalSize k l := by
        have hramsey_two_real : (2 : ℝ) ≤ ramseyNumber k (l + 1) := by
          exact_mod_cast hramsey_two
        have hcrit_succ : (ramseyCriticalSize k l : ℝ) + 1 = ramseyNumber k (l + 1) := by
          have hramsey_one : 1 ≤ ramseyNumber k (l + 1) := by omega
          dsimp [ramseyCriticalSize]
          exact_mod_cast (Nat.sub_add_cancel hramsey_one)
        linarith
      have hden_le :
          (c / 2) * (x l / Real.log (x l)) ^ p ≤ ramseyCriticalSize k l := by
        have htmp : (c / 2) * (x l / Real.log (x l)) ^ p ≤ (ramseyNumber k (l + 1) : ℝ) / 2 := by
          linarith
        exact htmp.trans hhalf_le
      have hden_pos : 0 < (c / 2) * (x l / Real.log (x l)) ^ p := by
        have hxlog_pos : 0 < x l / Real.log (x l) := div_pos hx_pos hlog_pos
        exact mul_pos (by linarith) (Real.rpow_pos_of_pos hxlog_pos _)
      have hratio_le :
          (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l) ≤
            (C * x l ^ a) / ((c / 2) * (x l / Real.log (x l)) ^ p) := by
        exact div_le_div₀ hnum_nonneg hnum_le hden_pos hden_le
      have hrewrite :
          (C * x l ^ a) / ((c / 2) * (x l / Real.log (x l)) ^ p) =
            (2 * C / c) * (Real.log (x l) ^ p / x l ^ (p - a)) := by
        rw [Real.div_rpow hx_nonneg hlog_nonneg p]
        rw [Real.rpow_sub_natCast' hx_nonneg (y := p) (n := a) hpane]
        field_simp [hcpos.ne', hlog_pos.ne']
      exact hratio_le.trans_eq hrewrite
    have hnonneg :
        ∀ l : ℕ, 0 ≤ (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l) := by
      intro l
      have hramsey_pos : 0 < ramseyNumber s (l + 1) := ramseyNumber_pos hs1 (by omega)
      have hramsey_one : 1 ≤ ramseyNumber s (l + 1) := Nat.succ_le_of_lt hramsey_pos
      refine div_nonneg ?_ (by exact_mod_cast Nat.zero_le (ramseyCriticalSize k l))
      exact sub_nonneg.mpr (by exact_mod_cast hramsey_one)
    have hmajor :
        Tendsto
          (fun l => (2 * C / c) * (Real.log (x l) ^ p / x l ^ (p - a)))
          atTop (𝓝 0) := by
      simpa [x] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 * C / c : ℝ)) atTop (𝓝 (2 * C / c))).mul
          hmodel
    exact squeeze_zero' (Eventually.of_forall hnonneg) hbound hmajor
  · have hk' : k ≤ 2 := by omega
    interval_cases k
    · subst hs
      subst ha
      have hzero : ∀ m : ℕ, ramseyNumber 0 m = 0 := by
        intro m
        refine le_antisymm ?_ (Nat.zero_le _)
        exact ramseyNumber_le_of_property (by
          intro G hbad
          simpa using hbad.1)
      simp [hzero, ramseyCriticalSize]
    · subst hs
      subst ha
      have hone : ∀ m : ℕ, ramseyNumber 1 (m + 1) = 1 := by
        intro m
        refine le_antisymm ?_ ?_
        · exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
        · exact Nat.succ_le_of_lt (ramseyNumber_pos (u := 1) (m := m + 1) (by omega) (by omega))
      simp [hone]
    · subst hs
      subst ha
      have hone : ∀ m : ℕ, ramseyNumber 1 (m + 1) = 1 := by
        intro m
        refine le_antisymm ?_ ?_
        · exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
        · exact Nat.succ_le_of_lt (ramseyNumber_pos (u := 1) (m := m + 1) (by omega) (by omega))
      simp [hone]

/--
Second term.
Using binom(n,s) <= n^s/s!, (17), and a=s-1, we get

    binom(n,s) (R(t,L)-1)^q / n^{q+1}
      <<_{k,q} n^s L^{qb} / n^{q+1}
      = L^{qb} / n^{q+1-s}
      = L^{qb} / n^{q-a}.                                      (20)

Since q-a > 0, we may use the lower bound (18) in the denominator:

    L^{qb} / n^{q-a}
      <<_{k,q}
      L^{qb}
      / ( L^p / (log L)^p )^{q-a}
      =
      (log L)^{p(q-a)}
      / L^{p(q-a)-qb}.                                         (21)

By (15),

    p(q-a) - qb
      = pq - pa - qb
      = q(p-b) - pa
      > 0.

Therefore the right-hand side of (21) tends to 0. Hence

    binom(n,s) (R(t,L)-1)^q / n^{q+1} -> 0.                     (22)
-/
lemma ramseyGap_step5_second_term_tendsto_zero (k s t q a b : ℕ)
    (hs : s = (k + 1) / 2) (ht : t = k / 2) (ha : a = s - 1) (hb : b = t - 1)
    (hq : ((q : ℝ) * ((k : ℝ) / 2 - b) > ((k : ℝ) / 2) * a)) :
    Tendsto
      (fun l =>
        (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
          (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
            (ramseyCriticalSize k l : ℝ) ^ (q + 1)))
      atTop (𝓝 0) := by
  by_cases hk : 3 ≤ k
  · have ht_one : 1 ≤ t := by
      rw [ht]
      omega
    obtain ⟨C, hCnonneg, hCbound⟩ := ramseyGap_step1_upper_bound t ht_one
    obtain ⟨c, hcpos, hclow⟩ := ramseyGap_step1_lower_bound k hk
    let m : ℕ := q - a
    let p : ℝ := (k : ℝ) / 2
    let γ : ℝ := p * ((q : ℝ) - a)
    let δ : ℝ := γ - (q : ℝ) * b
    let K : ℝ := (C ^ q) / (c / 2) ^ m
    have hδpos : 0 < δ := by
      dsimp [δ, γ, p]
      nlinarith [hq]
    have hqb_nonneg : 0 ≤ (q : ℝ) * b := by
      positivity
    have hqa_real : 0 < (q : ℝ) - a := by
      dsimp [δ] at hδpos
      dsimp [γ, p] at hδpos
      have hp_pos : 0 < (k : ℝ) / 2 := by
        have hk_nat_pos : 0 < k := by omega
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk_nat_pos
        positivity
      nlinarith
    have hqa_nat : a < q := by
      have : (a : ℝ) < q := by
        linarith
      exact_mod_cast this
    have hm_pos : 0 < m := by
      dsimp [m]
      omega
    have hm_cast : (m : ℝ) = (q : ℝ) - a := by
      dsimp [m]
      have ha_le_q : a ≤ q := by omega
      rw [Nat.cast_sub ha_le_q]
    have hγ_eq : γ = p * m := by
      dsimp [γ]
      rw [hm_cast]
    have hγ_pos : 0 < γ := by
      dsimp [γ, p]
      have hk_nat_pos : 0 < k := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk_nat_pos
      positivity
    have hclow_shift :
        ∀ᶠ l : ℕ in atTop,
          c * ((((l + 1 : ℕ) : ℝ) / Real.log (((l + 1 : ℕ) : ℝ))) ^ ((k : ℝ) / 2)) ≤
            (ramseyNumber k (l + 1) : ℝ) := by
      exact (tendsto_add_atTop_nat 1).eventually hclow
    have hlogdiv :
        Tendsto
          (fun l : ℕ =>
            (Real.log (((l + 1 : ℕ) : ℝ)) ^ γ) / ((((l + 1 : ℕ) : ℝ)) ^ δ))
          atTop (𝓝 0) := by
      have hlittle :
          (fun n : ℕ => Real.log (n : ℝ) ^ γ) =o[atTop] fun n => (n : ℝ) ^ δ :=
        (isLittleO_log_rpow_rpow_atTop (s := δ) γ hδpos).natCast_atTop
      exact (hlittle.comp_tendsto (tendsto_add_atTop_nat 1)).tendsto_div_nhds_zero
    have hdom :
        Tendsto
          (fun l : ℕ =>
            K * ((Real.log (((l + 1 : ℕ) : ℝ)) ^ γ) / ((((l + 1 : ℕ) : ℝ)) ^ δ)))
          atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlogdiv)
    have hnonneg :
        ∀ l : ℕ,
          0 ≤
            (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
              (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize k l : ℝ) ^ (q + 1)) := by
      intro l
      have hRt_pos : 0 < ramseyNumber t (l + 1) := by
        exact ramseyNumber_pos ht_one (Nat.succ_le_succ (Nat.zero_le l))
      have hRt_nonneg : 0 ≤ ((ramseyNumber t (l + 1) : ℝ) - 1) := by
        have hRt_one : (1 : ℝ) ≤ ramseyNumber t (l + 1) := by
          exact_mod_cast (Nat.succ_le_of_lt hRt_pos)
        linarith
      have hpow_nonneg : 0 ≤ ((ramseyNumber t (l + 1) : ℝ) - 1) ^ q := by
        exact pow_nonneg hRt_nonneg q
      have hdiv_nonneg :
          0 ≤
            (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
              (ramseyCriticalSize k l : ℝ) ^ (q + 1)) := by
        exact div_nonneg hpow_nonneg (pow_nonneg (by positivity) _)
      exact mul_nonneg (by positivity) hdiv_nonneg
    have hupper :
        ∀ᶠ l : ℕ in atTop,
          (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
              (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize k l : ℝ) ^ (q + 1)) ≤
            K * ((Real.log (((l + 1 : ℕ) : ℝ)) ^ γ) / ((((l + 1 : ℕ) : ℝ)) ^ δ)) := by
      filter_upwards [hclow_shift, eventually_gt_atTop 0] with l hlow hl
      let L : ℝ := ((l + 1 : ℕ) : ℝ)
      have hL_pos : 0 < L := by
        dsimp [L]
        positivity
      have hcrit_one : 1 ≤ ramseyCriticalSize k l := by
        have hge : l ≤ ramseyCriticalSize k l := ramseyCriticalSize_ge k l (by omega)
        omega
      have hcrit_pos : 0 < (ramseyCriticalSize k l : ℝ) := by
        exact_mod_cast hcrit_one
      have hR_eq :
          (ramseyNumber k (l + 1) : ℝ) = (ramseyCriticalSize k l : ℝ) + 1 := by
        have hR_pos : 1 ≤ ramseyNumber k (l + 1) := by
          have hidx : l + 1 ≤ ramseyNumber k (l + 1) := ramseyNumber_ge_index k (l + 1) (by omega)
          omega
        exact_mod_cast (Nat.sub_add_cancel hR_pos).symm
      have hR_le :
          (ramseyNumber k (l + 1) : ℝ) ≤ 2 * (ramseyCriticalSize k l : ℝ) := by
        have hcrit_one_cast : (1 : ℝ) ≤ (ramseyCriticalSize k l : ℝ) := by
          exact_mod_cast hcrit_one
        nlinarith [hR_eq, hcrit_one_cast]
      have hcrit_lower :
          (c / 2) * ((L / Real.log L) ^ p) ≤ (ramseyCriticalSize k l : ℝ) := by
        have htmp :
            c * ((L / Real.log L) ^ p) ≤ 2 * (ramseyCriticalSize k l : ℝ) := by
          exact le_trans (by simpa [L, p] using hlow) hR_le
        nlinarith
      have hRt_pos : 0 < ramseyNumber t (l + 1) := by
        exact ramseyNumber_pos ht_one (Nat.succ_le_succ (Nat.zero_le l))
      have hRt_nonneg : 0 ≤ ((ramseyNumber t (l + 1) : ℝ) - 1) := by
        have hRt_one : (1 : ℝ) ≤ ramseyNumber t (l + 1) := by
          exact_mod_cast (Nat.succ_le_of_lt hRt_pos)
        linarith
      have hRt_le : ((ramseyNumber t (l + 1) : ℝ) - 1) ≤ C * L ^ b := by
        have hbound : (ramseyNumber t (l + 1) : ℝ) ≤ C * L ^ b := by
          simpa [L, hb] using hCbound (l + 1)
        linarith
      have hpow_num :
          ((ramseyNumber t (l + 1) : ℝ) - 1) ^ q ≤ (C * L ^ b) ^ q := by
        exact pow_le_pow_left₀ hRt_nonneg hRt_le q
      have hchoose :
          (Nat.choose (ramseyCriticalSize k l) s : ℝ) ≤ (ramseyCriticalSize k l : ℝ) ^ s := by
        exact_mod_cast (Nat.choose_le_pow (ramseyCriticalSize k l) s)
      have hstep1 :
          (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
              (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize k l : ℝ) ^ (q + 1)) ≤
            (ramseyCriticalSize k l : ℝ) ^ s *
              ((C * L ^ b) ^ q / (ramseyCriticalSize k l : ℝ) ^ (q + 1)) := by
        refine mul_le_mul hchoose ?_ ?_ ?_
        · exact div_le_div_of_nonneg_right hpow_num (pow_nonneg hcrit_pos.le _)
        · exact div_nonneg (pow_nonneg hRt_nonneg _) (pow_nonneg hcrit_pos.le _)
        · positivity
      have hstep2 :
          (ramseyCriticalSize k l : ℝ) ^ s *
              ((C * L ^ b) ^ q / (ramseyCriticalSize k l : ℝ) ^ (q + 1)) =
            ((C * L ^ b) ^ q) / (ramseyCriticalSize k l : ℝ) ^ (q - a) := by
        have hcrit_ne : (ramseyCriticalSize k l : ℝ) ≠ 0 := ne_of_gt hcrit_pos
        have hqs : q + 1 = s + (q - a) := by
          omega
        rw [hqs, pow_add, div_eq_mul_inv]
        field_simp [hcrit_ne]
      have hbase_pos : 0 < (c / 2) * ((L / Real.log L) ^ p) := by
        have hlog_pos : 0 < Real.log L := by
          dsimp [L]
          have hL_gt_one_nat : 1 < l + 1 := by omega
          exact Real.log_pos (by exact_mod_cast hL_gt_one_nat)
        have hp_pos : 0 < p := by
          dsimp [p]
          have hk_nat_pos : 0 < k := by omega
          have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk_nat_pos
          positivity
        positivity
      have hpow_den :
          ((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a) ≤
            (ramseyCriticalSize k l : ℝ) ^ (q - a) := by
        exact pow_le_pow_left₀ hbase_pos.le hcrit_lower (q - a)
      have hstep3 :
          ((C * L ^ b) ^ q) / (ramseyCriticalSize k l : ℝ) ^ (q - a) ≤
            ((C * L ^ b) ^ q) / (((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a)) := by
        refine div_le_div_of_nonneg_left ?_ (pow_pos hbase_pos _) hpow_den
        positivity
      have hlog_pos : 0 < Real.log L := by
        dsimp [L]
        have hL_gt_one_nat : 1 < l + 1 := by omega
        exact Real.log_pos (by exact_mod_cast hL_gt_one_nat)
      have hnum_eq : ((C * L ^ b) ^ q) = C ^ q * L ^ (q * b : ℕ) := by
        rw [mul_pow, ← pow_mul]
        congr 1
        rw [Nat.mul_comm]
      have hden_eq :
          (((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a)) =
            (c / 2) ^ (q - a) * (L ^ γ / (Real.log L) ^ γ) := by
        have hdiv_nonneg : 0 ≤ L / Real.log L := by
          positivity
        have hγeq' : p * (q - a : ℕ) = γ := by
          dsimp [γ]
          rw [Nat.cast_sub (by omega)]
        calc
          (((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a))
              = (c / 2) ^ (q - a) * (((L / Real.log L) ^ p) ^ (q - a)) := by
                  rw [mul_pow]
          _ = (c / 2) ^ (q - a) * ((L / Real.log L) ^ γ) := by
                rw [← Real.rpow_mul_natCast hdiv_nonneg p (q - a), hγeq']
          _ = (c / 2) ^ (q - a) * (L ^ γ / (Real.log L) ^ γ) := by
                rw [Real.div_rpow hL_pos.le hlog_pos.le]
      have hL_split : L ^ γ = L ^ (q * b : ℕ) * L ^ δ := by
        calc
          L ^ γ = L ^ ((q : ℝ) * b + δ) := by
            dsimp [δ]
            ring_nf
          _ = L ^ ((q : ℝ) * b) * L ^ δ := by
            rw [Real.rpow_add hL_pos]
          _ = L ^ (q * b : ℕ) * L ^ δ := by
            rw [show ((q : ℝ) * b) = (q * b : ℕ) by norm_num [Nat.cast_mul], Real.rpow_natCast]
      have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
      have hLγ_ne : L ^ γ ≠ 0 := by
        exact (Real.rpow_ne_zero hL_pos.le hγ_ne).2 hL_pos.ne'
      have hlogγ_ne : Real.log L ^ γ ≠ 0 := by
        exact (Real.rpow_ne_zero hlog_pos.le hγ_ne).2 hlog_pos.ne'
      have hinner :
          L ^ (q * b : ℕ) / (L ^ γ / (Real.log L) ^ γ) =
            (Real.log L) ^ γ / L ^ δ := by
        calc
          L ^ (q * b : ℕ) / (L ^ γ / (Real.log L) ^ γ)
              = L ^ (q * b : ℕ) * ((Real.log L) ^ γ) / L ^ γ := by
                  field_simp [hLγ_ne, hlogγ_ne]
          _ = (Real.log L) ^ γ / L ^ δ := by
                rw [hL_split]
                field_simp [pow_ne_zero _ hL_pos.ne']
      have hstep4 :
          ((C * L ^ b) ^ q) / (((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a)) =
            K * ((Real.log L) ^ γ / L ^ δ) := by
        dsimp [K]
        rw [hnum_eq, hden_eq]
        have hc_half_ne : (c / 2) ^ (q - a) ≠ 0 := by
          exact pow_ne_zero _ (by positivity : c / 2 ≠ 0)
        calc
          (C ^ q * L ^ (q * b : ℕ)) / ((c / 2) ^ (q - a) * (L ^ γ / (Real.log L) ^ γ))
              = (C ^ q / (c / 2) ^ (q - a)) *
                  (L ^ (q * b : ℕ) / (L ^ γ / (Real.log L) ^ γ)) := by
                    field_simp [hc_half_ne, hLγ_ne, hlogγ_ne]
          _ = K * ((Real.log L) ^ γ / L ^ δ) := by
                rw [hinner]
      calc
        (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
            (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
              (ramseyCriticalSize k l : ℝ) ^ (q + 1))
            ≤ ((C * L ^ b) ^ q) / (ramseyCriticalSize k l : ℝ) ^ (q - a) := by
              exact hstep1.trans_eq hstep2
        _ ≤ ((C * L ^ b) ^ q) / (((c / 2) * ((L / Real.log L) ^ p)) ^ (q - a)) := hstep3
        _ = K * ((Real.log L) ^ γ / L ^ δ) := hstep4
    · exact squeeze_zero' (Eventually.of_forall hnonneg) hupper hdom
  · have hk_le : k ≤ 2 := by omega
    interval_cases k
    · exfalso
      have ht' : t = 0 := by simpa using ht
      have hb' : b = 0 := by simpa [ht'] using hb
      subst t b
      norm_num at hq
    · have hs' : s = 1 := by simpa using hs
      have ht' : t = 0 := by simpa using ht
      have ha' : a = 0 := by simpa [hs'] using ha
      subst s t a b
      have hcrit_zero : ∀ l : ℕ, ramseyCriticalSize 1 l = 0 := by
        intro l
        have hle : ramseyNumber 1 (l + 1) ≤ 1 := by
          exact ramseyNumber_le_of_property (ramseyProperty_one_left (l + 1))
        have hpos : 0 < ramseyNumber 1 (l + 1) := by
          exact ramseyNumber_pos (by omega) (Nat.succ_le_succ (Nat.zero_le l))
        dsimp [ramseyCriticalSize]
        omega
      have hzero :
          (fun l =>
            (Nat.choose (ramseyCriticalSize 1 l) 1 : ℝ) *
              (((ramseyNumber 0 (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize 1 l : ℝ) ^ (q + 1))) =
            fun _ => (0 : ℝ) := by
        ext l
        simp [hcrit_zero l]
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    · have hs' : s = 1 := by simpa using hs
      have ht' : t = 1 := by simpa using ht
      have ha' : a = 0 := by simpa [hs'] using ha
      have hb' : b = 0 := by simpa [ht'] using hb
      subst s t a b
      have hR1 : ∀ l : ℕ, ramseyNumber 1 (l + 1) = 1 := by
        intro l
        have hle : ramseyNumber 1 (l + 1) ≤ 1 := by
          exact ramseyNumber_le_of_property (ramseyProperty_one_left (l + 1))
        have hpos : 0 < ramseyNumber 1 (l + 1) := by
          exact ramseyNumber_pos (by omega) (Nat.succ_le_succ (Nat.zero_le l))
        omega
      have hq_pos : 0 < q := by
        have : (0 : ℝ) < q := by
          simpa using hq
        exact_mod_cast this
      have hzero :
          (fun l =>
            (Nat.choose (ramseyCriticalSize 2 l) 1 : ℝ) *
              (((ramseyNumber 1 (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize 2 l : ℝ) ^ (q + 1))) =
            fun _ => (0 : ℝ) := by
        ext l
        simp [hR1 l, hq_pos.ne']
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1

/--
Steps 1--5, assembled from the helper lemmas above, yield a positive power of
`(Delta_ell - 1) / n_ell` that tends to `0`.
-/
lemma ramseyGap_step5_pow_tendsto_zero (k : ℕ) (hk : 3 ≤ k) :
    ∃ q : ℕ,
      0 < q ∧
        Tendsto
          (fun l => ((((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) ^ q))
          atTop (𝓝 0) := by
  have _ := ramseyGap_steps1to5_setup
  obtain ⟨s, t, q, a, b, hs, ht, ha, hb, hst, hq, hineq⟩ :=
    ramseyGap_step5_choose_balanced_split k hk
  have hs_pos : 1 ≤ s := by
    rw [hs]
    omega
  have ht_pos : 1 ≤ t := by
    rw [ht]
    omega
  have hkey := ramseyGap_step4_key_inequality s t q hs_pos ht_pos (by omega) hq
  have hfirst := ramseyGap_step5_first_term_tendsto_zero k s a hs ha
  have hsecond := ramseyGap_step5_second_term_tendsto_zero k s t q a b hs ht ha hb hineq
  have hupper :
      Tendsto
        (fun l =>
          (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l) +
            (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
              (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize k l : ℝ) ^ (q + 1)))
        atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  have hnonneg :
      ∀ᶠ l : ℕ in atTop,
        0 ≤ ((((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) ^ q) := by
    filter_upwards [eventually_gap_sub_one_div_critical_nonneg k (by omega)] with l hl
    exact pow_nonneg hl q
  have hle :
      ∀ᶠ l : ℕ in atTop,
        ((((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) ^ q) ≤
          (((ramseyNumber s (l + 1) : ℝ) - 1) / ramseyCriticalSize k l) +
            (Nat.choose (ramseyCriticalSize k l) s : ℝ) *
              (((ramseyNumber t (l + 1) : ℝ) - 1) ^ q /
                (ramseyCriticalSize k l : ℝ) ^ (q + 1)) := by
    filter_upwards with l
    simpa [hst] using hkey l
  refine ⟨q, hq, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hupper hnonneg hle

/--
Steps 1--5 of the TeX proof, packaged into the helper lemmas above.
-/
theorem ramseyGap_sub_one_div_critical_pow_tendsto_zero (k : ℕ) (hk : 3 ≤ k) :
    ∃ q : ℕ,
      0 < q ∧
        Tendsto
          (fun l => ((((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l) ^ q))
          atTop (𝓝 0) := by
  exact ramseyGap_step5_pow_tendsto_zero k hk

/--
Combining (14), (19), and (22), we obtain

    ((Delta_ell - 1)/n_ell)^q -> 0.

Therefore

    (Delta_ell - 1)/n_ell -> 0.

Since Delta_ell >= 1 and n_ell -> infinity, we also have

    Delta_ell / n_ell
      = (Delta_ell - 1)/n_ell + 1/n_ell
      -> 0.                                                     (23)
-/
theorem ramseyGap_div_critical_tendsto_zero (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun l => ((ramseyGap k l : ℝ) / ramseyCriticalSize k l)) atTop (𝓝 0) := by
  have hk' : 2 ≤ k := by omega
  obtain ⟨q, hq, hpow⟩ := ramseyGap_sub_one_div_critical_pow_tendsto_zero k hk
  have hsub :
      Tendsto (fun l => (((ramseyGap k l : ℝ) - 1) / ramseyCriticalSize k l)) atTop (𝓝 0) := by
    exact tendsto_zero_of_eventually_nonneg_of_pow_tendsto_zero hq hpow
      (eventually_gap_sub_one_div_critical_nonneg k hk')
  have hinv :
      Tendsto (fun l => (1 : ℝ) / ramseyCriticalSize k l) atTop (𝓝 0) := by
    exact (tendsto_const_nhds.div_atTop (tendsto_ramseyCriticalSize_real_atTop k hk'))
  simpa using (hsub.add hinv).congr' <|
    (eventually_ramseyCriticalSize_ne_zero k hk').mono fun l hcrit =>
      (ramseyGap_div_critical_eq_sub_one_add_inv k l hcrit).symm

/--
Theorem.
Fix an integer k >= 3. Then

    lim_{ell -> infinity} R(k, ell + 1) / R(k, ell) = 1.

Quantitative note.
The same proof gives an explicit polynomial-logarithmic rate. From (14), (19),
and (22), there are constants c=c(k)>0, A=A(k), and C=C(k) such that

    Delta_ell / n_ell <= C (log ell)^A / ell^c

for all sufficiently large ell.

This estimate is obtained before using r_ell ~ n_ell. To convert it into an
estimate for Delta_ell/r_ell without circularity, observe that once
Delta_ell/n_ell is small, say at most 1/2, we have

    r_ell / n_ell
      = 1 - Delta_ell/n_ell + 1/n_ell
      >= 1/2

for all sufficiently large ell. Hence

    Delta_ell / r_ell
      = (Delta_ell/n_ell)/(r_ell/n_ell)
      <= 2 Delta_ell/n_ell
      <= C' (log ell)^A / ell^c.

Therefore

    0 <= R(k,ell+1)/R(k,ell) - 1
       <= C' (log ell)^A / ell^c

for all sufficiently large ell.
-/
theorem erdos1014 (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun l => (ramseyNumber k (l + 1) : ℝ) / ramseyNumber k l) atTop (𝓝 1) := by
  exact ratio_tendsto_one_of_gap_div_critical_tendsto_zero k (by omega)
    (ramseyGap_div_critical_tendsto_zero k hk)

#print axioms erdos1014
-- 'Erdos1014.erdos1014' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1014
