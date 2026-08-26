/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.EdmondsGallaiDecomposition
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Zhao's Claim 6.17: the reduced-graph switching/counting core

In the notation of Zhao (2011), Section 6.5.3, `Mᵢₙ` is a matching,
`V₁ = V(Mᵢₙ)`, `V₂` is its complement, and

`S₁ = {Y : {X,Y} ∈ Mᵢₙ for some large cluster X}`.

If many vertices of `S₁` have at least `5ρk` neighbors in the part of `V₂`
not reserved by `Mᵦ`, Hall's theorem produces Zhao's switching matching
`M₀'`.  Otherwise, summing the degrees from `S₁` to `V₂` gives
`e_Gᵣ(S₁,V₂) < 16ρk²`.  The parameters below are integral scales:
`r = ρk`, `q = d^(1/4)k`, and `h = ηk`.  The single displayed error
inequality is the exact integer form of the last use of
`d^(1/4), η ≪ ρ` in the source proof.

The principal theorem is a genuine finite dichotomy: it constructs the
switching matching or proves the claimed edge bound.  Its final corollary is
Claim 6.17 under the concrete obstruction that no such switch exists.  No
embedding oracle or copy of the desired conclusion is assumed.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim617

open Finset SimpleGraph
open Erdos547b.ZhaoStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : SimpleGraph ι} [DecidableRel R.Adj]

/-- The partners, on matching edges, of the clusters in `L`.  This is
Zhao's set `S₁` when `M = Mᵢₙ` and `L` is the set of large clusters. -/
noncomputable def matchingPartnerSet (M : R.Subgraph) (L : Finset ι) : Finset ι := by
  classical
  exact (matchingSupport M).filter fun y => ∃ x ∈ L, M.Adj x y

theorem matchingPartnerSet_subset_support (M : R.Subgraph) (L : Finset ι) :
    matchingPartnerSet M L ⊆ matchingSupport M := by
  classical
  exact Finset.filter_subset _ _

/-- The concrete switch made in the proof of Claim 6.17: an `m`-element
subset of `S` is matched injectively to distinct reduced neighbors in `W`.
The injection records the actual new matching edges, not an abstract
"switching is possible" oracle. -/
def HasZhaoSwitch (R : SimpleGraph ι) (S W : Finset ι) (m : ℕ) : Prop :=
  ∃ S₀ : Finset ι, S₀ ⊆ S ∧ S₀.card = m ∧
    ∃ f : {x // x ∈ S₀} → {y // y ∈ W},
      Function.Injective f ∧ ∀ x, R.Adj x.1 (f x).1

/-- The injective adjacent map in `HasZhaoSwitch` really is a subgraph
matching.  This packages it using the Gallai--Edmonds matching constructor
already used elsewhere in Section 6. -/
theorem HasZhaoSwitch.exists_subgraphMatching
    {S W : Finset ι} {m : ℕ} (hSW : Disjoint S W)
    (h : HasZhaoSwitch R S W m) :
    ∃ S₀ : Finset ι, S₀ ⊆ S ∧ S₀.card = m ∧
      ∃ M₀ : R.Subgraph, M₀.IsMatching ∧
        (S₀ : Set ι) ⊆ M₀.verts ∧
        M₀.verts ⊆ (S₀ : Set ι) ∪ (W : Set ι) := by
  classical
  obtain ⟨S₀, hS₀S, hS₀card, f, hfinj, hfadj⟩ := h
  let f' : {x : ι // x ∈ (S₀ : Set ι)} → {y : ι // y ∈ (W : Set ι)} :=
    fun x => ⟨(f ⟨x.1, x.2⟩).1, (f ⟨x.1, x.2⟩).2⟩
  have hf'inj : Function.Injective f' := by
    intro x y hxy
    apply Subtype.ext
    have hfxy : f ⟨x.1, x.2⟩ = f ⟨y.1, y.2⟩ := Subtype.ext (congrArg Subtype.val hxy)
    exact congrArg Subtype.val (hfinj hfxy)
  have hf'adj : ∀ x, R.Adj x.1 (f' x).1 := by
    intro x
    exact hfadj ⟨x.1, x.2⟩
  have hdisj : Disjoint (S₀ : Set ι) (W : Set ι) := by
    rw [Set.disjoint_left]
    intro x hxS₀ hxW
    exact Finset.disjoint_left.mp hSW (hS₀S hxS₀) hxW
  obtain ⟨M₀, hverts, hmatching⟩ :=
    SimpleGraph.IsMatching.exists_of_disjoint_sets_of_injective
      f' hdisj hf'adj hf'inj
  refine ⟨S₀, hS₀S, hS₀card, M₀, hmatching, ?_, ?_⟩
  · rw [hverts]
    exact Set.subset_union_left
  · rw [hverts]
    apply Set.union_subset Set.subset_union_left
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := hz
    exact Set.mem_union_right _ (f' x).2

/-- If at least `2m` vertices of `S` have `m` neighbors in `W`, one can
choose `m` of them and Hall's theorem gives the switch used by Zhao. -/
theorem hasZhaoSwitch_of_many_crossHeavy
    (S W : Finset ι) (m : ℕ)
    (hmany : 2 * m ≤ (Erdos547EC2.crossHeavy R S W m).card) :
    HasZhaoSwitch R S W m := by
  classical
  have hm : m ≤ (Erdos547EC2.crossHeavy R S W m).card := by omega
  obtain ⟨S₀, hS₀heavy, hS₀card⟩ := Finset.exists_subset_card_eq hm
  have hS₀S : S₀ ⊆ S :=
    hS₀heavy.trans (Erdos547EC2.crossHeavy_subset R S W m)
  let choices : {x // x ∈ S₀} → Finset ι := fun x =>
    W.filter fun y => R.Adj x.1 y
  have hchoices (x : {x // x ∈ S₀}) : m ≤ (choices x).card := by
    have hxheavy : x.1 ∈ Erdos547EC2.crossHeavy R S W m := hS₀heavy x.2
    simpa [choices, Erdos547EC2.crossHeavy, Erdos547EC2.degreeInto] using
      (Finset.mem_filter.mp hxheavy).2
  have hHall : ∀ s : Finset {x // x ∈ S₀},
      s.card ≤ (s.biUnion choices).card := by
    intro s
    by_cases hs : s = ∅
    · simp [hs]
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      calc
        s.card ≤ Fintype.card {x // x ∈ S₀} := Finset.card_le_univ s
        _ = S₀.card := Fintype.card_coe S₀
        _ = m := hS₀card
        _ ≤ (choices x).card := hchoices x
        _ ≤ (s.biUnion choices).card := by
          exact Finset.card_le_card (Finset.subset_biUnion_of_mem choices hx)
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  let f' : {x // x ∈ S₀} → {y // y ∈ W} := fun x =>
    ⟨f x, (Finset.mem_filter.mp (hfmem x)).1⟩
  have hf'inj : Function.Injective f' := by
    intro x y hxy
    apply hfinj
    exact congrArg Subtype.val hxy
  refine ⟨S₀, hS₀S, hS₀card, f', hf'inj, ?_⟩
  intro x
  exact (Finset.mem_filter.mp (hfmem x)).2

/-- Deleting a set `B` from the target side loses at most `|B|` neighbors. -/
theorem degreeInto_le_sdiff_add_card
    (v : ι) (V B : Finset ι) :
    Erdos547EC2.degreeInto R v V ≤
      Erdos547EC2.degreeInto R v (V \ B) + B.card := by
  classical
  let A := V.filter fun w => R.Adj v w
  let A' := (V \ B).filter fun w => R.Adj v w
  have hsub : A' ⊆ A := by
    intro w hw
    simp only [A', A, Finset.mem_filter, Finset.mem_sdiff] at hw ⊢
    exact ⟨hw.1.1, hw.2⟩
  have hdiff : A \ A' ⊆ B := by
    intro w hw
    simp only [A, A', Finset.mem_sdiff, Finset.mem_filter] at hw
    by_contra hwB
    exact hw.2 ⟨⟨hw.1.1, hwB⟩, hw.1.2⟩
  have hdecomp : A.card = A'.card + (A \ A').card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    omega
  change A.card ≤ A'.card + B.card
  rw [hdecomp]
  exact Nat.add_le_add_left (Finset.card_le_card hdiff) _

/-- The counting half of Claim 6.17.  If at most `heavyCap` vertices have
`r` neighbors after the reserved matching support is removed, then the
original cut has at most
`heavyCap |V₂| + |S₁| (r + |V(Mᵦ)|)` edges. -/
theorem interedges_le_of_crossHeavy_card_le
    (S₁ V₂ B : Finset ι) (r heavyCap : ℕ)
    (hheavy : (Erdos547EC2.crossHeavy R S₁ (V₂ \ B) r).card ≤ heavyCap) :
    (R.interedges S₁ V₂).card ≤
      heavyCap * V₂.card + S₁.card * (r + B.card) := by
  classical
  let H := Erdos547EC2.crossHeavy R S₁ (V₂ \ B) r
  let L := S₁ \ H
  have hsplit : H ∪ L = S₁ := by
    exact Finset.union_sdiff_of_subset (Erdos547EC2.crossHeavy_subset R S₁ (V₂ \ B) r)
  have hdisj : Disjoint H L := by
    rw [Finset.disjoint_left]
    intro v hvH hvL
    exact (Finset.mem_sdiff.mp hvL).2 hvH
  rw [← Erdos547EC2.sum_degreeInto_eq_card_interedges]
  calc
    (∑ v ∈ S₁, Erdos547EC2.degreeInto R v V₂) =
        (∑ v ∈ H, Erdos547EC2.degreeInto R v V₂) +
          ∑ v ∈ L, Erdos547EC2.degreeInto R v V₂ := by
            rw [← hsplit, Finset.sum_union hdisj]
    _ ≤ H.card * V₂.card + L.card * (r + B.card) := by
          apply Nat.add_le_add
          · simpa [Nat.mul_comm] using Finset.sum_le_card_nsmul H
              (fun v => Erdos547EC2.degreeInto R v V₂) V₂.card
              (fun v _ => Erdos547EC2.degreeInto_le_card R v V₂)
          · simpa [Nat.mul_comm] using Finset.sum_le_card_nsmul L
              (fun v => Erdos547EC2.degreeInto R v V₂) (r + B.card) (by
                intro v hv
                have hvS₁ : v ∈ S₁ := by
                  exact hsplit ▸ Finset.mem_union_right H hv
                have hvnotH : v ∉ H := (Finset.mem_sdiff.mp hv).2
                have hvsmall : Erdos547EC2.degreeInto R v (V₂ \ B) < r := by
                  simpa [H, Erdos547EC2.crossHeavy, hvS₁] using hvnotH
                have hloss := degreeInto_le_sdiff_add_card (R := R) v V₂ B
                omega)
    _ ≤ heavyCap * V₂.card + S₁.card * (r + B.card) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right V₂.card hheavy
      · exact Nat.mul_le_mul_right (r + B.card) (Finset.card_le_card (by
          intro v hv
          exact (Finset.mem_sdiff.mp hv).1))

/-- **Claim 6.17, finite switching dichotomy.**

Here `r = ρk`, `q = d^(1/4)k`, and `h = ηk`.  The matching `Mᵢₙ` defines
`V₁`, `V₂`, and `S₁` exactly as in the paper; `Mᵦ` is the reserved matching.
Either Zhao's replacement matching `M₀'` exists, or the claimed strict
`16ρk²` reduced-edge bound holds. -/
theorem zhaoClaim617_switch_or_sparse
    (Mᵢₙ Mᵦ : R.Subgraph) (L : Finset ι) (k r q h : ℕ)
    (hV₂ : (Finset.univ \ matchingSupport Mᵢₙ).card ≤ k + 8 * h)
    (hMᵦ : (matchingSupport Mᵦ).card ≤ 4 * q)
    (hMᵢₙ : (matchingSupport Mᵢₙ).card ≤ k)
    (herrors : 80 * r * h + 4 * q * k < r * k) :
    HasZhaoSwitch R (matchingPartnerSet Mᵢₙ L)
        ((Finset.univ \ matchingSupport Mᵢₙ) \ matchingSupport Mᵦ) (5 * r) ∨
      (R.interedges (matchingPartnerSet Mᵢₙ L)
        (Finset.univ \ matchingSupport Mᵢₙ)).card < 16 * r * k := by
  classical
  let S₁ := matchingPartnerSet Mᵢₙ L
  let V₂ := Finset.univ \ matchingSupport Mᵢₙ
  let B := matchingSupport Mᵦ
  let V₂' := V₂ \ B
  by_cases hmany : 10 * r ≤ (Erdos547EC2.crossHeavy R S₁ V₂' (5 * r)).card
  · left
    apply hasZhaoSwitch_of_many_crossHeavy
    have harith : 2 * (5 * r) = 10 * r := by omega
    simpa only [harith, S₁, V₂', V₂, B] using hmany
  · right
    have hheavy : (Erdos547EC2.crossHeavy R S₁ V₂' (5 * r)).card ≤ 10 * r := by
      omega
    have hcount := interedges_le_of_crossHeavy_card_le
      (R := R) S₁ V₂ B (5 * r) (10 * r) (by simpa [V₂'] using hheavy)
    have hS₁ : S₁.card ≤ k := by
      exact (Finset.card_le_card (matchingPartnerSet_subset_support Mᵢₙ L)).trans hMᵢₙ
    have hnum :
        10 * r * (k + 8 * h) + k * (5 * r + 4 * q) < 16 * r * k := by
      ring_nf at herrors ⊢
      omega
    exact lt_of_le_of_lt (hcount.trans (by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left (10 * r) hV₂
      · exact Nat.mul_le_mul hS₁ (Nat.add_le_add_left hMᵦ (5 * r)))) hnum

/-- **Zhao 2011, Claim 6.17.**  In the no-switch branch forced in the
paper by `T ⊄ G` and the preceding embedding lemmas, the reduced cut from
`S₁` to `V₂` contains fewer than `16ρk²` edges.  The premise here is the
literal finite matching obstruction, so the theorem has no abstract tree
embedding continuation hypothesis. -/
theorem zhaoClaim617
    (Mᵢₙ Mᵦ : R.Subgraph) (L : Finset ι) (k r q h : ℕ)
    (hV₂ : (Finset.univ \ matchingSupport Mᵢₙ).card ≤ k + 8 * h)
    (hMᵦ : (matchingSupport Mᵦ).card ≤ 4 * q)
    (hMᵢₙ : (matchingSupport Mᵢₙ).card ≤ k)
    (herrors : 80 * r * h + 4 * q * k < r * k)
    (hnoSwitch : ¬ HasZhaoSwitch R (matchingPartnerSet Mᵢₙ L)
      ((Finset.univ \ matchingSupport Mᵢₙ) \ matchingSupport Mᵦ) (5 * r)) :
    (R.interedges (matchingPartnerSet Mᵢₙ L)
      (Finset.univ \ matchingSupport Mᵢₙ)).card < 16 * r * k := by
  rcases zhaoClaim617_switch_or_sparse Mᵢₙ Mᵦ L k r q h
      hV₂ hMᵦ hMᵢₙ herrors with hswitch | hsparse
  · exact False.elim (hnoSwitch hswitch)
  · exact hsparse

/-- Literal real-valued form of the published inequality
`e_{Gᵣ}(S₁,V₂) < 16 ρ k²`.  It is enough that the integral
threshold `r` be rounded down from `ρ k`; no generally impossible exact
cast equality is required. -/
theorem zhaoClaim617_realScale
    (Mᵢₙ Mᵦ : R.Subgraph) (L : Finset ι) (k r q h : ℕ) (ρ : ℝ)
    (hV₂ : (Finset.univ \ matchingSupport Mᵢₙ).card ≤ k + 8 * h)
    (hMᵦ : (matchingSupport Mᵦ).card ≤ 4 * q)
    (hMᵢₙ : (matchingSupport Mᵢₙ).card ≤ k)
    (herrors : 80 * r * h + 4 * q * k < r * k)
    (hscale : (r : ℝ) ≤ ρ * k)
    (hnoSwitch : ¬ HasZhaoSwitch R (matchingPartnerSet Mᵢₙ L)
      ((Finset.univ \ matchingSupport Mᵢₙ) \ matchingSupport Mᵦ) (5 * r)) :
    ((R.interedges (matchingPartnerSet Mᵢₙ L)
      (Finset.univ \ matchingSupport Mᵢₙ)).card : ℝ) <
        16 * ρ * (k : ℝ) ^ 2 := by
  have hnat := zhaoClaim617 Mᵢₙ Mᵦ L k r q h
    hV₂ hMᵦ hMᵢₙ herrors hnoSwitch
  calc
    ((R.interedges (matchingPartnerSet Mᵢₙ L)
        (Finset.univ \ matchingSupport Mᵢₙ)).card : ℝ)
        < (16 * r * k : ℕ) := by exact_mod_cast hnat
    _ ≤ 16 * ρ * (k : ℝ) ^ 2 := by
      push_cast
      calc
        16 * (r : ℝ) * (k : ℝ) ≤
            16 * (ρ * (k : ℝ)) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscale (by norm_num)) (by positivity)
        _ = 16 * ρ * (k : ℝ) ^ 2 := by ring

end Erdos547b.ZhaoClaim617

#print axioms Erdos547b.ZhaoClaim617.hasZhaoSwitch_of_many_crossHeavy
#print axioms Erdos547b.ZhaoClaim617.zhaoClaim617_switch_or_sparse
#print axioms Erdos547b.ZhaoClaim617.zhaoClaim617
#print axioms Erdos547b.ZhaoClaim617.zhaoClaim617_realScale
