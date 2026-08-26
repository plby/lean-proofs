/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 608.
Informal authors: Zoltán Füredi, Zeinab Maleki; construction described by
Andrzej Grzesik, Ping Hu, and Jan Volec.
Formal authors: Claude Fable 5, Emerson Hsieh.
Source: https://github.com/teorth/erdosproblems/pull/365
https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908
Original Lean version: 4.27.0.
Original Mathlib revision: a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0).
-/
import ErdosProblems.Erdos608.PentCount

set_option linter.mathlibStandardSet false

/-
Erdős 608 — final assembly (lemma-ladder items L5 and L6 of
runs/phase2/erdos-608/CONSTRUCTION.md).

The witness graph `FM m` (a rational specialization of the Füredi–Maleki
template) lives on `V m` (a four-part sum type with
`28m` elements) while the campaign statements quantify over
`SimpleGraph (Fin n)`.  This module transports `FM m` to `Fin (28m)` along
the equivalence `toFin m := Fintype.equivFinOfCardEq (card_V m)` (as the
comap `FMFin m`), carries the two proved cardinalities across (the edge sets
correspond under the injection `Sym2.map (toFin m)`), and discharges the two
campaign targets:

* `disproof`        : `¬ Erdos608.Conjecture` — for `m ≥ 6` the graph
  `FMFin m` on `n = 28m` vertices has `4e = 788m² − 20m > 784m² = n²` edges
  but only `169m² − 5m` pentagonal edges, and
  `9(169m² − 5m) = 1521m² − 45m < 1568m² = 2n²`.
* `strong_disproof` : with `ε = 47/7056` the same witnesses give
  `pent ≤ (2/9 − ε)n²` (indeed `(2/9 − 47/7056)·784 = 169`).
-/

namespace Erdos608

/-! ## Transport of `OnC5`, `edgeSet` and `pentEdges` along an equivalence -/

section Transport

variable {α β : Type*}

/-- `OnC5` pushes forward through any injective adjacency-preserving map. -/
lemma OnC5.map {f : α → β} (hf : Function.Injective f)
    {G : SimpleGraph α} {G' : SimpleGraph β}
    (hadj : ∀ x y, G.Adj x y → G'.Adj (f x) (f y)) {s : Sym2 α}
    (h : OnC5 G s) : OnC5 G' (Sym2.map f s) := by
  obtain ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde,
    h1, h2, h3, h4, h5, hedge⟩ := h
  refine ⟨f a, f b, f c, f d, f e, hf.ne hab, hf.ne hac, hf.ne had, hf.ne hae,
    hf.ne hbc, hf.ne hbd, hf.ne hbe, hf.ne hcd, hf.ne hce, hf.ne hde,
    hadj _ _ h1, hadj _ _ h2, hadj _ _ h3, hadj _ _ h4, hadj _ _ h5, ?_⟩
  rcases hedge with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The edge set of the comap of `G` along `e.symm` is the image of the edge
set of `G` under `Sym2.map e`. -/
lemma edgeSet_comap_symm (e : α ≃ β) (G : SimpleGraph α) :
    (G.comap e.symm).edgeSet = Sym2.map e '' G.edgeSet := by
  ext s
  induction s using Sym2.ind with
  | _ i j =>
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj, Set.mem_image]
    constructor
    · intro h
      exact ⟨s(e.symm i, e.symm j), h, by simp⟩
    · rintro ⟨t, ht, heq⟩
      have hteq : t = s(e.symm i, e.symm j) := by
        have h' := congrArg (Sym2.map e.symm) heq
        rwa [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq,
          Sym2.map_mk] at h'
      rw [hteq] at ht
      exact ht

/-- The pentagonal edges of the comap of `G` along `e.symm` are the image of
the pentagonal edges of `G` under `Sym2.map e`. -/
lemma pentEdges_comap_symm (e : α ≃ β) (G : SimpleGraph α) :
    pentEdges (G.comap e.symm) = Sym2.map e '' pentEdges G := by
  ext s
  simp only [pentEdges, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hedge, hc5⟩
    rw [edgeSet_comap_symm] at hedge
    obtain ⟨t, ht, rfl⟩ := hedge
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have h' := OnC5.map e.symm.injective
      (G := G.comap e.symm) (G' := G) (fun x y h => h) hc5
    rwa [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq] at h'
  · rintro ⟨t, ⟨ht, htc5⟩, rfl⟩
    constructor
    · rw [edgeSet_comap_symm]
      exact Set.mem_image_of_mem _ ht
    · exact OnC5.map e.injective (fun x y h => by simpa using h) htc5

end Transport

/-! ## The Füredi–Maleki graph on `Fin (28m)` -/

/-- The transfer equivalence `V m ≃ Fin (28m)`. -/
noncomputable def toFin (m : ℕ) : V m ≃ Fin (28 * m) :=
  Fintype.equivFinOfCardEq (card_V m)

/-- The witness graph transported to `Fin (28m)`: the comap of `FM m`
along `(toFin m).symm`. -/
noncomputable def FMFin (m : ℕ) : SimpleGraph (Fin (28 * m)) :=
  (FM m).comap (toFin m).symm

lemma FMFin_edgeSet_ncard (m : ℕ) :
    (FMFin m).edgeSet.ncard = 197 * m ^ 2 - 5 * m := by
  unfold FMFin
  rw [edgeSet_comap_symm,
    Set.ncard_image_of_injective _ (Sym2.map.injective (toFin m).injective)]
  exact edgeSet_ncard m

lemma FMFin_pentEdges_ncard (m : ℕ) (hm : 1 ≤ m) :
    (pentEdges (FMFin m)).ncard = 169 * m ^ 2 - 5 * m := by
  unfold FMFin
  rw [pentEdges_comap_symm,
    Set.ncard_image_of_injective _ (Sym2.map.injective (toFin m).injective)]
  exact pentEdges_ncard m hm

/-- For `m ≥ 6` the transported graph clears the edge threshold:
`n² < 4e` on `n = 28m` vertices. -/
lemma FMFin_threshold (m : ℕ) (hm : 6 ≤ m) :
    (28 * m) ^ 2 < 4 * (FMFin m).edgeSet.ncard := by
  rw [FMFin_edgeSet_ncard]
  have h6 : 6 * m ≤ m ^ 2 := by nlinarith
  have hsq : (28 * m) ^ 2 = 784 * m ^ 2 := by ring
  rw [hsq]
  generalize m ^ 2 = t at h6 ⊢
  omega

/-! ## L5: the main disproof -/

/-- **Main campaign target.** The Füredi–Maleki construction disproves
Erdős 608: no threshold `n₀` makes the conjectured bound hold for all
`n ≥ n₀`, since `FMFin m` (for `m ≥ max 6 n₀`) has more than `n²/4` edges
but fewer than `(2/9)n²` pentagonal edges. -/
theorem disproof : ¬ Erdos608.Conjecture := by
  unfold Conjecture
  rintro ⟨n₀, h⟩
  obtain ⟨m, hm6, hn₀⟩ : ∃ m, 6 ≤ m ∧ n₀ ≤ 28 * m :=
    ⟨max 6 n₀, le_max_left _ _, by omega⟩
  have hcon := h (28 * m) hn₀ (FMFin m) (FMFin_threshold m hm6)
  rw [FMFin_pentEdges_ncard m (by omega)] at hcon
  have h6 : 6 * m ≤ m ^ 2 := by nlinarith
  have hsq : (28 * m) ^ 2 = 784 * m ^ 2 := by ring
  rw [hsq] at hcon
  generalize m ^ 2 = t at h6 hcon
  omega

/-! ## L6: the strong disproof -/

/-- **Secondary campaign target.** With `ε = 47/7056` there are arbitrarily
large `n` and `n`-vertex graphs with more than `n²/4` edges but at most
`(2/9 − ε)n²` pentagonal edges. -/
theorem strong_disproof :
    ∃ ε : ℚ, 0 < ε ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ G : SimpleGraph (Fin n),
      n ^ 2 < 4 * G.edgeSet.ncard ∧
      ((Erdos608.pentEdges G).ncard : ℚ) ≤ (2 / 9 - ε) * (n : ℚ) ^ 2 := by
  refine ⟨47 / 7056, by norm_num, fun N => ?_⟩
  obtain ⟨m, hm6, hN⟩ : ∃ m, 6 ≤ m ∧ N ≤ 28 * m :=
    ⟨max 6 N, le_max_left _ _, by omega⟩
  refine ⟨28 * m, hN, FMFin m, FMFin_threshold m hm6, ?_⟩
  rw [FMFin_pentEdges_ncard m (by omega)]
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  have hle : 5 * m ≤ 169 * m ^ 2 := by nlinarith
  rw [Nat.cast_sub hle]
  push_cast
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  nlinarith [hm0]

end Erdos608
