/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostCompleteD7Large

/-!
# Extracting the D7 orbit parameters

This file extracts the three separated-unit orbit values used by the large
universal-set correction.  The final normalization is proved by partitioning
the deleted graph's edges into nonuniversal, mixed, and universal pairs.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Two distinct universal vertices other than the distinguished deleted
vertex.  Four universal vertices are more than enough for this choice. -/
noncomputable def d7OtherUniversalPair (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    {p : ↑(universalVertices G) × ↑(universalVertices G) //
      p.1 ≠ z₀ ∧ p.2 ≠ z₀ ∧ p.1 ≠ p.2} := by
  have hcard : 2 < Fintype.card (↑(universalVertices G)) := by
    simpa only [Fintype.card_coe] using (show 2 < (universalVertices G).card by
      omega)
  have htriple : ∃ x y z : ↑(universalVertices G),
      x ≠ y ∧ x ≠ z ∧ y ≠ z := Fintype.two_lt_card_iff.mp hcard
  let x := Classical.choose htriple
  have hx : ∃ y z : ↑(universalVertices G),
      x ≠ y ∧ x ≠ z ∧ y ≠ z := Classical.choose_spec htriple
  let y := Classical.choose hx
  have hy : ∃ z : ↑(universalVertices G),
      x ≠ y ∧ x ≠ z ∧ y ≠ z := Classical.choose_spec hx
  let z := Classical.choose hy
  have hxyz : x ≠ y ∧ x ≠ z ∧ y ≠ z := Classical.choose_spec hy
  rcases hxyz with ⟨hxy, hxz, hyz⟩
  by_cases hzx : z₀ = x
  · exact ⟨(y, z), fun h ↦ hxy (hzx.symm.trans h.symm),
      fun h ↦ hxz (hzx.symm.trans h.symm), hyz⟩
  by_cases hzy : z₀ = y
  · exact ⟨(x, z), fun h ↦ hxy (h.trans hzy),
      fun h ↦ hyz (hzy.symm.trans h.symm), hxz⟩
  · exact ⟨(x, y), fun h ↦ hzx h.symm, fun h ↦ hzy h.symm, hxy⟩

def d7OtherUniversalFirst (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) : ↑(universalVertices G) :=
  (d7OtherUniversalPair G z₀ hm :
    ↑(universalVertices G) × ↑(universalVertices G)).1

def d7OtherUniversalSecond (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) : ↑(universalVertices G) :=
  (d7OtherUniversalPair G z₀ hm :
    ↑(universalVertices G) × ↑(universalVertices G)).2

lemma d7OtherUniversalFirst_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    d7OtherUniversalFirst G z₀ hm ≠ z₀ :=
  (d7OtherUniversalPair G z₀ hm).property.1

lemma d7OtherUniversalSecond_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    d7OtherUniversalSecond G z₀ hm ≠ z₀ :=
  (d7OtherUniversalPair G z₀ hm).property.2.1

lemma d7OtherUniversalFirst_ne_second (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    d7OtherUniversalFirst G z₀ hm ≠ d7OtherUniversalSecond G z₀ hm :=
  (d7OtherUniversalPair G z₀ hm).property.2.2

private lemma d7OtherUniversalFirst_val_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    (d7OtherUniversalFirst G z₀ hm : A) ≠ (z₀ : A) := by
  intro h
  exact d7OtherUniversalFirst_ne G z₀ hm (Subtype.ext h)

private lemma d7OtherUniversalSecond_val_ne (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (hm : 4 ≤ (universalVertices G).card) :
    (d7OtherUniversalSecond G z₀ hm : A) ≠ (z₀ : A) := by
  intro h
  exact d7OtherUniversalSecond_ne G z₀ hm (Subtype.ext h)

/-- The nonuniversal-edge orbit value of the base separated unit. -/
def d7ExtractedBeta (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (e : Sym2 (↑(nonUniversalVertices G))) : ℝ :=
  d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
    ((d7NonUniversalDeletedEmbedding G z₀).sym2Map e)

/-- The mixed-edge orbit value of the base separated unit. -/
def d7ExtractedAlpha (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
    s(d7NonUniversalDeletedEmbedding G z₀ u,
      d7DeletedVertex (z₀ : A) (d7OtherUniversalFirst G z₀ hm : A)
        (d7OtherUniversalFirst_val_ne G z₀ hm))

/-- The universal-pair orbit value of the base separated unit. -/
def d7ExtractedGamma (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card) : ℝ :=
  d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
    s(d7DeletedVertex (z₀ : A) (d7OtherUniversalFirst G z₀ hm : A)
        (d7OtherUniversalFirst_val_ne G z₀ hm),
      d7DeletedVertex (z₀ : A) (d7OtherUniversalSecond G z₀ hm : A)
        (d7OtherUniversalSecond_val_ne G z₀ hm))

lemma d7ExtractedBeta_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    0 ≤ d7ExtractedBeta G z₀ w₀ e := by
  exact d7SeparatedUnit_nonneg hw _

lemma d7ExtractedAlpha_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ d7ExtractedAlpha G z₀ w₀ hm u := by
  exact d7SeparatedUnit_nonneg hw _

lemma d7ExtractedGamma_nonneg (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀) :
    0 ≤ d7ExtractedGamma G z₀ w₀ hm := by
  exact d7SeparatedUnit_nonneg hw _

lemma d7SeparatedUnit_base_mixed_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G))
    (hy : (y : A) ≠ (z₀ : A)) :
    d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7NonUniversalDeletedEmbedding G z₀ u,
          d7DeletedVertex (z₀ : A) (y : A) hy) =
      d7ExtractedAlpha G z₀ w₀ hm u := by
  let u₀ := d7NonUniversalDeletedEmbedding G z₀ u
  let y₀ := d7DeletedVertex (z₀ : A) (y : A) hy
  let r₀ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalFirst G z₀ hm : A)
    (d7OtherUniversalFirst_val_ne G z₀ hm)
  have hu₀ : (u₀ : A) ∉ universalVertices G := by
    exact nonUniversalVertex_not_mem_universalVertices G u.property
  have hy₀ : (y₀ : A) ∈ universalVertices G := y.property
  have hr₀ : (r₀ : A) ∈ universalVertices G :=
    (d7OtherUniversalFirst G z₀ hm).property
  have h := d7SeparatedUnit_mixed_eq_of_invariant G (z₀ : A) w₀ hsymm
    u₀ y₀ r₀ hu₀ hy₀ hr₀
  simpa only [u₀, y₀, r₀, d7ExtractedAlpha] using h

lemma d7SeparatedUnit_base_universal_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (x y : ↑(universalVertices G))
    (hx : (x : A) ≠ (z₀ : A)) (hy : (y : A) ≠ (z₀ : A))
    (hxy : x ≠ y) :
    d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7DeletedVertex (z₀ : A) (x : A) hx,
          d7DeletedVertex (z₀ : A) (y : A) hy) =
      d7ExtractedGamma G z₀ w₀ hm := by
  let x₀ := d7DeletedVertex (z₀ : A) (x : A) hx
  let y₀ := d7DeletedVertex (z₀ : A) (y : A) hy
  let r₀ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalFirst G z₀ hm : A)
    (d7OtherUniversalFirst_val_ne G z₀ hm)
  let s₀ := d7DeletedVertex (z₀ : A)
    (d7OtherUniversalSecond G z₀ hm : A)
    (d7OtherUniversalSecond_val_ne G z₀ hm)
  have hx₀ : (x₀ : A) ∈ universalVertices G := x.property
  have hy₀ : (y₀ : A) ∈ universalVertices G := y.property
  have hr₀ : (r₀ : A) ∈ universalVertices G :=
    (d7OtherUniversalFirst G z₀ hm).property
  have hs₀ : (s₀ : A) ∈ universalVertices G :=
    (d7OtherUniversalSecond G z₀ hm).property
  have hxy₀ : x₀ ≠ y₀ := by
    intro h
    apply hxy
    apply Subtype.ext
    exact congrArg (fun q : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦
      (q : A)) h
  have hrs₀ : r₀ ≠ s₀ := by
    intro h
    apply d7OtherUniversalFirst_ne_second G z₀ hm
    apply Subtype.ext
    exact congrArg (fun q : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦
      (q : A)) h
  have h := d7SeparatedUnit_universal_pair_eq_of_invariant G (z₀ : A) w₀
    hsymm x₀ y₀ r₀ s₀ hx₀ hy₀ hr₀ hs₀ hxy₀ hrs₀
  simpa only [x₀, y₀, r₀, s₀, d7ExtractedGamma] using h

lemma d7SeparatedUnit_coherent_beta_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G))) :
    d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) =
      d7ExtractedBeta G z₀ w₀ e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      have hu₀ : (u : A) ≠ (z₀ : A) := by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G u.property
          (h ▸ z₀.property)
      have huz : (u : A) ≠ (z : A) := by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G u.property
          (h ▸ z.property)
      have hv₀ : (v : A) ≠ (z₀ : A) := by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (h ▸ z₀.property)
      have hvz : (v : A) ≠ (z : A) := by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (h ▸ z.property)
      have h := d7SeparatedUnit_coherent_eq G z₀ z w₀ (u : A) (v : A)
        hu₀ huz hv₀ hvz
      have huzEq : d7NonUniversalDeletedEmbedding G z u =
          d7DeletedVertex (z : A) (u : A) huz := by
        apply Subtype.ext
        rfl
      have hvzEq : d7NonUniversalDeletedEmbedding G z v =
          d7DeletedVertex (z : A) (v : A) hvz := by
        apply Subtype.ext
        rfl
      have hu₀Eq : d7NonUniversalDeletedEmbedding G z₀ u =
          d7DeletedVertex (z₀ : A) (u : A) hu₀ := by
        apply Subtype.ext
        rfl
      have hv₀Eq : d7NonUniversalDeletedEmbedding G z₀ v =
          d7DeletedVertex (z₀ : A) (v : A) hv₀ := by
        apply Subtype.ext
        rfl
      change d7SeparatedUnit (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
          s(d7NonUniversalDeletedEmbedding G z u,
            d7NonUniversalDeletedEmbedding G z v) =
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
          s(d7NonUniversalDeletedEmbedding G z₀ u,
            d7NonUniversalDeletedEmbedding G z₀ v)
      rw [huzEq, hvzEq, hu₀Eq, hv₀Eq]
      exact h

/-- The special coherence identity for an edge whose target-deletion
endpoint is the original distinguished vertex.  Its preimage is the new
deleted vertex. -/
lemma d7SeparatedUnit_coherent_swap_endpoint
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (x : A) (hx₀ : x ≠ (z₀ : A)) (hxz : x ≠ (z : A))
    (hz₀z : (z₀ : A) ≠ (z : A)) :
    d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) x hxz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) =
      d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7DeletedVertex (z₀ : A) x hx₀,
          d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm) := by
  let e₀ : Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A))) :=
    s(d7DeletedVertex (z₀ : A) x hx₀,
      d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm)
  have hmap :
      (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map e₀ =
        s(d7DeletedVertex (z : A) x hxz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) := by
    change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A)) e₀ = _
    rw [show e₀ = s(d7DeletedVertex (z₀ : A) x hx₀,
      d7DeletedVertex (z₀ : A) (z : A) hz₀z.symm) from rfl, Sym2.map_mk]
    congr 1
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      exact Equiv.swap_apply_of_ne_of_ne hx₀ hxz
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val,
        Equiv.swap_apply_right]
  have h := d7SeparatedUnit_d7TransportDeletedWeight G z₀.property z.property
    w₀ e₀
  rw [hmap] at h
  exact h

lemma d7SeparatedUnit_coherent_alpha_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (z y : ↑(universalVertices G))
    (hyz : (y : A) ≠ (z : A)) (u : ↑(nonUniversalVertices G)) :
    d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (y : A) hyz) =
      d7ExtractedAlpha G z₀ w₀ hm u := by
  have hu₀ : (u : A) ≠ (z₀ : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z₀.property)
  have huz : (u : A) ≠ (z : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)
  have huEq : d7NonUniversalDeletedEmbedding G z u =
      d7DeletedVertex (z : A) (u : A) huz := by
    apply Subtype.ext
    rfl
  by_cases hy₀ : (y : A) ≠ (z₀ : A)
  · have hcoh := d7SeparatedUnit_coherent_eq G z₀ z w₀ (u : A) (y : A)
      hu₀ huz hy₀ hyz
    have hbase := d7SeparatedUnit_base_mixed_eq_extracted G z₀ w₀ hm
      hsymm u y hy₀
    have hu₀Eq : d7NonUniversalDeletedEmbedding G z₀ u =
        d7DeletedVertex (z₀ : A) (u : A) hu₀ := by
      apply Subtype.ext
      rfl
    rw [huEq, hcoh, ← hu₀Eq]
    exact hbase
  · have hyEq : y = z₀ := by
      apply Subtype.ext
      exact not_ne_iff.mp hy₀
    subst y
    have hz₀z : (z₀ : A) ≠ (z : A) := hyz
    have hswap := d7SeparatedUnit_coherent_swap_endpoint G z₀ z w₀ (u : A)
      hu₀ huz hz₀z
    have hbase := d7SeparatedUnit_base_mixed_eq_extracted G z₀ w₀ hm
      hsymm u z hz₀z.symm
    have hu₀Eq : d7NonUniversalDeletedEmbedding G z₀ u =
        d7DeletedVertex (z₀ : A) (u : A) hu₀ := by
      apply Subtype.ext
      rfl
    rw [huEq, hswap, ← hu₀Eq]
    exact hbase

lemma d7SeparatedUnit_coherent_gamma_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (hxy : (x : A) ≠ (y : A)) :
    d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz) =
      d7ExtractedGamma G z₀ w₀ hm := by
  by_cases hx₀ : (x : A) ≠ (z₀ : A)
  · by_cases hy₀ : (y : A) ≠ (z₀ : A)
    · have hcoh := d7SeparatedUnit_coherent_eq G z₀ z w₀ (x : A) (y : A)
        hx₀ hxz hy₀ hyz
      have hbase := d7SeparatedUnit_base_universal_eq_extracted G z₀ w₀ hm
        hsymm x y hx₀ hy₀ (by
          intro h
          exact hxy (congrArg Subtype.val h))
      rw [hcoh]
      exact hbase
    · have hyEq : y = z₀ := by
        apply Subtype.ext
        exact not_ne_iff.mp hy₀
      subst y
      have hz₀z : (z₀ : A) ≠ (z : A) := hyz
      have hswap := d7SeparatedUnit_coherent_swap_endpoint G z₀ z w₀ (x : A)
        hx₀ hxz hz₀z
      have hxzSub : x ≠ z := by
        intro h
        exact hxz (congrArg Subtype.val h)
      have hbase := d7SeparatedUnit_base_universal_eq_extracted G z₀ w₀ hm
        hsymm x z hx₀ hz₀z.symm hxzSub
      rw [hswap]
      exact hbase
  · have hxEq : x = z₀ := by
      apply Subtype.ext
      exact not_ne_iff.mp hx₀
    subst x
    have hz₀z : (z₀ : A) ≠ (z : A) := hxz
    have hy₀ : (y : A) ≠ (z₀ : A) := by
      exact hxy.symm
    have hswap := d7SeparatedUnit_coherent_swap_endpoint G z₀ z w₀ (y : A)
      hy₀ hyz hz₀z
    have hyzSub : y ≠ z := by
      intro h
      exact hyz (congrArg Subtype.val h)
    have hbase := d7SeparatedUnit_base_universal_eq_extracted G z₀ w₀ hm
      hsymm y z hy₀ hz₀z.symm hyzSub
    rw [show s(d7DeletedVertex (z : A) (z₀ : A) hz₀z,
          d7DeletedVertex (z : A) (y : A) hyz) =
        s(d7DeletedVertex (z : A) (y : A) hyz,
          d7DeletedVertex (z : A) (z₀ : A) hz₀z) from Sym2.eq_swap,
      hswap]
    exact hbase

/-- The extracted orbit values, packaged once their global orbit-count
normalization has been established. -/
def d7ExtractedSeparatedParameters
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (hnorm :
      ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
            d7ExtractedGamma G z₀ w₀ hm +
        (((universalVertices G).card : ℝ) - 1) *
          ∑ u, d7ExtractedAlpha G z₀ w₀ hm u +
        ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
            d7ExtractedBeta G z₀ w₀ e = 1) :
    D7SeparatedParameters G where
  gamma := d7ExtractedGamma G z₀ w₀ hm
  alpha := d7ExtractedAlpha G z₀ w₀ hm
  beta := d7ExtractedBeta G z₀ w₀
  gamma_nonneg := d7ExtractedGamma_nonneg G z₀ hm hw
  alpha_nonneg := d7ExtractedAlpha_nonneg G z₀ hm hw
  beta_nonneg := fun e _ ↦ d7ExtractedBeta_nonneg G z₀ hw e
  normalization := hnorm

lemma d7ExtractedSeparatedParameters_realizes
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (hnorm :
      ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
            d7ExtractedGamma G z₀ w₀ hm +
        (((universalVertices G).card : ℝ) - 1) *
          ∑ u, d7ExtractedAlpha G z₀ w₀ hm u +
        ∑ e ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset,
            d7ExtractedBeta G z₀ w₀ e = 1) :
    (d7ExtractedSeparatedParameters G z₀ w₀ hm hw hnorm).RealizesCoherentFamily
      G z₀ w₀ := by
  constructor
  · intro z e _he
    change d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) =
      d7ExtractedBeta G z₀ w₀ e
    exact d7SeparatedUnit_coherent_beta_eq_extracted G z₀ w₀ z e
  · intro z y hyz u
    change d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (y : A) hyz) =
      d7ExtractedAlpha G z₀ w₀ hm u
    exact d7SeparatedUnit_coherent_alpha_eq_extracted G z₀ w₀ hm hsymm
      z y hyz u
  · intro z x y hxz hyz hxy
    change d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz) =
      d7ExtractedGamma G z₀ w₀ hm
    exact d7SeparatedUnit_coherent_gamma_eq_extracted G z₀ w₀ hm hsymm
      z x y hxz hyz hxy

/-! ## The three edge orbits in the base deletion -/

def d7RemainingUniversalEmbedding (G : SimpleGraph A) (z₀ : A) :
    d7RemainingUniversalVertices G z₀ ↪
      ↑(d7DeletedFinset (A := A) z₀) :=
  Function.Embedding.subtype _

@[simp] lemma d7RemainingUniversalEmbedding_val (G : SimpleGraph A)
    (z₀ : A) (x : d7RemainingUniversalVertices G z₀) :
    (d7RemainingUniversalEmbedding G z₀ x : A) = (x.1 : A) := rfl

def d7MixedDeletedEdgeEmbedding (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    (↑(nonUniversalVertices G) ×
      d7RemainingUniversalVertices G (z₀ : A)) ↪
        Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A))) where
  toFun p := s(d7NonUniversalDeletedEmbedding G z₀ p.1,
    d7RemainingUniversalEmbedding G (z₀ : A) p.2)
  inj' := by
    intro p q h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · apply Prod.ext
      · exact (d7NonUniversalDeletedEmbedding G z₀).injective h.1
      · exact (d7RemainingUniversalEmbedding G (z₀ : A)).injective h.2
    · exfalso
      have hval := congrArg
        (fun x : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦ (x : A)) h.1
      exact nonUniversalVertex_not_mem_universalVertices G p.1.property
        (hval ▸ q.2.property)

def d7BaseNonUniversalEdges (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Finset (Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A)))) :=
  (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset.map
    (d7NonUniversalDeletedEmbedding G z₀).sym2Map

def d7BaseMixedEdges (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Finset (Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A)))) :=
  Finset.univ.map (d7MixedDeletedEdgeEmbedding G z₀)

def d7BaseUniversalEdges (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Finset (Sym2 (↑(d7DeletedFinset (A := A) (z₀ : A)))) :=
  (⊤ : SimpleGraph (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset.map
    (d7RemainingUniversalEmbedding G (z₀ : A)).sym2Map

def d7RemainingUniversalEquivErase (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    d7RemainingUniversalVertices G (z₀ : A) ≃
      {z : ↑(universalVertices G) // z ≠ z₀} where
  toFun x := ⟨⟨(x.1 : A), x.property⟩, by
    intro h
    have hval : (x.1 : A) = (z₀ : A) := congrArg Subtype.val h
    have hxdel := x.1.property
    simp only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true] at hxdel
    exact hxdel hval⟩
  invFun z := ⟨d7DeletedVertex (z₀ : A) (z : A) (by
      intro h
      exact z.property (Subtype.ext h)), z.1.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma card_d7RemainingUniversalVertices (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Fintype.card (d7RemainingUniversalVertices G (z₀ : A)) =
      (universalVertices G).card - 1 := by
  rw [Fintype.card_congr (d7RemainingUniversalEquivErase G z₀)]
  calc
    Fintype.card {z : ↑(universalVertices G) // z ≠ z₀} =
        Fintype.card (↑(universalVertices G)) -
          Fintype.card {z : ↑(universalVertices G) // z = z₀} := by
      simpa only [ne_eq] using
        (Fintype.card_subtype_compl (fun z : ↑(universalVertices G) ↦ z = z₀))
    _ = (universalVertices G).card - 1 := by
      rw [Fintype.card_coe, Fintype.card_subtype_eq]

lemma d7BaseNonUniversalEdges_subset (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    d7BaseNonUniversalEdges G z₀ ⊆
      (d7DeletedGraph G (z₀ : A)).edgeFinset := by
  intro e he
  rw [d7BaseNonUniversalEdges, Finset.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  exact d7NonUniversalDeletedEdge_mem G z₀ q hq

lemma d7BaseMixedEdges_subset (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    d7BaseMixedEdges G z₀ ⊆
      (d7DeletedGraph G (z₀ : A)).edgeFinset := by
  intro e he
  rw [d7BaseMixedEdges, Finset.mem_map] at he
  obtain ⟨p, _hp, rfl⟩ := he
  rcases p with ⟨u, y⟩
  rw [SimpleGraph.mem_edgeFinset]
  change (d7DeletedGraph G (z₀ : A)).Adj
    (d7NonUniversalDeletedEmbedding G z₀ u)
    (d7RemainingUniversalEmbedding G (z₀ : A) y)
  change G.Adj (u : A) (y.1 : A)
  exact (adj_of_mem_universalVertices G y.property (by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property))).symm

lemma d7BaseUniversalEdges_subset (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    d7BaseUniversalEdges G z₀ ⊆
      (d7DeletedGraph G (z₀ : A)).edgeFinset := by
  intro e he
  rw [d7BaseUniversalEdges, Finset.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  induction q using Sym2.inductionOn with
  | hf x y =>
      rw [SimpleGraph.mem_edgeFinset]
      change (d7DeletedGraph G (z₀ : A)).Adj
        (d7RemainingUniversalEmbedding G (z₀ : A) x)
        (d7RemainingUniversalEmbedding G (z₀ : A) y)
      change G.Adj (x.1 : A) (y.1 : A)
      apply adj_of_mem_universalVertices G x.property
      intro h
      have hxy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        exact h
      have hdiag : s(x, y).IsDiag := by
        simpa only [Sym2.mk_isDiag_iff]
      exact ((⊤ : SimpleGraph
        (d7RemainingUniversalVertices G (z₀ : A))).not_isDiag_of_mem_edgeFinset
          hq) hdiag

lemma d7DeletedGraph_edgeFinset_eq_three_orbits (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    (d7DeletedGraph G (z₀ : A)).edgeFinset =
      (d7BaseNonUniversalEdges G z₀ ∪ d7BaseMixedEdges G z₀) ∪
        d7BaseUniversalEdges G z₀ := by
  apply Finset.Subset.antisymm
  · intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
        have hadj : G.Adj (x : A) (y : A) := by
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          exact he
        have hxy : x ≠ y := by
          intro h
          exact G.ne_of_adj hadj
            (congrArg (fun q : ↑(d7DeletedFinset (A := A) (z₀ : A)) ↦
              (q : A)) h)
        have nonUniversal_of_not_universal : ∀ {v : A},
            v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
          intro v hv
          apply mem_nonUniversalVertices.mpr
          have hvne : Gᶜ.degree v ≠ 0 := by
            intro hz
            exact hv (mem_universalVertices.mpr hz)
          exact Nat.pos_of_ne_zero hvne
        by_cases hxZ : (x : A) ∈ universalVertices G
        · by_cases hyZ : (y : A) ∈ universalVertices G
          · rw [Finset.mem_union]
            right
            rw [d7BaseUniversalEdges, Finset.mem_map]
            let rx : d7RemainingUniversalVertices G (z₀ : A) := ⟨x, hxZ⟩
            let ry : d7RemainingUniversalVertices G (z₀ : A) := ⟨y, hyZ⟩
            refine ⟨s(rx, ry), ?_, ?_⟩
            · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              simp only [SimpleGraph.top_adj]
              intro h
              exact hxy (congrArg Subtype.val h)
            · change Sym2.map (d7RemainingUniversalEmbedding G (z₀ : A))
                s(rx, ry) = s(x, y)
              rw [Sym2.map_mk]
              rfl
          · rw [Finset.mem_union]
            left
            rw [Finset.mem_union]
            right
            rw [d7BaseMixedEdges, Finset.mem_map]
            let uy : ↑(nonUniversalVertices G) :=
              ⟨(y : A), nonUniversal_of_not_universal hyZ⟩
            let rx : d7RemainingUniversalVertices G (z₀ : A) := ⟨x, hxZ⟩
            refine ⟨(uy, rx), Finset.mem_univ _, ?_⟩
            change s(d7NonUniversalDeletedEmbedding G z₀ uy,
              d7RemainingUniversalEmbedding G (z₀ : A) rx) = s(x, y)
            rw [show s(x, y) = s(y, x) from Sym2.eq_swap]
            congr 1 <;> apply Subtype.ext <;> rfl
        · by_cases hyZ : (y : A) ∈ universalVertices G
          · rw [Finset.mem_union]
            left
            rw [Finset.mem_union]
            right
            rw [d7BaseMixedEdges, Finset.mem_map]
            let ux : ↑(nonUniversalVertices G) :=
              ⟨(x : A), nonUniversal_of_not_universal hxZ⟩
            let ry : d7RemainingUniversalVertices G (z₀ : A) := ⟨y, hyZ⟩
            refine ⟨(ux, ry), Finset.mem_univ _, ?_⟩
            change s(d7NonUniversalDeletedEmbedding G z₀ ux,
              d7RemainingUniversalEmbedding G (z₀ : A) ry) = s(x, y)
            congr 1 <;> apply Subtype.ext <;> rfl
          · rw [Finset.mem_union]
            left
            rw [Finset.mem_union]
            left
            rw [d7BaseNonUniversalEdges, Finset.mem_map]
            let ux : ↑(nonUniversalVertices G) :=
              ⟨(x : A), nonUniversal_of_not_universal hxZ⟩
            let uy : ↑(nonUniversalVertices G) :=
              ⟨(y : A), nonUniversal_of_not_universal hyZ⟩
            refine ⟨s(ux, uy), ?_, ?_⟩
            · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              exact hadj
            · change Sym2.map (d7NonUniversalDeletedEmbedding G z₀)
                s(ux, uy) = s(x, y)
              rw [Sym2.map_mk]
              congr 1 <;> apply Subtype.ext <;> rfl
  · intro e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · rw [Finset.mem_union] at he
      rcases he with he | he
      · exact d7BaseNonUniversalEdges_subset G z₀ he
      · exact d7BaseMixedEdges_subset G z₀ he
    · exact d7BaseUniversalEdges_subset G z₀ he

lemma d7BaseNonUniversalEdges_endpoint_not_universal (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {e : Sym2
      (↑(d7DeletedFinset (A := A) (z₀ : A)))}
    (he : e ∈ d7BaseNonUniversalEdges G z₀)
    {x : ↑(d7DeletedFinset (A := A) (z₀ : A))} (hx : x ∈ e) :
    (x : A) ∉ universalVertices G := by
  rw [d7BaseNonUniversalEdges, Finset.mem_map] at he
  obtain ⟨q, _hq, rfl⟩ := he
  change x ∈ Sym2.map (d7NonUniversalDeletedEmbedding G z₀) q at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨u, _hu, rfl⟩ := hx
  exact nonUniversalVertex_not_mem_universalVertices G u.property

lemma d7BaseUniversalEdges_endpoint_universal (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {e : Sym2
      (↑(d7DeletedFinset (A := A) (z₀ : A)))}
    (he : e ∈ d7BaseUniversalEdges G z₀)
    {x : ↑(d7DeletedFinset (A := A) (z₀ : A))} (hx : x ∈ e) :
    (x : A) ∈ universalVertices G := by
  rw [d7BaseUniversalEdges, Finset.mem_map] at he
  obtain ⟨q, _hq, rfl⟩ := he
  change x ∈ Sym2.map (d7RemainingUniversalEmbedding G (z₀ : A)) q at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  exact y.property

lemma d7BaseMixedEdges_has_universal_endpoint (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {e : Sym2
      (↑(d7DeletedFinset (A := A) (z₀ : A)))}
    (he : e ∈ d7BaseMixedEdges G z₀) :
    ∃ x : ↑(d7DeletedFinset (A := A) (z₀ : A)),
      x ∈ e ∧ (x : A) ∈ universalVertices G := by
  rw [d7BaseMixedEdges, Finset.mem_map] at he
  obtain ⟨p, _hp, rfl⟩ := he
  refine ⟨d7RemainingUniversalEmbedding G (z₀ : A) p.2, ?_, p.2.property⟩
  exact Sym2.mem_mk_right _ _

lemma d7BaseMixedEdges_has_nonuniversal_endpoint (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) {e : Sym2
      (↑(d7DeletedFinset (A := A) (z₀ : A)))}
    (he : e ∈ d7BaseMixedEdges G z₀) :
    ∃ x : ↑(d7DeletedFinset (A := A) (z₀ : A)),
      x ∈ e ∧ (x : A) ∉ universalVertices G := by
  rw [d7BaseMixedEdges, Finset.mem_map] at he
  obtain ⟨p, _hp, rfl⟩ := he
  refine ⟨d7NonUniversalDeletedEmbedding G z₀ p.1, ?_, ?_⟩
  · exact Sym2.mem_mk_left _ _
  · exact nonUniversalVertex_not_mem_universalVertices G p.1.property

lemma d7BaseNonUniversalEdges_disjoint_mixed (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Disjoint (d7BaseNonUniversalEdges G z₀) (d7BaseMixedEdges G z₀) := by
  rw [Finset.disjoint_left]
  intro e heN heM
  obtain ⟨x, hxe, hxZ⟩ := d7BaseMixedEdges_has_universal_endpoint G z₀ heM
  exact d7BaseNonUniversalEdges_endpoint_not_universal G z₀ heN hxe hxZ

lemma d7BaseNonUniversalEdges_disjoint_universal (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Disjoint (d7BaseNonUniversalEdges G z₀) (d7BaseUniversalEdges G z₀) := by
  rw [Finset.disjoint_left]
  intro e heN heZ
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxmem : x ∈ s(x, y) := Sym2.mem_mk_left _ _
      exact d7BaseNonUniversalEdges_endpoint_not_universal G z₀ heN hxmem
        (d7BaseUniversalEdges_endpoint_universal G z₀ heZ hxmem)

lemma d7BaseMixedEdges_disjoint_universal (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Disjoint (d7BaseMixedEdges G z₀) (d7BaseUniversalEdges G z₀) := by
  rw [Finset.disjoint_left]
  intro e heM heZ
  obtain ⟨x, hxe, hxNZ⟩ := d7BaseMixedEdges_has_nonuniversal_endpoint G z₀ heM
  exact hxNZ (d7BaseUniversalEdges_endpoint_universal G z₀ heZ hxe)

lemma d7BaseNonUniversalUnionMixed_disjoint_universal (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G)) :
    Disjoint (d7BaseNonUniversalEdges G z₀ ∪ d7BaseMixedEdges G z₀)
      (d7BaseUniversalEdges G z₀) := by
  rw [Finset.disjoint_union_left]
  exact ⟨d7BaseNonUniversalEdges_disjoint_universal G z₀,
    d7BaseMixedEdges_disjoint_universal G z₀⟩

lemma d7SeparatedUnit_base_mixed_remaining_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (u : ↑(nonUniversalVertices G))
    (y : d7RemainingUniversalVertices G (z₀ : A)) :
    d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7NonUniversalDeletedEmbedding G z₀ u,
          d7RemainingUniversalEmbedding G (z₀ : A) y) =
      d7ExtractedAlpha G z₀ w₀ hm u := by
  let yZ : ↑(universalVertices G) := ⟨(y.1 : A), y.property⟩
  have hy : (yZ : A) ≠ (z₀ : A) := by
    have hyDel := y.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, yZ] using hyDel
  have h := d7SeparatedUnit_base_mixed_eq_extracted G z₀ w₀ hm hsymm
    u yZ hy
  have hyEq : d7RemainingUniversalEmbedding G (z₀ : A) y =
      d7DeletedVertex (z₀ : A) (yZ : A) hy := by
    apply Subtype.ext
    rfl
  rw [hyEq]
  exact h

lemma d7SeparatedUnit_base_universal_remaining_eq_extracted
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀)
    (x y : d7RemainingUniversalVertices G (z₀ : A)) (hxy : x ≠ y) :
    d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7RemainingUniversalEmbedding G (z₀ : A) x,
          d7RemainingUniversalEmbedding G (z₀ : A) y) =
      d7ExtractedGamma G z₀ w₀ hm := by
  let xZ : ↑(universalVertices G) := ⟨(x.1 : A), x.property⟩
  let yZ : ↑(universalVertices G) := ⟨(y.1 : A), y.property⟩
  have hx : (xZ : A) ≠ (z₀ : A) := by
    have hxDel := x.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, xZ] using hxDel
  have hy : (yZ : A) ≠ (z₀ : A) := by
    have hyDel := y.1.property
    simpa only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ,
      and_true, yZ] using hyDel
  have hxyZ : xZ ≠ yZ := by
    intro h
    have hval : (x.1 : A) = (y.1 : A) :=
      congrArg (fun q : ↑(universalVertices G) ↦ (q : A)) h
    exact hxy (Subtype.ext (Subtype.ext hval))
  have h := d7SeparatedUnit_base_universal_eq_extracted G z₀ w₀ hm hsymm
    xZ yZ hx hy hxyZ
  have hxEq : d7RemainingUniversalEmbedding G (z₀ : A) x =
      d7DeletedVertex (z₀ : A) (xZ : A) hx := by
    apply Subtype.ext
    rfl
  have hyEq : d7RemainingUniversalEmbedding G (z₀ : A) y =
      d7DeletedVertex (z₀ : A) (yZ : A) hy := by
    apply Subtype.ext
    rfl
  rw [hxEq, hyEq]
  exact h

lemma sum_d7SeparatedUnit_base_nonUniversalEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ) :
    ∑ e ∈ d7BaseNonUniversalEdges G z₀,
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀ e =
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          d7ExtractedBeta G z₀ w₀ e := by
  rw [d7BaseNonUniversalEdges, Finset.sum_map]
  rfl

lemma sum_d7SeparatedUnit_base_mixedEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀) :
    ∑ e ∈ d7BaseMixedEdges G z₀,
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀ e =
      (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d7ExtractedAlpha G z₀ w₀ hm u := by
  rw [d7BaseMixedEdges, Finset.sum_map]
  change (∑ p : (↑(nonUniversalVertices G) ×
      d7RemainingUniversalVertices G (z₀ : A)),
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
          ((d7MixedDeletedEdgeEmbedding G z₀) p)) = _
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ y : d7RemainingUniversalVertices G (z₀ : A),
          d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
            ((d7MixedDeletedEdgeEmbedding G z₀) (u, y))) =
        ∑ u : ↑(nonUniversalVertices G),
          ∑ _y : d7RemainingUniversalVertices G (z₀ : A),
            d7ExtractedAlpha G z₀ w₀ hm u := by
      apply Fintype.sum_congr
      intro u
      apply Fintype.sum_congr
      intro y
      exact d7SeparatedUnit_base_mixed_remaining_eq_extracted G z₀ w₀ hm
        hsymm u y
    _ = ∑ u : ↑(nonUniversalVertices G),
        (Fintype.card (d7RemainingUniversalVertices G (z₀ : A)) : ℝ) *
          d7ExtractedAlpha G z₀ w₀ hm u := by
      apply Fintype.sum_congr
      intro u
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d7ExtractedAlpha G z₀ w₀ hm u := by
      rw [card_d7RemainingUniversalVertices G z₀,
        Nat.cast_sub (by omega : 1 ≤ (universalVertices G).card), Nat.cast_one,
        Finset.mul_sum]

lemma sum_d7SeparatedUnit_base_universalEdges
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀) :
    ∑ e ∈ d7BaseUniversalEdges G z₀,
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀ e =
      ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
        d7ExtractedGamma G z₀ w₀ hm := by
  rw [d7BaseUniversalEdges, Finset.sum_map]
  calc
    (∑ e ∈ (⊤ : SimpleGraph
        (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset,
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
          ((d7RemainingUniversalEmbedding G (z₀ : A)).sym2Map e)) =
        ∑ _e ∈ (⊤ : SimpleGraph
          (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset,
            d7ExtractedGamma G z₀ w₀ hm := by
      apply Finset.sum_congr rfl
      intro e he
      induction e using Sym2.inductionOn with
      | hf x y =>
          have hxy : x ≠ y := by
            exact (⊤ : SimpleGraph
              (d7RemainingUniversalVertices G (z₀ : A))).ne_of_adj
                (SimpleGraph.mem_edgeFinset.mp he)
          change d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
              s(d7RemainingUniversalEmbedding G (z₀ : A) x,
                d7RemainingUniversalEmbedding G (z₀ : A) y) = _
          exact d7SeparatedUnit_base_universal_remaining_eq_extracted G z₀ w₀
            hm hsymm x y hxy
    _ = (((⊤ : SimpleGraph
        (d7RemainingUniversalVertices G (z₀ : A))).edgeFinset.card : ℝ) *
          d7ExtractedGamma G z₀ w₀ hm) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ((((universalVertices G).card : ℝ) - 1) *
          (((universalVertices G).card : ℝ) - 2) / 2) *
        d7ExtractedGamma G z₀ w₀ hm := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
        Nat.cast_choose_two, card_d7RemainingUniversalVertices G z₀]
      have hm1 : 1 ≤ (universalVertices G).card := by omega
      rw [Nat.cast_sub hm1, Nat.cast_one]
      ring

/-- Equation (5.4): the three orbit masses exhaust the canonical separated
unit on the base deletion. -/
lemma d7ExtractedSeparatedParameters_normalization
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (hone : 1 ≤ fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀) :
    ((((universalVertices G).card : ℝ) - 1) *
        (((universalVertices G).card : ℝ) - 2) / 2) *
          d7ExtractedGamma G z₀ w₀ hm +
      (((universalVertices G).card : ℝ) - 1) *
        ∑ u, d7ExtractedAlpha G z₀ w₀ hm u +
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset,
          d7ExtractedBeta G z₀ w₀ e = 1 := by
  have htotal := sum_d7SeparatedUnit (G := d7DeletedGraph G (z₀ : A))
    (w := w₀) hone
  rw [d7DeletedGraph_edgeFinset_eq_three_orbits G z₀,
    Finset.sum_union (d7BaseNonUniversalUnionMixed_disjoint_universal G z₀),
    Finset.sum_union (d7BaseNonUniversalEdges_disjoint_mixed G z₀),
    sum_d7SeparatedUnit_base_nonUniversalEdges G z₀ w₀,
    sum_d7SeparatedUnit_base_mixedEdges G z₀ w₀ hm hsymm,
    sum_d7SeparatedUnit_base_universalEdges G z₀ w₀ hm hsymm] at htotal
  linarith

theorem exists_d7SeparatedParameters_realizing_coherent_family
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (hm : 4 ≤ (universalVertices G).card)
    (hw : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (hone : 1 ≤ fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀)
    (hsymm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
      relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀) :
    ∃ P : D7SeparatedParameters G, P.RealizesCoherentFamily G z₀ w₀ := by
  have hnorm := d7ExtractedSeparatedParameters_normalization G z₀ w₀ hm hw
    hone hsymm
  let P := d7ExtractedSeparatedParameters G z₀ w₀ hm hw hnorm
  refine ⟨P, ?_⟩
  exact d7ExtractedSeparatedParameters_realizes G z₀ w₀ hm hw hsymm hnorm

/-- The large-universal-set subcase of D7, assembled from the induction
packing on one universal-vertex deletion and the extracted orbit correction. -/
theorem d7_large_universal_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : n - 7 ≤ (universalVertices G).card)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  obtain ⟨z₀, w₀, hwPack₀, hwHalf₀, hwUncov₀, hsymm, _hwOne, hfamily⟩ :=
    exists_d7CoherentUniversalDeletedWeights hcard hn ha G hexact hm
      (fun _ ↦ 0) (fun _ ↦ Nat.zero_le _) hstrong
  obtain ⟨P, hreal⟩ := exists_d7SeparatedParameters_realizing_coherent_family
    G z₀ w₀ hm hwPack₀ hwUncov₀.1 hsymm
  apply hasStrongFractionalPacking_d7LargeAverageWeight G z₀ w₀ P hreal
    (hcard ▸ hn) hm (hcard ▸ hlarge)
  · intro z
    exact (hfamily z).1
  · intro z
    exact (hfamily z).2.1
  · intro z
    exact (hfamily z).2.2.1
  · have hupper := hwUncov₀.2
    norm_num [Nat.cast_add, Nat.cast_one] at hupper ⊢
    exact hupper

end

end Erdos76
