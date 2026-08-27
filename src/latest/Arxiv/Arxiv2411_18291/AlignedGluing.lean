import Arxiv.Arxiv2411_18291.VertexGluing

/-!
# Aligning the common edge when gluing cliques

The gluing operation in Section 3 must carry the seed's distinguished edge
to a specified edge of the existing clique. This module constructs the
required bijection, rather than assuming its existence.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q r : ℕ}

omit [DecidableEq V] in
/-- A bijection of the chosen `r`-edges extends to a bijection of the enclosing
`q`-cliques, and the resulting vertex gluing identifies the chosen edges. -/
theorem exists_glue_bijection (P : Block V q) (Q : Block W q)
    (d : Block V r) (e : Block W r) (hdP : d.val ⊆ P.val) (heQ : e.val ⊆ Q.val) :
    ∃ σ : Q.val ≃ P.val,
      mapBlock (glueRight P Q σ) e = mapBlock (glueLeft Q.val) d := by
  classical
  let δ : e.val ≃ d.val := Fintype.equivOfCardEq
    (by simp only [Fintype.card_coe, e.property, d.property])
  let σ₀ : Q.val ≃ P.val := Fintype.equivOfCardEq
    (by simp only [Fintype.card_coe, Q.property, P.property])
  let f (x : Q.val) : V :=
    if hx : x.val ∈ e.val then (δ ⟨x.val, hx⟩).val else (σ₀ x).val
  have hmap : Set.MapsTo f {x : Q.val | x.val ∈ e.val} (P.val : Set V) := by
    intro x hx
    change x.val ∈ e.val at hx
    change f x ∈ P.val
    simp only [f, dif_pos hx]
    exact hdP (δ ⟨x.val, hx⟩).property
  have hinj : Set.InjOn f {x : Q.val | x.val ∈ e.val} := by
    intro a ha b hb h
    change a.val ∈ e.val at ha
    change b.val ∈ e.val at hb
    simp only [f, dif_pos ha, dif_pos hb] at h
    have heq : (⟨a.val, ha⟩ : e.val) = ⟨b.val, hb⟩ := δ.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (fun x : e.val => x.val) heq)
  obtain ⟨σ, hσ⟩ := hmap.exists_equiv_extend_of_card_eq
    (by simp only [Fintype.card_coe, Q.property, P.property]) hinj
  have hσedge (w : W) (hw : w ∈ e.val) :
      (σ ⟨w, heQ hw⟩).val = (δ ⟨w, hw⟩).val := by
    simpa only [f, dif_pos hw] using hσ ⟨w, heQ hw⟩ hw
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  ext z
  change z ∈ e.val.map (glueRight P Q σ) ↔ z ∈ d.val.map (glueLeft Q.val)
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
    rw [glueRight_of_mem P Q σ (heQ hw), hσedge w hw]
    exact mem_map.mpr ⟨(δ ⟨w, hw⟩).val, (δ ⟨w, hw⟩).property, rfl⟩
  · intro hz
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hz
    let w := δ.symm ⟨v, hv⟩
    refine mem_map.mpr ⟨w.val, w.property, ?_⟩
    rw [glueRight_of_mem P Q σ (heQ w.property), hσedge w.val w.property]
    change Sum.inl (δ (δ.symm ⟨v, hv⟩)).val = Sum.inl v
    rw [δ.apply_symm_apply]

end Arxiv2411_18291
