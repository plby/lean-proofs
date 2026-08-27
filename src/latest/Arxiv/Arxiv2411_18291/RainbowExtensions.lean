import Arxiv.Arxiv2411_18291.ExtensionColourMoments

/-!
# Rainbow pattern extensions

A rainbow edge family has an injective assignment to colours containing
the assigned edges. A successful group in the colour experiment supplies
such an assignment. An extra unused colour permits empty pattern families.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} {r : ℕ}

def IsRainbow (colour : I → Hypergraph V r) (H : Hypergraph V r) : Prop :=
  ∃ c : H ↪ I, ∀ e : H, e.val ∈ colour (c e)

theorem isRainbow_mapGraph (colour : I → Hypergraph V r) (E : Hypergraph W r)
    (f : W ↪ V) (c : E ↪ I) (hc : ∀ e : E, mapBlock f e.val ∈ colour (c e)) :
    IsRainbow colour (mapGraph f E) := by
  let e : E ≃ mapGraph f E := equivMap (blockEmbedding f) E
  refine ⟨e.symm.toEmbedding.trans c, fun P => ?_⟩
  have hp := hc (e.symm P)
  have he : mapBlock f (e.symm P).val = P.val :=
    congrArg Subtype.val (e.apply_symm_apply P)
  exact he ▸ hp

theorem IsRainbow.mono {colour : I → Hypergraph V r} {H H' : Hypergraph V r}
    (hH : IsRainbow colour H) (hsub : H' ⊆ H) : IsRainbow colour H' := by
  obtain ⟨c, hc⟩ := hH
  let e : H' ↪ H := ⟨fun x => ⟨x.val, hsub x.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : H => z.val) h)⟩
  exact ⟨e.trans c, fun x => hc (e x)⟩

def groupedPermutation {L : ℕ} (ω : Fin L → I → Equiv.Perm V) :
    Option (Fin L × I) → Equiv.Perm V :=
  fun c => c.elim (Equiv.refl V) (fun p => ω p.1 p.2)

variable [Fintype W] [Fintype V] [DecidableEq V] {F : Finset W}

open Classical in
def rainbowExtensions (φ : F ↪ V) (E : Hypergraph W r)
    (σ : I → Equiv.Perm V) (G : Hypergraph V r) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (mapGraph f.val E)

theorem mem_rainbowExtensions (φ : F ↪ V) (E : Hypergraph W r)
    (σ : I → Equiv.Perm V) (G : Hypergraph V r) (f : EmbeddingExtension φ) :
    f ∈ rainbowExtensions φ E σ G ↔
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (mapGraph f.val E) := by
  simp only [rainbowExtensions, mem_filter, mem_univ, true_and]

theorem extensionColourCount_le_rainbow_card (φ : F ↪ V) (E : Hypergraph W r)
    (G : Hypergraph V r) {L : ℕ} (ω : Fin L → E → Equiv.Perm V) (j : Fin L) :
    extensionColourCount φ univ (fun e : E => e.val) univ G (ω j) ≤
      (rainbowExtensions φ E (groupedPermutation ω) G).card := by
  classical
  rw [extensionColourCount_eq_card]
  apply Nat.cast_le.mpr
  apply card_le_card
  intro f hf
  have hcol : ∀ e : E, mapBlock f.val e.val ∈ mapGraph (ω j e).toEmbedding G := by
    simpa only [mem_filter, mem_univ, true_and, forall_const] using hf
  apply (mem_rainbowExtensions φ E (groupedPermutation ω) G f).mpr
  let c : E ↪ Option (Fin L × E) := ⟨fun e => some (j, e),
    fun _ _ h => (Prod.mk.inj (Option.some.inj h)).2⟩
  exact isRainbow_mapGraph _ E f.val c hcol

theorem extensionColourCount_le_rainbow_card_injected (φ : F ↪ V) (E : Hypergraph W r)
    (G : Hypergraph V r) {L : ℕ} (σ : I → Equiv.Perm V) (e : Fin L × E ↪ I) (j : Fin L) :
    extensionColourCount φ univ (fun f : E => f.val) univ G (fun f => σ (e (j, f))) ≤
      (rainbowExtensions φ E σ G).card := by
  classical
  rw [extensionColourCount_eq_card]
  apply Nat.cast_le.mpr
  apply card_le_card
  intro f hf
  have hcol : ∀ P : E, mapBlock f.val P.val ∈ mapGraph (σ (e (j, P))).toEmbedding G := by
    simpa only [mem_filter, mem_univ, true_and, forall_const] using hf
  apply (mem_rainbowExtensions φ E σ G f).mpr
  let c : E ↪ I := ⟨fun P => e (j, P), fun _ _ h => (Prod.mk.inj (e.injective h)).2⟩
  exact isRainbow_mapGraph _ E f.val c hcol

end Arxiv2411_18291
