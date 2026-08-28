import ErdosProblems.Erdos577.Remainders

/-! Transport of positive finite exchange witnesses to arbitrary vertex types. -/

namespace Erdos577

open Finset Function

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

lemma QuadOn.image {s : Finset V} (h : QuadOn G s) (f : G.Copy H) :
    QuadOn H (s.image f) := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨f.comp q, ?_⟩
  simp only [Quadrilateral.support, SimpleGraph.Copy.coe_comp, image_image]

omit [DecidableEq V] in
lemma TriangleIn.image {s : Finset V} (h : TriangleIn G s) (f : G.Copy H) :
    TriangleIn H (s.image f) := by
  obtain ⟨t, hts, ht⟩ := h
  refine ⟨t.image f, image_subset_image hts, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    exact f.toHom.map_rel' (ht.isClique hx hy (fun he ↦ hab (congrArg f he)))
  · have hinj : Injective (f : V → W) := f.injective
    rw [card_image_of_injective _ hinj, ht.card_eq]

/-- The local conclusion is a genuine four-cycle, with either another
four-cycle or a triangle among the remaining vertices. -/
def LocalExchange (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ q ⊆ s, QuadOn G q ∧ (QuadOn G (s \ q) ∨ TriangleIn G (s \ q))

namespace LocalExchange

lemma image {s : Finset V} (h : LocalExchange G s) (f : G.Copy H) :
    LocalExchange H (s.image f) := by
  obtain ⟨q, hqs, hq, hr⟩ := h
  refine ⟨q.image f, image_subset_image hqs, hq.image f, ?_⟩
  have hinj : Injective (f : V → W) := f.injective
  have he : (s \ q).image f = s.image f \ q.image f := image_sdiff s q hinj
  rcases hr with hr | hr
  · exact Or.inl (he ▸ hr.image f)
  · exact Or.inr (he ▸ hr.image f)

lemma mono {J : SimpleGraph V} {s : Finset V} (h : LocalExchange G s) (hGJ : G ≤ J) :
    LocalExchange J s := by
  have hm := h.image (SimpleGraph.Copy.ofLE G J hGJ)
  simpa only [SimpleGraph.Copy.coe_ofLE, image_id] using hm

end LocalExchange

namespace PathExchange

/-- The seven compulsory undirected edges are stored in one orientation. -/
def basePairs : Finset (Fin 8 × Fin 8) :=
  {(0, 1), (1, 2), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7)}

def relation (m : ℕ) (a b : Fin 8) : Prop :=
  (a, b) ∈ basePairs ∨ (a.val < 4 ∧ 4 ≤ b.val ∧ m.testBit (4 * a.val + b.val - 4) = true)

instance (m : ℕ) : DecidableRel (relation m) := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The finite path--cycle graph with the specified sixteen cross-edge bits. -/
def graph (m : ℕ) : SimpleGraph (Fin 8) := SimpleGraph.fromRel (relation m)

instance (m : ℕ) : DecidableRel (graph m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (relation m)).Adj)

lemma graph_mono {small large : ℕ} (h : large &&& small = small) : graph small ≤ graph large := by
  have hb (i : ℕ) (hi : small.testBit i = true) : large.testBit i = true := by
    have he := congrArg (fun n : ℕ ↦ n.testBit i) h
    simpa only [Nat.testBit_and, hi, Bool.and_true] using he
  have hr {a b : Fin 8} (h : relation small a b) : relation large a b := by
    rcases h with h | ⟨ha, hb', hbit⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb', hb _ hbit⟩
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, hab | hba⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr hab)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr hba)⟩

end PathExchange

end Erdos577
