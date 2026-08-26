-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DecompRestrict

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reconstruction from a separation

Given a finite triple system `F` and a partition of its edges into `S` and its
complement, we reconstruct `F` (up to isomorphism) as a disjoint union or a
one-point amalgamation of the two restrictions, according to whether the two
sides share `0` or exactly `1` vertex.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

variable {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})

/-- The vertex predicate "incident to an edge of `S`". -/
abbrev IncS (v : F.V) : Prop := ∃ e ∈ S, v ∈ e.1

/-- The separation equivalence classifying each vertex by the side it lies on. -/
noncomputable def sepEquiv
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → False) :
    F.V ≃ (F.restrict S).V ⊕ (F.restrict Sᶜ).V where
  toFun v := if hv : IncS S v then Sum.inl ⟨v, hv⟩ else Sum.inr ⟨v, (hcov v).resolve_left hv⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv := by
    intro v; by_cases hv : IncS S v <;> simp [hv]
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · simp only [Sum.elim_inl]; rw [dif_pos hv]
    · simp only [Sum.elim_inr]
      rw [dif_neg (fun hS => hsep v hS hv)]

@[simp] theorem sepEquiv_inl {hcov hsep} {v : F.V} (hv : IncS S v) :
    sepEquiv S hcov hsep v = Sum.inl ⟨v, hv⟩ := by
  simp only [sepEquiv, Equiv.coe_fn_mk]; rw [dif_pos hv]

theorem sepEquiv_inr {hcov hsep} {v : F.V} (hv : ¬ IncS S v)
    (hv' : ∃ e ∈ Sᶜ, v ∈ e.1) :
    sepEquiv S hcov hsep v = Sum.inr ⟨v, hv'⟩ := by
  simp only [sepEquiv, Equiv.coe_fn_mk]; rw [dif_neg hv]

/-
An `S`-edge is sent by `sepEquiv` to the corresponding restricted edge on the
left.
-/
theorem sepEquiv_map_left {hcov hsep} {e : Finset F.V} (he : ∀ v ∈ e, IncS S v) :
    e.map (sepEquiv S hcov hsep).toEmbedding =
      (Finset.subtype (fun v => IncS S v) e).map Function.Embedding.inl := by
  ext x;
  constructor <;> intro hx;
  · obtain ⟨ v, hv, rfl ⟩ := Finset.mem_map.mp hx; specialize he v hv; aesop;
  · rw [ Finset.mem_map ] at hx; obtain ⟨ v, hv, rfl ⟩ := hx; simp_all +decide [ Finset.mem_subtype ] ;
    convert! hv using 1

/-
A `Sᶜ`-edge is sent by `sepEquiv` to the corresponding restricted edge on the
right.
-/
theorem sepEquiv_map_right {hcov hsep} {e : Finset F.V} (he : ∀ v ∈ e, ¬ IncS S v)
    (he' : ∀ v ∈ e, ∃ e' ∈ Sᶜ, v ∈ e'.1) :
    e.map (sepEquiv S hcov hsep).toEmbedding =
      (Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e).map Function.Embedding.inr := by
  ext x;
  constructor <;> intro hx;
  · rw [ Finset.mem_map ] at hx; obtain ⟨ v, hv, rfl ⟩ := hx; specialize he v hv; specialize he' v hv; simp_all +decide [ sepEquiv_inr ] ;
    exact ⟨ v, hv, he', rfl ⟩;
  · aesop

/-
**Disjoint-union reconstruction.**  If the edges split into two parts `S` and
`Sᶜ` sharing no vertex (and covering all vertices), then `F` is the disjoint
union of the two restrictions.
-/
theorem recon_disjUnion
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → False) :
    FTS.Iso F (FTS.disjUnion (F.restrict S) (F.restrict Sᶜ)) := by
  refine' ⟨ _, _ ⟩;
  convert! ( sepEquiv S hcov hsep ) using 1;
  intro e;
  constructor <;> intro he;
  · by_cases h : ⟨ e, he ⟩ ∈ S <;> simp_all +decide [ FTS.disjUnion ];
    · refine' Or.inl ⟨ _, FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, h, rfl ⟩, _ ⟩;
      convert! sepEquiv_map_left S ( fun v hv => ⟨ _, h, hv ⟩ ) |> Eq.symm using 1;
    · refine Or.inr ⟨ Finset.subtype ( fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1 ) e, ?_, ?_ ⟩;
      · exact FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, Finset.mem_compl.mpr h, rfl ⟩;
      · convert! sepEquiv_map_right S ( fun v hv => ?_ ) ( fun v hv => ?_ ) |> Eq.symm;
        · exact fun hv' => hsep v hv' ⟨ _, Finset.mem_compl.mpr h, hv ⟩;
        · exact Or.resolve_left ( hcov v ) fun ⟨ e', he', hv' ⟩ => hsep v ⟨ e', he', hv' ⟩ ⟨ ⟨ e, he ⟩, by aesop ⟩;
  · cases' Finset.mem_union.mp he with he he;
    · obtain ⟨ d, hd, hd' ⟩ := Finset.mem_image.mp he;
      obtain ⟨ e₀, he₀, rfl ⟩ := FTS.mem_restrict_edges.mp hd;
      have h_eq : e₀.1.map (sepEquiv S hcov hsep).toEmbedding = e.map (sepEquiv S hcov hsep).toEmbedding := by
        convert! hd' using 1;
        convert! sepEquiv_map_left S ( fun v hv => ⟨ e₀, he₀, hv ⟩ ) using 1;
      have := Finset.map_injective ( sepEquiv S hcov hsep ).toEmbedding h_eq; aesop;
    · obtain ⟨ d, hd, hd' ⟩ := Finset.mem_image.mp he;
      obtain ⟨ e₀, he₀, rfl ⟩ := FTS.mem_restrict_edges.mp hd;
      convert! e₀.2 using 1;
      apply Finset.map_injective (sepEquiv S hcov hsep).toEmbedding;
      convert! hd'.symm using 1;
      convert! sepEquiv_map_right S _ _ using 1;
      · exact fun v hv => fun hv' => hsep v hv' ⟨ e₀, he₀, hv ⟩;
      · exact fun v hv => ⟨ e₀, he₀, hv ⟩

/-! ### Amalgamation reconstruction -/

variable (g : F.V)

/-- The amalgamation equivalence: classify each vertex by side, sending the glue
vertex `g` to the left copy. -/
noncomputable def amalgEquiv
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = g)
    (hgS : IncS S g) (hgT : ∃ e ∈ Sᶜ, g ∈ e.1) :
    F.V ≃ (F.restrict S).V ⊕ {b : (F.restrict Sᶜ).V // b ≠ ⟨g, hgT⟩} where
  toFun v := if hv : IncS S v then Sum.inl ⟨v, hv⟩
    else Sum.inr ⟨⟨v, (hcov v).resolve_left hv⟩, by
      intro heq
      apply hv
      have hvg : v = g := congrArg Subtype.val heq
      rw [hvg]; exact hgS⟩
  invFun := Sum.elim Subtype.val (fun b => b.1.1)
  left_inv := by
    intro v; by_cases hv : IncS S v <;> simp [hv]
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨⟨v, hv⟩, hne⟩)
    · simp only [Sum.elim_inl]; rw [dif_pos hv]
    · simp only [Sum.elim_inr]
      have hvS : ¬ IncS S v := by
        intro hS; exact hne (by rw [Subtype.ext_iff]; exact hsep v hS hv)
      rw [dif_neg hvS]

@[simp] theorem amalgEquiv_inl {hcov hsep hgS hgT} {v : F.V} (hv : IncS S v) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inl ⟨v, hv⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_pos hv]

theorem amalgEquiv_inr {hcov hsep hgS hgT} {v : F.V} (hv : ¬ IncS S v)
    (hv' : ∃ e ∈ Sᶜ, v ∈ e.1) (hne : v ≠ g) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inr ⟨⟨v, hv'⟩, by
      intro heq; exact hne (congrArg Subtype.val heq)⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_neg hv]

/-
An `S`-edge maps to a left restricted edge under `amalgEquiv`.
-/
theorem amalgEquiv_map_left {hcov hsep hgS hgT} {e : Finset F.V} (he : ∀ v ∈ e, IncS S v) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => IncS S v) e).map Function.Embedding.inl := by
  ext x;
  constructor;
  · rcases x with ( x | ⟨ ⟨ x, hx ⟩, hx' ⟩ ) <;> simp +decide [ Finset.mem_map, Finset.mem_subtype ];
    · intro hx;
      use x.val;
      simp +zetaDelta at *;
      exact ⟨ by simpa [ amalgEquiv ] using! hx, he _ hx, rfl ⟩;
    · exact fun h => False.elim <| hx' <| Subtype.ext <| hsep x ( he x h ) hx;
  · simp [Finset.mem_map];
    rintro v hv _ _ _ _ rfl; exact hv;

/-
A `Sᶜ`-edge maps to a right restricted edge under `amalgEquiv`, via the
amalgamation embedding `amalgEmbG`.
-/
set_option maxHeartbeats 1000000 in
theorem amalgEquiv_map_amalg {hcov hsep hgS hgT} {e : Finset F.V}
    (he' : ∀ v ∈ e, ∃ e' ∈ Sᶜ, v ∈ e'.1) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e).map
        (amalgEmbG (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  convert! Set.ext _;
  rotate_left;
  exact ( F.restrict S ).V ⊕ { b : ( F.restrict Sᶜ ).V // b ≠ ⟨ g, hgT ⟩ };
  exact { x | ∃ v ∈ e, amalgEquiv S g hcov hsep hgS hgT v = x };
  exact { x | ∃ v ∈ e, ∃ ( hv : ∃ e' ∈ Sᶜ, v ∈ e'.1 ), amalgEmbG ( F.restrict S ) ( F.restrict Sᶜ ) ⟨ g, hgS ⟩ ⟨ g, hgT ⟩ ⟨ v, hv ⟩ = x };
  · intro x; constructor <;> intro hx; rcases hx with ⟨ v, hv, rfl ⟩ ; by_cases hv' : v = g <;> simp +decide [ hv', amalgEquiv_inl, amalgEquiv_inr, amalgEmbG ] ;
    · use v; aesop;
    · use v, hv, by
        exact Exists.elim ( he' v hv ) fun x hx => ⟨ x.1, ⟨ x.2, by aesop ⟩, hx.2 ⟩
      generalize_proofs at *;
      rw [ amalgEquiv_inr ];
      grind;
      · exact fun h => hv' <| hsep v h <| he' v hv;
      · assumption;
      · assumption;
    · obtain ⟨ v, hv, hv', rfl ⟩ := hx;
      use v;
      by_cases hv'' : IncS S v <;> simp +decide [ hv'', amalgEquiv_inl, amalgEquiv_inr, amalgEmbG ];
      · specialize hsep v hv'' hv'; aesop;
      · have hvg : v ≠ g := by
          intro h
          subst v
          exact hv'' hgS
        rw [amalgEquiv_inr S g hv'' hv' hvg]
        simp [hv]
        exact fun h => hvg (congrArg Subtype.val h)
  · simp +decide [ Finset.ext_iff, Set.ext_iff ];
    congr! 3;
    · grind;
    · constructor;
      · rintro ⟨ v, hv, hv' ⟩;
        use v.val;
        simp +zetaDelta at *;
        exact ⟨ Finset.mem_subtype.mp hv, he' _ ( Finset.mem_subtype.mp hv ), hv' ⟩;
      · rintro ⟨ v, hv, hv', hv'' ⟩;
        use ⟨ v, he' v hv ⟩;
        exact ⟨ Finset.mem_subtype.mpr hv, hv'' ⟩;
    · congr! 2;
      · grind;
      · constructor;
        · rintro ⟨ v, hv, hv' ⟩;
          use v.val;
          simp +zetaDelta at *;
          exact ⟨ Finset.mem_subtype.mp hv, he' _ ( Finset.mem_subtype.mp hv ), hv' ⟩;
        · rintro ⟨ v, hv, hv', hv'' ⟩;
          use ⟨ v, by aesop ⟩;
          exact ⟨ Finset.mem_subtype.mpr hv, hv'' ⟩

/-
**Amalgamation reconstruction.**  If the edges split into two parts `S` and
`Sᶜ` whose only shared vertex is the glue vertex `g` (and covering all vertices),
then `F` is the one-point amalgamation of the two restrictions at `g`.
-/
theorem recon_amalg
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = g)
    (hgS : IncS S g) (hgT : ∃ e ∈ Sᶜ, g ∈ e.1) :
    FTS.Iso F (FTS.amalgamate (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  refine' ⟨ _, _ ⟩;
  exact ( amalgEquiv S g hcov hsep hgS hgT );
  intro e;
  constructor;
  · intro he
    by_cases h : ⟨ e, he ⟩ ∈ S;
    · refine' Finset.mem_union_left _ ( Finset.mem_image.mpr ⟨ _, _, _ ⟩ );
      exact Finset.subtype ( fun v => IncS S v ) e;
      · exact FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, h, rfl ⟩;
      · convert! amalgEquiv_map_left S g ( fun v hv => ⟨ _, h, hv ⟩ ) |> Eq.symm using 1;
    · refine' Finset.mem_union_right _ ( Finset.mem_image.mpr ⟨ Finset.subtype ( fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1 ) e, _, _ ⟩ );
      · exact FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, Finset.mem_compl.mpr h, rfl ⟩;
      · convert! amalgEquiv_map_amalg S g ( fun v hv => ⟨ ⟨ e, he ⟩, Finset.mem_compl.mpr h, hv ⟩ ) |> Eq.symm using 1;
  · simp +decide [ FTS.amalgamate ];
    rintro ( ⟨ a, ha, ha' ⟩ | ⟨ a, ha, ha' ⟩ );
    · obtain ⟨ e₀, he₀, rfl ⟩ := FTS.mem_restrict_edges.mp ha;
      have h_eq : e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding = e₀.1.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding := by
        exact ha'.symm.trans
          (amalgEquiv_map_left S g (fun v hv => ⟨e₀, he₀, hv⟩)).symm
      have := Finset.map_injective ( amalgEquiv S g hcov hsep hgS hgT ).toEmbedding h_eq; aesop;
    · obtain ⟨ e₀, he₀, rfl ⟩ := FTS.mem_restrict_edges.mp ha;
      convert! e₀.2 using 1;
      apply Finset.map_injective (amalgEquiv S g hcov hsep hgS hgT).toEmbedding;
      convert! ha'.symm using 1;
      convert! amalgEquiv_map_amalg S g ( fun v hv => ⟨ e₀, he₀, hv ⟩ ) using 1

end Erdos1177
