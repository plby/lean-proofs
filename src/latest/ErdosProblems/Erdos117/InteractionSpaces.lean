import ErdosProblems.Erdos117.CentralForm
import ErdosProblems.Erdos117.Symplectic

/-!
# Subgroup images in scalar commutator spaces

The image of a subgroup under a homomorphism to a prime-field vector space
is a subspace. Its codimension is controlled by the subgroup index.
-/

namespace Erdos117

variable {p : ℕ} {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod p) V]

def subgroupImageSpace (f : G →* Multiplicative V) (H : Subgroup G) :
    Submodule (ZMod p) V :=
  AddSubgroup.toZModSubmodule p (H.map f).toAddSubgroup

@[simp] theorem mem_subgroupImageSpace (f : G →* Multiplicative V)
    (H : Subgroup G) (v : V) :
    v ∈ subgroupImageSpace (p := p) f H ↔ Multiplicative.ofAdd v ∈ H.map f := Iff.rfl

theorem card_subgroupImageSpace (f : G →* Multiplicative V) (H : Subgroup G) :
    Nat.card (subgroupImageSpace (p := p) f H) = Nat.card (H.map f) := rfl

theorem mem_subgroupImageSpace_iff (f : G →* Multiplicative V)
    (H : Subgroup G) (v : V) :
    v ∈ subgroupImageSpace (p := p) f H ↔ ∃ x ∈ H, (f x).toAdd = v := by
  rw [mem_subgroupImageSpace]
  exact Iff.rfl

def subgroupImageHom (f : G →* Multiplicative V) (H : Subgroup G) :
    H →* Multiplicative (subgroupImageSpace (p := p) f H) where
  toFun x := Multiplicative.ofAdd
    ⟨(f x).toAdd, (mem_subgroupImageSpace_iff f H _).mpr ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f (x : G) (y : G))

theorem subgroupImageHom_surjective (f : G →* Multiplicative V) (H : Subgroup G) :
    Function.Surjective (subgroupImageHom (p := p) f H) := by
  intro v
  obtain ⟨x, hx, heq⟩ := (mem_subgroupImageSpace_iff f H v.toAdd.val).mp v.toAdd.2
  exact ⟨⟨x, hx⟩, Subtype.ext heq⟩

theorem subgroupImageHom_ker_index [Fact p.Prime] [Finite V]
    (f : G →* Multiplicative V) (H : Subgroup G) :
    (subgroupImageHom (p := p) f H).ker.index =
      p ^ Module.finrank (ZMod p) (subgroupImageSpace (p := p) f H) := by
  classical
  let U := subgroupImageSpace (p := p) f H
  let := Fintype.ofFinite U
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (subgroupImageHom_surjective (p := p) f H),
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem exists_nonorthogonal_family_in_subgroup [Fact p.Prime]
    (f : G →* Multiplicative V) (B : LinearMap.BilinForm (ZMod p) V)
    (H : Subgroup G) {ι : Type*} {a : ι → subgroupImageSpace (p := p) f H}
    (ha : NonorthogonalFamily (B.restrict (subgroupImageSpace (p := p) f H)) a) :
    ∃ b : ι → H, NonorthogonalFamily B (fun i => (f (b i)).toAdd) := by
  have hsurj := subgroupImageHom_surjective (p := p) f H
  choose b hb using fun i => hsurj (Multiplicative.ofAdd (a i))
  refine ⟨b, ?_⟩
  intro i j hij
  have hval (i : ι) : (f (b i)).toAdd = (a i).val := congrArg (fun v => v.toAdd.val) (hb i)
  change B (f (b i)).toAdd (f (b j)).toAdd ≠ 0
  rw [hval i, hval j]
  exact ha i j hij

/-- A clique in the form restricted to a subgroup image lifts to a clique
inside that subgroup. -/
theorem exists_clique_in_subgroup [Fact p.Prime]
    (f : G →* Multiplicative V) (B : LinearMap.BilinForm (ZMod p) V)
    (hcomm : ∀ x y : G, Commute x y → B (f x).toAdd (f y).toAdd = 0)
    (H : Subgroup G) {ι : Type*} {a : ι → subgroupImageSpace (p := p) f H}
    (ha : NonorthogonalFamily (B.restrict (subgroupImageSpace (p := p) f H)) a) :
    ∃ b : ι → H, ∀ i j, i ≠ j → ¬Commute (b i) (b j) := by
  obtain ⟨b, hb⟩ := exists_nonorthogonal_family_in_subgroup f B H ha
  exact ⟨b, fun i j hij hc => hb i j hij (hcomm _ _ (hc.map H.subtype))⟩

theorem subgroupImageSpace_index [Fact p.Prime] [Finite V]
    (f : G →* Multiplicative V) (H : Subgroup G) :
    (H.map f).index = p ^ (Module.finrank (ZMod p) V -
      Module.finrank (ZMod p) (subgroupImageSpace (p := p) f H)) := by
  classical
  let U := subgroupImageSpace (p := p) f H
  let := Fintype.ofFinite V
  let := Fintype.ofFinite U
  have hU : Nat.card (H.map f) = p ^ Module.finrank (ZMod p) U := by
    rw [← card_subgroupImageSpace (p := p)]
    change Nat.card U = _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hV : Nat.card (Multiplicative V) = p ^ Module.finrank (ZMod p) V := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have h := (H.map f).card_mul_index
  rw [hU, hV] at h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _)
  calc
    p ^ Module.finrank (ZMod p) U * (H.map f).index = p ^ Module.finrank (ZMod p) V := h
    _ = p ^ Module.finrank (ZMod p) U *
        p ^ (Module.finrank (ZMod p) V - Module.finrank (ZMod p) U) := by
      rw [← pow_add, Nat.add_sub_of_le (Submodule.finrank_le U)]

/-- Passing to the image cannot increase the subgroup index, so restricting
the domain to index at most `p^c` loses at most `c` dimensions. -/
theorem subgroupImageSpace_codim_le [Fact p.Prime] [Finite G] [Finite V]
    (f : G →* Multiplicative V) (hf : Function.Surjective f)
    (H : Subgroup G) {c : ℕ} (hH : H.index ≤ p ^ c) :
    Module.finrank (ZMod p) V -
      Module.finrank (ZMod p) (subgroupImageSpace (p := p) f H) ≤ c := by
  have hindex : (H.map f).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H)))
      (H.index_map_dvd hf)
  have h := hindex.trans hH
  rw [subgroupImageSpace_index (p := p)] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h

theorem subgroupImageSpace_rank_loss [Fact p.Prime] [Finite G] [Finite V]
    (f : G →* Multiplicative V) (hf : Function.Surjective f)
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.Nondegenerate) (hrefl : B.IsRefl)
    (H : Subgroup G) {c : ℕ} (hH : H.index ≤ p ^ c) :
    Module.finrank (ZMod p) V ≤
      Module.finrank (ZMod p) (B.restrict (subgroupImageSpace (p := p) f H)).range + 2 * c := by
  have hcodim := subgroupImageSpace_codim_le f hf H hH
  have hrank := finrank_le_restrict_rank_add_twice_codim B hB hrefl
    (subgroupImageSpace (p := p) f H)
  omega

/-- The scalar-credit estimate after restricting the group to index at most
`p^q`, with the clique lifted into that restricted subgroup. -/
theorem exists_restricted_scalar_family [Fact p.Prime] [Finite G] [Finite V]
    (f : G →* Multiplicative V) (hf : Function.Surjective f)
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.Nondegenerate) (halt : B.IsAlt)
    (H : Subgroup G) {q : ℕ} (hH : H.index ≤ p ^ q) :
    ∃ (c : ℕ) (a : Fin (c + 1) → H),
      NonorthogonalFamily B (fun i => (f (a i)).toAdd) ∧
      scalarCreditRate p * (Module.finrank (ZMod p) V / 2) ≤
        c + scalarDefect p + scalarCreditRate p * q := by
  let U := subgroupImageSpace (p := p) f H
  obtain ⟨c, a, ha, hcredit⟩ := exists_scalar_credit (B.restrict U) (fun x => halt x)
  obtain ⟨b, hb⟩ := exists_nonorthogonal_family_in_subgroup f B H ha
  refine ⟨c, b, hb, ?_⟩
  have hrank := subgroupImageSpace_rank_loss f hf B hB halt.isRefl H hH
  have hhalf : Module.finrank (ZMod p) V / 2 ≤
      Module.finrank (ZMod p) (B.restrict U).range / 2 + q := by
    dsimp [U]
    omega
  calc
    scalarCreditRate p * (Module.finrank (ZMod p) V / 2) ≤
        scalarCreditRate p * (Module.finrank (ZMod p) (B.restrict U).range / 2 + q) :=
      Nat.mul_le_mul_left _ hhalf
    _ = scalarCreditRate p * (Module.finrank (ZMod p) (B.restrict U).range / 2) +
        scalarCreditRate p * q := Nat.mul_add _ _ _
    _ ≤ c + scalarDefect p + scalarCreditRate p * q := Nat.add_le_add_right hcredit _

theorem exists_restricted_scalar_clique [Fact p.Prime] [Finite G] [Finite V]
    (f : G →* Multiplicative V) (hf : Function.Surjective f)
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.Nondegenerate) (halt : B.IsAlt)
    (hcomm : ∀ x y : G, Commute x y → B (f x).toAdd (f y).toAdd = 0)
    (H : Subgroup G) {q : ℕ} (hH : H.index ≤ p ^ q) :
    ∃ (c : ℕ) (a : Fin (c + 1) → H),
      (∀ i j, i ≠ j → ¬Commute (a i) (a j)) ∧
      scalarCreditRate p * (Module.finrank (ZMod p) V / 2) ≤
        c + scalarDefect p + scalarCreditRate p * q := by
  obtain ⟨c, a, ha, hcredit⟩ := exists_restricted_scalar_family f hf B hB halt H hH
  exact ⟨c, a, fun i j hij hc => ha i j hij (hcomm _ _ (hc.map H.subtype)), hcredit⟩

end Erdos117
