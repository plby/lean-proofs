import ErdosProblems.Erdos117.CentralForm
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

/-!
# Prime factors of finite abelian p-groups

A maximal proper subgroup gives a scalar character with image `ZMod p`.
This supplies the successive central factors in the class-two reduction.
-/

namespace Erdos117

theorem exists_prime_character {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] [Finite A] [Nontrivial A] (hA : IsPGroup p A) :
    ∃ χ : A →* Multiplicative (ZMod p), Function.Surjective χ ∧
      χ.ker.index = p ∧ Nat.card χ.ker * p = Nat.card A := by
  classical
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (α := Subgroup A)
  have : Nontrivial (A ⧸ M) := not_subsingleton_iff_nontrivial.mp (fun h =>
    hM.ne_top (QuotientGroup.subgroup_eq_top_of_subsingleton M h))
  have : IsSimpleOrder (Set.Ici M) := Set.isSimpleOrder_Ici_iff_isCoatom.mpr hM
  let eM : Subgroup (A ⧸ M) ≃o Set.Ici M := QuotientGroup.comapMk'OrderIso M
  have : IsSimpleOrder (Subgroup (A ⧸ M)) :=
    eM.isSimpleOrder_iff.mpr inferInstance
  have : IsSimpleGroup (A ⧸ M) :=
    ⟨fun H _ => IsSimpleOrder.eq_bot_or_eq_top H⟩
  have hprime : (Nat.card (A ⧸ M)).Prime := IsSimpleGroup.prime_card
  have hdiv : p ∣ Nat.card (A ⧸ M) :=
    ((hA.to_quotient M).card_eq_or_dvd).resolve_left hprime.ne_one
  have hcard : Nat.card (A ⧸ M) = p :=
    ((Nat.dvd_prime hprime).mp hdiv |>.resolve_left (Fact.out : p.Prime).ne_one).symm
  let e : (A ⧸ M) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let χ := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hχ : Function.Surjective χ := e.surjective.comp (QuotientGroup.mk'_surjective M)
  have hindex : χ.ker.index = p := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχ,
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  refine ⟨χ, hχ, hindex, ?_⟩
  calc
    Nat.card χ.ker * p = Nat.card χ.ker * χ.ker.index := congrArg (Nat.card χ.ker * ·) hindex.symm
    _ = Nat.card A := χ.ker.card_mul_index

/-- A finite abelian `p`-group has a descending series with factors of order
`p`. Its length is exactly the base-`p` exponent of the group order. -/
theorem exists_prime_series {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup p A) :
    ∃ (L : ℕ) (S : ℕ → Subgroup A), S 0 = ⊤ ∧ S L = ⊥ ∧
      (∀ j < L, S (j + 1) ≤ S j ∧ (S (j + 1)).relIndex (S j) = p) ∧
      Nat.card A = p ^ L := by
  classical
  generalize hcard : Nat.card A = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    rcases subsingleton_or_nontrivial A with htriv | hnontriv
    · let := htriv
      refine ⟨0, fun _ => ⊤, rfl, ?_, fun j hj => (Nat.not_lt_zero j hj).elim, ?_⟩
      · ext x
        simp only [Subgroup.mem_top, Subgroup.mem_bot, true_iff]
        exact Subsingleton.elim _ _
      · rw [← hcard, pow_zero]
        exact Nat.card_eq_one_iff_unique.mpr ⟨htriv, ⟨1⟩⟩
    · let := hnontriv
      obtain ⟨χ, hχ, hindex, hmul⟩ := exists_prime_character hA
      let M := χ.ker
      have hMlt : Nat.card M < d := by
        have hpos : 0 < Nat.card M := Nat.card_pos
        have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
        dsimp [M] at hpos ⊢
        nlinarith
      obtain ⟨L, S, hS0, hSL, hstep, hcardM⟩ :=
        ih (Nat.card M) hMlt (hA.of_injective M.subtype M.subtype_injective) rfl
      let T : ℕ → Subgroup A
        | 0 => ⊤
        | j + 1 => (S j).map M.subtype
      refine ⟨L + 1, T, rfl, ?_, ?_, ?_⟩
      · change (S L).map M.subtype = ⊥
        rw [hSL, Subgroup.map_bot]
      · intro j hj
        cases j with
        | zero =>
          refine ⟨le_top, ?_⟩
          change ((S 0).map M.subtype).relIndex ⊤ = p
          rw [hS0, ← MonoidHom.range_eq_map, M.range_subtype, Subgroup.relIndex_top_right]
          exact hindex
        | succ j =>
          obtain ⟨hinc, hidx⟩ := hstep j (by omega)
          refine ⟨Subgroup.map_mono hinc, ?_⟩
          change ((S (j + 1)).map M.subtype).relIndex ((S j).map M.subtype) = p
          rw [Subgroup.relIndex_map_map_of_injective _ _ M.subtype_injective]
          exact hidx
      · rw [← hcard, ← hmul]
        change Nat.card M * p = p ^ (L + 1)
        rw [hcardM, pow_succ]

/-- A prescribed subgroup of index `p` is the kernel of a scalar character.
This lets every step of a fixed series use the same subgroup chain. -/
theorem exists_character_of_prime_index {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] (M : Subgroup A) (hM : M.index = p) :
    ∃ χ : A →* Multiplicative (ZMod p), Function.Surjective χ ∧ χ.ker = M := by
  classical
  let e : (A ⧸ M) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hM (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let χ := e.toMonoidHom.comp (QuotientGroup.mk' M)
  refine ⟨χ, e.surjective.comp (QuotientGroup.mk'_surjective M), ?_⟩
  ext x
  change e ((QuotientGroup.mk' M) x) = 1 ↔ x ∈ M
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- Embed the prime-factor chain in an ambient group. All its terms remain
central; the construction therefore applies to the derived subgroup of a
class-two group. -/
theorem exists_central_prime_series {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hN : N ≤ Subgroup.center G) (hP : IsPGroup p N) :
    ∃ (L : ℕ) (S : ℕ → Subgroup G), S 0 = N ∧ S L = ⊥ ∧
      (∀ j, S j ≤ N) ∧
      (∀ j < L, S (j + 1) ≤ S j ∧ (S (j + 1)).relIndex (S j) = p) ∧
      Nat.card N = p ^ L := by
  let : CommGroup N := { (inferInstance : Group N) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hN y.2) x) }
  obtain ⟨L, S, hS0, hSL, hstep, hcard⟩ := exists_prime_series hP
  refine ⟨L, fun j => (S j).map N.subtype, ?_, ?_, ?_, ?_, hcard⟩
  · change (S 0).map N.subtype = N
    rw [hS0, ← MonoidHom.range_eq_map, N.range_subtype]
  · change (S L).map N.subtype = ⊥
    rw [hSL, Subgroup.map_bot]
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · intro j hj
    refine ⟨Subgroup.map_mono (hstep j hj).1, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective]
    exact (hstep j hj).2

end Erdos117
