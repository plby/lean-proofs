import ErdosProblems.Erdos117.Basic
import ErdosProblems.Erdos1098
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic

/-!
# Finite models of the commutation relation

The finite reduction uses a finitely generated subgroup representing all central
cosets, followed by a quotient by a central torsion-free subgroup of finite index.
This avoids assuming a stem-group or isoclinism theorem.
-/

universe u

namespace Erdos117

open scoped commutatorElement

variable {G : Type u} [Group G]

/-- A finitely generated abelian group has a finite-index subgroup containing
no nonidentity element of finite order. -/
theorem exists_finiteIndex_without_torsion (A : Type*) [CommGroup A] [Group.FG A] :
    ∃ K : Subgroup A, K.FiniteIndex ∧ ∀ x ∈ K, IsOfFinOrder x → x = 1 := by
  obtain ⟨ι, j, _, _, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod A
  let T := (i : ι) → Multiplicative (ZMod (p i ^ e i))
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let q : A →* T := (MonoidHom.snd (j → Multiplicative ℤ) T).comp f.toMonoidHom
  refine ⟨q.ker, inferInstance, ?_⟩
  intro x hx hfin
  have hfirst : (f x).1 = 1 :=
    (((MonoidHom.fst (j → Multiplicative ℤ) T).comp f.toMonoidHom).isOfFinOrder hfin).eq_one'
  apply f.injective
  rw [map_one]
  exact Prod.ext hfirst (show (f x).2 = 1 from hx)

theorem commutator_mul_center_left (z x y : G) (hz : z ∈ Subgroup.center G) :
    ⁅z * x, y⁆ = ⁅x, y⁆ := by
  have hzy : Commute z y := (Subgroup.mem_center_iff.mp hz y).symm
  have hzc : Commute z ⁅x, y⁆ := (Subgroup.mem_center_iff.mp hz _).symm
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr hzy.eq, mul_one, hzc.mul_inv_cancel]

theorem commutator_eq_of_center_quotient_eq {x x' y : G}
    (h : (x : G ⧸ Subgroup.center G) = x') : ⁅x, y⁆ = ⁅x', y⁆ := by
  have hz := QuotientGroup.eq_iff_div_mem.mp h
  simpa only [div_mul_cancel] using commutator_mul_center_left (x / x') x' y hz

/-- Schur's finiteness input, obtained from the finite set of central cosets. -/
theorem finite_commutatorSet_of_finiteIndex_center [(Subgroup.center G).FiniteIndex] :
    Finite (commutatorSet G) := by
  let Q := G ⧸ Subgroup.center G
  let f : Q × Q → commutatorSet G := fun q =>
    ⟨⁅q.1.out, q.2.out⁆, commutator_mem_commutatorSet _ _⟩
  apply Finite.of_surjective f
  intro c
  obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp c.2
  refine ⟨((x : Q), (y : Q)), Subtype.ext ?_⟩
  dsimp [f]
  rw [commutator_eq_of_center_quotient_eq (Quotient.out_eq' (x : Q))]
  rw [← inv_inj, commutatorElement_inv]
  rw [commutator_eq_of_center_quotient_eq (Quotient.out_eq' (y : Q))]
  simpa only [commutatorElement_inv] using congrArg Inv.inv hxy

/-- The finitely generated case of finite reduction. The quotient map preserves
commutation in both directions, not just in the usual forward direction. -/
theorem exists_finite_commutation_quotient [Group.FG G]
    [(Subgroup.center G).FiniteIndex] :
    ∃ N : Subgroup G, ∃ _ : N.Normal, N.FiniteIndex ∧
      ∀ x y : G, Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) ↔ Commute x y := by
  let Z := Subgroup.center G
  let : CommGroup Z := { (inferInstance : Group Z) with mul_comm := mul_comm' }
  obtain ⟨K, hK, hKfree⟩ := exists_finiteIndex_without_torsion Z
  let N := K.map Z.subtype
  have hNZ : N ≤ Z := Subgroup.map_le_range _ _ |>.trans_eq Z.range_subtype
  have hN : N.Normal := ⟨fun x hx g => by
    have hcomm : Commute g x := Subgroup.mem_center_iff.mp (hNZ hx) g
    simpa only [hcomm.mul_inv_cancel] using hx⟩
  have hNindex : N.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hK.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hNfree : ∀ x ∈ N, IsOfFinOrder x → x = 1 := by
    intro x hx hfin
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzfin : IsOfFinOrder z := Z.subtype_injective.isOfFinOrder_iff.mp hfin
    exact congrArg Subtype.val (hKfree z hz hzfin)
  have : Finite (commutatorSet G) := finite_commutatorSet_of_finiteIndex_center
  refine ⟨N, hN, hNindex, fun x y => ⟨?_, fun h => h.map (QuotientGroup.mk' N)⟩⟩
  intro hxy
  have hcN : ⁅x, y⁆ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact (map_commutatorElement (QuotientGroup.mk' N) x y).trans hxy.commutator_eq
  have hcD : ⁅x, y⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcfin : IsOfFinOrder ⁅x, y⁆ :=
    (commutator G).subtype.isOfFinOrder (isOfFinOrder_of_finite ⟨⁅x, y⁆, hcD⟩)
  exact commutatorElement_eq_one_iff_commute.mp (hNfree _ hcN hcfin)

theorem commutator_eq_of_center_quotient_eq₂ {x x' y y' : G}
    (hx : (x : G ⧸ Subgroup.center G) = x')
    (hy : (y : G ⧸ Subgroup.center G) = y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  rw [commutator_eq_of_center_quotient_eq hx]
  simpa only [commutatorElement_inv] using
    congrArg Inv.inv (commutator_eq_of_center_quotient_eq (y := x') hy)

/-- Each central coset is a commuting color class. -/
theorem hasAbelianCover_centerIndex [(Subgroup.center G).FiniteIndex] :
    HasAbelianCover G (Subgroup.center G).index := by
  let Q := G ⧸ Subgroup.center G
  let := Fintype.ofFinite Q
  let e : Q ≃ Fin (Subgroup.center G).index :=
    Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  apply (hasAbelianCover_iff_coloring _).mpr
  refine ⟨fun x => e (x : Q), fun x y hxy => ?_⟩
  have hq : (x : Q) = y := e.injective hxy
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutator_eq_of_center_quotient_eq hq]
  exact (Commute.refl y).commutator_eq

/-- Every group with finite center index has a finitely generated subgroup
representing its entire commutation relation. -/
theorem exists_fg_commutation_subgroup [(Subgroup.center G).FiniteIndex] :
    ∃ K : Subgroup G, Group.FG K ∧ (Subgroup.center K).FiniteIndex ∧
      ∃ f : G → K, ∀ x y, Commute (f x) (f y) ↔ Commute x y := by
  classical
  let Q := G ⧸ Subgroup.center G
  let r : Q → G := Quotient.out
  let K := Subgroup.closure (Set.range r)
  have hZK : (Subgroup.center G).subgroupOf K ≤ Subgroup.center K := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx y)
  have hKcenter : (Subgroup.center K).FiniteIndex := Subgroup.finiteIndex_of_le hZK
  let f : G → K := fun x => ⟨r (x : Q), Subgroup.subset_closure (Set.mem_range_self _)⟩
  refine ⟨K, inferInstance, hKcenter, f, ?_⟩
  intro x y
  rw [commute_iff_eq, Subtype.ext_iff]
  change Commute (r (x : Q)) (r (y : Q)) ↔ Commute x y
  rw [← commutatorElement_eq_one_iff_commute, ← commutatorElement_eq_one_iff_commute,
    commutator_eq_of_center_quotient_eq₂ (Quotient.out_eq' (x : Q))
      (Quotient.out_eq' (y : Q))]

/-- The qualitative center-index theorem is already proved in this repository;
its hypotheses follow from the original bounded-clique condition. -/
theorem finiteIndex_center_of_noncommutingBound {n : ℕ} (hn : NoncommutingBound G n) :
    (Subgroup.center G).FiniteIndex := by
  apply Erdos1098.pe_iff_fiz.mp
  intro S hS
  by_contra hfin
  obtain ⟨s, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin (n + 1)
  have hs : (s : Set G).Pairwise (fun x y => ¬ Commute x y) := hS.mono hsub
  have hc := hn s hs
  omega

/-- Finite reduction preserving all clique bounds and all abelian-cover sizes.
Both directions are explicit, so infinite groups have not been excluded from
the original extremal problem. -/
theorem finite_reduction {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ (H : Type u) (_ : Group H) (_ : Finite H),
      (∀ m, NoncommutingBound H m ↔ NoncommutingBound G m) ∧
      (∀ k, HasAbelianCover H k ↔ HasAbelianCover G k) := by
  have := finiteIndex_center_of_noncommutingBound hn
  obtain ⟨K, hKfg, hKcenter, f, hf⟩ := exists_fg_commutation_subgroup (G := G)
  obtain ⟨N, hN, hNindex, hq⟩ := exists_finite_commutation_quotient (G := K)
  let H := K ⧸ N
  let q : K →* H := QuotientGroup.mk' N
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hsub : ∀ x y : K, Commute (x : G) (y : G) → Commute x y :=
    fun x y h => Subtype.ext h.eq
  refine ⟨H, inferInstance, inferInstance, ?_, ?_⟩
  · intro m
    constructor
    · intro h
      exact noncommutingBound_of_commute_reflecting f (fun x y h => (hf x y).mp h)
        (noncommutingBound_of_commute_reflecting q (fun x y h => (hq x y).mp h) h)
    · intro h
      exact noncommutingBound_of_surjective q hqsurj (fun x y h => h.map q)
        (noncommutingBound_of_commute_reflecting Subtype.val hsub h)
  · intro k
    constructor
    · intro h
      exact hasAbelianCover_of_commute_reflecting f (fun x y h => (hf x y).mp h)
        (hasAbelianCover_of_commute_reflecting q (fun x y h => (hq x y).mp h) h)
    · intro h
      exact hasAbelianCover_of_surjective q hqsurj (fun x y h => h.map q)
        (hasAbelianCover_of_commute_reflecting Subtype.val hsub h)

end Erdos117
