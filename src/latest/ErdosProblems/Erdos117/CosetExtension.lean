import ErdosProblems.Erdos117.FiniteCover
import ErdosProblems.Erdos117.FiniteReduction
import ErdosProblems.Erdos117.Compression

/-!
# Extending abelian covers through cosets

Domination is performed on central cosets, so the cost depends on a central
index rather than on the possibly arbitrarily large order of the center.
-/

namespace Erdos117

open Finset
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A color in a commuting neighborhood records the chosen anchor and the
color of the difference from that anchor inside the subgroup. -/
theorem coset_coloring_of_dominating_family (F : Subgroup G) (g : G)
    {ι κ : Type*} (a : ι → F)
    (hdom : ∀ x : F, ∃ i, Commute (g * (a i : G)) (g * (x : G)))
    (c : F → κ) (hc : ∀ x y, c x = c y → Commute x y) :
    ∃ d : F → ι × κ, ∀ x y, d x = d y → Commute (g * (x : G)) (g * (y : G)) := by
  classical
  choose i hi using hdom
  let r : F → F := fun x => (a (i x))⁻¹ * x
  have hsplit (x : F) : g * (x : G) = (g * (a (i x) : G)) * (r x : G) := by
    simp [r, mul_assoc]
  have hcomm (x : F) : Commute (g * (a (i x) : G)) (r x : G) := by
    have h := (Commute.refl (g * (a (i x) : G))).inv_right.mul_right (hi x)
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, r, Subgroup.coe_mul,
      Subgroup.coe_inv] using h
  refine ⟨fun x => (i x, c (r x)), fun x y hxy => ?_⟩
  have hi_eq : i x = i y := congrArg Prod.fst hxy
  have hc_eq : c (r x) = c (r y) := congrArg Prod.snd hxy
  have hr : Commute (r x : G) (r y : G) := (hc _ _ hc_eq).map F.subtype
  rw [hsplit x, hsplit y, ← hi_eq]
  have hay : Commute (g * (a (i x) : G)) (r y : G) := hi_eq ▸ hcomm y
  exact ((Commute.refl _).mul_right hay).mul_left ((hcomm x).symm.mul_right hr)

/-- Equality modulo the ambient center is respected by a subgroup's central
quotient. This is stronger than commutation in the quotient group. -/
theorem ambient_center_quotient_eq (F : Subgroup G) {x y : F}
    (h : (x : F ⧸ (Subgroup.center G).subgroupOf F) = y) :
    ((x : G) : G ⧸ Subgroup.center G) = (y : G) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hh : x / y ∈ (Subgroup.center G).subgroupOf F := QuotientGroup.eq_iff_div_mem.mp h
  exact hh

theorem coset_commute_of_quotient_eq (F : Subgroup G) (g : G) {x x' y y' : F}
    (hx : (x : F ⧸ (Subgroup.center G).subgroupOf F) = x')
    (hy : (y : F ⧸ (Subgroup.center G).subgroupOf F) = y') :
    Commute (g * (x : G)) (g * (y : G)) ↔ Commute (g * (x' : G)) (g * (y' : G)) := by
  have hx' := congrArg (fun q : G ⧸ Subgroup.center G => (g : G ⧸ Subgroup.center G) * q)
    (ambient_center_quotient_eq F hx)
  have hy' := congrArg (fun q : G ⧸ Subgroup.center G => (g : G ⧸ Subgroup.center G) * q)
    (ambient_center_quotient_eq F hy)
  rw [← commutatorElement_eq_one_iff_commute, ← commutatorElement_eq_one_iff_commute,
    commutator_eq_of_center_quotient_eq₂ hx' hy']

/-- The central cosets inside a subgroup, using the ambient group's center. -/
abbrev CentralCosets (F : Subgroup G) := F ⧸ (Subgroup.center G).subgroupOf F

private theorem commute_mul_self_left_iff (a b : G) :
    Commute a (a * b) ↔ Commute a b := by
  constructor
  · intro h
    simpa only [inv_mul_cancel_left] using (Commute.refl a).inv_right.mul_right h
  · intro h
    exact (Commute.refl a).mul_right h

/-- Neighborhood membership in a central coset is membership in a translate
of the image of the corresponding centralizer. -/
theorem coset_neighborhood_iff (F : Subgroup G) (g : G) (q r : CentralCosets F) :
    Commute (g * (q.out : G)) (g * (r.out : G)) ↔
      q⁻¹ * r ∈ ((Subgroup.centralizer ({g * (q.out : G)} : Set G)).subgroupOf F).map
        (QuotientGroup.mk' ((Subgroup.center G).subgroupOf F)) := by
  let Z := (Subgroup.center G).subgroupOf F
  let π : F →* CentralCosets F := QuotientGroup.mk' Z
  let C := (Subgroup.centralizer ({g * (q.out : G)} : Set G)).subgroupOf F
  have hZC : π.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    change (z : G) ∈ Subgroup.centralizer {g * (q.out : G)}
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_center_iff.mp hz _).symm
  have hmap (x : F) : π x ∈ C.map π ↔ x ∈ C := by
    change x ∈ (C.map π).comap π ↔ x ∈ C
    rw [Subgroup.comap_map_eq_self hZC]
  have hπ : π (q.out⁻¹ * r.out) = q⁻¹ * r := by
    have hq : π q.out = q := Quotient.out_eq' q
    have hr : π r.out = r := Quotient.out_eq' r
    rw [map_mul, map_inv, hq, hr]
  rw [← hπ, hmap]
  simp only [C, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_mul, Subgroup.coe_inv]
  change Commute (g * (q.out : G)) (g * (r.out : G)) ↔
    Commute ((q.out : G)⁻¹ * (r.out : G)) (g * (q.out : G))
  have heq : g * (r.out : G) = (g * (q.out : G)) * ((q.out : G)⁻¹ * (r.out : G)) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [heq, commute_mul_self_left_iff, commute_iff_eq, commute_iff_eq]
  exact eq_comm

/-- The neighborhood cardinality is exactly the order of the image of the
centralizer in the subgroup's central quotient. -/
theorem coset_neighborhood_card (F : Subgroup G) (g : G) (q : CentralCosets F) :
    Nat.card {r : CentralCosets F // Commute (g * (q.out : G)) (g * (r.out : G))} =
      Nat.card (((Subgroup.centralizer ({g * (q.out : G)} : Set G)).subgroupOf F).map
        (QuotientGroup.mk' ((Subgroup.center G).subgroupOf F))) := by
  let C := ((Subgroup.centralizer ({g * (q.out : G)} : Set G)).subgroupOf F).map
    (QuotientGroup.mk' ((Subgroup.center G).subgroupOf F))
  let e : C ≃ {r : CentralCosets F // Commute (g * (q.out : G)) (g * (r.out : G))} :=
    (Equiv.mulLeft q).subtypeEquiv (fun x => by
      rw [coset_neighborhood_iff]
      change x ∈ C ↔ q⁻¹ * (q * x) ∈ C
      rw [inv_mul_cancel_left])
  exact Nat.card_congr e.symm

/-- A conjugacy bound `B` gives closed-neighborhood density at least `1/B`
on every central coset of every subgroup. -/
theorem coset_neighborhood_density [Finite G] (F : Subgroup G) (g : G) {B : ℕ}
    (hB : ∀ x : G, centralizerIndex x ≤ B) (q : CentralCosets F) :
    Nat.card (CentralCosets F) ≤ B *
      Nat.card {r : CentralCosets F // Commute (g * (q.out : G)) (g * (r.out : G))} := by
  let Z := (Subgroup.center G).subgroupOf F
  let π : F →* CentralCosets F := QuotientGroup.mk' Z
  let A := Subgroup.centralizer ({g * (q.out : G)} : Set G)
  let C := A.subgroupOf F
  have hZC : π.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_center_iff.mp hz _).symm
  have hindex : (C.map π).index = C.index :=
    C.index_map_eq (QuotientGroup.mk'_surjective Z) hZC
  have hC : C.index ≤ B := by
    have hrel : A.relIndex F ≤ A.index := by
      have hne : A.relIndex ⊤ ≠ 0 := by
        simpa using (Subgroup.index_ne_zero_of_finite (H := A))
      simpa using (Subgroup.relIndex_le_of_le_right (H := A) (K := F) (L := ⊤) le_top hne)
    exact hrel.trans (hB _)
  rw [coset_neighborhood_card]
  calc
    Nat.card (CentralCosets F) = (C.map π).index * Nat.card (C.map π) :=
      (Subgroup.index_mul_card _).symm
    _ ≤ B * Nat.card (C.map π) := Nat.mul_le_mul_right _ (hindex.trans_le hC)

/-- The number of anchors needed for one subgroup coset. -/
noncomputable def cosetCoverCost (F : Subgroup G) (B : ℕ) : ℕ :=
  2 * B * (Nat.log 2 (Nat.card (CentralCosets F)) + 1)

theorem exists_coset_dominating_set [Finite G] (F : Subgroup G) (g : G) {B : ℕ}
    (hBpos : 0 < B) (hB : ∀ x : G, centralizerIndex x ≤ B) :
    ∃ s : Finset (CentralCosets F), s.card ≤ cosetCoverCost F B ∧
      ∀ x : F, ∃ q ∈ s, Commute (g * (q.out : G)) (g * (x : G)) := by
  classical
  let Q := CentralCosets F
  let := Fintype.ofFinite Q
  let N : Q → Finset Q := fun q => univ.filter
    (fun r => Commute (g * (q.out : G)) (g * (r.out : G)))
  have hsymm : ∀ q r, q ∈ N r ↔ r ∈ N q := by
    intro q r
    simp only [N, mem_filter, mem_univ, true_and, commute_iff_eq, eq_comm]
  have hdegree : ∀ q, Fintype.card Q ≤ B * (N q).card := by
    intro q
    have h := coset_neighborhood_density F g hB q
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, N] using h
  obtain ⟨s, hs, hdom⟩ := exists_logarithmic_dominating_set N hsymm hBpos hdegree
  refine ⟨s, by simpa only [cosetCoverCost, Nat.card_eq_fintype_card] using hs, ?_⟩
  intro x
  obtain ⟨q, hq, hx⟩ := hdom (x : Q)
  have hx' : Commute (g * (q.out : G)) (g * ((x : Q).out : G)) := (mem_filter.mp hx).2
  exact ⟨q, hq, (coset_commute_of_quotient_eq F g (x := q.out) (x' := q.out)
    rfl (Quotient.out_eq' (x : Q))).mp hx'⟩

/-- A coset of a subgroup with a `k`-element abelian cover has a commuting
coloring with at most `cosetCoverCost F B * k` colors. -/
theorem exists_coset_coloring [Finite G] (F : Subgroup G) (g : G) {B k : ℕ}
    (hBpos : 0 < B) (hB : ∀ x : G, centralizerIndex x ≤ B)
    (hF : HasAbelianCover F k) :
    ∃ c : F → Fin (cosetCoverCost F B * k),
      ∀ x y, c x = c y → Commute (g * (x : G)) (g * (y : G)) := by
  classical
  obtain ⟨s, hs, hdom⟩ := exists_coset_dominating_set F g hBpos hB
  obtain ⟨c, hc⟩ := (hasAbelianCover_iff_coloring k).mp hF
  obtain ⟨d, hd⟩ := coset_coloring_of_dominating_family F g
    (fun q : s => q.1.out) (fun x => by
      obtain ⟨q, hq, hx⟩ := hdom x
      exact ⟨⟨q, hq⟩, hx⟩) c hc
  have hcard : Fintype.card (s × Fin k) ≤ cosetCoverCost F B * k := by
    simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
      Nat.mul_le_mul_right k hs
  let e : s × Fin k ↪ Fin (cosetCoverCost F B * k) :=
    (Fintype.equivFin (s × Fin k)).toEmbedding.trans (Fin.castLEEmb hcard)
  exact ⟨fun x => e (d x), fun x y hxy => hd x y (e.injective hxy)⟩

/-- Extend an abelian cover of any subgroup to the whole finite group.
The factor involving central cosets is independent of `|Z(G)|`. -/
theorem hasAbelianCover_extension [Finite G] (F : Subgroup G) {B k : ℕ}
    (hBpos : 0 < B) (hB : ∀ x : G, centralizerIndex x ≤ B)
    (hF : HasAbelianCover F k) :
    HasAbelianCover G (F.index * (cosetCoverCost F B * k)) := by
  classical
  let Q := G ⧸ F
  let := Fintype.ofFinite Q
  have hcoset : ∀ q : Q, ∃ c : F → Fin (cosetCoverCost F B * k),
      ∀ x y, c x = c y → Commute (q.out * (x : G)) (q.out * (y : G)) :=
    fun q => exists_coset_coloring F q.out hBpos hB hF
  choose c hc using hcoset
  let r : G → F := fun x => ⟨(x : Q).out⁻¹ * x,
    QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' (x : Q)))⟩
  have hsplit (x : G) : (x : Q).out * (r x : G) = x := by
    dsimp [r]
    exact mul_inv_cancel_left _ _
  let d : G → Q × Fin (cosetCoverCost F B * k) := fun x => ((x : Q), c (x : Q) (r x))
  let e : Q × Fin (cosetCoverCost F B * k) ≃ Fin (F.index * (cosetCoverCost F B * k)) :=
    Fintype.equivFinOfCardEq (by
      rw [Fintype.card_prod, Fintype.card_fin]
      exact congrArg (fun m => m * (cosetCoverCost F B * k))
        (Nat.card_eq_fintype_card (α := Q)).symm)
  apply (hasAbelianCover_iff_coloring _).mpr
  refine ⟨fun x => e (d x), fun x y hxy => ?_⟩
  have hd : d x = d y := e.injective hxy
  have hq : (x : Q) = (y : Q) := congrArg Prod.fst hd
  have hcol : c (x : Q) (r x) = c (y : Q) (r y) := congrArg Prod.snd hd
  rw [← hq] at hcol
  have h := hc (x : Q) (r x) (r y) hcol
  rw [hsplit x, hq, hsplit y] at h
  exact h

theorem cosetCoverCost_le_centerIndex [Finite G] (F : Subgroup G) (B : ℕ) :
    cosetCoverCost F B ≤ 2 * B * (Nat.log 2 (Subgroup.center G).index + 1) := by
  have hrel : Nat.card (CentralCosets F) ≤ (Subgroup.center G).index := by
    have hne : (Subgroup.center G).relIndex ⊤ ≠ 0 := by
      simpa using (Subgroup.index_ne_zero_of_finite (H := Subgroup.center G))
    exact (Subgroup.relIndex_le_of_le_right (H := Subgroup.center G) (K := F) (L := ⊤)
      le_top hne).trans_eq (Subgroup.relIndex_top_right _)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right hrel) 1)

/-- The extension loss apart from the subgroup index and its cover is a
polynomial in the original clique bound. This avoids invoking an exponential
center-index theorem solely to obtain a polynomial covering factor. -/
theorem cosetCoverCost_le_polynomial [Finite G] (F : Subgroup G) {n : ℕ}
    (hn : NoncommutingBound G n) :
    cosetCoverCost F ((2 * n) ^ 2) ≤
      2 * (2 * n) ^ 2 * ((2 * n) ^ 2 * n + 1) := by
  have hpow : ((2 * n) ^ 2) ^ n ≤ 2 ^ ((2 * n) ^ 2 * n) := by
    calc
      ((2 * n) ^ 2) ^ n ≤ (2 ^ ((2 * n) ^ 2)) ^ n :=
        Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
      _ = 2 ^ ((2 * n) ^ 2 * n) := (pow_mul _ _ _).symm
  have hlog : Nat.log 2 (Subgroup.center G).index ≤ (2 * n) ^ 2 * n := by
    have h := Nat.log_mono_right (b := 2) ((centerIndex_le hn).trans hpow)
    simpa only [Nat.log_pow (by decide : 1 < 2)] using h
  exact (cosetCoverCost_le_centerIndex F _).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))

theorem hasAbelianCover_extension_polynomial [Finite G] (F : Subgroup G) {n k : ℕ}
    (hn : NoncommutingBound G n) (hF : HasAbelianCover F k) :
    HasAbelianCover G (F.index * (2 * (2 * n) ^ 2 * ((2 * n) ^ 2 * n + 1) * k)) := by
  have hnpos := one_le_of_noncommutingBound hn
  apply hasAbelianCover_mono
    (hasAbelianCover_extension F (by positivity) (centralizerIndex_le hn) hF)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (cosetCoverCost_le_polynomial F hn))

end Erdos117
