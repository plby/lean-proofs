import ErdosProblems.Erdos207.Prefix

namespace Erdos207

open Finset

/-- A minimal forbidden configuration of girth exactly `r`. -/
def IsErdosConfigOn {V : Type*} [DecidableEq V] (r : ℕ)
    (C : TripleSystemOn V) : Prop :=
  IsConfigOn r (r - 2) C ∧ GirthGreaterOn (r - 1) C

abbrev IsErdosConfig {n : ℕ} (r : ℕ) (C : TripleSystem n) : Prop :=
  IsErdosConfigOn r C

def ConsistsOfTriangles {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : TripleSystemOn V) : Prop :=
  ∀ T ∈ C, ∀ u ∈ T.1, ∀ v ∈ T.1, u ≠ v → G.Adj u v

def HasAbsorberLocalization {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V) : Prop :=
  ∀ K : SimpleGraph V, H ≤ K → ∀ R : TripleSystemOn V,
    R.card ≤ q → ConsistsOfTriangles K R →
      ∃ L_R : TripleSystemOn V, L_R ⊆ B ∧ L_R.card ≤ M ∧
        ∀ r : ℕ, 5 ≤ r → r ≤ q → ∀ E : TripleSystemOn V,
          IsErdosConfigOn r E → R ⊆ E →
            E ∩ B ⊆ L_R ∨
              ∃ T ∈ E, T ∉ R ∪ B ∧
                ∃ v ∈ T.1, (∃ w, H.Adj v w) ∧ v ∉ X

def HasHighGirthAbsorptionBank {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) : Prop :=
  (∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ H.Adj u v) ∧
    ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      GraphSupportedOn L (X : Set V) → TriangleDivisible L →
        ∃ C : TripleSystemOn V, C ⊆ B ∧
          IsHighGirthTriangleDecomposition q (H ⊔ L) C

def EfficientHighGirthAbsorbers : Prop :=
  ∃ C_A : ℕ, ∀ q : ℕ, ∃ M_A : ℕ, ∀ m : ℕ, 1 ≤ m →
    ∃ N : ℕ, ∃ H : SimpleGraph (Fin N), ∃ X : Finset (Fin N),
      ∃ B : TripleSystemOn (Fin N),
        N ≤ M_A * m ^ C_A ∧ X.card = m ∧
          HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q M_A H X B

namespace IsErdosConfig

lemma subset_span {V : Type*} [DecidableEq V] {r : ℕ}
    {C D : TripleSystemOn V} (hC : IsErdosConfigOn r C)
    (hDC : D ⊆ C) (hD2 : 2 ≤ D.card) (hDsmall : D.card ≤ r - 3) :
    D.card + 3 ≤ (verticesOn D).card := by
  by_contra hspan
  have hspan' : (verticesOn D).card ≤ D.card + 2 := by omega
  have hs4 : 4 ≤ D.card + 2 := by omega
  have hsr : D.card + 2 ≤ r - 1 := by omega
  apply hC.2 (D.card + 2) hs4 hsr
  refine ⟨D, hDC, ?_⟩
  constructor
  · omega
  · exact hspan'

lemma vertices_card_eq {V : Type*} [DecidableEq V] {r : ℕ}
    {C : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r) :
    (verticesOn C).card = r := by
  have hCpos : 0 < C.card := by rw [hC.1.1]; omega
  obtain ⟨T, hTC⟩ := card_pos.mp hCpos
  let D := C.erase T
  have hDC : D ⊆ C := erase_subset T C
  have hDcard : D.card = r - 3 := by
    dsimp [D]
    rw [card_erase_of_mem hTC, hC.1.1]
    omega
  have hDspan := subset_span hC hDC (by omega) (by omega)
  have hspan_mono := card_le_card (verticesOn_mono hDC)
  apply Nat.le_antisymm hC.1.2
  omega

lemma subset_span_weak {V : Type*} [DecidableEq V] {r : ℕ}
    {C D : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r)
    (hDC : D ⊆ C) (hD1 : 1 ≤ D.card) (hDsmall : D.card ≤ r - 2) :
    D.card + 2 ≤ (verticesOn D).card := by
  by_cases hDone : D.card = 1
  · obtain ⟨T, rfl⟩ := card_eq_one.mp hDone
    simpa [verticesOn] using T.2.ge
  have hD2 : 2 ≤ D.card := by omega
  by_cases hproper : D.card ≤ r - 3
  · exact (by omega : D.card + 2 ≤ D.card + 3).trans
      (subset_span hC hDC hD2 hproper)
  have hcards : D.card = C.card := by rw [hC.1.1]; omega
  have hDCeq : D = C := eq_of_subset_of_card_le hDC (by omega)
  rw [hDCeq, vertices_card_eq hC hr, hC.1.1]
  omega

lemma two_le_card_triplesThrough {V : Type*} [DecidableEq V] {r : ℕ}
    {C : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r)
    {x : V} (hx : x ∈ verticesOn C) :
    2 ≤ (triplesThrough C x).card := by
  obtain ⟨T, hTC, hxT⟩ := (mem_biUnion.mp hx)
  have hTthrough : T ∈ triplesThrough C x := mem_filter.mpr ⟨hTC, hxT⟩
  by_contra hsmall
  have hcard : (triplesThrough C x).card = 1 := by
    have hpos : 0 < (triplesThrough C x).card := card_pos.mpr ⟨T, hTthrough⟩
    omega
  obtain ⟨U, hthrough⟩ := card_eq_one.mp hcard
  have hTU : T = U := by simpa [hthrough] using hTthrough
  let D := C.erase T
  have hDC : D ⊆ C := erase_subset T C
  have hDcard : D.card = r - 3 := by
    dsimp [D]
    rw [card_erase_of_mem hTC, hC.1.1]
    omega
  have hxD : x ∉ verticesOn D := by
    intro hxD
    obtain ⟨S, hSD, hxS⟩ := mem_biUnion.mp hxD
    have hSC := hDC hSD
    have hSthrough : S ∈ triplesThrough C x := mem_filter.mpr ⟨hSC, hxS⟩
    have hSU : S = U := by simpa [hthrough] using hSthrough
    exact (mem_erase.mp hSD).1 (hSU.trans hTU.symm)
  have hspanSub := verticesOn_mono hDC
  have hspanNe : verticesOn D ≠ verticesOn C := by
    intro heq
    apply hxD
    rw [heq]
    exact hx
  have hspanLt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hspanSub, hspanNe⟩)
  have hDspan := subset_span hC hDC (by omega) (by omega)
  have hCspan := vertices_card_eq hC hr
  omega

lemma vertices_eq_of_card_sub_three {V : Type*} [DecidableEq V] {r : ℕ}
    {C D : TripleSystemOn V} (hC : IsErdosConfigOn r C) (hr : 5 ≤ r)
    (hDC : D ⊆ C) (hDcard : D.card = r - 3) :
    verticesOn D = verticesOn C := by
  apply eq_of_subset_of_card_le (verticesOn_mono hDC)
  have hDspan := subset_span hC hDC (by omega) (by omega)
  rw [vertices_card_eq hC hr]
  omega

end IsErdosConfig

theorem exists_erdosConfig_of_not_girthGreater
    {V : Type*} [DecidableEq V] {q : ℕ} {H : TripleSystemOn V}
    (h : ¬ GirthGreaterOn q H) :
    ∃ r, 4 ≤ r ∧ r ≤ q ∧ ∃ C ⊆ H, IsErdosConfigOn r C := by
  classical
  unfold GirthGreaterOn at h
  push Not at h
  obtain ⟨r, hr4, hrq, C, hCH, hconfig⟩ := h
  let P : ℕ → Prop := fun s ↦
    4 ≤ s ∧ s ≤ q ∧ ∃ D ⊆ H, IsConfigOn s (s - 2) D
  have hPex : ∃ s, P s := ⟨r, hr4, hrq, C, hCH, hconfig⟩
  let r₀ := Nat.find hPex
  have hP₀ := Nat.find_spec hPex
  change P r₀ at hP₀
  obtain ⟨hr₀4, hr₀q, C₀, hC₀H, hC₀config⟩ := hP₀
  refine ⟨r₀, hr₀4, hr₀q, C₀, hC₀H, hC₀config, ?_⟩
  intro s hs4 hsr₀
  rintro ⟨D, hDC₀, hDconfig⟩
  have hsP : P s :=
    ⟨hs4, by omega, D, hDC₀.trans hC₀H, hDconfig⟩
  have hminimal : r₀ ≤ s := Nat.find_min' hPex hsP
  omega

lemma IsPackingOn.no_four_config {V : Type*} [DecidableEq V]
    {H : TripleSystemOn V} (hH : IsPackingOn H) :
    ¬ ∃ C ⊆ H, IsConfigOn 4 2 C := by
  rintro ⟨C, hCH, hCcard, hCspan⟩
  obtain ⟨T, U, hTU, rfl⟩ := card_eq_two.mp hCcard
  have hTH : T ∈ H := hCH (by simp)
  have hUH : U ∈ H := hCH (by simp)
  have hinter := hH.inter_card_le_one hTH hUH hTU
  have hunion := card_union_add_card_inter T.1 U.1
  have hvertices : verticesOn ({T, U} : TripleSystemOn V) = T.1 ∪ U.1 := by
    simp [verticesOn]
  rw [hvertices] at hCspan
  have hTcard := T.2
  have hUcard := U.2
  omega

theorem IsPackingOn.girthGreater_of_leaf
    {V : Type*} [DecidableEq V] {q : ℕ} {H : TripleSystemOn V}
    (hH : IsPackingOn H)
    (hleaf : ∀ r : ℕ, 5 ≤ r → r ≤ q →
      ∀ C ⊆ H, IsErdosConfigOn r C →
        ∃ x ∈ verticesOn C, (triplesThrough C x).card = 1) :
    GirthGreaterOn q H := by
  classical
  by_contra hgirth
  obtain ⟨r, hr4, hrq, C, hCH, hC⟩ :=
    exists_erdosConfig_of_not_girthGreater hgirth
  by_cases hr : r = 4
  · subst r
    exact hH.no_four_config ⟨C, hCH, hC.1⟩
  have hr5 : 5 ≤ r := by omega
  obtain ⟨x, hxC, hxone⟩ := hleaf r hr5 hrq C hCH hC
  have hxtwo := IsErdosConfig.two_le_card_triplesThrough hC hr5 hxC
  omega

def HasShortLeafProperty {V : Type*} [DecidableEq V]
    (q : ℕ) (H : TripleSystemOn V) : Prop :=
  ∀ C ⊆ H, C.Nonempty → C.card ≤ q →
    ∃ x ∈ verticesOn C, (triplesThrough C x).card = 1

theorem IsPackingOn.girthGreater_of_shortLeaf
    {V : Type*} [DecidableEq V] {q : ℕ} {H : TripleSystemOn V}
    (hH : IsPackingOn H) (hleaf : HasShortLeafProperty q H) :
    GirthGreaterOn q H := by
  apply hH.girthGreater_of_leaf
  intro r hr5 hrq C hCH hC
  apply hleaf C hCH
  · rw [nonempty_iff_ne_empty]
    intro hCempty
    have : C.card = 0 := by simp [hCempty]
    rw [hC.1.1] at this
    omega
  · rw [hC.1.1]
    omega

def HasFiberwiseShortLeaf {V I : Type*} [DecidableEq V] [DecidableEq I]
    (q : ℕ) (H : TripleSystemOn V) (color : TripleOn V → I)
    (privateVerts : I → Finset V) : Prop :=
  ∀ i : I,
    (∀ T ∈ H, ∀ x ∈ privateVerts i, x ∈ T.1 → color T = i) ∧
      ∀ D ⊆ H.filter fun T ↦ color T = i,
        D.Nonempty → D.card ≤ q →
          ∃ x ∈ privateVerts i, x ∈ verticesOn D ∧
            (triplesThrough D x).card = 1

theorem HasFiberwiseShortLeaf.hasShortLeafProperty
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    {q : ℕ} {H : TripleSystemOn V} {color : TripleOn V → I}
    {privateVerts : I → Finset V}
    (h : HasFiberwiseShortLeaf q H color privateVerts) :
    HasShortLeafProperty q H := by
  intro C hCH hCne hCq
  obtain ⟨T, hTC⟩ := hCne
  let i := color T
  let D := C.filter fun U ↦ color U = i
  have hDH : D ⊆ H.filter fun U ↦ color U = i := by
    intro U hUD
    exact mem_filter.mpr ⟨hCH (mem_filter.mp hUD).1, (mem_filter.mp hUD).2⟩
  have hDne : D.Nonempty :=
    ⟨T, mem_filter.mpr ⟨hTC, rfl⟩⟩
  have hDq : D.card ≤ q := (card_le_card (filter_subset _ _)).trans hCq
  obtain ⟨x, hxprivate, hxD, hxone⟩ := (h i).2 D hDH hDne hDq
  have hDC : D ⊆ C := filter_subset _ _
  refine ⟨x, verticesOn_mono hDC hxD, ?_⟩
  have hthrough : triplesThrough C x = triplesThrough D x := by
    dsimp [D]
    ext U
    simp only [triplesThrough, mem_filter]
    constructor
    · rintro ⟨hUC, hxU⟩
      have hcolor := (h i).1 U (hCH hUC) x hxprivate hxU
      exact ⟨⟨hUC, hcolor⟩, hxU⟩
    · rintro ⟨⟨hUC, _⟩, hxU⟩
      exact ⟨hUC, hxU⟩
  rw [hthrough]
  exact hxone

/-- Incidence data abstracted from one sphere bank. -/
structure SphereIndexing {V : Type*} [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) where
  edgeIndex : TripleOn V → Fin (2 * q)
  cycleVertex : Fin (2 * q) → V
  hub : V
  sharedPair : ∀ T ∈ B, ∀ U ∈ B, edgeIndex T = edgeIndex U →
    ∃ x y, x ≠ y ∧ x ∈ T.1 ∧ y ∈ T.1 ∧ x ∈ U.1 ∧ y ∈ U.1
  privateIncidence : ∀ (k : Fin (2 * q)) (hk : 2 ≤ k.val),
    ∀ T ∈ B, cycleVertex k ∈ T.1 ↔
      edgeIndex T = finPred k (by omega) ∨ edgeIndex T = k
  exceptionalHub : ∀ T ∈ B, (edgeIndex T).val = 0 → hub ∈ T.1

namespace SphereIndexing

lemma index_injective_on_packing {V : Type*} [DecidableEq V] {q : ℕ}
    {B C : TripleSystemOn V} (S : SphereIndexing q B)
    (hCB : C ⊆ B) (hC : IsPackingOn C)
    {T U : TripleOn V} (hTC : T ∈ C) (hUC : U ∈ C)
    (hindex : S.edgeIndex T = S.edgeIndex U) : T = U := by
  obtain ⟨x, y, hxy, hxT, hyT, hxU, hyU⟩ :=
    S.sharedPair T (hCB hTC) U (hCB hUC) hindex
  exact hC x y hxy T hTC hxT hyT U hUC hxU hyU

theorem short_leaf {V : Type*} [DecidableEq V] {q : ℕ} (hq : 2 ≤ q)
    {B C : TripleSystemOn V} (S : SphereIndexing q B)
    (hCB : C ⊆ B) (hpacking : IsPackingOn C)
    (hCne : C.Nonempty) (hCq : C.card ≤ q) :
    ∃ x ∈ verticesOn C, (triplesThrough C x).card = 1 := by
  let indices := C.image S.edgeIndex
  have hindicesCard : indices.card ≤ q := card_image_le.trans hCq
  rcases exists_private_cycle_leaf_or_exceptional hq indices hindicesCard with
      hzero | ⟨k, hk2, hkpos, hkchange⟩
  · obtain ⟨T, hTC⟩ := hCne
    have hTzero : (S.edgeIndex T).val = 0 :=
      hzero _ (mem_image.mpr ⟨T, hTC, rfl⟩)
    have hhubT := S.exceptionalHub T (hCB hTC) hTzero
    have hallT : ∀ U ∈ C, U = T := by
      intro U hUC
      have hUzero : (S.edgeIndex U).val = 0 :=
        hzero _ (mem_image.mpr ⟨U, hUC, rfl⟩)
      have hindex : S.edgeIndex U = S.edgeIndex T := by
        apply Fin.ext
        omega
      exact S.index_injective_on_packing hCB hpacking hUC hTC hindex
    refine ⟨S.hub, ?_, ?_⟩
    · exact mem_biUnion.mpr ⟨T, hTC, hhubT⟩
    · have hthrough : triplesThrough C S.hub = {T} := by
        ext U
        simp only [triplesThrough, mem_filter, mem_singleton]
        constructor
        · rintro ⟨hUC, _⟩
          exact hallT U hUC
        · rintro rfl
          exact ⟨hTC, hhubT⟩
      rw [hthrough, card_singleton]
  · let p := finPred k hkpos
    have hxor :
        (p ∈ indices ∧ k ∉ indices) ∨ (p ∉ indices ∧ k ∈ indices) := by
      dsimp [p]
      by_cases hp : finPred k hkpos ∈ indices
      · left
        refine ⟨hp, ?_⟩
        intro hk
        exact hkchange ⟨fun _ ↦ hk, fun _ ↦ hp⟩
      · right
        refine ⟨hp, ?_⟩
        by_contra hk
        exact hkchange ⟨fun h ↦ (hp h).elim, fun h ↦ (hk h).elim⟩
    rcases hxor with hleft | hright
    · obtain ⟨T, hTC, hTp⟩ := mem_image.mp hleft.1
      have hkT := (S.privateIncidence k hk2 T (hCB hTC)).mpr (Or.inl hTp)
      have hunique : ∀ U ∈ C, S.cycleVertex k ∈ U.1 → U = T := by
        intro U hUC hkU
        rcases (S.privateIncidence k hk2 U (hCB hUC)).mp hkU with hUp | hUk
        · exact S.index_injective_on_packing hCB hpacking hUC hTC
            (hUp.trans hTp.symm)
        · exact (hleft.2 (mem_image.mpr ⟨U, hUC, hUk⟩)).elim
      refine ⟨S.cycleVertex k, mem_biUnion.mpr ⟨T, hTC, hkT⟩, ?_⟩
      have hthrough : triplesThrough C (S.cycleVertex k) = {T} := by
        ext U
        simp only [triplesThrough, mem_filter, mem_singleton]
        constructor
        · rintro ⟨hUC, hkU⟩
          exact hunique U hUC hkU
        · rintro rfl
          exact ⟨hTC, hkT⟩
      rw [hthrough, card_singleton]
    · obtain ⟨T, hTC, hTk⟩ := mem_image.mp hright.2
      have hkT := (S.privateIncidence k hk2 T (hCB hTC)).mpr (Or.inr hTk)
      have hunique : ∀ U ∈ C, S.cycleVertex k ∈ U.1 → U = T := by
        intro U hUC hkU
        rcases (S.privateIncidence k hk2 U (hCB hUC)).mp hkU with hUp | hUk
        · exact (hright.1 (mem_image.mpr ⟨U, hUC, hUp⟩)).elim
        · exact S.index_injective_on_packing hCB hpacking hUC hTC
            (hUk.trans hTk.symm)
      refine ⟨S.cycleVertex k, mem_biUnion.mpr ⟨T, hTC, hkT⟩, ?_⟩
      have hthrough : triplesThrough C (S.cycleVertex k) = {T} := by
        ext U
        simp only [triplesThrough, mem_filter, mem_singleton]
        constructor
        · rintro ⟨hUC, hkU⟩
          exact hunique U hUC hkU
        · rintro rfl
          exact ⟨hTC, hkT⟩
      rw [hthrough, card_singleton]

end SphereIndexing

inductive SphereVertex (q : ℕ) where
  | cycle : Fin (2 * q) → SphereVertex q
  | pole : Bool → SphereVertex q
  deriving DecidableEq, Fintype

abbrev ConcreteSphereTag (q : ℕ) :=
  {p : Fin (2 * q) × Bool // p.1.val = 0 → p.2 = false}

def concreteSphereDefaultTag {q : ℕ} (hq : 2 ≤ q) : ConcreteSphereTag q :=
  ⟨(⟨0, by omega⟩, false), by simp⟩

def sphereTriangle {q : ℕ} (hq : 2 ≤ q)
    (t : ConcreteSphereTag q) : TripleOn (SphereVertex q) := by
  let j := t.1.1
  let b := t.1.2
  let j' := finCycleSucc (by omega) j
  refine ⟨{SphereVertex.cycle j, SphereVertex.cycle j', SphereVertex.pole b}, ?_⟩
  have hjj' : j ≠ j' := (finCycleSucc_ne (by omega) j).symm
  have hfirst : SphereVertex.cycle j ∉
      ({SphereVertex.cycle j', SphereVertex.pole b} : Finset (SphereVertex q)) := by
    simp [hjj']
  have hsecond : SphereVertex.cycle j' ∉
      ({SphereVertex.pole b} : Finset (SphereVertex q)) := by simp
  simp [hfirst, hsecond]

def sphereBank {q : ℕ} (hq : 2 ≤ q) : TripleSystemOn (SphereVertex q) :=
  univ.image (sphereTriangle hq)

@[simp]
lemma sphere_cycle_mem {q : ℕ} (hq : 2 ≤ q)
    (t : ConcreteSphereTag q) (k : Fin (2 * q)) :
    SphereVertex.cycle k ∈ (sphereTriangle hq t).1 ↔
      k = t.1.1 ∨ k = finCycleSucc (by omega) t.1.1 := by
  simp [sphereTriangle]

@[simp]
lemma sphere_pole_mem {q : ℕ} (hq : 2 ≤ q)
    (t : ConcreteSphereTag q) (b : Bool) :
    SphereVertex.pole b ∈ (sphereTriangle hq t).1 ↔ b = t.1.2 := by
  simp [sphereTriangle]

lemma sphereTriangle_injective {q : ℕ} (hq : 2 ≤ q) :
    Function.Injective (sphereTriangle hq) := by
  intro t u htu
  have hpole : t.1.2 = u.1.2 := by
    have hm : SphereVertex.pole t.1.2 ∈ (sphereTriangle hq u).1 := by
      rw [← htu]
      simp
    simpa using (sphere_pole_mem hq u t.1.2).mp hm
  have hedge : ({t.1.1, finCycleSucc (by omega) t.1.1} : Finset (Fin (2 * q))) =
      {u.1.1, finCycleSucc (by omega) u.1.1} := by
    ext k
    have hmem : SphereVertex.cycle k ∈ (sphereTriangle hq t).1 ↔
        SphereVertex.cycle k ∈ (sphereTriangle hq u).1 := by rw [htu]
    simpa using hmem
  have hindex : t.1.1 = u.1.1 :=
    cycleEdge_index_unique (by omega) _ _ hedge
  apply Subtype.ext
  exact Prod.ext hindex hpole

noncomputable def sphereTagOf {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn (SphereVertex q)) : ConcreteSphereTag q :=
  if h : ∃ t, sphereTriangle hq t = T then h.choose
  else concreteSphereDefaultTag hq

lemma sphereTriangle_tagOf {q : ℕ} (hq : 2 ≤ q)
    {T : TripleOn (SphereVertex q)} (hT : T ∈ sphereBank hq) :
    sphereTriangle hq (sphereTagOf hq T) = T := by
  obtain ⟨t, _, rfl⟩ := mem_image.mp hT
  unfold sphereTagOf
  rw [dif_pos ⟨t, rfl⟩]
  exact Classical.choose_spec
    (show ∃ u, sphereTriangle hq u = sphereTriangle hq t from ⟨t, rfl⟩)

noncomputable def sphereIndexing {q : ℕ} (hq : 2 ≤ q) :
    SphereIndexing q (sphereBank hq) where
  edgeIndex T := (sphereTagOf hq T).1.1
  cycleVertex := SphereVertex.cycle
  hub := SphereVertex.pole false
  sharedPair T hT U hU hindex := by
    let t := sphereTagOf hq T
    let u := sphereTagOf hq U
    have hTrep := sphereTriangle_tagOf hq hT
    have hUrep := sphereTriangle_tagOf hq hU
    refine ⟨SphereVertex.cycle t.1.1,
      SphereVertex.cycle (finCycleSucc (by omega) t.1.1), ?_, ?_, ?_, ?_, ?_⟩
    · intro heq
      exact finCycleSucc_ne (by omega) t.1.1 (SphereVertex.cycle.inj heq).symm
    · rw [← hTrep]
      exact (sphere_cycle_mem hq t t.1.1).mpr (Or.inl rfl)
    · rw [← hTrep]
      exact (sphere_cycle_mem hq t (finCycleSucc (by omega) t.1.1)).mpr
        (Or.inr rfl)
    · rw [← hUrep]
      exact (sphere_cycle_mem hq u t.1.1).mpr (Or.inl hindex)
    · rw [← hUrep]
      exact (sphere_cycle_mem hq u (finCycleSucc (by omega) t.1.1)).mpr
        (Or.inr (congrArg (finCycleSucc (by omega)) hindex))
  privateIncidence k hk T hT := by
    let t := sphereTagOf hq T
    have hTrep := sphereTriangle_tagOf hq hT
    change SphereVertex.cycle k ∈ T.1 ↔
      t.1.1 = finPred k (by omega) ∨ t.1.1 = k
    constructor
    · intro hkT
      have hkSphere : SphereVertex.cycle k ∈ (sphereTriangle hq t).1 := by
        rw [hTrep]
        exact hkT
      rcases (sphere_cycle_mem hq t k).mp hkSphere with hkt | hksucc
      · exact Or.inr hkt.symm
      · left
        exact (finCycleSucc_eq_iff_eq_finPred (by omega) t.1.1 k (by omega)).mp
          hksucc.symm
    · intro h
      have hkSphere : SphereVertex.cycle k ∈ (sphereTriangle hq t).1 := by
        apply (sphere_cycle_mem hq t k).mpr
        rcases h with htprev | htk
        · right
          exact ((finCycleSucc_eq_iff_eq_finPred (by omega) t.1.1 k (by omega)).mpr
            htprev).symm
        · exact Or.inl htk.symm
      rw [hTrep] at hkSphere
      exact hkSphere
  exceptionalHub T hT hzero := by
    let t := sphereTagOf hq T
    have hTrep := sphereTriangle_tagOf hq hT
    rw [← hTrep]
    exact (sphere_pole_mem hq t false).mpr (t.2 hzero).symm

theorem sphere_short_leaf {q : ℕ} (hq : 2 ≤ q)
    {C : TripleSystemOn (SphereVertex q)}
    (hCB : C ⊆ sphereBank hq) (hC : IsPackingOn C)
    (hCne : C.Nonempty) (hCq : C.card ≤ q) :
    ∃ x ∈ verticesOn C, (triplesThrough C x).card = 1 :=
  SphereIndexing.short_leaf hq (sphereIndexing hq) hCB hC hCne hCq

def spherePhase {q : ℕ} (j : Fin (2 * q)) : Bool :=
  decide (j.val % 2 = 1)

def sphereTagSelected {q : ℕ} (inward : Bool)
    (t : ConcreteSphereTag q) : Prop :=
  (t.1.2 == spherePhase t.1.1) = inward

noncomputable def sphereSelectedTags {q : ℕ} (inward : Bool) :
    Finset (ConcreteSphereTag q) := by
  classical
  exact univ.filter (sphereTagSelected inward)

noncomputable def sphereDecomposition {q : ℕ} (hq : 2 ≤ q) (inward : Bool) :
    TripleSystemOn (SphereVertex q) :=
  (sphereSelectedTags inward).image (sphereTriangle hq)

@[simp]
lemma mem_sphereSelectedTags_iff {q : ℕ} {inward : Bool}
    {t : ConcreteSphereTag q} :
    t ∈ sphereSelectedTags inward ↔ sphereTagSelected inward t := by
  simp [sphereSelectedTags]

lemma sphereTagSelected_unique {q : ℕ} {inward : Bool}
    {t u : ConcreteSphereTag q} (ht : sphereTagSelected inward t)
    (hu : sphereTagSelected inward u) (hindex : t.1.1 = u.1.1) : t = u := by
  apply Subtype.ext
  apply Prod.ext hindex
  unfold sphereTagSelected at ht hu
  rw [hindex] at ht
  cases htphase : spherePhase u.1.1 <;>
    cases htbool : t.1.2 <;> cases hubool : u.1.2 <;>
    simp [htphase, htbool, hubool] at ht hu ⊢ <;> simp_all

lemma sphereTagSelected_phase_eq {q : ℕ} {inward : Bool}
    {t : ConcreteSphereTag q} (ht : sphereTagSelected inward t) :
    (t.1.2 = spherePhase t.1.1) ↔ inward = true := by
  unfold sphereTagSelected at ht
  cases hphase : spherePhase t.1.1 <;> cases hb : t.1.2 <;>
    simp [hphase, hb] at ht ⊢ <;> simp [← ht]

def sphereInTag {q : ℕ} (_hq : 2 ≤ q) (j : Fin (2 * q)) :
    ConcreteSphereTag q := by
  refine ⟨(j, spherePhase j), ?_⟩
  intro hj
  change j.val = 0 at hj
  have hmod : j.val % 2 = 0 := by simp [hj]
  simp [spherePhase, hmod]

def sphereOutTag {q : ℕ} (_hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) : ConcreteSphereTag q := by
  refine ⟨(j, !spherePhase j), ?_⟩
  intro hzero
  exact (hj hzero).elim

lemma sphereInTag_selected {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    sphereTagSelected true (sphereInTag hq j) := by
  simp [sphereInTag, sphereTagSelected]

lemma sphereOutTag_selected {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) : sphereTagSelected false (sphereOutTag hq j hj) := by
  simp [sphereOutTag, sphereTagSelected]

lemma sphereTagSelected_true_iff {q : ℕ} (t : ConcreteSphereTag q) :
    sphereTagSelected true t ↔ t.1.2 = spherePhase t.1.1 := by
  unfold sphereTagSelected
  cases spherePhase t.1.1 <;> cases t.1.2 <;> decide

lemma sphereTagSelected_false_iff {q : ℕ} (t : ConcreteSphereTag q) :
    sphereTagSelected false t ↔ t.1.2 = !spherePhase t.1.1 := by
  unfold sphereTagSelected
  cases spherePhase t.1.1 <;> cases t.1.2 <;> decide

lemma sphereTagSelected_false_index_ne_zero {q : ℕ}
    {t : ConcreteSphereTag q} (ht : sphereTagSelected false t) :
    t.1.1.val ≠ 0 := by
  intro hzero
  have hphase : spherePhase t.1.1 = false := by
    simp [spherePhase, hzero]
  have hbfalse := t.2 hzero
  have := (sphereTagSelected_false_iff t).mp ht
  simp [hphase, hbfalse] at this

lemma spherePhase_cycleSucc {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    spherePhase (finCycleSucc (by omega) j) = !spherePhase j := by
  rcases Nat.mod_two_eq_zero_or_one j.val with hj0 | hj1
  · have hnext : (j.val + 1) % 2 = 1 := by
      simp [Nat.add_mod, hj0]
    simp [spherePhase, hj0, hnext]
  · have hnext : (j.val + 1) % 2 = 0 := by
      simp [Nat.add_mod, hj1]
    simp [spherePhase, hj1, hnext]

lemma spherePhase_cyclePred {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    spherePhase (finCyclePred (by omega) j) = !spherePhase j := by
  have hs := spherePhase_cycleSucc hq (finCyclePred (by omega) j)
  rw [finCycleSucc_pred] at hs
  cases hp : spherePhase (finCyclePred (by omega) j) <;>
    cases hj : spherePhase j <;> simp_all

def sphereRootTriple {q : ℕ} (hq : 2 ≤ q) : TripleOn (SphereVertex q) := by
  let z : Fin (2 * q) := ⟨0, by omega⟩
  let o : Fin (2 * q) := ⟨1, by omega⟩
  refine ⟨{SphereVertex.pole true, SphereVertex.cycle z,
    SphereVertex.cycle o}, ?_⟩
  have hzo : z ≠ o := by
    intro h
    have := congrArg Fin.val h
    simp [z, o] at this
  simp [hzo]

@[simp]
lemma mem_sphereDecomposition_iff {q : ℕ} (hq : 2 ≤ q)
    {inward : Bool} {T : TripleOn (SphereVertex q)} :
    T ∈ sphereDecomposition hq inward ↔
      ∃ t, sphereTagSelected inward t ∧ sphereTriangle hq t = T := by
  classical
  simp [sphereDecomposition]

lemma sphereInTag_mem_raw {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    sphereTriangle hq (sphereInTag hq j) ∈ sphereDecomposition hq true := by
  exact mem_sphereDecomposition_iff hq |>.mpr
    ⟨sphereInTag hq j, sphereInTag_selected hq j, rfl⟩

lemma sphereOutTag_mem_raw {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) :
    sphereTriangle hq (sphereOutTag hq j hj) ∈ sphereDecomposition hq false := by
  exact mem_sphereDecomposition_iff hq |>.mpr
    ⟨sphereOutTag hq j hj, sphereOutTag_selected hq j hj, rfl⟩

lemma sphereTagSelected_phase_congr {q : ℕ} {inward : Bool}
    {t u : ConcreteSphereTag q} (ht : sphereTagSelected inward t)
    (hu : sphereTagSelected inward u) (hbool : t.1.2 = u.1.2) :
    spherePhase t.1.1 = spherePhase u.1.1 := by
  unfold sphereTagSelected at ht hu
  rw [hbool] at ht
  cases htb : u.1.2 <;> cases htp : spherePhase t.1.1 <;>
    cases hup : spherePhase u.1.1 <;> cases inward <;>
    simp_all

lemma sphereTag_eq_of_cycle_pole_mem {q : ℕ} (hq : 2 ≤ q)
    {inward : Bool} {t u : ConcreteSphereTag q} {k : Fin (2 * q)} {b : Bool}
    (htselected : sphereTagSelected inward t)
    (huselected : sphereTagSelected inward u)
    (hkt : SphereVertex.cycle k ∈ (sphereTriangle hq t).1)
    (hbt : SphereVertex.pole b ∈ (sphereTriangle hq t).1)
    (hku : SphereVertex.cycle k ∈ (sphereTriangle hq u).1)
    (hbu : SphereVertex.pole b ∈ (sphereTriangle hq u).1) : t = u := by
  have htb := (sphere_pole_mem hq t b).mp hbt
  have hub := (sphere_pole_mem hq u b).mp hbu
  have hbool : t.1.2 = u.1.2 := htb.symm.trans hub
  have hphase := sphereTagSelected_phase_congr htselected huselected hbool
  rcases (sphere_cycle_mem hq t k).mp hkt with hkt' | hkt'
  · rcases (sphere_cycle_mem hq u k).mp hku with hku' | hku'
    · exact sphereTagSelected_unique htselected huselected (hkt'.symm.trans hku')
    · have hidx : t.1.1 = finCycleSucc (by omega) u.1.1 :=
        hkt'.symm.trans hku'
      have hs := spherePhase_cycleSucc hq u.1.1
      rw [← hidx] at hs
      cases spherePhase u.1.1 <;> simp_all
  · rcases (sphere_cycle_mem hq u k).mp hku with hku' | hku'
    · have hidx : u.1.1 = finCycleSucc (by omega) t.1.1 :=
        hku'.symm.trans hkt'
      have hs := spherePhase_cycleSucc hq t.1.1
      rw [← hidx] at hs
      cases spherePhase t.1.1 <;> simp_all
    · have hidx : t.1.1 = u.1.1 := by
        apply finCycleSucc_injective (by omega)
        exact hkt'.symm.trans hku'
      exact sphereTagSelected_unique htselected huselected hidx

theorem sphereDecomposition_isPacking {q : ℕ} (hq : 2 ≤ q)
    (inward : Bool) : IsPackingOn (sphereDecomposition hq inward) := by
  intro x y hxy T hT hxT hyT U hU hxU hyU
  obtain ⟨t, htselected, rfl⟩ := (mem_sphereDecomposition_iff hq).mp hT
  obtain ⟨u, huselected, rfl⟩ := (mem_sphereDecomposition_iff hq).mp hU
  apply congrArg (sphereTriangle hq)
  cases x with
  | cycle k =>
      cases y with
      | pole b =>
          exact sphereTag_eq_of_cycle_pole_mem hq htselected huselected
            hxT hyT hxU hyU
      | cycle l =>
          have htEdge : ({k, l} : Finset (Fin (2 * q))) =
              {t.1.1, finCycleSucc (by omega) t.1.1} := by
            apply eq_of_subset_of_card_le
            · intro z hz
              simp only [mem_insert, mem_singleton] at hz ⊢
              rcases hz with rfl | rfl
              · exact (sphere_cycle_mem hq t _).mp hxT
              · exact (sphere_cycle_mem hq t _).mp hyT
            · have hkl : k ≠ l := by
                intro hkl
                apply hxy
                exact congrArg SphereVertex.cycle hkl
              rw [card_pair hkl,
                card_pair (finCycleSucc_ne (by omega) t.1.1).symm]
          have huEdge : ({k, l} : Finset (Fin (2 * q))) =
              {u.1.1, finCycleSucc (by omega) u.1.1} := by
            apply eq_of_subset_of_card_le
            · intro z hz
              simp only [mem_insert, mem_singleton] at hz ⊢
              rcases hz with rfl | rfl
              · exact (sphere_cycle_mem hq u _).mp hxU
              · exact (sphere_cycle_mem hq u _).mp hyU
            · have hkl : k ≠ l := by
                intro hkl
                apply hxy
                exact congrArg SphereVertex.cycle hkl
              rw [card_pair hkl,
                card_pair (finCycleSucc_ne (by omega) u.1.1).symm]
          have hindex : t.1.1 = u.1.1 :=
            cycleEdge_index_unique (by omega) _ _ (htEdge.symm.trans huEdge)
          exact sphereTagSelected_unique htselected huselected hindex
  | pole b =>
      cases y with
      | cycle k =>
          exact sphereTag_eq_of_cycle_pole_mem hq htselected huselected
            hyT hxT hyU hxU
      | pole c =>
          have hbt := (sphere_pole_mem hq t b).mp hxT
          have hct := (sphere_pole_mem hq t c).mp hyT
          exfalso
          apply hxy
          rw [hbt, hct]

lemma IsPackingOn.mono {V : Type*} [DecidableEq V]
    {C H : TripleSystemOn V} (hH : IsPackingOn H) (hCH : C ⊆ H) :
    IsPackingOn C := by
  intro x y hxy T hTC hxT hyT U hUC hxU hyU
  exact hH x y hxy T (hCH hTC) hxT hyT U (hCH hUC) hxU hyU

lemma sphereDecomposition_subset_bank {q : ℕ} (hq : 2 ≤ q)
    (inward : Bool) : sphereDecomposition hq inward ⊆ sphereBank hq := by
  intro T hT
  obtain ⟨t, _, rfl⟩ := (mem_sphereDecomposition_iff hq).mp hT
  simp [sphereBank]

theorem sphereDecomposition_hasShortLeaf {q : ℕ} (hq : 2 ≤ q)
    (inward : Bool) : HasShortLeafProperty q (sphereDecomposition hq inward) := by
  intro C hCD hCne hCq
  apply sphere_short_leaf hq
  · exact hCD.trans (sphereDecomposition_subset_bank hq inward)
  · exact (sphereDecomposition_isPacking hq inward).mono hCD
  · exact hCne
  · exact hCq

theorem sphereDecomposition_girthGreater {q : ℕ} (hq : 2 ≤ q)
    (inward : Bool) : GirthGreaterOn q (sphereDecomposition hq inward) :=
  (sphereDecomposition_isPacking hq inward).girthGreater_of_shortLeaf
    (sphereDecomposition_hasShortLeaf hq inward)

lemma sphereIn_cycle_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.cycle j) (SphereVertex.cycle (finCycleSucc (by omega) j)) := by
  refine ⟨sphereTriangle hq (sphereInTag hq j), sphereInTag_mem_raw hq j, ?_, ?_, ?_⟩
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inl rfl)
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inr rfl)
  · intro h
    exact finCycleSucc_ne (by omega) j (SphereVertex.cycle.inj h).symm

lemma sphereOut_cycle_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) :
    (coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.cycle j) (SphereVertex.cycle (finCycleSucc (by omega) j)) := by
  refine ⟨sphereTriangle hq (sphereOutTag hq j hj),
    sphereOutTag_mem_raw hq j hj, ?_, ?_, ?_⟩
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inl rfl)
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inr rfl)
  · intro h
    exact finCycleSucc_ne (by omega) j (SphereVertex.cycle.inj h).symm

lemma sphereIn_pole_lower_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.pole (spherePhase j)) (SphereVertex.cycle j) := by
  refine ⟨sphereTriangle hq (sphereInTag hq j), sphereInTag_mem_raw hq j, ?_, ?_, ?_⟩
  · exact (sphere_pole_mem hq _ _).mpr rfl
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inl rfl)
  · simp

lemma sphereIn_pole_upper_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q)) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.pole (spherePhase j))
      (SphereVertex.cycle (finCycleSucc (by omega) j)) := by
  refine ⟨sphereTriangle hq (sphereInTag hq j), sphereInTag_mem_raw hq j, ?_, ?_, ?_⟩
  · exact (sphere_pole_mem hq _ _).mpr rfl
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inr rfl)
  · simp

lemma sphereOut_pole_lower_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) :
    (coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.pole (!spherePhase j)) (SphereVertex.cycle j) := by
  refine ⟨sphereTriangle hq (sphereOutTag hq j hj),
    sphereOutTag_mem_raw hq j hj, ?_, ?_, ?_⟩
  · exact (sphere_pole_mem hq _ _).mpr rfl
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inl rfl)
  · simp

lemma sphereOut_pole_upper_adj {q : ℕ} (hq : 2 ≤ q) (j : Fin (2 * q))
    (hj : j.val ≠ 0) :
    (coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.pole (!spherePhase j))
      (SphereVertex.cycle (finCycleSucc (by omega) j)) := by
  refine ⟨sphereTriangle hq (sphereOutTag hq j hj),
    sphereOutTag_mem_raw hq j hj, ?_, ?_, ?_⟩
  · exact (sphere_pole_mem hq _ _).mpr rfl
  · exact (sphere_cycle_mem hq _ _).mpr (Or.inr rfl)
  · simp

lemma sphereOut_coveredGraph_le_in {q : ℕ} (hq : 2 ≤ q) :
    coveredGraph (sphereDecomposition hq false) ≤
      coveredGraph (sphereDecomposition hq true) := by
  intro x y hxy
  obtain ⟨T, hT, hxT, hyT, hxyne⟩ := hxy
  obtain ⟨t, htselected, rfl⟩ := (mem_sphereDecomposition_iff hq).mp hT
  have hjne := sphereTagSelected_false_index_ne_zero htselected
  have hpole : ∀ b, SphereVertex.pole b ∈ (sphereTriangle hq t).1 →
      b = !spherePhase t.1.1 := by
    intro b hb
    rw [(sphere_pole_mem hq t b).mp hb]
    exact (sphereTagSelected_false_iff t).mp htselected
  cases x with
  | cycle k =>
      cases y with
      | cycle l =>
          rcases (sphere_cycle_mem hq t k).mp hxT with hk | hk <;>
            rcases (sphere_cycle_mem hq t l).mp hyT with hl | hl
          · exact (hxyne (congrArg SphereVertex.cycle (hk.trans hl.symm))).elim
          · simpa [hk, hl] using sphereIn_cycle_adj hq t.1.1
          · simpa [hk, hl] using (sphereIn_cycle_adj hq t.1.1).symm
          · exact (hxyne (congrArg SphereVertex.cycle (hk.trans hl.symm))).elim
      | pole b =>
          have hb := hpole b hyT
          rcases (sphere_cycle_mem hq t k).mp hxT with hk | hk
          · have h := (sphereIn_pole_upper_adj hq
                (finCyclePred (by omega) t.1.1)).symm
            rw [spherePhase_cyclePred hq t.1.1, finCycleSucc_pred] at h
            simpa [hk, hb] using h
          · have h := (sphereIn_pole_lower_adj hq
                (finCycleSucc (by omega) t.1.1)).symm
            rw [spherePhase_cycleSucc hq t.1.1] at h
            simpa [hk, hb] using h
  | pole b =>
      cases y with
      | pole c =>
          have hb := (sphere_pole_mem hq t b).mp hxT
          have hc := (sphere_pole_mem hq t c).mp hyT
          exact (hxyne (congrArg SphereVertex.pole (hb.trans hc.symm))).elim
      | cycle k =>
          have hb := hpole b hxT
          rcases (sphere_cycle_mem hq t k).mp hyT with hk | hk
          · have h := sphereIn_pole_upper_adj hq
                (finCyclePred (by omega) t.1.1)
            rw [spherePhase_cyclePred hq t.1.1, finCycleSucc_pred] at h
            simpa [hk, hb] using h
          · have h := sphereIn_pole_lower_adj hq
                (finCycleSucc (by omega) t.1.1)
            rw [spherePhase_cycleSucc hq t.1.1] at h
            simpa [hk, hb] using h

lemma finCycleSucc_zero_eq_one {q : ℕ} (hq : 2 ≤ q) :
    finCycleSucc (by omega) (⟨0, by omega⟩ : Fin (2 * q)) =
      (⟨1, by omega⟩ : Fin (2 * q)) := by
  apply Fin.ext
  simp [finCycleSucc_val, Nat.mod_eq_of_lt (by omega : 1 < 2 * q)]

lemma finCyclePred_val_ne_zero_of_val_ne_one {q : ℕ} (hq : 2 ≤ q)
    (j : Fin (2 * q)) (hj : j.val ≠ 1) :
    (finCyclePred (by omega) j).val ≠ 0 := by
  intro hp0
  have hp : finCyclePred (by omega) j = (⟨0, by omega⟩ : Fin (2 * q)) :=
    Fin.ext hp0
  have hs := finCycleSucc_pred (by omega) j
  rw [hp, finCycleSucc_zero_eq_one hq] at hs
  exact hj (congrArg Fin.val hs.symm)

lemma sphereRoot_cycle_adj {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q))).Adj
      (SphereVertex.cycle ⟨0, by omega⟩)
      (SphereVertex.cycle ⟨1, by omega⟩) := by
  refine ⟨sphereRootTriple hq, by simp, ?_, ?_, ?_⟩ <;>
    simp [sphereRootTriple]

lemma sphereRoot_pole_zero_adj {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q))).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨0, by omega⟩) := by
  refine ⟨sphereRootTriple hq, by simp, ?_, ?_, ?_⟩ <;>
    simp [sphereRootTriple]

lemma sphereRoot_pole_one_adj {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q))).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨1, by omega⟩) := by
  refine ⟨sphereRootTriple hq, by simp, ?_, ?_, ?_⟩ <;>
    simp [sphereRootTriple]

lemma spherePhase_eq_true_of_pred_zero {q : ℕ} (hq : 2 ≤ q)
    (j : Fin (2 * q)) (hzero : (finCyclePred (by omega) j).val = 0) :
    spherePhase j = true := by
  have hp : spherePhase (finCyclePred (by omega) j) = false := by
    change decide ((finCyclePred (by omega) j).val % 2 = 1) = false
    rw [hzero]
    decide
  have hs := spherePhase_cyclePred hq j
  rw [hp] at hs
  cases hj : spherePhase j with
  | false => simp [hj] at hs
  | true => rfl

lemma spherePhase_eq_true_of_succ_zero {q : ℕ} (hq : 2 ≤ q)
    (j : Fin (2 * q)) (hzero : (finCycleSucc (by omega) j).val = 0) :
    spherePhase j = true := by
  have hs0 : spherePhase (finCycleSucc (by omega) j) = false := by
    change decide ((finCycleSucc (by omega) j).val % 2 = 1) = false
    rw [hzero]
    decide
  have hs := spherePhase_cycleSucc hq j
  rw [hs0] at hs
  cases hj : spherePhase j with
  | false => simp [hj] at hs
  | true => rfl

lemma sphereIn_coveredGraph_le_out_sup_root {q : ℕ} (hq : 2 ≤ q) :
    coveredGraph (sphereDecomposition hq true) ≤
      coveredGraph (sphereDecomposition hq false) ⊔
        coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q)) := by
  intro x y hxy
  obtain ⟨T, hT, hxT, hyT, hxyne⟩ := hxy
  obtain ⟨t, htselected, rfl⟩ := (mem_sphereDecomposition_iff hq).mp hT
  have hpole : ∀ b, SphereVertex.pole b ∈ (sphereTriangle hq t).1 →
      b = spherePhase t.1.1 := by
    intro b hb
    rw [(sphere_pole_mem hq t b).mp hb]
    exact (sphereTagSelected_true_iff t).mp htselected
  rw [SimpleGraph.sup_adj]
  cases x with
  | cycle k =>
      cases y with
      | cycle l =>
          rcases (sphere_cycle_mem hq t k).mp hxT with hk | hk <;>
            rcases (sphere_cycle_mem hq t l).mp hyT with hl | hl
          · exact (hxyne (congrArg SphereVertex.cycle (hk.trans hl.symm))).elim
          · by_cases hj0 : t.1.1.val = 0
            · right
              have ht0 : t.1.1 = (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext hj0
              have hs := finCycleSucc_zero_eq_one hq
              simpa [hk, hl, ht0, hs] using sphereRoot_cycle_adj hq
            · left
              simpa [hk, hl] using sphereOut_cycle_adj hq t.1.1 hj0
          · by_cases hj0 : t.1.1.val = 0
            · right
              have ht0 : t.1.1 = (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext hj0
              have hs := finCycleSucc_zero_eq_one hq
              simpa [hk, hl, ht0, hs] using (sphereRoot_cycle_adj hq).symm
            · left
              simpa [hk, hl] using (sphereOut_cycle_adj hq t.1.1 hj0).symm
          · exact (hxyne (congrArg SphereVertex.cycle (hk.trans hl.symm))).elim
      | pole b =>
          have hb := hpole b hyT
          rcases (sphere_cycle_mem hq t k).mp hxT with hk | hk
          · by_cases hj1 : t.1.1.val = 1
            · right
              have ht1 : t.1.1 = (⟨1, by omega⟩ : Fin (2 * q)) := Fin.ext hj1
              have hphase : spherePhase t.1.1 = true := by rw [ht1]; simp [spherePhase]
              have hk1 : k = (⟨1, by omega⟩ : Fin (2 * q)) := hk.trans ht1
              have hbtrue : b = true := hb.trans hphase
              rw [hk1, hbtrue]
              exact (sphereRoot_pole_one_adj hq).symm
            · left
              let p := finCyclePred (by omega) t.1.1
              have hp0 : p.val ≠ 0 := finCyclePred_val_ne_zero_of_val_ne_one hq _ hj1
              have h := (sphereOut_pole_upper_adj hq p hp0).symm
              have hphase := spherePhase_cyclePred hq t.1.1
              have hsucc := finCycleSucc_pred (by omega) t.1.1
              change spherePhase p = !spherePhase t.1.1 at hphase
              change finCycleSucc (by omega) p = t.1.1 at hsucc
              rw [hphase, hsucc] at h
              simpa [hk, hb] using h
          · by_cases hs0 : (finCycleSucc (by omega) t.1.1).val = 0
            · right
              have hsphere : finCycleSucc (by omega) t.1.1 =
                  (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext hs0
              have hphaseSucc := spherePhase_cycleSucc hq t.1.1
              have hzeroPhase : spherePhase (finCycleSucc (by omega) t.1.1) = false := by
                rw [hsphere]
                simp [spherePhase]
              rw [hzeroPhase] at hphaseSucc
              have hphase : spherePhase t.1.1 = true := by
                cases hp : spherePhase t.1.1 <;>
                  simp [hp] at hphaseSucc ⊢
              have hk0 : k = (⟨0, by omega⟩ : Fin (2 * q)) := hk.trans hsphere
              have hbtrue : b = true := hb.trans hphase
              rw [hk0, hbtrue]
              exact (sphereRoot_pole_zero_adj hq).symm
            · left
              have h := (sphereOut_pole_lower_adj hq
                (finCycleSucc (by omega) t.1.1) hs0).symm
              rw [spherePhase_cycleSucc hq t.1.1] at h
              simpa [hk, hb] using h
  | pole b =>
      cases y with
      | pole c =>
          have hb := (sphere_pole_mem hq t b).mp hxT
          have hc := (sphere_pole_mem hq t c).mp hyT
          exact (hxyne (congrArg SphereVertex.pole (hb.trans hc.symm))).elim
      | cycle k =>
          have hb := hpole b hxT
          rcases (sphere_cycle_mem hq t k).mp hyT with hk | hk
          · by_cases hj1 : t.1.1.val = 1
            · right
              have ht1 : t.1.1 = (⟨1, by omega⟩ : Fin (2 * q)) := Fin.ext hj1
              have hphase : spherePhase t.1.1 = true := by rw [ht1]; simp [spherePhase]
              have hk1 : k = (⟨1, by omega⟩ : Fin (2 * q)) := hk.trans ht1
              have hbtrue : b = true := hb.trans hphase
              rw [hk1, hbtrue]
              exact sphereRoot_pole_one_adj hq
            · left
              let p := finCyclePred (by omega) t.1.1
              have hp0 : p.val ≠ 0 := finCyclePred_val_ne_zero_of_val_ne_one hq _ hj1
              have h := sphereOut_pole_upper_adj hq p hp0
              have hphase := spherePhase_cyclePred hq t.1.1
              have hsucc := finCycleSucc_pred (by omega) t.1.1
              change spherePhase p = !spherePhase t.1.1 at hphase
              change finCycleSucc (by omega) p = t.1.1 at hsucc
              rw [hphase, hsucc] at h
              simpa [hk, hb] using h
          · by_cases hs0 : (finCycleSucc (by omega) t.1.1).val = 0
            · right
              have hsphere : finCycleSucc (by omega) t.1.1 =
                  (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext hs0
              have hphaseSucc := spherePhase_cycleSucc hq t.1.1
              have hzeroPhase : spherePhase (finCycleSucc (by omega) t.1.1) = false := by
                rw [hsphere]
                simp [spherePhase]
              rw [hzeroPhase] at hphaseSucc
              have hphase : spherePhase t.1.1 = true := by
                cases hp : spherePhase t.1.1 <;>
                  simp [hp] at hphaseSucc ⊢
              have hk0 : k = (⟨0, by omega⟩ : Fin (2 * q)) := hk.trans hsphere
              have hbtrue : b = true := hb.trans hphase
              rw [hk0, hbtrue]
              exact sphereRoot_pole_zero_adj hq
            · left
              have h := sphereOut_pole_lower_adj hq
                (finCycleSucc (by omega) t.1.1) hs0
              rw [spherePhase_cycleSucc hq t.1.1] at h
              simpa [hk, hb] using h

lemma sphereRoot_cycle_adj_in {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.cycle ⟨0, by omega⟩)
      (SphereVertex.cycle ⟨1, by omega⟩) := by
  have h := sphereIn_cycle_adj hq (⟨0, by omega⟩ : Fin (2 * q))
  rw [finCycleSucc_zero_eq_one hq] at h
  exact h

lemma sphereRoot_pole_one_adj_in {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨1, by omega⟩) := by
  have h := sphereIn_pole_lower_adj hq (⟨1, by omega⟩ : Fin (2 * q))
  simpa [spherePhase] using h

lemma sphereRoot_pole_zero_adj_in {q : ℕ} (hq : 2 ≤ q) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨0, by omega⟩) := by
  let z : Fin (2 * q) := ⟨0, by omega⟩
  have h := sphereIn_pole_upper_adj hq (finCyclePred (by omega) z)
  have hp := spherePhase_cyclePred hq z
  have hs := finCycleSucc_pred (by omega) z
  have hz : spherePhase z = false := by simp [z, spherePhase]
  rw [hp, hs, hz] at h
  simpa [z] using h

lemma sphereRoot_coveredGraph_le_in {q : ℕ} (hq : 2 ≤ q) :
    coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q)) ≤
      coveredGraph (sphereDecomposition hq true) := by
  intro x y hxy
  obtain ⟨T, hT, hxT, hyT, hxyne⟩ := hxy
  simp only [mem_singleton] at hT
  subst T
  cases x with
  | cycle k =>
      cases y with
      | cycle l =>
          have hk : k = (⟨0, by omega⟩ : Fin (2 * q)) ∨
              k = (⟨1, by omega⟩ : Fin (2 * q)) := by
            simpa [sphereRootTriple] using hxT
          have hl : l = (⟨0, by omega⟩ : Fin (2 * q)) ∨
              l = (⟨1, by omega⟩ : Fin (2 * q)) := by
            simpa [sphereRootTriple] using hyT
          rcases hk with hk0 | hk1 <;> rcases hl with hl0 | hl1
          · exact (hxyne (congrArg SphereVertex.cycle (hk0.trans hl0.symm))).elim
          · simpa [hk0, hl1] using sphereRoot_cycle_adj_in hq
          · simpa [hk1, hl0] using (sphereRoot_cycle_adj_in hq).symm
          · exact (hxyne (congrArg SphereVertex.cycle (hk1.trans hl1.symm))).elim
      | pole b =>
          have hb : b = true := by simpa [sphereRootTriple] using hyT
          have hk : k = (⟨0, by omega⟩ : Fin (2 * q)) ∨
              k = (⟨1, by omega⟩ : Fin (2 * q)) := by
            simpa [sphereRootTriple] using hxT
          rcases hk with hk | hk
          · simpa [hk, hb] using (sphereRoot_pole_zero_adj_in hq).symm
          · simpa [hk, hb] using (sphereRoot_pole_one_adj_in hq).symm
  | pole b =>
      cases y with
      | pole c =>
          have hb : b = true := by simpa [sphereRootTriple] using hxT
          have hc : c = true := by simpa [sphereRootTriple] using hyT
          exact (hxyne (congrArg SphereVertex.pole (hb.trans hc.symm))).elim
      | cycle k =>
          have hb : b = true := by simpa [sphereRootTriple] using hxT
          have hk : k = (⟨0, by omega⟩ : Fin (2 * q)) ∨
              k = (⟨1, by omega⟩ : Fin (2 * q)) := by
            simpa [sphereRootTriple] using hyT
          rcases hk with hk | hk
          · simpa [hk, hb] using sphereRoot_pole_zero_adj_in hq
          · simpa [hk, hb] using sphereRoot_pole_one_adj_in hq

theorem sphere_switch_coveredGraph_eq {q : ℕ} (hq : 2 ≤ q) :
    coveredGraph (sphereDecomposition hq true) =
      coveredGraph (sphereDecomposition hq false) ⊔
        coveredGraph ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q)) := by
  apply le_antisymm (sphereIn_coveredGraph_le_out_sup_root hq)
  rw [sup_le_iff]
  exact ⟨sphereOut_coveredGraph_le_in hq, sphereRoot_coveredGraph_le_in hq⟩

def IsHighGirthTradeOn {V : Type*} [DecidableEq V] (q : ℕ)
    (R Aout Ain : TripleSystemOn V) : Prop :=
  IsPackingOn Aout ∧ GirthGreaterOn q Aout ∧
    IsPackingOn Ain ∧ GirthGreaterOn q Ain ∧
      coveredGraph Ain = coveredGraph Aout ⊔ coveredGraph R

theorem sphere_isHighGirthTrade {q : ℕ} (hq : 2 ≤ q) :
    IsHighGirthTradeOn q
      ({sphereRootTriple hq} : TripleSystemOn (SphereVertex q))
      (sphereDecomposition hq false) (sphereDecomposition hq true) := by
  exact ⟨sphereDecomposition_isPacking hq false,
    sphereDecomposition_girthGreater hq false,
    sphereDecomposition_isPacking hq true,
    sphereDecomposition_girthGreater hq true,
    sphere_switch_coveredGraph_eq hq⟩

lemma IsHighGirthTradeOn.out_decomposition {V : Type*} [DecidableEq V]
    {q : ℕ} {R Aout Ain : TripleSystemOn V}
    (h : IsHighGirthTradeOn q R Aout Ain) :
    IsTriangleDecomposition (coveredGraph Aout) Aout :=
  h.1.isTriangleDecomposition

lemma IsHighGirthTradeOn.in_decomposition {V : Type*} [DecidableEq V]
    {q : ℕ} {R Aout Ain : TripleSystemOn V}
    (h : IsHighGirthTradeOn q R Aout Ain) :
    IsTriangleDecomposition (coveredGraph Aout ⊔ coveredGraph R) Ain := by
  rw [← h.2.2.2.2]
  exact h.2.2.1.isTriangleDecomposition

end Erdos207
