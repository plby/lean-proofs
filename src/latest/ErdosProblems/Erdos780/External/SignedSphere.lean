import ErdosProblems.Erdos780.External.SourceFlags
import ErdosProblems.Erdos780.External.ZpTuckerDefs

/-!
A concrete finite-chain model of the free `ZMod p`-sphere carried by the
order complex of nonzero signed vectors.  The chains constructed below are
the standard chains for the periodic cyclic resolution: their boundaries
alternate between `tau = sigma - 1` and the group norm.
-/

namespace SignedSphere

open scoped BigOperators
open SourceFlags ZpTuckerScratch

noncomputable section

variable {α β : Type*}

/-- A chain is supported on `P` when every basis list with nonzero
coefficient satisfies `P`. -/
def Supported (P : List α → Prop) (c : Chain α) : Prop :=
  ∀ l, c l ≠ 0 → P l

theorem Supported.mono {P Q : List α → Prop} {c : Chain α}
    (hc : Supported P c) (hPQ : ∀ l, P l → Q l) : Supported Q c := by
  intro l hl
  exact hPQ l (hc l hl)

theorem supported_zero (P : List α → Prop) : Supported P (0 : Chain α) := by
  intro l hl
  simp at hl

theorem supported_basis {P : List α → Prop} {l : List α} (hl : P l) :
    Supported P (basis l) := by
  intro k hk
  by_cases hkl : k = l
  · simpa [hkl] using hl
  · simp [basis, Finsupp.single_apply, hkl] at hk

theorem supported_add {P : List α → Prop} {c d : Chain α}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c + d) := by
  intro l hl
  by_cases hcl : c l = 0
  · apply hd l
    intro hdl
    apply hl
    simp [hcl, hdl]
  · exact hc l hcl

theorem supported_neg {P : List α → Prop} {c : Chain α}
    (hc : Supported P c) : Supported P (-c) := by
  intro l hl
  apply hc l
  intro h
  apply hl
  simp [h]

theorem supported_sub {P : List α → Prop} {c d : Chain α}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c - d) := by
  exact supported_add hc (supported_neg hd)

theorem supported_smul {P : List α → Prop} {c : Chain α} (z : ℤ)
    (hc : Supported P c) : Supported P (z • c) := by
  intro l hl
  apply hc l
  intro h
  apply hl
  simp [h]

theorem supported_sum {ι : Type*} {P : List α → Prop} {s : Finset ι}
    {c : ι → Chain α} (hc : ∀ i ∈ s, Supported P (c i)) :
    Supported P (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supported_zero P
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact supported_add (hc a (by simp)) (ih (fun i hi => hc i (by simp [hi])))

/-- Support propagation through a linear map specified on the list basis. -/
theorem supported_linearOfBasis {P : List α → Prop} {Q : List β → Prop}
    (f : List α → Chain β)
    (hf : ∀ l, P l → Supported Q (f l)) {c : Chain α}
    (hc : Supported P c) : Supported Q (linearOfBasis f c) := by
  classical
  intro k hk
  have hkmem : k ∈ (linearOfBasis f c).support := Finsupp.mem_support_iff.mpr hk
  rw [linearOfBasis, Finsupp.lift_apply] at hkmem
  have hsub := Finsupp.support_sum (f := c)
      (g := fun l z => z • f l)
  have hkU := hsub hkmem
  simp only [Finset.mem_biUnion] at hkU
  obtain ⟨l, hlc, hkl⟩ := hkU
  have hlP : P l := hc l (Finsupp.mem_support_iff.mp hlc)
  apply hf l hlP k
  have hz : c l • f l k ≠ 0 := Finsupp.mem_support_iff.mp hkl
  intro hzero
  apply hz
  simp [hzero]

theorem supported_mapVertices {P : List α → Prop} {Q : List β → Prop}
    (f : α → β) (hf : ∀ l, P l → Q (l.map f)) {c : Chain α}
    (hc : Supported P c) : Supported Q (mapVertices f c) := by
  simpa [mapVertices, mapLists] using
    (supported_linearOfBasis (fun l => basis (l.map f))
      (fun l hl => supported_basis (hf l hl)) hc)

theorem supported_prepend {P Q : List α → Prop} (x : α)
    (hx : ∀ l, P l → Q (x :: l)) {c : Chain α} (hc : Supported P c) :
    Supported Q (prepend x c) := by
  simpa [prepend, mapLists] using
    (supported_linearOfBasis (fun l => basis (x :: l))
      (fun l hl => supported_basis (hx l hl)) hc)

/-! ## Signed vertices and a fresh-coordinate join -/

abbrev Vertex (p n : ℕ) := NonzeroSignedVector p n
abbrev SChain (p n : ℕ) := Chain (Vertex p n)

def rawUnit {p n : ℕ} (q : Fin n) (a : ZMod p) : SignedVector p n :=
  fun j => if j = q then some a else none

@[simp] theorem rawUnit_same {p n : ℕ} (q : Fin n) (a : ZMod p) :
    rawUnit q a q = some a := by simp [rawUnit]

@[simp] theorem rawUnit_ne {p n : ℕ} {q j : Fin n} (h : j ≠ q) (a : ZMod p) :
    rawUnit q a j = none := by simp [rawUnit, h]

def unit {p n : ℕ} (q : Fin n) (a : ZMod p) : Vertex p n :=
  ⟨rawUnit q a, ⟨q, by simp⟩⟩

def rawAdjoin {p n : ℕ} (q : Fin n) (a : ZMod p)
    (x : SignedVector p n) : SignedVector p n :=
  fun j => if j = q then some a else x j

@[simp] theorem rawAdjoin_same {p n : ℕ} (q : Fin n) (a : ZMod p)
    (x : SignedVector p n) : rawAdjoin q a x q = some a := by
  simp [rawAdjoin]

@[simp] theorem rawAdjoin_ne {p n : ℕ} {q j : Fin n} (h : j ≠ q)
    (a : ZMod p) (x : SignedVector p n) : rawAdjoin q a x j = x j := by
  simp [rawAdjoin, h]

def adjoin {p n : ℕ} (q : Fin n) (a : ZMod p) (x : Vertex p n) : Vertex p n :=
  ⟨rawAdjoin q a x.1, ⟨q, by simp⟩⟩

def FreshAt {p n : ℕ} (q : Fin n) (x : Vertex p n) : Prop := x.1 q = none

theorem le_adjoin_of_fresh {p n : ℕ} {q : Fin n} {a : ZMod p} {x : Vertex p n}
    (hx : FreshAt q x) : x ≤ adjoin q a x := by
  intro j g hj
  by_cases h : j = q
  · subst j
    rw [hx] at hj
    contradiction
  · simpa [adjoin, rawAdjoin, h] using hj

theorem lt_adjoin_of_fresh {p n : ℕ} {q : Fin n} {a : ZMod p} {x : Vertex p n}
    (hx : FreshAt q x) : x < adjoin q a x := by
  refine lt_of_le_of_ne (le_adjoin_of_fresh hx) ?_
  intro heq
  have hq := congrArg (fun z : Vertex p n => z.1 q) heq
  simp only [adjoin, rawAdjoin_same] at hq
  rw [hx] at hq
  contradiction

theorem unit_le_adjoin {p n : ℕ} (q : Fin n) (a : ZMod p) (x : Vertex p n) :
    unit q a ≤ adjoin q a x := by
  intro j g hj
  by_cases h : j = q
  · subst j
    simpa [unit, adjoin] using hj
  · simp [unit, rawUnit, h] at hj

theorem unit_lt_adjoin_of_fresh {p n : ℕ} {q : Fin n} {a : ZMod p}
    {x : Vertex p n} (hx : FreshAt q x) : unit q a < adjoin q a x := by
  refine lt_of_le_of_ne (unit_le_adjoin q a x) ?_
  intro heq
  obtain ⟨j, hj⟩ := x.2
  have hjq : j ≠ q := by
    intro h
    subst j
    exact hj hx
  have hval := congrArg (fun z : Vertex p n => z.1 j) heq
  simp [unit, adjoin, rawUnit, rawAdjoin, hjq] at hval
  exact hj hval.symm

theorem adjoin_mono {p n : ℕ} (q : Fin n) (a : ZMod p)
    {x y : Vertex p n} (hxy : x ≤ y) : adjoin q a x ≤ adjoin q a y := by
  intro j g hj
  by_cases h : j = q
  · subst j
    simpa [adjoin] using hj
  · simpa [adjoin, rawAdjoin, h] using hxy j g (by simpa [adjoin, rawAdjoin, h] using hj)

theorem adjoin_injective_on_fresh {p n : ℕ} (q : Fin n) (a : ZMod p)
    {x y : Vertex p n} (hx : FreshAt q x) (hy : FreshAt q y)
    (h : adjoin q a x = adjoin q a y) : x = y := by
  apply Subtype.ext
  funext j
  by_cases hj : j = q
  · subst j
    exact hx.trans hy.symm
  · have hv := congrArg (fun z : Vertex p n => z.1 j) h
    simpa [adjoin, rawAdjoin, hj] using hv

theorem adjoin_lt_adjoin {p n : ℕ} (q : Fin n) (a : ZMod p)
    {x y : Vertex p n} (hx : FreshAt q x) (hy : FreshAt q y) (hxy : x < y) :
    adjoin q a x < adjoin q a y := by
  refine lt_of_le_of_ne (adjoin_mono q a hxy.le) ?_
  exact fun h => hxy.ne (adjoin_injective_on_fresh q a hx hy h)

theorem lt_adjoin_of_lt {p n : ℕ} (q : Fin n) (a : ZMod p)
    {x y : Vertex p n} (hy : FreshAt q y) (hxy : x < y) :
    x < adjoin q a y :=
  lt_of_lt_of_le hxy (le_adjoin_of_fresh hy)

def IsStrictFlag {p n : ℕ} (l : List (Vertex p n)) : Prop :=
  l.Pairwise (· < ·)

def AllFresh {p n : ℕ} (q : Fin n) (l : List (Vertex p n)) : Prop :=
  ∀ x ∈ l, FreshAt q x

def RaisedFrom {p n : ℕ} (q : Fin n) (a : ZMod p)
    (l : List (Vertex p n)) (z : Vertex p n) : Prop :=
  z ∈ l ∨ ∃ x ∈ l, z = adjoin q a x

def MixedFlag {p n : ℕ} (q : Fin n) (a : ZMod p)
    (source out : List (Vertex p n)) : Prop :=
  IsStrictFlag out ∧ ∀ z ∈ out, RaisedFrom q a source z

theorem pairwise_adjoin {p n : ℕ} (q : Fin n) (a : ZMod p)
    {l : List (Vertex p n)} (hflag : IsStrictFlag l) (hfresh : AllFresh q l) :
    IsStrictFlag (l.map (adjoin q a)) := by
  rw [IsStrictFlag, List.pairwise_map]
  apply hflag.imp_of_mem
  intro x y hx hy hxy
  exact adjoin_lt_adjoin q a (hfresh x hx) (hfresh y hy) hxy

/-- The actual descriptor for filler terms also admits the new cone vertex. -/
def FillVertex {p n : ℕ} (q : Fin n) (a : ZMod p)
    (l : List (Vertex p n)) (z : Vertex p n) : Prop :=
  z = unit q a ∨ RaisedFrom q a l z

def FilledFlag {p n : ℕ} (q : Fin n) (a : ZMod p)
    (source out : List (Vertex p n)) : Prop :=
  IsStrictFlag out ∧ ∀ z ∈ out, FillVertex q a source z

theorem coneList_filled {p n : ℕ} (q : Fin n) (a : ZMod p)
    {l : List (Vertex p n)} (hflag : IsStrictFlag l) (hfresh : AllFresh q l) :
    FilledFlag q a l (unit q a :: l.map (adjoin q a)) := by
  constructor
  · rw [IsStrictFlag, List.pairwise_cons]
    constructor
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact unit_lt_adjoin_of_fresh (hfresh x hx)
    · exact pairwise_adjoin q a hflag hfresh
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact Or.inr (Or.inr ⟨x, hx, rfl⟩)

theorem prismBasis_filled {p n : ℕ} (q : Fin n) (a : ZMod p)
    {l : List (Vertex p n)} (hflag : IsStrictFlag l) (hfresh : AllFresh q l) :
    Supported (MixedFlag q a l) (prism id (adjoin q a) (basis l)) := by
  induction l with
  | nil =>
      simp [prismBasis, supported_zero]
  | cons x xs ih =>
      have hpair := List.pairwise_cons.mp hflag
      have hxxs : ∀ z ∈ xs, x < z := hpair.1
      have hxsflag : IsStrictFlag xs := hpair.2
      have hxfresh : FreshAt q x := hfresh x (by simp)
      have hxsfresh : AllFresh q xs := by
        intro z hz
        exact hfresh z (by simp [hz])
      rw [prism_basis, prismBasis_cons]
      apply supported_sub
      · apply supported_basis
        constructor
        · rw [IsStrictFlag, List.pairwise_cons]
          constructor
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact lt_adjoin_of_fresh hxfresh
            · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
              exact lt_adjoin_of_lt q a (hxsfresh w hw) (hxxs w hw)
          · rw [List.pairwise_cons]
            constructor
            · intro z hz
              obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
              exact adjoin_lt_adjoin q a hxfresh (hxsfresh w hw) (hxxs w hw)
            · exact pairwise_adjoin q a hxsflag hxsfresh
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact Or.inl (by simp)
          · rcases hz with rfl | hz
            · exact Or.inr ⟨x, by simp, rfl⟩
            · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
              exact Or.inr ⟨w, by simp [hw], rfl⟩
      · have hrec := ih hxsflag hxsfresh
        rw [show prismBasis id (adjoin q a) xs =
          prism id (adjoin q a) (basis xs) by simp]
        simp only [id_eq]
        apply supported_prepend
          (P := MixedFlag q a xs) (Q := MixedFlag q a (x :: xs)) x _ hrec
        intro out hout
        constructor
        · rw [IsStrictFlag, List.pairwise_cons]
          constructor
          · intro z hz
            rcases hout.2 z hz with hzorig | ⟨w, hw, rfl⟩
            · exact hxxs z hzorig
            · exact lt_adjoin_of_lt q a (hxsfresh w hw) (hxxs w hw)
          · exact hout.1
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact Or.inl (by simp)
          · rcases hout.2 z hz with hzorig | ⟨w, hw, rfl⟩
            · exact Or.inl (by simp [hzorig])
            · exact Or.inr ⟨w, by simp [hw], rfl⟩

theorem freshFill_basis_filled {p n : ℕ} (q : Fin n) (a : ZMod p)
    {l : List (Vertex p n)} (hflag : IsStrictFlag l) (hfresh : AllFresh q l) :
    Supported (FilledFlag q a l)
      (freshFill (unit q a) (adjoin q a) (basis l)) := by
  rw [show freshFill (unit q a) (adjoin q a) (basis l) =
      cone (unit q a) (adjoin q a) (basis l) -
        prism id (adjoin q a) (basis l) by rfl]
  apply supported_sub
  · simpa [cone] using supported_basis (coneList_filled q a hflag hfresh)
  · exact (prismBasis_filled q a hflag hfresh).mono
      (fun out hout => ⟨hout.1, fun z hz => Or.inr (hout.2 z hz)⟩)

theorem supported_linearMap {P : List α → Prop} {Q : List β → Prop}
    (L : Chain α →ₗ[ℤ] Chain β)
    (hL : ∀ l, P l → Supported Q (L (basis l))) {c : Chain α}
    (hc : Supported P c) : Supported Q (L c) := by
  have heq_all : ∀ d : Chain α, linearOfBasis (fun l => L (basis l)) d = L d := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single l z =>
        rw [show Finsupp.single l z = z • basis l by simp [basis]]
        simp
  rw [← heq_all c]
  exact supported_linearOfBasis (fun l => L (basis l)) hL hc

theorem freshFill_supported {p n : ℕ} (q : Fin n) (a : ZMod p)
    {P : List (Vertex p n) → Prop} {c : SChain p n}
    (hc : Supported P c)
    (hgood : ∀ l, P l → IsStrictFlag l ∧ AllFresh q l) :
    Supported (fun out => IsStrictFlag out ∧
      ∃ source, P source ∧ ∀ z ∈ out, FillVertex q a source z)
      (freshFill (unit q a) (adjoin q a) c) := by
  apply supported_linearMap (P := P)
    (Q := fun out => IsStrictFlag out ∧
      ∃ source, P source ∧ ∀ z ∈ out, FillVertex q a source z)
    (freshFill (unit q a) (adjoin q a)) _ hc
  intro l hl
  have hfill := freshFill_basis_filled q a (hgood l hl).1 (hgood l hl).2
  exact hfill.mono (fun out hout => ⟨hout.1, l, hl, hout.2⟩)

/-! ## The cyclic operators -/

@[simp] theorem vertex_shift_zero {p n : ℕ} (x : Vertex p n) : x.shift 0 = x := by
  apply Subtype.ext
  exact SignedVector.shift_zero x.1

@[simp] theorem vertex_shift_add {p n : ℕ} (a b : ZMod p) (x : Vertex p n) :
    (x.shift b).shift a = x.shift (a + b) := by
  apply Subtype.ext
  exact SignedVector.shift_add a b x.1

theorem vertex_shift_lt {p n : ℕ} (a : ZMod p) {x y : Vertex p n} (hxy : x < y) :
    x.shift a < y.shift a := by
  refine lt_of_le_of_ne (NonzeroSignedVector.shift_mono hxy.le a) ?_
  intro heq
  have hback := congrArg (fun z : Vertex p n => z.shift (-a)) heq
  simp [vertex_shift_add] at hback
  exact hxy.ne hback

def shiftChain {p n : ℕ} (a : ZMod p) : SChain p n →ₗ[ℤ] SChain p n :=
  mapVertices (NonzeroSignedVector.shift a)

@[simp] theorem shiftChain_zero {p n : ℕ} (c : SChain p n) : shiftChain 0 c = c := by
  have hshift : (NonzeroSignedVector.shift (0 : ZMod p) : Vertex p n → Vertex p n) = id := by
    funext x
    exact vertex_shift_zero x
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp [shiftChain, hshift]

theorem shiftChain_add {p n : ℕ} (a b : ZMod p) (c : SChain p n) :
    shiftChain a (shiftChain b c) = shiftChain (a + b) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp [shiftChain, List.map_map, Function.comp_def, vertex_shift_add]

def tau {p n : ℕ} : SChain p n →ₗ[ℤ] SChain p n :=
  shiftChain 1 - LinearMap.id

def norm {p n : ℕ} [NeZero p] : SChain p n →ₗ[ℤ] SChain p n :=
  ∑ a : ZMod p, shiftChain a

theorem boundary_shiftChain {p n : ℕ} (a : ZMod p) (c : SChain p n) :
    boundary (shiftChain a c) = shiftChain a (boundary c) :=
  boundary_mapVertices _ _

theorem boundary_tau {p n : ℕ} (c : SChain p n) :
    boundary (tau c) = tau (boundary c) := by
  simp [tau, boundary_shiftChain]

theorem boundary_norm {p n : ℕ} [NeZero p] (c : SChain p n) :
    boundary (norm c) = norm (boundary c) := by
  simp [norm, boundary_shiftChain]

theorem sum_shiftChain_add_left {p n : ℕ} [NeZero p]
    (b : ZMod p) (c : SChain p n) :
    (∑ a : ZMod p, shiftChain (b + a) c) = ∑ a : ZMod p, shiftChain a c := by
  exact Fintype.sum_equiv (Equiv.addLeft b)
    (fun a => shiftChain (b + a) c) (fun a => shiftChain a c) (fun _ => rfl)

theorem sum_shiftChain_add_right {p n : ℕ} [NeZero p]
    (b : ZMod p) (c : SChain p n) :
    (∑ a : ZMod p, shiftChain (a + b) c) = ∑ a : ZMod p, shiftChain a c := by
  exact Fintype.sum_equiv (Equiv.addRight b)
    (fun a => shiftChain (a + b) c) (fun a => shiftChain a c) (fun _ => rfl)

theorem tau_norm {p n : ℕ} [NeZero p] (c : SChain p n) : tau (norm c) = 0 := by
  rw [tau, norm]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply]
  rw [map_sum]
  simp_rw [shiftChain_add]
  rw [sum_shiftChain_add_left]
  simp

theorem norm_tau {p n : ℕ} [NeZero p] (c : SChain p n) : norm (tau c) = 0 := by
  rw [norm, tau]
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    shiftChain_add, Finset.sum_sub_distrib]
  rw [sum_shiftChain_add_right]
  simp

theorem shiftChain_supported {p n : ℕ} (a : ZMod p)
    {P : Vertex p n → Prop} {c : SChain p n}
    (hc : Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) c)
    (hP : ∀ x, P x → P (x.shift a)) :
    Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) (shiftChain a c) := by
  apply supported_mapVertices
    (P := fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x)
    (Q := fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x)
    (NonzeroSignedVector.shift a) _ hc
  intro l hl
  constructor
  · rw [IsStrictFlag, List.pairwise_map]
    exact hl.1.imp (vertex_shift_lt a)
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact hP x (hl.2 x hx)

theorem tau_supported {p n : ℕ} {P : Vertex p n → Prop} {c : SChain p n}
    (hc : Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) c)
    (hP : ∀ x, P x → P (x.shift (1 : ZMod p))) :
    Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) (tau c) := by
  exact supported_sub (shiftChain_supported 1 hc hP) hc

theorem norm_supported {p n : ℕ} [NeZero p] {P : Vertex p n → Prop} {c : SChain p n}
    (hc : Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) c)
    (hP : ∀ a x, P x → P (x.shift a)) :
    Supported (fun l => IsStrictFlag l ∧ ∀ x ∈ l, P x) (norm c) := by
  rw [norm]
  simp only [LinearMap.sum_apply]
  exact supported_sum (s := Finset.univ) (c := fun a => shiftChain a c)
    (fun a _ => shiftChain_supported a hc (hP a))

/-! ## Recursive sphere chains -/

/-- A signed vector is supported in the first `d` coordinates. -/
def Below {p n : ℕ} (d : ℕ) (x : Vertex p n) : Prop :=
  ∀ q : Fin n, d ≤ q.val → x.1 q = none

def GoodFlag {p n : ℕ} (d : ℕ) (l : List (Vertex p n)) : Prop :=
  IsStrictFlag l ∧ ∀ x ∈ l, Below d x

theorem below_mono {p n d e : ℕ} {x : Vertex p n} (hde : d ≤ e)
    (hx : Below d x) : Below e x := by
  intro q hq
  exact hx q (hde.trans hq)

theorem below_shift {p n d : ℕ} {x : Vertex p n} (hx : Below d x) (a : ZMod p) :
    Below d (x.shift a) := by
  intro q hq
  rw [NonzeroSignedVector.coe_shift, SignedVector.shift_apply, hx q hq]
  rfl

theorem unit_below_succ {p n d : ℕ} (q : Fin n) (hq : q.val = d) (a : ZMod p) :
    Below (d + 1) (unit q a) := by
  intro r hr
  have hrq : r ≠ q := by
    intro h
    subst r
    omega
  simp [unit, rawUnit, hrq]

theorem adjoin_below_succ {p n d : ℕ} (q : Fin n) (hq : q.val = d) (a : ZMod p)
    {x : Vertex p n} (hx : Below d x) : Below (d + 1) (adjoin q a x) := by
  intro r hr
  have hrq : r ≠ q := by
    intro h
    subst r
    omega
  rw [show (adjoin q a x : SignedVector p n) r = x.1 r by
    simp [adjoin, rawAdjoin, hrq]]
  exact hx r (by omega)

theorem fill_below_supported {p n d : ℕ} (q : Fin n) (hq : q.val = d)
    (a : ZMod p) {c : SChain p n} (hc : Supported (GoodFlag d) c) :
    Supported (GoodFlag (d + 1)) (freshFill (unit q a) (adjoin q a) c) := by
  have hf := freshFill_supported q a hc (fun l hl => by
    refine ⟨hl.1, ?_⟩
    intro x hx
    exact hl.2 x hx q (by omega))
  apply Supported.mono
    (P := fun out => IsStrictFlag out ∧
      ∃ source, GoodFlag d source ∧ ∀ z ∈ out, FillVertex q a source z)
    (Q := GoodFlag (d + 1)) hf
  intro out hout
  constructor
  · exact hout.1
  · obtain ⟨source, hsource, hverts⟩ := hout.2
    intro z hz
    rcases hverts z hz with rfl | hzraised
    · exact unit_below_succ q hq a
    · rcases hzraised with hzorig | ⟨x, hx, rfl⟩
      · exact below_mono (by omega) (hsource.2 z hzorig)
      · exact adjoin_below_succ q hq a (hsource.2 x hx)

/-- The differential used at positive degree in the periodic cyclic
resolution: `tau` in odd degree and the norm in even degree. -/
def periodicOp {p n : ℕ} [NeZero p] (i : ℕ) : SChain p n →ₗ[ℤ] SChain p n :=
  if i % 2 = 1 then tau else norm

theorem boundary_periodicOp {p n : ℕ} [NeZero p] (i : ℕ) (c : SChain p n) :
    boundary (periodicOp i c) = periodicOp i (boundary c) := by
  by_cases hi : i % 2 = 1
  · simp [periodicOp, hi, boundary_tau]
  · simp [periodicOp, hi, boundary_norm]

theorem periodicOp_supported {p n d : ℕ} [NeZero p] (i : ℕ) {c : SChain p n}
    (hc : Supported (GoodFlag d) c) : Supported (GoodFlag d) (periodicOp i c) := by
  have hshift : ∀ (a : ZMod p) (x : Vertex p n), Below d x → Below d (x.shift a) :=
    fun a x hx => below_shift hx a
  by_cases hi : i % 2 = 1
  · rw [periodicOp, if_pos hi]
    exact tau_supported hc (hshift 1)
  · rw [periodicOp, if_neg hi]
    exact norm_supported hc hshift

theorem periodicOp_next_cycle {p n : ℕ} [NeZero p] (i : ℕ)
    {x y : SChain p n} (hy : boundary y = periodicOp i x) :
    boundary (periodicOp (i + 1) y) = 0 := by
  have hi01 : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
  rcases hi01 with hi | hi
  · have hnext : (i + 1) % 2 = 1 := by omega
    rw [periodicOp, if_pos hnext, boundary_tau, hy, periodicOp, if_neg (by omega)]
    exact tau_norm x
  · have hnext : (i + 1) % 2 ≠ 1 := by omega
    rw [periodicOp, if_neg hnext, boundary_norm, hy, periodicOp, if_pos hi]
    exact norm_tau x

@[simp] theorem shiftChain_empty {p n : ℕ} (a : ZMod p) :
    shiftChain a (basis ([] : List (Vertex p n))) = basis [] := by
  simp [shiftChain]

@[simp] theorem tau_empty {p n : ℕ} :
    tau (basis ([] : List (Vertex p n))) = 0 := by
  simp [tau]

/-- The chain `y i`, defined for all naturals but equal to zero beyond the
ambient dimension.  At a valid successor degree it fills the alternating
cyclic boundary using coordinate `i+1`. -/
def y (p n : ℕ) [NeZero p] : ℕ → SChain p n
  | 0 => if h : 0 < n then basis [unit ⟨0, h⟩ 0] else 0
  | i + 1 => if h : i + 1 < n then
      freshFill (unit ⟨i + 1, h⟩ 0) (adjoin ⟨i + 1, h⟩ 0)
        (periodicOp (i + 1) (y p n i))
    else 0

theorem y_zero {p n : ℕ} [NeZero p] (hn : 0 < n) :
    y p n 0 = basis [unit ⟨0, hn⟩ 0] := by
  simp [y, hn]

theorem y_succ {p n : ℕ} [NeZero p] {i : ℕ} (hi : i + 1 < n) :
    y p n (i + 1) =
      freshFill (unit ⟨i + 1, hi⟩ 0) (adjoin ⟨i + 1, hi⟩ 0)
        (periodicOp (i + 1) (y p n i)) := by
  simp [y, hi]

/-- The degree-zero chain has augmentation one.  In the augmented complex
this is exactly the assertion that its boundary is the empty simplex. -/
theorem boundary_y_zero {p n : ℕ} [NeZero p] (hn : 0 < n) :
    boundary (y p n 0) = basis ([] : List (Vertex p n)) := by
  rw [y_zero hn]
  simp [boundaryBasis]

theorem y_zero_coefficient {p n : ℕ} [NeZero p] (hn : 0 < n) :
    y p n 0 [unit ⟨0, hn⟩ 0] = 1 := by
  rw [y_zero hn]
  simp [basis]

/-- Boundary recurrence for all valid positive degrees. -/
theorem boundary_y_succ {p n : ℕ} [NeZero p] {i : ℕ} (hi : i + 1 < n) :
    boundary (y p n (i + 1)) = periodicOp (i + 1) (y p n i) := by
  induction i with
  | zero =>
      rw [y_succ hi]
      apply boundary_freshFill_of_cycle
      rw [periodicOp, if_pos (by decide), boundary_tau, boundary_y_zero (by omega)]
      exact tau_empty
  | succ i ih =>
      rw [y_succ hi]
      apply boundary_freshFill_of_cycle
      apply periodicOp_next_cycle (i + 1)
      exact ih (by omega)

/-- Every basis list occurring in `y i` is a strict flag and is supported
in the first `i+1` coordinates. -/
theorem y_supported_good {p n : ℕ} [NeZero p] {i : ℕ} (hi : i < n) :
    Supported (GoodFlag (i + 1)) (y p n i) := by
  induction i with
  | zero =>
      rw [y_zero hi]
      apply supported_basis
      constructor
      · simp [IsStrictFlag]
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact unit_below_succ ⟨0, hi⟩ rfl 0
  | succ i ih =>
      rw [y_succ hi]
      apply fill_below_supported ⟨i + 1, hi⟩ rfl 0
      exact periodicOp_supported (i + 1) (ih (by omega))

/-- In particular, no non-flag basis list occurs in a valid sphere chain. -/
theorem y_supported_strictFlags {p n : ℕ} [NeZero p] {i : ℕ} (hi : i < n) :
    Supported IsStrictFlag (y p n i) :=
  (y_supported_good hi).mono (fun _ h => h.1)

end

end SignedSphere
