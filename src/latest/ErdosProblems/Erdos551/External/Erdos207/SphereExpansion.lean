import ErdosProblems.Erdos551.External.Erdos207.Core

namespace Erdos207

open Finset

def tripleVertex {V : Type*} [LinearOrder V]
    (T : TripleOn V) (i : Fin 3) : V :=
  (T.1.orderIsoOfFin T.2 i).1

lemma tripleVertex_mem {V : Type*} [LinearOrder V]
    (T : TripleOn V) (i : Fin 3) : tripleVertex T i ∈ T.1 :=
  (T.1.orderIsoOfFin T.2 i).2

lemma tripleVertex_injective {V : Type*} [LinearOrder V]
    (T : TripleOn V) : Function.Injective (tripleVertex T) := by
  intro i j hij
  apply (T.1.orderIsoOfFin T.2).injective
  apply Subtype.ext
  exact hij

def sphereIsInterior {q : ℕ} : SphereVertex q → Prop
  | .pole b => b = false
  | .cycle j => 2 ≤ j.val

abbrev SphereInterior (q : ℕ) := {x : SphereVertex q // sphereIsInterior x}

inductive SphereExpansionVertex (V : Type*) (q : ℕ) where
  | root : V → SphereExpansionVertex V q
  | interior : {s : Finset V // s.card = 3} → SphereInterior q →
      SphereExpansionVertex V q
  deriving DecidableEq

def sphereExpansionVertexEquiv {V : Type*} {q : ℕ} :
    SphereExpansionVertex V q ≃
      V ⊕ ({s : Finset V // s.card = 3} × SphereInterior q) where
  toFun
    | .root v => Sum.inl v
    | .interior T x => Sum.inr (T, x)
  invFun
    | .inl v => .root v
    | .inr Tx => .interior Tx.1 Tx.2
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} :
    Fintype (SphereExpansionVertex V q) :=
  letI : Fintype {s : Finset V // s.card = 3} := Fintype.ofFinite _
  letI : Fintype (SphereInterior q) := Fintype.ofFinite _
  Fintype.ofEquiv
      (V ⊕ ({s : Finset V // s.card = 3} × SphereInterior q))
      sphereExpansionVertexEquiv.symm

def attachSphereVertex {V : Type*} [LinearOrder V] {q : ℕ}
    (T : TripleOn V) : SphereVertex q → SphereExpansionVertex V q
  | .pole false => .interior T ⟨.pole false, rfl⟩
  | .pole true => .root (tripleVertex T 0)
  | .cycle j =>
      if h0 : j.val = 0 then .root (tripleVertex T 1)
      else if h1 : j.val = 1 then .root (tripleVertex T 2)
      else .interior T ⟨.cycle j, by simp [sphereIsInterior]; omega⟩

def sphereRootVertex {q : ℕ} (hq : 2 ≤ q) : Fin 3 → SphereVertex q
  | ⟨0, _⟩ => .pole true
  | ⟨1, _⟩ => .cycle ⟨0, by omega⟩
  | ⟨2, _⟩ => .cycle ⟨1, by omega⟩

lemma fin_three_cases (i : Fin 3) :
    i = 0 ∨ i = 1 ∨ i = 2 := by
  have := i.isLt
  omega

lemma sphereRootVertex_injective {q : ℕ} (hq : 2 ≤ q) :
    Function.Injective (sphereRootVertex hq) := by
  intro i j hij
  rcases fin_three_cases i with hi | hi | hi <;>
    rcases fin_three_cases j with hj | hj | hj <;>
    subst i <;> subst j <;> simp [sphereRootVertex] at hij ⊢

@[simp]
lemma attachSphereVertex_root {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) (i : Fin 3) :
    attachSphereVertex T (sphereRootVertex hq i) =
      SphereExpansionVertex.root (tripleVertex T i) := by
  rcases fin_three_cases i with hi | hi | hi <;>
    subst i <;> simp [sphereRootVertex, attachSphereVertex]

lemma exists_rootIndex_of_attach_eq_root
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) {y : SphereVertex q} {a : V}
    (h : attachSphereVertex T y = SphereExpansionVertex.root a) :
    ∃ i : Fin 3, y = sphereRootVertex hq i ∧ tripleVertex T i = a := by
  cases y with
  | pole b =>
      cases b
      · simp [attachSphereVertex] at h
      · refine ⟨0, ?_, ?_⟩
        · rfl
        · exact SphereExpansionVertex.root.inj h
  | cycle j =>
      by_cases h0 : j.val = 0
      · have hj : j = (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext (by simpa using h0)
        refine ⟨1, ?_, ?_⟩
        · rw [hj]
          rfl
        · have h' : (SphereExpansionVertex.root (tripleVertex T 1) :
              SphereExpansionVertex V q) = SphereExpansionVertex.root a := by
            simpa [attachSphereVertex, h0] using h
          exact SphereExpansionVertex.root.inj h'
      · by_cases h1 : j.val = 1
        · have hj : j = (⟨1, by omega⟩ : Fin (2 * q)) := Fin.ext (by simpa using h1)
          refine ⟨2, ?_, ?_⟩
          · rw [hj]
            rfl
          · have h' : (SphereExpansionVertex.root (tripleVertex T 2) :
                SphereExpansionVertex V q) = SphereExpansionVertex.root a := by
              simpa [attachSphereVertex, h0, h1] using h
            exact SphereExpansionVertex.root.inj h'
        · simp [attachSphereVertex, h0, h1] at h

lemma sphereOut_not_cycle_zero_one_adj {q : ℕ} (hq : 2 ≤ q) :
    ¬(coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.cycle ⟨0, by omega⟩)
      (SphereVertex.cycle ⟨1, by omega⟩) := by
  classical
  rintro ⟨T, hT, hzT, hoT, _⟩
  obtain ⟨t, httags, rfl⟩ := Finset.mem_image.mp hT
  have htselected : sphereTagSelected false t := (mem_filter.mp httags).2
  have ht0 := (sphere_cycle_mem hq t (⟨0, by omega⟩ : Fin (2 * q))).mp hzT
  have ht1 := (sphere_cycle_mem hq t (⟨1, by omega⟩ : Fin (2 * q))).mp hoT
  have h01 : (⟨0, by omega⟩ : Fin (2 * q)) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hsub : ({(⟨0, by omega⟩ : Fin (2 * q)), ⟨1, by omega⟩} :
      Finset (Fin (2 * q))) ⊆
      {t.1.1, finCycleSucc (by omega) t.1.1} := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk ⊢
    rcases hk with rfl | rfl
    · exact ht0
    · exact ht1
  have hedge : ({t.1.1, finCycleSucc (by omega) t.1.1} :
      Finset (Fin (2 * q))) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    symm
    apply eq_of_subset_of_card_le hsub
    rw [card_pair h01,
      card_pair (finCycleSucc_ne (by omega) t.1.1).symm]
  have hs0 : finCycleSucc (by omega) (⟨0, by omega⟩ : Fin (2 * q)) =
      (⟨1, by omega⟩ : Fin (2 * q)) := by
    apply Fin.ext
    have hmod : 1 % (2 * q) = 1 := Nat.mod_eq_of_lt (by omega)
    simp [finCycleSucc_val, hmod]
  have hj : t.1.1 = (⟨0, by omega⟩ : Fin (2 * q)) :=
    cycleEdge_index_unique (by omega) _ _ (by simpa [hs0] using hedge)
  exact sphereTagSelected_false_index_ne_zero htselected (by simp [hj])

lemma sphereOut_not_pole_zero_adj {q : ℕ} (hq : 2 ≤ q) :
    ¬(coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨0, by omega⟩) := by
  classical
  rintro ⟨T, hT, hpT, hzT, _⟩
  obtain ⟨t, httags, rfl⟩ := Finset.mem_image.mp hT
  have htselected : sphereTagSelected false t := (mem_filter.mp httags).2
  have hpole := (sphere_pole_mem hq t true).mp hpT
  have hcycle :=
    (sphere_cycle_mem hq t (⟨0, by omega⟩ : Fin (2 * q))).mp hzT
  rcases hcycle with hzero | hsucc
  · apply sphereTagSelected_false_index_ne_zero htselected
    rw [← hzero]
  · have hsval : (finCycleSucc (by omega) t.1.1).val = 0 := by
      rw [← hsucc]
    have hphase := spherePhase_eq_true_of_succ_zero hq t.1.1 hsval
    have hsel := (sphereTagSelected_false_iff t).mp htselected
    rw [← hpole, hphase] at hsel
    simp at hsel

lemma sphereOut_not_pole_one_adj {q : ℕ} (hq : 2 ≤ q) :
    ¬(coveredGraph (sphereDecomposition hq false)).Adj
      (SphereVertex.pole true) (SphereVertex.cycle ⟨1, by omega⟩) := by
  classical
  rintro ⟨T, hT, hpT, hoT, _⟩
  obtain ⟨t, httags, rfl⟩ := Finset.mem_image.mp hT
  have htselected : sphereTagSelected false t := (mem_filter.mp httags).2
  have hpole := (sphere_pole_mem hq t true).mp hpT
  have hcycle :=
    (sphere_cycle_mem hq t (⟨1, by omega⟩ : Fin (2 * q))).mp hoT
  rcases hcycle with hone | hsucc
  · have hphase : spherePhase t.1.1 = true := by
      unfold spherePhase
      have hval : t.1.1.val = 1 := by
        have := congrArg Fin.val hone
        simpa using this.symm
      simp [hval]
    have hsel := (sphereTagSelected_false_iff t).mp htselected
    rw [← hpole, hphase] at hsel
    simp at hsel
  · have hs0 : finCycleSucc (by omega) (⟨0, by omega⟩ : Fin (2 * q)) =
        (⟨1, by omega⟩ : Fin (2 * q)) := by
      apply Fin.ext
      have hmod : 1 % (2 * q) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [finCycleSucc_val, hmod]
    have hj : t.1.1 = (⟨0, by omega⟩ : Fin (2 * q)) := by
      apply finCycleSucc_injective (by omega)
      exact hsucc.symm.trans hs0.symm
    exact sphereTagSelected_false_index_ne_zero htselected (by simp [hj])

lemma sphereOut_no_root_adj {q : ℕ} (hq : 2 ≤ q) (i j : Fin 3) :
    ¬(coveredGraph (sphereDecomposition hq false)).Adj
      (sphereRootVertex hq i) (sphereRootVertex hq j) := by
  rcases fin_three_cases i with hi | hi | hi <;>
    rcases fin_three_cases j with hj | hj | hj <;>
    subst i <;> subst j
  · exact (coveredGraph _).loopless.irrefl _
  · exact sphereOut_not_pole_zero_adj hq
  · exact sphereOut_not_pole_one_adj hq
  · exact fun h ↦ sphereOut_not_pole_zero_adj hq h.symm
  · exact (coveredGraph _).loopless.irrefl _
  · exact sphereOut_not_cycle_zero_one_adj hq
  · exact fun h ↦ sphereOut_not_pole_one_adj hq h.symm
  · exact fun h ↦ sphereOut_not_cycle_zero_one_adj hq h.symm
  · exact (coveredGraph _).loopless.irrefl _

lemma sphereIn_root_adj {q : ℕ} (hq : 2 ≤ q) {i j : Fin 3} (hij : i ≠ j) :
    (coveredGraph (sphereDecomposition hq true)).Adj
      (sphereRootVertex hq i) (sphereRootVertex hq j) := by
  rcases fin_three_cases i with hi | hi | hi <;>
    rcases fin_three_cases j with hj | hj | hj <;>
    subst i <;> subst j
  · exact (hij rfl).elim
  · exact sphereRoot_pole_zero_adj_in hq
  · exact sphereRoot_pole_one_adj_in hq
  · exact (sphereRoot_pole_zero_adj_in hq).symm
  · exact (hij rfl).elim
  · exact sphereRoot_cycle_adj_in hq
  · exact (sphereRoot_pole_one_adj_in hq).symm
  · exact (sphereRoot_cycle_adj_in hq).symm
  · exact (hij rfl).elim

lemma sphereSelected_root_adj_iff {q : ℕ} (hq : 2 ≤ q)
    (inward : Bool) (i j : Fin 3) :
    (coveredGraph (sphereDecomposition hq inward)).Adj
        (sphereRootVertex hq i) (sphereRootVertex hq j) ↔
      inward = true ∧ i ≠ j := by
  cases inward with
  | false =>
      simp only [Bool.false_eq_true, false_and, iff_false]
      exact sphereOut_no_root_adj hq i j
  | true =>
      simp only [true_and]
      exact ⟨fun h hij ↦
        (coveredGraph _).ne_of_adj h (congrArg (sphereRootVertex hq) hij),
        sphereIn_root_adj hq⟩

/-
lemma attachedSphere_root_adj_iff
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) (inward : Bool) (a b : V) :
    (coveredGraph (attachSphereFamily hq T (sphereDecomposition hq inward))).Adj
        (SphereExpansionVertex.root a) (SphereExpansionVertex.root b) ↔
      inward = true ∧ a ∈ T.1 ∧ b ∈ T.1 ∧ a ≠ b := by
  constructor
  · rintro ⟨A, hAfam, haA, hbA, habroot⟩
    obtain ⟨S, hSselected, rfl⟩ := Finset.mem_map.mp hAfam
    obtain ⟨x, hxS, hxa⟩ := Finset.mem_map.mp haA
    obtain ⟨y, hyS, hyb⟩ := Finset.mem_map.mp hbA
    obtain ⟨i, hxi, hia⟩ :=
      exists_rootIndex_of_attach_eq_root hq T hxa
    obtain ⟨j, hyj, hjb⟩ :=
      exists_rootIndex_of_attach_eq_root hq T hyb
    have hij : i ≠ j := by
      intro hij
      apply habroot
      apply congrArg (fun z ↦
        (SphereExpansionVertex.root z : SphereExpansionVertex V q))
      rw [← hia, ← hjb, hij]
    have horiginal :
        (coveredGraph (sphereDecomposition hq inward)).Adj
          (sphereRootVertex hq i) (sphereRootVertex hq j) := by
      refine ⟨S, hSselected, ?_, ?_, ?_⟩
      · rwa [← hxi]
      · rwa [← hyj]
      · exact (sphereRootVertex_injective hq).ne hij
    have hinward := (sphereSelected_root_adj_iff hq inward i j).mp horiginal |>.1
    refine ⟨hinward, ?_, ?_, ?_⟩
    · rw [← hia]
      exact tripleVertex_mem T i
    · rw [← hjb]
      exact tripleVertex_mem T j
    · intro hab
      apply habroot
      exact congrArg SphereExpansionVertex.root hab
  · rintro ⟨hinward, haT, hbT, hab⟩
    let ai : T.1 := ⟨a, haT⟩
    let bi : T.1 := ⟨b, hbT⟩
    let i : Fin 3 := (T.1.orderIsoOfFin T.2).symm ai
    let j : Fin 3 := (T.1.orderIsoOfFin T.2).symm bi
    have hia : tripleVertex T i = a := by
      simp [tripleVertex, i, ai]
    have hjb : tripleVertex T j = b := by
      simp [tripleVertex, j, bi]
    have hij : i ≠ j := by
      intro hij
      apply hab
      rw [← hia, ← hjb, hij]
    have horiginal :=
      (sphereSelected_root_adj_iff hq inward i j).mpr ⟨hinward, hij⟩
    obtain ⟨S, hSselected, hiS, hjS, hrootne⟩ := horiginal
    refine ⟨attachSphereTriple hq T S, ?_, ?_, ?_, ?_⟩
    · exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
        (sphereDecomposition hq inward) S).mpr hSselected
    · apply Finset.mem_map.mpr
      refine ⟨sphereRootVertex hq i, hiS, ?_⟩
      change attachSphereVertex T (sphereRootVertex hq i) =
        SphereExpansionVertex.root a
      rw [attachSphereVertex_root, hia]
    · apply Finset.mem_map.mpr
      refine ⟨sphereRootVertex hq j, hjS, ?_⟩
      change attachSphereVertex T (sphereRootVertex hq j) =
        SphereExpansionVertex.root b
      rw [attachSphereVertex_root, hjb]
    · exact fun h ↦ hab (SphereExpansionVertex.root.inj h)
-/

def detachSphereVertex {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) : SphereExpansionVertex V q → SphereVertex q
  | .root v =>
      if v = tripleVertex T 0 then .pole true
      else if v = tripleVertex T 1 then .cycle ⟨0, by omega⟩
      else .cycle ⟨1, by omega⟩
  | .interior _ x => x.1

lemma detach_attachSphereVertex {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) (x : SphereVertex q) :
    detachSphereVertex hq T (attachSphereVertex T x) = x := by
  have h01 : tripleVertex T (0 : Fin 3) ≠ tripleVertex T (1 : Fin 3) :=
    (tripleVertex_injective T).ne (by decide)
  have h20 : tripleVertex T (2 : Fin 3) ≠ tripleVertex T (0 : Fin 3) :=
    (tripleVertex_injective T).ne (by decide)
  have h21 : tripleVertex T (2 : Fin 3) ≠ tripleVertex T (1 : Fin 3) :=
    (tripleVertex_injective T).ne (by decide)
  cases x with
  | pole b =>
      cases b <;> simp [attachSphereVertex, detachSphereVertex]
  | cycle j =>
      by_cases h0 : j.val = 0
      · have hj : j = (⟨0, by omega⟩ : Fin (2 * q)) := Fin.ext (by simpa using h0)
        rw [hj]
        simp [attachSphereVertex, detachSphereVertex, h01.symm]
      · by_cases h1 : j.val = 1
        · have hj : j = (⟨1, by omega⟩ : Fin (2 * q)) := Fin.ext (by simpa using h1)
          rw [hj]
          simp [attachSphereVertex, detachSphereVertex, h20, h21]
        · simp [attachSphereVertex, detachSphereVertex, h0, h1]

lemma attachSphereVertex_injective {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) :
    Function.Injective (attachSphereVertex (q := q) T) :=
  Function.LeftInverse.injective (detach_attachSphereVertex hq T)

@[simp]
lemma attachSphereVertex_interior {V : Type*} [LinearOrder V] {q : ℕ}
    (T : TripleOn V) (x : SphereInterior q) :
    attachSphereVertex T x.1 = SphereExpansionVertex.interior T x := by
  obtain ⟨x, hx⟩ := x
  cases x with
  | pole b =>
      simp only [sphereIsInterior] at hx
      subst b
      rfl
  | cycle j =>
      simp only [sphereIsInterior] at hx
      have h0 : j.val ≠ 0 := by omega
      have h1 : j.val ≠ 1 := by omega
      simp [attachSphereVertex, h0, h1]

lemma exists_interior_mem_sphereTriangle {q : ℕ} (hq : 2 ≤ q)
    (t : ConcreteSphereTag q) :
    ∃ x : SphereInterior q, x.1 ∈ (sphereTriangle hq t).1 := by
  cases hb : t.1.2 with
  | false =>
      refine ⟨⟨SphereVertex.pole false, rfl⟩, ?_⟩
      exact (sphere_pole_mem hq t false).mpr hb.symm
  | true =>
      have hj0 : t.1.1.val ≠ 0 := by
        intro hj
        have h := t.2 hj
        rw [hb] at h
        simp at h
      by_cases hj1 : t.1.1.val = 1
      · let s := finCycleSucc (by omega) t.1.1
        have hsval : s.val = 2 := by
          dsimp [s]
          rw [finCycleSucc_val]
          rw [hj1]
          exact Nat.mod_eq_of_lt (by omega)
        refine ⟨⟨SphereVertex.cycle s, by simp [sphereIsInterior, hsval]⟩, ?_⟩
        exact (sphere_cycle_mem hq t s).mpr (Or.inr rfl)
      · have hj2 : 2 ≤ t.1.1.val := by omega
        refine ⟨⟨SphereVertex.cycle t.1.1, by simpa [sphereIsInterior]⟩, ?_⟩
        exact (sphere_cycle_mem hq t t.1.1).mpr (Or.inl rfl)

/-- Strengthened sphere expansion: the private leaf can always be chosen
away from the three root vertices. -/
theorem sphere_short_interior_leaf {q : ℕ} (hq : 2 ≤ q)
    {C : TripleSystemOn (SphereVertex q)}
    (hCB : C ⊆ sphereBank hq) (hpacking : IsPackingOn C)
    (hCne : C.Nonempty) (hCq : C.card ≤ q) :
    ∃ x : SphereInterior q, x.1 ∈ verticesOn C ∧
      (triplesThrough C x.1).card = 1 := by
  let S := sphereIndexing hq
  let indices : Finset (Fin (2 * q)) := C.image S.edgeIndex
  have hindicesCard : indices.card ≤ q := card_image_le.trans hCq
  rcases exists_private_cycle_leaf_or_exceptional hq indices hindicesCard with
      hzero | ⟨k, hk2, hkchange⟩
  · obtain ⟨T, hTC⟩ := hCne
    have hTzero : (S.edgeIndex T).val = 0 :=
      hzero (S.edgeIndex T) (mem_image.mpr ⟨T, hTC, rfl⟩)
    have hhubT : S.hub ∈ T.1 := S.exceptionalHub T (hCB hTC) hTzero
    have hallT : ∀ U ∈ C, U = T := by
      intro U hUC
      have hUzero : (S.edgeIndex U).val = 0 :=
        hzero (S.edgeIndex U) (mem_image.mpr ⟨U, hUC, rfl⟩)
      have hindex : S.edgeIndex U = S.edgeIndex T := by
        apply Fin.ext
        omega
      exact S.index_injective_on_packing hCB hpacking hUC hTC hindex
    refine ⟨⟨SphereVertex.pole false, rfl⟩, ?_, ?_⟩
    · simp only [verticesOn, mem_biUnion]
      exact ⟨T, hTC, hhubT⟩
    · have hthrough : triplesThrough C (SphereVertex.pole false) = {T} := by
        ext U
        simp only [triplesThrough, mem_filter, mem_singleton]
        constructor
        · rintro ⟨hUC, _⟩
          exact hallT U hUC
        · intro hUT
          subst U
          exact ⟨hTC, hhubT⟩
      rw [hthrough]
      simp
  · obtain ⟨hkpos, hkchange⟩ := hkchange
    let p := finPred k hkpos
    have hxor : (p ∈ indices ∧ k ∉ indices) ∨
        (p ∉ indices ∧ k ∈ indices) := by
      dsimp [p]
      tauto
    rcases hxor with hleft | hright
    · obtain ⟨T, hTC, hTp⟩ := mem_image.mp hleft.1
      have hkT : S.cycleVertex k ∈ T.1 :=
        (S.privateIncidence k hk2 T (hCB hTC)).mpr (Or.inl hTp)
      have hunique : ∀ U ∈ C, S.cycleVertex k ∈ U.1 → U = T := by
        intro U hUC hkU
        rcases (S.privateIncidence k hk2 U (hCB hUC)).mp hkU with hUp | hUk
        · exact S.index_injective_on_packing hCB hpacking hUC hTC
            (hUp.trans hTp.symm)
        · exact (hleft.2 (mem_image.mpr ⟨U, hUC, hUk⟩)).elim
      refine ⟨⟨SphereVertex.cycle k, hk2⟩, ?_, ?_⟩
      · simp only [verticesOn, mem_biUnion]
        exact ⟨T, hTC, hkT⟩
      · have hthrough : triplesThrough C (SphereVertex.cycle k) = {T} := by
          ext U
          simp only [triplesThrough, mem_filter, mem_singleton]
          constructor
          · rintro ⟨hUC, hkU⟩
            exact hunique U hUC hkU
          · intro hUT
            subst U
            exact ⟨hTC, hkT⟩
        rw [hthrough]
        simp
    · obtain ⟨T, hTC, hTk⟩ := mem_image.mp hright.2
      have hkT : S.cycleVertex k ∈ T.1 :=
        (S.privateIncidence k hk2 T (hCB hTC)).mpr (Or.inr hTk)
      have hunique : ∀ U ∈ C, S.cycleVertex k ∈ U.1 → U = T := by
        intro U hUC hkU
        rcases (S.privateIncidence k hk2 U (hCB hUC)).mp hkU with hUp | hUk
        · exact (hright.1 (mem_image.mpr ⟨U, hUC, hUp⟩)).elim
        · exact S.index_injective_on_packing hCB hpacking hUC hTC
            (hUk.trans hTk.symm)
      refine ⟨⟨SphereVertex.cycle k, hk2⟩, ?_, ?_⟩
      · simp only [verticesOn, mem_biUnion]
        exact ⟨T, hTC, hkT⟩
      · have hthrough : triplesThrough C (SphereVertex.cycle k) = {T} := by
          ext U
          simp only [triplesThrough, mem_filter, mem_singleton]
          constructor
          · rintro ⟨hUC, hkU⟩
            exact hunique U hUC hkU
          · intro hUT
            subst U
            exact ⟨hTC, hkT⟩
        rw [hthrough]
        simp

def mapTriple {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (T : TripleOn V) : TripleOn W :=
  ⟨T.1.map f, by simpa using T.2⟩

lemma mapTriple_injective {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) : Function.Injective (mapTriple f) := by
  intro T U h
  apply Subtype.ext
  exact (Finset.map_injective f) (congrArg Subtype.val h)

def mapTripleEmbedding {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) : TripleOn V ↪ TripleOn W :=
  ⟨mapTriple f, mapTriple_injective f⟩

def mapTripleSystem {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (C : TripleSystemOn V) : TripleSystemOn W :=
  C.map (mapTripleEmbedding f)

@[simp]
lemma mem_mapTriple_apply_iff {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (T : TripleOn V) (v : V) :
    f v ∈ (mapTriple f T).1 ↔ v ∈ T.1 := by
  simp [mapTriple]

@[simp]
lemma mem_mapTripleSystem_iff {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (C : TripleSystemOn V) (T : TripleOn V) :
    mapTriple f T ∈ mapTripleSystem f C ↔ T ∈ C := by
  simp [mapTripleSystem, mapTripleEmbedding]

@[simp]
lemma card_mapTripleSystem {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (C : TripleSystemOn V) :
    (mapTripleSystem f C).card = C.card := by
  simp [mapTripleSystem]

lemma IsPackingOn.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {C : TripleSystemOn V} (hC : IsPackingOn C) (f : V ↪ W) :
    IsPackingOn (mapTripleSystem f C) := by
  intro x y hxy T hT hxT hyT U hU hxU hyU
  obtain ⟨T₀, hT₀, rfl⟩ := Finset.mem_map.mp hT
  obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
  obtain ⟨a, haT, hax⟩ := Finset.mem_map.mp hxT
  obtain ⟨b, hbT, hby⟩ := Finset.mem_map.mp hyT
  obtain ⟨c, hcU, hcx⟩ := Finset.mem_map.mp hxU
  obtain ⟨d, hdU, hdy⟩ := Finset.mem_map.mp hyU
  have hac : a = c := f.injective (hax.trans hcx.symm)
  have hbd : b = d := f.injective (hby.trans hdy.symm)
  subst c
  subst d
  have hab : a ≠ b := by
    intro hab
    apply hxy
    rw [← hax, ← hby, hab]
  congr 1
  exact hC a b hab T₀ hT₀ haT hbT U₀ hU₀ hcU hdU

lemma IsPackingOn.of_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {C : TripleSystemOn V} {f : V ↪ W}
    (hC : IsPackingOn (mapTripleSystem f C)) : IsPackingOn C := by
  intro x y hxy T hT hxT hyT U hU hxU hyU
  have hfxy : f x ≠ f y := f.injective.ne hxy
  have hmap := hC (f x) (f y) hfxy
      (mapTriple f T) ((mem_mapTripleSystem_iff f C T).mpr hT)
      ((mem_mapTriple_apply_iff f T x).mpr hxT)
      ((mem_mapTriple_apply_iff f T y).mpr hyT)
      (mapTriple f U) ((mem_mapTripleSystem_iff f C U).mpr hU)
      ((mem_mapTriple_apply_iff f U x).mpr hxU)
      ((mem_mapTriple_apply_iff f U y).mpr hyU)
  exact mapTriple_injective f hmap

lemma triplesThrough_map_apply {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (C : TripleSystemOn V) (v : V) :
    triplesThrough (mapTripleSystem f C) (f v) =
      mapTripleSystem f (triplesThrough C v) := by
  ext U
  constructor
  · intro hU
    change U ∈ (mapTripleSystem f C).filter (fun T ↦ f v ∈ T.1) at hU
    rw [mem_filter] at hU
    obtain ⟨T, hTC, rfl⟩ := Finset.mem_map.mp hU.1
    apply Finset.mem_map.mpr
    exact ⟨T, mem_filter.mpr ⟨hTC,
      (mem_mapTriple_apply_iff f T v).mp hU.2⟩, rfl⟩
  · intro hU
    obtain ⟨T, hTC, rfl⟩ := Finset.mem_map.mp hU
    change T ∈ C.filter (fun T ↦ v ∈ T.1) at hTC
    change mapTriple f T ∈
      (mapTripleSystem f C).filter (fun U ↦ f v ∈ U.1)
    rw [mem_filter] at hTC ⊢
    exact ⟨(mem_mapTripleSystem_iff f C T).mpr hTC.1,
      (mem_mapTriple_apply_iff f T v).mpr hTC.2⟩

def attachSphereEmbedding {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) :
    SphereVertex q ↪ SphereExpansionVertex V q :=
  ⟨attachSphereVertex T, attachSphereVertex_injective hq T⟩

def attachSphereTriple {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) (S : TripleOn (SphereVertex q)) :
    TripleOn (SphereExpansionVertex V q) :=
  mapTriple (attachSphereEmbedding hq T) S

def attachSphereFamily {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) (C : TripleSystemOn (SphereVertex q)) :
    TripleSystemOn (SphereExpansionVertex V q) :=
  mapTripleSystem (attachSphereEmbedding hq T) C

def sphereExpansionFiber {V : Type*} [DecidableEq V] {q : ℕ} :
    SphereExpansionVertex V q → Option (TripleOn V)
  | .root _ => none
  | .interior T _ => some T

def sphereExpansionFiberOr {V : Type*} [DecidableEq V] {q : ℕ}
    (T₀ : TripleOn V) : SphereExpansionVertex V q → TripleOn V
  | .root _ => T₀
  | .interior T _ => T

@[simp]
lemma sphereExpansionFiberOr_attach {V : Type*} [LinearOrder V] {q : ℕ}
    (T : TripleOn V) (y : SphereVertex q) :
    sphereExpansionFiberOr T (attachSphereVertex T y) = T := by
  cases y with
  | pole b => cases b <;> rfl
  | cycle j =>
      by_cases h0 : j.val = 0
      · simp [attachSphereVertex, sphereExpansionFiberOr, h0]
      · by_cases h1 : j.val = 1
        · simp [attachSphereVertex, sphereExpansionFiberOr, h1]
        · simp [attachSphereVertex, sphereExpansionFiberOr, h0, h1]

@[simp]
lemma interior_mem_attachSphereTriple_iff {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T U : TripleOn V) (x : SphereInterior q)
    (S : TripleOn (SphereVertex q)) :
    SphereExpansionVertex.interior U x ∈ (attachSphereTriple hq T S).1 ↔
      U = T ∧ x.1 ∈ S.1 := by
  constructor
  · intro h
    obtain ⟨y, hyS, hy⟩ := Finset.mem_map.mp h
    have hUT : U = T := by
      have hf := congrArg (sphereExpansionFiberOr T) hy
      change sphereExpansionFiberOr T (attachSphereVertex T y) =
        sphereExpansionFiberOr T (SphereExpansionVertex.interior U x) at hf
      rw [sphereExpansionFiberOr_attach] at hf
      exact hf.symm
    subst U
    refine ⟨rfl, ?_⟩
    have hdet := congrArg (detachSphereVertex hq T) hy
    have hyx : y = x.1 := by
      change detachSphereVertex hq T (attachSphereVertex T y) =
        detachSphereVertex hq T (SphereExpansionVertex.interior T x) at hdet
      rw [detach_attachSphereVertex] at hdet
      exact hdet
    exact hyx ▸ hyS
  · rintro ⟨hUT, hxS⟩
    subst U
    apply Finset.mem_map.mpr
    exact ⟨x.1, hxS, attachSphereVertex_interior T x⟩

lemma attachedSphere_root_adj_iff
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) (inward : Bool) (a b : V) :
    (coveredGraph (attachSphereFamily hq T (sphereDecomposition hq inward))).Adj
        (SphereExpansionVertex.root a) (SphereExpansionVertex.root b) ↔
      inward = true ∧ a ∈ T.1 ∧ b ∈ T.1 ∧ a ≠ b := by
  constructor
  · rintro ⟨A, hAfam, haA, hbA, habroot⟩
    obtain ⟨S, hSselected, rfl⟩ := Finset.mem_map.mp hAfam
    obtain ⟨x, hxS, hxa⟩ := Finset.mem_map.mp haA
    obtain ⟨y, hyS, hyb⟩ := Finset.mem_map.mp hbA
    obtain ⟨i, hxi, hia⟩ :=
      exists_rootIndex_of_attach_eq_root hq T hxa
    obtain ⟨j, hyj, hjb⟩ :=
      exists_rootIndex_of_attach_eq_root hq T hyb
    have hij : i ≠ j := by
      intro hij
      apply habroot
      apply congrArg (fun z ↦
        (SphereExpansionVertex.root z : SphereExpansionVertex V q))
      rw [← hia, ← hjb, hij]
    have horiginal :
        (coveredGraph (sphereDecomposition hq inward)).Adj
          (sphereRootVertex hq i) (sphereRootVertex hq j) := by
      refine ⟨S, hSselected, ?_, ?_, ?_⟩
      · rwa [← hxi]
      · rwa [← hyj]
      · exact (sphereRootVertex_injective hq).ne hij
    have hinward := (sphereSelected_root_adj_iff hq inward i j).mp horiginal |>.1
    refine ⟨hinward, ?_, ?_, ?_⟩
    · rw [← hia]
      exact tripleVertex_mem T i
    · rw [← hjb]
      exact tripleVertex_mem T j
    · intro hab
      apply habroot
      exact congrArg SphereExpansionVertex.root hab
  · rintro ⟨hinward, haT, hbT, hab⟩
    let ai : T.1 := ⟨a, haT⟩
    let bi : T.1 := ⟨b, hbT⟩
    let i : Fin 3 := (T.1.orderIsoOfFin T.2).symm ai
    let j : Fin 3 := (T.1.orderIsoOfFin T.2).symm bi
    have hia : tripleVertex T i = a := by
      simp [tripleVertex, i, ai]
    have hjb : tripleVertex T j = b := by
      simp [tripleVertex, j, bi]
    have hij : i ≠ j := by
      intro hij
      apply hab
      rw [← hia, ← hjb, hij]
    have horiginal :=
      (sphereSelected_root_adj_iff hq inward i j).mpr ⟨hinward, hij⟩
    obtain ⟨S, hSselected, hiS, hjS, hrootne⟩ := horiginal
    refine ⟨attachSphereTriple hq T S, ?_, ?_, ?_, ?_⟩
    · exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
        (sphereDecomposition hq inward) S).mpr hSselected
    · apply Finset.mem_map.mpr
      refine ⟨sphereRootVertex hq i, hiS, ?_⟩
      change attachSphereVertex T (sphereRootVertex hq i) =
        SphereExpansionVertex.root a
      rw [attachSphereVertex_root, hia]
    · apply Finset.mem_map.mpr
      refine ⟨sphereRootVertex hq j, hjS, ?_⟩
      change attachSphereVertex T (sphereRootVertex hq j) =
        SphereExpansionVertex.root b
      rw [attachSphereVertex_root, hjb]
    · exact fun h ↦ hab (SphereExpansionVertex.root.inj h)

@[simp]
lemma attachSphereFamily_card {V : Type*} [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (T : TripleOn V) (C : TripleSystemOn (SphereVertex q)) :
    (attachSphereFamily hq T C).card = C.card :=
  card_mapTripleSystem _ _

/-- The attached copy retains the strong private-interior-leaf property. -/
theorem attachSphereFamily_short_interior_leaf
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) {D : TripleSystemOn (SphereExpansionVertex V q)}
    (hDB : D ⊆ attachSphereFamily hq T (sphereBank hq))
    (hpacking : IsPackingOn D) (hDne : D.Nonempty) (hDq : D.card ≤ q) :
    ∃ x : SphereInterior q,
      SphereExpansionVertex.interior T x ∈ verticesOn D ∧
        (triplesThrough D (SphereExpansionVertex.interior T x)).card = 1 := by
  let C : TripleSystemOn (SphereVertex q) :=
    (sphereBank hq).filter fun S ↦ attachSphereTriple hq T S ∈ D
  have hmap : attachSphereFamily hq T C = D := by
    ext U
    constructor
    · intro hU
      obtain ⟨S, hSC, rfl⟩ := Finset.mem_map.mp hU
      exact (mem_filter.mp hSC).2
    · intro hUD
      have hUB := hDB hUD
      obtain ⟨S, hSB, hSU⟩ := Finset.mem_map.mp hUB
      change attachSphereTriple hq T S = U at hSU
      rw [← hSU]
      apply Finset.mem_map.mpr
      exact ⟨S, mem_filter.mpr ⟨hSB, by rwa [hSU]⟩, rfl⟩
  have hCB : C ⊆ sphereBank hq := filter_subset _ _
  have hCne : C.Nonempty := by
    obtain ⟨U, hUD⟩ := hDne
    rw [← hmap] at hUD
    obtain ⟨S, hSC, _⟩ := Finset.mem_map.mp hUD
    exact ⟨S, hSC⟩
  have hCq : C.card ≤ q := by
    rw [← attachSphereFamily_card hq T C, hmap]
    exact hDq
  have hCpacking : IsPackingOn C := by
    apply IsPackingOn.of_map (f := attachSphereEmbedding hq T)
    change IsPackingOn (attachSphereFamily hq T C)
    rwa [hmap]
  obtain ⟨x, hxvertices, hxone⟩ :=
    sphere_short_interior_leaf hq hCB hCpacking hCne hCq
  refine ⟨x, ?_, ?_⟩
  · simp only [verticesOn, mem_biUnion] at hxvertices ⊢
    obtain ⟨S, hSC, hxS⟩ := hxvertices
    refine ⟨attachSphereTriple hq T S, ?_, ?_⟩
    · rw [← hmap]
      exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T) C S).mpr hSC
    · exact (interior_mem_attachSphereTriple_iff hq T T x S).mpr ⟨rfl, hxS⟩
  · have hthrough := triplesThrough_map_apply
        (attachSphereEmbedding hq T) C x.1
    change triplesThrough (attachSphereFamily hq T C)
      (attachSphereVertex T x.1) =
        attachSphereFamily hq T (triplesThrough C x.1) at hthrough
    rw [hmap, attachSphereVertex_interior] at hthrough
    rw [hthrough, attachSphereFamily_card, hxone]

/-- Simultaneously attach a sphere to every root triple, selecting the
in-side precisely for the triples in `C`. -/
noncomputable def sphereTransform {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
    (hq : 2 ≤ q) (C : TripleSystemOn V) :
    TripleSystemOn (SphereExpansionVertex V q) :=
  (univ : Finset (TripleOn V)).biUnion fun T ↦
    attachSphereFamily hq T (sphereDecomposition hq (decide (T ∈ C)))

@[simp]
lemma mem_sphereTransform_iff {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) (C : TripleSystemOn V)
    (U : TripleOn (SphereExpansionVertex V q)) :
    U ∈ sphereTransform hq C ↔
      ∃ T : TripleOn V,
        U ∈ attachSphereFamily hq T
          (sphereDecomposition hq (decide (T ∈ C))) := by
  simp [sphereTransform]

theorem sphereTransform_isPacking
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    {C : TripleSystemOn V} (hC : IsPackingOn C) :
    IsPackingOn (sphereTransform hq C) := by
  intro x y hxy A hA hxA hyA B hB hxB hyB
  obtain ⟨T, hAT⟩ := (mem_sphereTransform_iff hq C A).mp hA
  obtain ⟨R, hBR⟩ := (mem_sphereTransform_iff hq C B).mp hB
  obtain ⟨S, hSselected, hSA⟩ := Finset.mem_map.mp hAT
  obtain ⟨U, hUselected, hUB⟩ := Finset.mem_map.mp hBR
  subst A
  subst B
  have hSmem : attachSphereTriple hq T S ∈
      attachSphereFamily hq T (sphereDecomposition hq (decide (T ∈ C))) :=
    (mem_mapTripleSystem_iff (attachSphereEmbedding hq T) _ S).mpr hSselected
  have hUmem : attachSphereTriple hq R U ∈
      attachSphereFamily hq R (sphereDecomposition hq (decide (R ∈ C))) :=
    (mem_mapTripleSystem_iff (attachSphereEmbedding hq R) _ U).mpr hUselected
  cases x with
  | interior X ix =>
      have hXT :=
        (interior_mem_attachSphereTriple_iff hq T X ix S).mp hxA |>.1
      have hXR :=
        (interior_mem_attachSphereTriple_iff hq R X ix U).mp hxB |>.1
      have hTR : T = R := hXT.symm.trans hXR
      cases hTR
      exact (sphereDecomposition_isPacking hq (decide (T ∈ C))).map
        (attachSphereEmbedding hq T) _ _ hxy
          (attachSphereTriple hq T S) hSmem hxA hyA
          (attachSphereTriple hq T U) hUmem hxB hyB
  | root a =>
      cases y with
      | interior X ix =>
          have hXT :=
            (interior_mem_attachSphereTriple_iff hq T X ix S).mp hyA |>.1
          have hXR :=
            (interior_mem_attachSphereTriple_iff hq R X ix U).mp hyB |>.1
          have hTR : T = R := hXT.symm.trans hXR
          cases hTR
          exact (sphereDecomposition_isPacking hq (decide (T ∈ C))).map
            (attachSphereEmbedding hq T) _ _ hxy
              (attachSphereTriple hq T S) hSmem hxA hyA
              (attachSphereTriple hq T U) hUmem hxB hyB
      | root b =>
          have hab : a ≠ b := by
            intro hab
            apply hxy
            exact congrArg SphereExpansionVertex.root hab
          have hAdjT :
              (coveredGraph (attachSphereFamily hq T
                (sphereDecomposition hq (decide (T ∈ C))))).Adj
                (SphereExpansionVertex.root a) (SphereExpansionVertex.root b) :=
            ⟨attachSphereTriple hq T S, hSmem, hxA, hyA, hxy⟩
          have hAdjR :
              (coveredGraph (attachSphereFamily hq R
                (sphereDecomposition hq (decide (R ∈ C))))).Adj
                (SphereExpansionVertex.root a) (SphereExpansionVertex.root b) :=
            ⟨attachSphereTriple hq R U, hUmem, hxB, hyB, hxy⟩
          have hTdata :=
            (attachedSphere_root_adj_iff hq T (decide (T ∈ C)) a b).mp hAdjT
          have hRdata :=
            (attachedSphere_root_adj_iff hq R (decide (R ∈ C)) a b).mp hAdjR
          have hTC : T ∈ C := by simpa using hTdata.1
          have hRC : R ∈ C := by simpa using hRdata.1
          have hTR : T = R := hC a b hab T hTC hTdata.2.1 hTdata.2.2.1
            R hRC hRdata.2.1 hRdata.2.2.1
          cases hTR
          exact (sphereDecomposition_isPacking hq (decide (T ∈ C))).map
            (attachSphereEmbedding hq T) _ _ hxy
              (attachSphereTriple hq T S) hSmem hxA hyA
              (attachSphereTriple hq T U) hUmem hxB hyB

/-- Once the simultaneous transform is known to be a packing, fiberwise
interior leaves force every short subfamily to have a global private leaf. -/
theorem sphereTransform_hasShortLeaf
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (C : TripleSystemOn V) (hpacking : IsPackingOn (sphereTransform hq C)) :
    HasShortLeafProperty q (sphereTransform hq C) := by
  intro D hDH hDne hDq
  obtain ⟨U, hUD⟩ := hDne
  obtain ⟨T, hUfiber⟩ := (mem_sphereTransform_iff hq C U).mp (hDH hUD)
  let F : TripleSystemOn (SphereExpansionVertex V q) :=
    D.filter fun S ↦ S ∈ attachSphereFamily hq T (sphereBank hq)
  have hselectedBank : sphereDecomposition hq (decide (T ∈ C)) ⊆
      sphereBank hq := sphereDecomposition_subset_bank hq _
  have hUFbank : U ∈ attachSphereFamily hq T (sphereBank hq) := by
    obtain ⟨S, hSselected, rfl⟩ := Finset.mem_map.mp hUfiber
    exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
      (sphereBank hq) S).mpr (hselectedBank hSselected)
  have hFne : F.Nonempty :=
    ⟨U, mem_filter.mpr ⟨hUD, hUFbank⟩⟩
  have hFD : F ⊆ D := filter_subset _ _
  have hFbank : F ⊆ attachSphereFamily hq T (sphereBank hq) := by
    intro S hSF
    exact (mem_filter.mp hSF).2
  have hFpacking : IsPackingOn F :=
    hpacking.mono (hFD.trans hDH)
  have hFq : F.card ≤ q :=
    (card_le_card hFD).trans hDq
  obtain ⟨x, hxF, hxone⟩ :=
    attachSphereFamily_short_interior_leaf hq T hFbank hFpacking hFne hFq
  refine ⟨SphereExpansionVertex.interior T x,
    verticesOn_mono hFD hxF, ?_⟩
  have hthrough : triplesThrough D (SphereExpansionVertex.interior T x) =
      triplesThrough F (SphereExpansionVertex.interior T x) := by
    dsimp [F]
    ext S
    simp only [triplesThrough, mem_filter]
    constructor
    · rintro ⟨hSD, hxS⟩
      refine ⟨⟨hSD, ?_⟩, hxS⟩
      obtain ⟨R, hSR⟩ :=
        (mem_sphereTransform_iff hq C S).mp (hDH hSD)
      obtain ⟨A, hAselected, hAS⟩ := Finset.mem_map.mp hSR
      rw [← hAS] at hxS ⊢
      have hTR :=
        (interior_mem_attachSphereTriple_iff hq R T x A).mp hxS |>.1
      subst R
      exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
        (sphereBank hq) A).mpr
          (sphereDecomposition_subset_bank hq _ hAselected)
    · rintro ⟨⟨hSD, _⟩, hxS⟩
      exact ⟨hSD, hxS⟩
  rw [hthrough]
  exact hxone

theorem sphereTransform_girthGreater
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    {C : TripleSystemOn V} (hC : IsPackingOn C) :
    GirthGreaterOn q (sphereTransform hq C) := by
  have hpacking := sphereTransform_isPacking hq hC
  exact hpacking.girthGreater_of_shortLeaf
    (sphereTransform_hasShortLeaf hq C hpacking)

end Erdos207
