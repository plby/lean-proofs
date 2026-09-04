import ErdosProblems.Erdos720.Extend

namespace Erdos720

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ExtendableState

variable {G : SimpleGraph V} {M : ℕ}

lemma singleton_state (root : V)
    (hM : 1 ≤ M)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card) :
    ∃ S : ExtendableState G 3 M,
      S.used = {root} ∧ S.deg = fun _ => 0 := by
  classical
  have hbalance : ∀ X : Finset V, X.card ≤ 2 * M →
      3 * X.card ≤ (outsideNeighbors G {root} X).card + ∑ _x ∈ X, 0 := by
    intro X hX
    simp only [sum_const_zero, add_zero]
    by_cases hzero : X = ∅
    · subst X
      simp [outsideNeighbors]
    · have hpos : 1 ≤ X.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
      have hN := hexp X hX
      have hcover : (setNeighbors G X).card ≤
          (outsideNeighbors G {root} X).card + 1 := by
        calc
          (setNeighbors G X).card ≤
              (outsideNeighbors G {root} X ∪ {root}).card := by
                apply card_le_card
                intro v hv
                by_cases hvr : v = root
                · subst v
                  exact mem_union_right _ (mem_singleton_self root)
                · exact mem_union_left _ (mem_sdiff.mpr ⟨hv, by simpa using hvr⟩)
          _ ≤ (outsideNeighbors G {root} X).card + ({root} : Finset V).card := card_union_le _ _
          _ = (outsideNeighbors G {root} X).card + 1 := by simp
      omega
  let S : ExtendableState G 3 M :=
    { used := {root}
      deg := fun _ => 0
      deg_off := by simp
      deg_le := by simp
      balance := hbalance }
  exact ⟨S, rfl, rfl⟩

/-- The data obtained by replacing every vertex of a frontier by two fresh
children. -/
structure FrontierExpansion (S S' : ExtendableState G 3 M) (L : Finset V) where
  children : Finset V
  used_eq : S'.used = S.used ∪ children
  fresh : Disjoint children S.used
  card_children : children.card = 2 * L.card
  parent : ∀ ⦃y⦄, y ∈ children → ∃ s ∈ L, G.Adj s y
  child_deg : ∀ ⦃y⦄, y ∈ children → S'.deg y = 1
  preserve : ∀ ⦃v⦄, v ∈ S.used → v ∉ L → S'.deg v = S.deg v

lemma large_expansion_for_state
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card)
    (S : ExtendableState G 3 M) (hused : S.used.card < M) :
    ∀ X : Finset V, M < X.card → X.card ≤ 2 * M →
      3 * X.card + S.used.card + 1 ≤ (setNeighbors G X).card := by
  intro X hMX hX
  have h := hexp X hX
  omega

/-- One full binary branching step, performed sequentially so that the
extendability invariant is preserved. -/
lemma expand_frontier
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card)
    (hM : 1 ≤ M) (S : ExtendableState G 3 M) (L : Finset V)
    (hcap : S.used.card + 2 * L.card ≤ M)
    (hLused : L ⊆ S.used)
    (hLdeg : ∀ v ∈ L, S.deg v ≤ 1) :
    ∃ S' : ExtendableState G 3 M, Nonempty (FrontierExpansion S S' L) := by
  classical
  induction L using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S, ⟨{
        children := ∅
        used_eq := by simp
        fresh := by simp
        card_children := by simp
        parent := ?_
        child_deg := ?_
        preserve := ?_ }⟩⟩
      · simp
      · simp
      · simp
  | @insert s L hsL ih =>
      have hsused : s ∈ S.used := hLused (mem_insert_self s L)
      have hsdeg : S.deg s < 3 := by
        have := hLdeg s (mem_insert_self s L)
        omega
      have hused0 : S.used.card < M := by
        rw [card_insert_of_notMem hsL] at hcap
        omega
      obtain ⟨y₁, hy₁fresh, hsy₁, S₁, hS₁used, hS₁deg⟩ :=
        S.exists_add_leaf hM (by omega)
          (large_expansion_for_state hexp S hused0) hsused hsdeg
      have hS₁card : S₁.used.card = S.used.card + 1 := by
        rw [hS₁used, card_insert_of_notMem hy₁fresh]
      have hsS₁ : s ∈ S₁.used := hS₁used.symm ▸ mem_insert_of_mem hsused
      have hsy₁ne : s ≠ y₁ := by
        intro h
        subst y₁
        exact hy₁fresh hsused
      have hsdeg₁ : S₁.deg s < 3 := by
        rw [hS₁deg]
        simp [addLeafDeg, hsy₁ne]
        have := hLdeg s (mem_insert_self s L)
        omega
      have hused1 : S₁.used.card < M := by
        rw [hS₁card]
        rw [card_insert_of_notMem hsL] at hcap
        omega
      obtain ⟨y₂, hy₂fresh, hsy₂, S₂, hS₂used, hS₂deg⟩ :=
        S₁.exists_add_leaf hM (by omega)
          (large_expansion_for_state hexp S₁ hused1) hsS₁ hsdeg₁
      have hy₁S₁ : y₁ ∈ S₁.used := hS₁used.symm ▸ mem_insert_self y₁ _
      have hy₁ne₂ : y₁ ≠ y₂ := by
        intro h
        subst y₂
        exact hy₂fresh hy₁S₁
      have hS₂card : S₂.used.card = S.used.card + 2 := by
        rw [hS₂used, card_insert_of_notMem hy₂fresh, hS₁card]
      have hLS₂ : L ⊆ S₂.used := by
        intro v hv
        rw [hS₂used, hS₁used]
        exact mem_insert_of_mem (mem_insert_of_mem (hLused (mem_insert_of_mem hv)))
      have hLdeg₂ : ∀ v ∈ L, S₂.deg v ≤ 1 := by
        intro v hv
        have hvs : v ≠ s := fun h => hsL (h ▸ hv)
        have hvy₁ : v ≠ y₁ := by
          intro h
          subst v
          exact hy₁fresh (hLused (mem_insert_of_mem hv))
        have hvS₁ : v ∈ S₁.used := hS₁used.symm ▸
          mem_insert_of_mem (hLused (mem_insert_of_mem hv))
        have hvy₂ : v ≠ y₂ := by
          intro h
          subst v
          exact hy₂fresh hvS₁
        rw [hS₂deg]
        simp only [addLeafDeg, hvs, hvy₂, if_false, add_zero]
        rw [hS₁deg]
        simp only [ge_iff_le]
        exact hLdeg v (mem_insert_of_mem hv)
      have hcap₂ : S₂.used.card + 2 * L.card ≤ M := by
        rw [hS₂card]
        have hcap' := hcap
        rw [card_insert_of_notMem hsL] at hcap'
        omega
      obtain ⟨S₃, ⟨R⟩⟩ := ih S₂ hcap₂ hLS₂ hLdeg₂
      let C := insert y₁ (insert y₂ R.children)
      have hy₁notR : y₁ ∉ R.children := by
        intro hy
        have hy₁S₂ : y₁ ∈ S₂.used := hS₂used.symm ▸ mem_insert_of_mem hy₁S₁
        exact (Finset.disjoint_left.mp R.fresh) hy hy₁S₂
      have hy₂S₂ : y₂ ∈ S₂.used := hS₂used.symm ▸ mem_insert_self y₂ _
      have hy₂notR : y₂ ∉ R.children := by
        intro hy
        exact (Finset.disjoint_left.mp R.fresh) hy hy₂S₂
      have hCcard : C.card = 2 * (insert s L).card := by
        simp [C, hy₁notR, hy₂notR, hy₁ne₂, hsL, R.card_children]
        omega
      have husedEq : S₃.used = S.used ∪ C := by
        rw [R.used_eq, hS₂used, hS₁used]
        ext v
        simp [C]
        aesop
      have hCfresh : Disjoint C S.used := by
        rw [Finset.disjoint_left]
        intro v hvC hvS
        simp only [C, mem_insert] at hvC
        rcases hvC with rfl | rfl | hvR
        · exact hy₁fresh hvS
        · exact hy₂fresh (hS₁used.symm ▸ mem_insert_of_mem hvS)
        · exact (Finset.disjoint_left.mp R.fresh) hvR
            (hS₂used.symm ▸ mem_insert_of_mem
              (hS₁used.symm ▸ mem_insert_of_mem hvS))
      refine ⟨S₃, ⟨{
          children := C
          used_eq := husedEq
          fresh := hCfresh
          card_children := hCcard
          parent := ?_
          child_deg := ?_
          preserve := ?_ }⟩⟩
      · intro y hyC
        simp only [C, mem_insert] at hyC
        rcases hyC with hy | hy | hyR
        · subst y
          exact ⟨s, mem_insert_self _ _, hsy₁⟩
        · subst y
          exact ⟨s, mem_insert_self _ _, hsy₂⟩
        · obtain ⟨p, hpL, hpy⟩ := R.parent hyR
          exact ⟨p, mem_insert_of_mem hpL, hpy⟩
      · intro y hyC
        simp only [C, mem_insert] at hyC
        rcases hyC with hy | hy | hyR
        · subst y
          have hy₁S₂ : y₁ ∈ S₂.used := hS₂used.symm ▸ mem_insert_of_mem hy₁S₁
          have hy₁notL : y₁ ∉ L := fun h => hy₁fresh (hLused (mem_insert_of_mem h))
          have hpres := R.preserve hy₁S₂ hy₁notL
          have hy₁off : S.deg y₁ = 0 := S.deg_off hy₁fresh
          have hy₁degS₁ : S₁.deg y₁ = 1 := by
            rw [hS₁deg]
            simp [addLeafDeg, hsy₁ne.symm, hy₁off]
          rw [hpres, hS₂deg]
          simp [addLeafDeg, hsy₁ne.symm, hy₁ne₂, hy₁degS₁]
        · subst y
          have hy₂notL : y₂ ∉ L := fun h => hy₂fresh
            (hS₁used.symm ▸ mem_insert_of_mem (hLused (mem_insert_of_mem h)))
          have hpres := R.preserve hy₂S₂ hy₂notL
          rw [hpres, hS₂deg]
          have hy₂off : S₁.deg y₂ = 0 := S₁.deg_off hy₂fresh
          have hsy₂ne : s ≠ y₂ := by
            intro h
            subst y₂
            exact hy₂fresh hsS₁
          simp [addLeafDeg, hsy₂ne.symm, hy₂off]
        · exact R.child_deg hyR
      · intro v hvS hvnot
        have hvnL : v ∉ L := fun h => hvnot (mem_insert_of_mem h)
        have hvns : v ≠ s := fun h => hvnot (h ▸ mem_insert_self s L)
        have hvny₁ : v ≠ y₁ := by
          intro h
          subst v
          exact hy₁fresh hvS
        have hvS₁ : v ∈ S₁.used := hS₁used.symm ▸ mem_insert_of_mem hvS
        have hvny₂ : v ≠ y₂ := by
          intro h
          subst v
          exact hy₂fresh hvS₁
        have hvS₂ : v ∈ S₂.used := hS₂used.symm ▸ mem_insert_of_mem hvS₁
        rw [R.preserve hvS₂ hvnL, hS₂deg]
        simp only [addLeafDeg, hvns, hvny₂, if_false, add_zero]
        rw [hS₁deg]
        simp [addLeafDeg, hvns, hvny₁]

/-- A simple path of exactly `length` edges, all of whose vertices lie in
`support`, with specified endpoints. -/
def ExactPathIn (G : SimpleGraph V) (support base : Finset V)
    (root : V) (length : ℕ) (last : V) : Prop :=
  ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = length + 1 ∧
    l.head? = some root ∧ l.getLast? = some last ∧
    (∀ x ∈ l, x ∈ support) ∧ (∀ x ∈ l, x = root ∨ x ∉ base)

lemma exactPathIn_zero {support : Finset V} {root : V} (hr : root ∈ support) :
    ExactPathIn G support support root 0 root := by
  refine ⟨[root], by simp, by simp, by simp, by simp, by simp, ?_, by simp⟩
  simp only [List.mem_singleton]
  intro x hx
  simpa [hx] using hr

lemma ExactPathIn.mono {U W base : Finset V} {root last : V} {length : ℕ}
    (h : ExactPathIn G U base root length last) (hUW : U ⊆ W) :
    ExactPathIn G W base root length last := by
  rcases h with ⟨l, hnd, hch, hlen, hhead, hlast, hsub, hfresh⟩
  exact ⟨l, hnd, hch, hlen, hhead, hlast,
    fun x hx => hUW (hsub x hx), hfresh⟩

lemma ExactPathIn.snoc {U W base : Finset V} {root last y : V} {length : ℕ}
    (h : ExactPathIn G U base root length last) (hUW : U ⊆ W) (hbaseU : base ⊆ U)
    (hyU : y ∉ U) (hyW : y ∈ W) (hxy : G.Adj last y) :
    ExactPathIn G W base root (length + 1) y := by
  rcases h with ⟨l, hnd, hch, hlen, hhead, hlast, hsub, hfresh⟩
  have hlne : l ≠ [] := by
    intro hz
    simp [hz] at hhead
  have hlastval : l.getLast hlne = last := by
    have := hlast
    rw [List.getLast?_eq_getLast_of_ne_nil hlne] at this
    simpa using Option.some.inj this
  have hynmem : y ∉ l := by
    intro hy
    exact hyU (hsub y hy)
  have hnd' : (l ++ [y]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact fun h => hynmem (h ▸ ha)
  refine ⟨l ++ [y], hnd',
    ?_, by simp [hlen], ?_, by simp, ?_, ?_⟩
  · apply List.isChain_append.mpr
    refine ⟨hch, by simp, ?_⟩
    intro a ha b hb
    simp [hlast] at ha
    simp at hb
    subst a
    subst b
    exact hxy
  · simp [List.head?_append, hhead]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hUW (hsub x hx)
    · exact hyW
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hfresh x hx
    · exact Or.inr fun hy => hyU (hbaseU hy)

lemma ExactPathIn.end_eq_start {U base : Finset V} {root last : V}
    (h : ExactPathIn G U base root 0 last) : last = root := by
  rcases h with ⟨l, -, -, hlen, hhead, hlast, -, -⟩
  have : l.length = 1 := by omega
  cases l with
  | nil => simp at this
  | cons a l =>
      cases l with
      | nil =>
          simp at hhead hlast
          exact hlast.symm.trans hhead
      | cons b l => simp at this

/-- A complete binary fan of a specified height, rooted at an already used
vertex of an extendable state. -/
structure BinaryFan (S S' : ExtendableState G 3 M) (root : V) (height : ℕ) where
  leaves : Finset V
  used_card : S'.used.card = S.used.card + (2 ^ (height + 1) - 2)
  used_mono : S.used ⊆ S'.used
  card_leaves : leaves.card = 2 ^ height
  leaves_used : leaves ⊆ S'.used
  leaf_deg : ∀ ⦃v⦄, v ∈ leaves → S'.deg v ≤ 1
  paths : ∀ ⦃v⦄, v ∈ leaves → ExactPathIn G S'.used S.used root height v
  leaf_old : ∀ ⦃v⦄, v ∈ leaves → v ∈ S.used → height = 0 ∧ v = root
  preserve : ∀ ⦃v⦄, v ∈ S.used → v ≠ root → S'.deg v = S.deg v

lemma binary_fan
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card)
    (hM : 1 ≤ M) (S : ExtendableState G 3 M) (root : V) (height : ℕ)
    (hcap : S.used.card + (2 ^ (height + 1) - 2) ≤ M)
    (hroot : root ∈ S.used) (hrootdeg : S.deg root ≤ 1) :
    ∃ S' : ExtendableState G 3 M, Nonempty (BinaryFan S S' root height) := by
  classical
  induction height generalizing S with
  | zero =>
      refine ⟨S, ⟨{
        leaves := {root}
        used_card := by simp
        used_mono := Subset.rfl
        card_leaves := by simp
        leaves_used := by simpa using hroot
        leaf_deg := by simpa using hrootdeg
        paths := by
          intro v hv
          have : v = root := by simpa using hv
          subst v
          simpa using exactPathIn_zero (G := G) hroot
        leaf_old := by simp
        preserve := by simp }⟩⟩
  | succ height ih =>
      have hcap0 : S.used.card + (2 ^ (height + 1) - 2) ≤ M := by
        have hpowmono : 2 ^ (height + 1) ≤ 2 ^ (height + 2) := by
          rw [show height + 2 = (height + 1) + 1 by omega, pow_succ]
          have hp : 0 < 2 ^ (height + 1) := pow_pos (by omega) _
          omega
        calc
          S.used.card + (2 ^ (height + 1) - 2)
              ≤ S.used.card + (2 ^ (height + 2) - 2) := by
                exact Nat.add_le_add_left (Nat.sub_le_sub_right hpowmono 2) _
          _ = S.used.card + (2 ^ (height.succ + 1) - 2) := by congr 2 <;> omega
          _ ≤ M := hcap
      obtain ⟨T, ⟨F⟩⟩ := ih S hcap0 hroot hrootdeg
      have hfrontCap : T.used.card + 2 * F.leaves.card ≤ M := by
        rw [F.used_card, F.card_leaves]
        have hpow1 : 2 ^ (height + 1) = 2 * 2 ^ height := by
          rw [pow_succ]
          omega
        have hpow2 : 2 ^ (height + 2) = 4 * 2 ^ height := by
          rw [show height + 2 = (height + 1) + 1 by omega, pow_succ, hpow1]
          omega
        rw [show height.succ + 1 = height + 2 by omega] at hcap
        rw [hpow2] at hcap
        rw [hpow1]
        have hp : 1 ≤ 2 ^ height := one_le_pow₀ (by omega)
        omega
      obtain ⟨T', ⟨E⟩⟩ := expand_frontier hexp hM T F.leaves
        hfrontCap F.leaves_used F.leaf_deg
      have hTsub : T.used ⊆ T'.used := by
        rw [E.used_eq]
        exact subset_union_left
      have hSsub : S.used ⊆ T'.used := fun _ hv => hTsub (F.used_mono hv)
      have husedCard : T'.used.card =
          S.used.card + (2 ^ (height.succ + 1) - 2) := by
        rw [E.used_eq, card_union_of_disjoint E.fresh.symm,
          E.card_children, F.card_leaves, F.used_card]
        have hpow1 : 2 ^ (height + 1) = 2 * 2 ^ height := by
          rw [pow_succ]
          omega
        have hpow2 : 2 ^ (height + 2) = 4 * 2 ^ height := by
          rw [show height + 2 = (height + 1) + 1 by omega, pow_succ, hpow1]
          omega
        rw [show height.succ + 1 = height + 2 by omega, hpow1, hpow2]
        have hp : 1 ≤ 2 ^ height := one_le_pow₀ (by omega)
        omega
      refine ⟨T', ⟨{
        leaves := E.children
        used_card := husedCard
        used_mono := hSsub
        card_leaves := by
          rw [E.card_children, F.card_leaves, pow_succ]
          omega
        leaves_used := by
          rw [E.used_eq]
          exact subset_union_right
        leaf_deg := fun _ hv => Nat.le_of_eq (E.child_deg hv)
        paths := ?_
        leaf_old := ?_
        preserve := ?_ }⟩⟩
      · intro y hy
        obtain ⟨p, hp, hpy⟩ := E.parent hy
        have hpPath := F.paths hp
        have hyT : y ∉ T.used := fun hyT => (Finset.disjoint_left.mp E.fresh) hy hyT
        have hyT' : y ∈ T'.used := E.used_eq.symm ▸ mem_union_right _ hy
        exact hpPath.snoc hTsub F.used_mono hyT hyT' hpy
      · intro y hy hyS
        exact ((Finset.disjoint_left.mp E.fresh) hy (F.used_mono hyS)).elim
      · intro v hvS hvroot
        have hvT : v ∈ T.used := F.used_mono hvS
        have hvnotleaf : v ∉ F.leaves := by
          intro hvleaf
          exact hvroot (F.leaf_old hvleaf hvS).2
        rw [E.preserve hvT hvnotleaf, F.preserve hvS hvroot]

/-- A fresh path grown from a used root while maintaining extendability. -/
structure PathExtension (S S' : ExtendableState G 3 M) (root : V) (length : ℕ) where
  endpoint : V
  used_card : S'.used.card = S.used.card + length
  used_mono : S.used ⊆ S'.used
  endpoint_used : endpoint ∈ S'.used
  endpoint_deg : S'.deg endpoint ≤ 1
  path : ExactPathIn G S'.used S.used root length endpoint
  endpoint_old : endpoint ∈ S.used → length = 0 ∧ endpoint = root
  root_deg : S'.deg root = S.deg root + if 0 < length then 1 else 0
  preserve : ∀ ⦃v⦄, v ∈ S.used → v ≠ root → S'.deg v = S.deg v

lemma extend_path
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card)
    (hM : 1 ≤ M) (S : ExtendableState G 3 M) (root : V) (length : ℕ)
    (hcap : S.used.card + length ≤ M)
    (hroot : root ∈ S.used) (hrootdeg : S.deg root ≤ 1) :
    ∃ S' : ExtendableState G 3 M, Nonempty (PathExtension S S' root length) := by
  classical
  induction length generalizing S with
  | zero =>
      refine ⟨S, ⟨{
        endpoint := root
        used_card := by simp
        used_mono := Subset.rfl
        endpoint_used := hroot
        endpoint_deg := hrootdeg
        path := by simpa using exactPathIn_zero (G := G) hroot
        endpoint_old := by simp
        root_deg := by simp
        preserve := by simp }⟩⟩
  | succ length ih =>
      have hcap0 : S.used.card + length ≤ M := by omega
      obtain ⟨T, ⟨P⟩⟩ := ih S hcap0 hroot hrootdeg
      have hTlt : T.used.card < M := by
        rw [P.used_card]
        omega
      have hendlt : T.deg P.endpoint < 3 := P.endpoint_deg.trans_lt (by omega)
      obtain ⟨y, hyfresh, hendy, T', hT'used, hT'deg⟩ :=
        T.exists_add_leaf hM (by omega)
          (large_expansion_for_state hexp T hTlt) P.endpoint_used hendlt
      have husedCard : T'.used.card = S.used.card + length.succ := by
        rw [hT'used, card_insert_of_notMem hyfresh, P.used_card]
        omega
      have hTsub : T.used ⊆ T'.used := by
        rw [hT'used]
        exact subset_insert _ _
      have hSsub : S.used ⊆ T'.used := fun _ hv => hTsub (P.used_mono hv)
      have hyused : y ∈ T'.used := hT'used.symm ▸ mem_insert_self y _
      have hydeg : T'.deg y ≤ 1 := by
        have hyoff : T.deg y = 0 := T.deg_off hyfresh
        have hyne : y ≠ P.endpoint := by
          intro heq
          subst y
          exact hyfresh P.endpoint_used
        rw [hT'deg]
        simp [addLeafDeg, hyoff, hyne]
      have hpath : ExactPathIn G T'.used S.used root length.succ y := by
        simpa [Nat.succ_eq_add_one] using
          P.path.snoc hTsub P.used_mono hyfresh hyused hendy
      have hrootEq : T'.deg root =
          S.deg root + if 0 < length.succ then 1 else 0 := by
        rw [hT'deg]
        by_cases hzero : length = 0
        · subst length
          have hend : P.endpoint = root := P.path.end_eq_start
          have hrooty : root ≠ y := by
            intro heq
            subst y
            exact hyfresh (P.used_mono hroot)
          rw [hend]
          simp [addLeafDeg, P.root_deg, hrooty]
        · have hne : P.endpoint ≠ root := by
            intro heq
            have hold : P.endpoint ∈ S.used := heq.symm ▸ hroot
            exact hzero (P.endpoint_old hold).1
          have hrooty : root ≠ y := by
            intro heq
            subst y
            exact hyfresh (P.used_mono hroot)
          simp [addLeafDeg, hne.symm, hrooty, P.root_deg, hzero,
            Nat.pos_of_ne_zero hzero]
      have hpres : ∀ ⦃v⦄, v ∈ S.used → v ≠ root → T'.deg v = S.deg v := by
        intro v hvS hvroot
        have hvT : v ∈ T.used := P.used_mono hvS
        have hvend : v ≠ P.endpoint := by
          intro heq
          have hold : P.endpoint ∈ S.used := heq ▸ hvS
          exact hvroot (heq.trans (P.endpoint_old hold).2)
        have hvy : v ≠ y := by
          intro heq
          subst y
          exact hyfresh hvT
        rw [hT'deg]
        simp [addLeafDeg, hvend, hvy, P.preserve hvS hvroot]
      refine ⟨T', ⟨{
        endpoint := y
        used_card := husedCard
        used_mono := hSsub
        endpoint_used := hyused
        endpoint_deg := hydeg
        path := hpath
        endpoint_old := fun hyS => (hyfresh (P.used_mono hyS)).elim
        root_deg := hrootEq
        preserve := hpres }⟩⟩

end ExtendableState

end Erdos720
