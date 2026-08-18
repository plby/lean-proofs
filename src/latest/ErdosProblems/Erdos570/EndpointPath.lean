/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleSequence
import ErdosProblems.Erdos570.FiniteSelection

/-!
# Endpoint-preserving path extensions

This file formalizes the elementary rerouting move behind the endpoint-path
lemma of Erdős--Faudree--Rousseau--Schelp.  A path is recorded as an injective
finite sequence with adjacent consecutive entries.  If an outside vertex is
joined to two path vertices, and the successors of those vertices are also
joined, reversing the intervening segment inserts the outside vertex while
leaving both endpoints fixed.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- An injective path with two distinguished endpoints.  The sequence has
`n + 2` vertices, so the endpoint expressions are always meaningful. -/
structure IsEndpointPath {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 2) → V) : Prop where
  injective : Function.Injective p
  adj : ∀ i j : Fin (n + 2), i.val + 1 = j.val → G.Adj (p i) (p j)

/-- There is no path with one additional vertex and the same ordered pair of
endpoints. -/
def EndpointUnextendable {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 2) → V) : Prop :=
  ¬ ∃ q : Fin (n + 3) → V, IsEndpointPath G q ∧
      q 0 = p 0 ∧ q (Fin.last (n + 2)) = p (Fin.last (n + 1))

/-- The endpoint-preserving rerouting sequence.  Its order is

`p 0, ..., p i, x, p j, p (j-1), ..., p (i+1), p (j+1), ..., p last`.
-/
def rerouteEndpointPath {V : Type*} {n : ℕ}
    (p : Fin (n + 2) → V) (x : V) (i j : Fin (n + 1))
    (r : Fin (n + 3)) : V :=
  if hri : r.val ≤ i.val then
    p ⟨r.val, by omega⟩
  else if hrx : r.val = i.val + 1 then
    x
  else if hrj : r.val ≤ j.val + 1 then
    p ⟨i.val + j.val + 2 - r.val, by omega⟩
  else
    p ⟨r.val - 1, by omega⟩

theorem rerouteEndpointPath_injective
    {V : Type*} {n : ℕ} {p : Fin (n + 2) → V} {x : V}
    {i j : Fin (n + 1)} (hp : Function.Injective p)
    (hx : x ∉ Set.range p) (hij : i.val < j.val) :
    Function.Injective (rerouteEndpointPath p x i j) := by
  intro a b hab
  simp only [rerouteEndpointPath] at hab
  split at hab <;> rename_i ha0
  · split at hab <;> rename_i hb0
    · have hv := congrArg Fin.val (hp hab)
      simp only [Fin.val_mk] at hv
      exact Fin.ext hv
    · split at hab <;> rename_i hbx
      · exact (hx ⟨_, hab⟩).elim
      · split at hab <;> rename_i hbj
        · have hv := congrArg Fin.val (hp hab)
          simp only [Fin.val_mk] at hv
          omega
        · have hv := congrArg Fin.val (hp hab)
          simp only [Fin.val_mk] at hv
          omega
  · split at hab <;> rename_i hax
    · split at hab <;> rename_i hb0
      · exact (hx ⟨_, hab.symm⟩).elim
      · split at hab <;> rename_i hbx
        · exact Fin.ext (hax.trans hbx.symm)
        · split at hab <;> rename_i hbj
          · exact (hx ⟨_, hab.symm⟩).elim
          · exact (hx ⟨_, hab.symm⟩).elim
    · split at hab <;> rename_i haj
      · split at hab <;> rename_i hb0
        · have hv := congrArg Fin.val (hp hab)
          simp only [Fin.val_mk] at hv
          omega
        · split at hab <;> rename_i hbx
          · exact (hx ⟨_, hab⟩).elim
          · split at hab <;> rename_i hbj
            · have hv := congrArg Fin.val (hp hab)
              simp only [Fin.val_mk] at hv
              exact Fin.ext (by omega)
            · have hv := congrArg Fin.val (hp hab)
              simp only [Fin.val_mk] at hv
              omega
      · split at hab <;> rename_i hb0
        · have hv := congrArg Fin.val (hp hab)
          simp only [Fin.val_mk] at hv
          omega
        · split at hab <;> rename_i hbx
          · exact (hx ⟨_, hab⟩).elim
          · split at hab <;> rename_i hbj
            · have hv := congrArg Fin.val (hp hab)
              simp only [Fin.val_mk] at hv
              omega
            · have hv := congrArg Fin.val (hp hab)
              simp only [Fin.val_mk] at hv
              exact Fin.ext (by omega)

theorem rerouteEndpointPath_adj
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    {p : Fin (n + 2) → V} {x : V} {i j : Fin (n + 1)}
    (hp : IsEndpointPath G p) (hij : i.val < j.val)
    (hxi : G.Adj x (p i.castSucc))
    (hxj : G.Adj x (p j.castSucc))
    (hsucc : G.Adj (p i.succ) (p j.succ)) :
    ∀ a b : Fin (n + 3), a.val + 1 = b.val →
      G.Adj (rerouteEndpointPath p x i j a)
        (rerouteEndpointPath p x i j b) := by
  intro a b hab
  simp only [rerouteEndpointPath]
  split <;> rename_i ha0
  · split <;> rename_i hb0
    · apply hp.adj
      exact hab
    · split <;> rename_i hbx
      · have hai : a.val = i.val := by omega
        have haeq : (⟨a.val, by omega⟩ : Fin (n + 2)) = i.castSucc :=
          Fin.ext hai
        rw [haeq]
        exact hxi.symm
      · omega
  · split <;> rename_i hax
    · split <;> rename_i hb0
      · omega
      · split <;> rename_i hbx
        · omega
        · split <;> rename_i hbj
          · have hbval : b.val = i.val + 2 := by omega
            have hindex :
                (⟨i.val + j.val + 2 - b.val, by omega⟩ : Fin (n + 2)) =
                  j.castSucc := by
              apply Fin.ext
              simp only [Fin.val_mk, Fin.val_castSucc]
              omega
            rw [hindex]
            exact hxj
          · omega
    · split <;> rename_i haj
      · split <;> rename_i hb0
        · omega
        · split <;> rename_i hbx
          · omega
          · split <;> rename_i hbj
            · apply (hp.adj _ _ ?_).symm
              simp only [Fin.val_mk]
              omega
            · have haindex :
                  (⟨i.val + j.val + 2 - a.val, by omega⟩ : Fin (n + 2)) =
                    i.succ := by
                apply Fin.ext
                simp only [Fin.val_mk, Fin.val_succ]
                omega
              have hbindex :
                  (⟨b.val - 1, by omega⟩ : Fin (n + 2)) = j.succ := by
                apply Fin.ext
                simp only [Fin.val_mk, Fin.val_succ]
                omega
              rw [haindex, hbindex]
              exact hsucc
      · split <;> rename_i hb0
        · omega
        · split <;> rename_i hbx
          · omega
          · split <;> rename_i hbj
            · omega
            · apply hp.adj _ _
              simp only [Fin.val_mk]
              omega

@[simp] theorem rerouteEndpointPath_zero
    {V : Type*} {n : ℕ} (p : Fin (n + 2) → V) (x : V)
    (i j : Fin (n + 1)) :
    rerouteEndpointPath p x i j 0 = p 0 := by
  simp [rerouteEndpointPath]

@[simp] theorem rerouteEndpointPath_last
    {V : Type*} {n : ℕ} (p : Fin (n + 2) → V) (x : V)
    (i j : Fin (n + 1)) :
    rerouteEndpointPath p x i j (Fin.last (n + 2)) =
      p (Fin.last (n + 1)) := by
  unfold rerouteEndpointPath
  split <;> rename_i hri
  · simp only [Fin.val_last] at hri
    omega
  · split <;> rename_i hrx
    · simp only [Fin.val_last] at hrx
      omega
    · split <;> rename_i hrj
      · simp only [Fin.val_last] at hrj
        omega
      · congr 1

/-- In an endpoint-unextendable path, successors of two distinct neighbors
of an outside vertex cannot be adjacent: otherwise the intervening path
segment can be reversed and the outside vertex inserted. -/
theorem not_adj_successors_of_endpointUnextendable
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p) {x : V}
    (hx : x ∉ Set.range p) {i j : Fin (n + 1)} (hij : i.val < j.val)
    (hxi : G.Adj x (p i.castSucc)) (hxj : G.Adj x (p j.castSucc)) :
    ¬ G.Adj (p i.succ) (p j.succ) := by
  intro hsucc
  apply hmax
  refine ⟨rerouteEndpointPath p x i j, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact rerouteEndpointPath_injective hp.injective hx hij
  · exact rerouteEndpointPath_adj hp hij hxi hxj hsucc
  · exact rerouteEndpointPath_zero p x i j
  · exact rerouteEndpointPath_last p x i j

/-- Indices, excluding the final path vertex, at which an outside vertex is
adjacent to an endpoint path. -/
noncomputable def endpointPathNeighborIndices
    {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 2) → V) (x : V) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦ G.Adj x (p i.castSucc)

@[simp] theorem mem_endpointPathNeighborIndices
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    {p : Fin (n + 2) → V} {x : V} {i : Fin (n + 1)} :
    i ∈ endpointPathNeighborIndices G p x ↔ G.Adj x (p i.castSucc) := by
  classical
  simp [endpointPathNeighborIndices]

/-- If the complementary color has no clique of order `2s+1`, an outside
vertex has at most `2s` neighbors among all path vertices except the last.
The successors of any larger family would be a complementary clique by the
rerouting lemma. -/
theorem card_endpointPathNeighborIndices_le
    {V : Type*} {G : SimpleGraph V} {n s : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p) {x : V}
    (hx : x ∉ Set.range p) (hfree : Gᶜ.CliqueFree (2 * s + 1)) :
    (endpointPathNeighborIndices G p x).card ≤ 2 * s := by
  classical
  let S := endpointPathNeighborIndices G p x
  change S.card ≤ 2 * s
  by_contra hle
  have hrS : 2 * s + 1 ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hrS
  let succEmbedding : Fin (n + 1) ↪ V :=
    ⟨fun i ↦ p i.succ, by
      intro i j hij
      have hs := hp.injective hij
      apply Fin.ext
      have hv := congrArg Fin.val hs
      simpa using hv⟩
  let K : Finset V := T.map succEmbedding
  have hKcard : K.card = 2 * s + 1 := by
    simpa [K] using hTcard
  have hKclique : Gᶜ.IsClique (K : Set V) := by
    intro y hy z hz hyz
    change y ∈ K at hy
    change z ∈ K at hz
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hz
    rw [SimpleGraph.compl_adj]
    refine ⟨hyz, ?_⟩
    intro hadj
    have hijne : i ≠ j := by
      intro hij
      subst j
      exact hyz rfl
    rcases lt_or_gt_of_ne hijne with hij | hji
    · exact (not_adj_successors_of_endpointUnextendable hp hmax hx hij
        (mem_endpointPathNeighborIndices.mp (hTS hiT))
        (mem_endpointPathNeighborIndices.mp (hTS hjT))) hadj
    · exact (not_adj_successors_of_endpointUnextendable hp hmax hx hji
        (mem_endpointPathNeighborIndices.mp (hTS hjT))
        (mem_endpointPathNeighborIndices.mp (hTS hiT))) hadj.symm
  apply hfree K
  rw [SimpleGraph.isNClique_iff]
  exact ⟨hKclique, hKcard⟩

/-- Path indices (again excluding the final path vertex) that are adjacent in
the complementary color to both specified vertices. -/
noncomputable def endpointPathCommonComplIndices
    {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 2) → V) (a b : V) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦
    Gᶜ.Adj a (p i.castSucc) ∧ Gᶜ.Adj b (p i.castSucc)

@[simp] theorem mem_endpointPathCommonComplIndices
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    {p : Fin (n + 2) → V} {a b : V} {i : Fin (n + 1)} :
    i ∈ endpointPathCommonComplIndices G p a b ↔
      Gᶜ.Adj a (p i.castSucc) ∧ Gᶜ.Adj b (p i.castSucc) := by
  classical
  simp [endpointPathCommonComplIndices]

/-- Two outside vertices have many common complementary neighbors on a long
unextendable path.  The loss of `4s` accounts for at most `2s` exceptional
indices for each endpoint. -/
theorem card_endpointPathCommonComplIndices_ge
    {V : Type*} {G : SimpleGraph V} {n s : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p) {a b : V}
    (ha : a ∉ Set.range p) (hb : b ∉ Set.range p)
    (hfree : Gᶜ.CliqueFree (2 * s + 1)) :
    n + 1 - 4 * s ≤ (endpointPathCommonComplIndices G p a b).card := by
  classical
  let A := endpointPathNeighborIndices G p a
  let B := endpointPathNeighborIndices G p b
  let Bad := A ∪ B
  let Good : Finset (Fin (n + 1)) := Finset.univ \ Bad
  have hA : A.card ≤ 2 * s := by
    exact card_endpointPathNeighborIndices_le hp hmax ha hfree
  have hB : B.card ≤ 2 * s := by
    exact card_endpointPathNeighborIndices_le hp hmax hb hfree
  have hBad : Bad.card ≤ 4 * s := by
    calc
      Bad.card ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ 4 * s := by omega
  have hsplit : Good.card + Bad.card = n + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (show Bad ⊆ (Finset.univ : Finset (Fin (n + 1))) from
        Finset.subset_univ Bad)
    simpa [Good] using h
  have hGood : n + 1 - 4 * s ≤ Good.card := by omega
  apply hGood.trans
  apply Finset.card_le_card
  intro i hi
  have hiBad : i ∉ Bad := (Finset.mem_sdiff.mp hi).2
  apply mem_endpointPathCommonComplIndices.mpr
  constructor
  · rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · intro hai
      apply ha
      exact ⟨i.castSucc, hai.symm⟩
    · intro hGa
      apply hiBad
      apply Finset.mem_union_left B
      exact mem_endpointPathNeighborIndices.mpr hGa
  · rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · intro hbi
      apply hb
      exact ⟨i.castSucc, hbi.symm⟩
    · intro hGb
      apply hiBad
      apply Finset.mem_union_right A
      exact mem_endpointPathNeighborIndices.mpr hGb

/-- Interleave outside vertices with selected path vertices.  There are
`r+2` outside vertices and `r+1` selected path vertices, hence `2r+3`
vertices in total. -/
def alternatingEndpointSequence
    {V : Type*} {n r : ℕ} (p : Fin (n + 2) → V)
    (w : Fin (r + 2) → V) (f : Fin (r + 1) → Fin (n + 1))
    (z : Fin (2 * r + 3)) : V :=
  if hz : z.val % 2 = 0 then
    w ⟨z.val / 2, by omega⟩
  else
    p (f ⟨z.val / 2, by omega⟩).castSucc

theorem alternatingEndpointSequence_injective
    {V : Type*} {n r : ℕ} {p : Fin (n + 2) → V}
    {w : Fin (r + 2) → V} {f : Fin (r + 1) → Fin (n + 1)}
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hf : Function.Injective f)
    (hout : ∀ i, w i ∉ Set.range p) :
    Function.Injective (alternatingEndpointSequence p w f) := by
  intro a b hab
  simp only [alternatingEndpointSequence] at hab
  split at hab <;> rename_i ha
  · split at hab <;> rename_i hb
    · have hq := congrArg Fin.val (hw hab)
      simp only [Fin.val_mk] at hq
      apply Fin.ext
      omega
    · exact (hout _ ⟨_, hab.symm⟩).elim
  · split at hab <;> rename_i hb
    · exact (hout _ ⟨_, hab⟩).elim
    · have hpidx := hp hab
      have hval := congrArg Fin.val hpidx
      have hbase :
          f ⟨a.val / 2, by omega⟩ = f ⟨b.val / 2, by omega⟩ := by
        apply Fin.ext
        simpa using hval
      have hfidx := hf hbase
      have hq := congrArg Fin.val hfidx
      simp only [Fin.val_mk] at hq
      apply Fin.ext
      omega

/-- Consecutive entries of the alternating sequence are complementary
edges whenever every selected path index is a common complementary neighbor
of the corresponding consecutive outside pair. -/
theorem alternatingEndpointSequence_adj
    {V : Type*} {G : SimpleGraph V} {n r : ℕ}
    {p : Fin (n + 2) → V} {w : Fin (r + 2) → V}
    {f : Fin (r + 1) → Fin (n + 1)}
    (hf : ∀ i, f i ∈ endpointPathCommonComplIndices G p
      (w i.castSucc) (w i.succ)) :
    ∀ a b : Fin (2 * r + 3), a.val + 1 = b.val →
      Gᶜ.Adj (alternatingEndpointSequence p w f a)
        (alternatingEndpointSequence p w f b) := by
  intro a b hab
  simp only [alternatingEndpointSequence]
  split <;> rename_i ha
  · split <;> rename_i hb
    · omega
    · let i : Fin (r + 1) := ⟨a.val / 2, by omega⟩
      have hwa : (⟨a.val / 2, by omega⟩ : Fin (r + 2)) = i.castSucc := by
        apply Fin.ext
        rfl
      have hfb : (⟨b.val / 2, by omega⟩ : Fin (r + 1)) = i := by
        apply Fin.ext
        simp only [i, Fin.val_mk]
        omega
      rw [hwa, hfb]
      exact (mem_endpointPathCommonComplIndices.mp (hf i)).1
  · split <;> rename_i hb
    · let i : Fin (r + 1) := ⟨a.val / 2, by omega⟩
      have hfa : (⟨a.val / 2, by omega⟩ : Fin (r + 1)) = i := by
        apply Fin.ext
        rfl
      have hwb : (⟨b.val / 2, by omega⟩ : Fin (r + 2)) = i.succ := by
        apply Fin.ext
        simp only [i, Fin.val_mk, Fin.val_succ]
        omega
      rw [hfa, hwb]
      exact (mem_endpointPathCommonComplIndices.mp (hf i)).2.symm
    · omega

@[simp] theorem alternatingEndpointSequence_zero
    {V : Type*} {n r : ℕ} (p : Fin (n + 2) → V)
    (w : Fin (r + 2) → V) (f : Fin (r + 1) → Fin (n + 1)) :
    alternatingEndpointSequence p w f 0 = w 0 := by
  simp [alternatingEndpointSequence]

@[simp] theorem alternatingEndpointSequence_last
    {V : Type*} {n r : ℕ} (p : Fin (n + 2) → V)
    (w : Fin (r + 2) → V) (f : Fin (r + 1) → Fin (n + 1)) :
    alternatingEndpointSequence p w f (Fin.last (2 * r + 2)) =
      w (Fin.last (r + 1)) := by
  unfold alternatingEndpointSequence
  split <;> rename_i hz
  · congr 1
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_last]
    omega
  · simp only [Fin.val_last] at hz
    omega

/-- A sufficiently long endpoint-unextendable path supplies a complementary
alternating path through any prescribed injective sequence of outside
vertices. -/
theorem exists_compl_path_between_outside_sequence
    {V : Type*} {G : SimpleGraph V} {n r : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p)
    (hlong : 5 * (r + 2) ≤ n + 2)
    (hfree : Gᶜ.CliqueFree (2 * (r + 2) + 1))
    (w : Fin (r + 2) → V) (hw : Function.Injective w)
    (hout : ∀ i, w i ∉ Set.range p) :
    ∃ q : Fin (2 * r + 3) → V,
      Function.Injective q ∧
      (∀ i j : Fin (2 * r + 3), i.val + 1 = j.val →
        Gᶜ.Adj (q i) (q j)) ∧
      q 0 = w 0 ∧ q (Fin.last (2 * r + 2)) = w (Fin.last (r + 1)) := by
  classical
  let A : Fin (r + 1) → Finset (Fin (n + 1)) := fun i ↦
    endpointPathCommonComplIndices G p (w i.castSucc) (w i.succ)
  have hAcard : ∀ i, r + 1 ≤ (A i).card := by
    intro i
    have hcommon := card_endpointPathCommonComplIndices_ge hp hmax
      (hout i.castSucc) (hout i.succ) hfree
    change r + 1 ≤ (endpointPathCommonComplIndices G p
      (w i.castSucc) (w i.succ)).card
    apply (show r + 1 ≤ n + 1 - 4 * (r + 2) by omega).trans
    exact hcommon
  obtain ⟨f, hfinj, hfmem⟩ :=
    exists_injective_mem_of_card_ge A hAcard
  let q := alternatingEndpointSequence p w f
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact alternatingEndpointSequence_injective hp.injective hw hfinj hout
  · exact alternatingEndpointSequence_adj hfmem
  · exact alternatingEndpointSequence_zero p w f
  · exact alternatingEndpointSequence_last p w f

/-- In the absence of the complementary odd cycle, the first and last
vertices of every sufficiently large outside sequence must be adjacent in
the path color. -/
theorem endpointPath_outside_endpoints_adj
    {V : Type*} {G : SimpleGraph V} {n r : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p)
    (hlong : 5 * (r + 2) ≤ n + 2)
    (hcycle : ¬ SimpleGraph.cycleGraph (2 * r + 3) ⊑ Gᶜ)
    (w : Fin (r + 2) → V) (hw : Function.Injective w)
    (hout : ∀ i, w i ∉ Set.range p) :
    G.Adj (w 0) (w (Fin.last (r + 1))) := by
  have hfree : Gᶜ.CliqueFree (2 * (r + 2) + 1) := by
    by_contra hnfree
    apply hcycle
    have hsmallTop : SimpleGraph.cycleGraph (2 * r + 3) ⊑
        SimpleGraph.completeGraph (Fin (2 * (r + 2) + 1)) := by
      rw [SimpleGraph.isContained_top_iff]
      exact ⟨
        ⟨fun i ↦ ⟨i.val, by omega⟩, by
          intro i j hij
          apply Fin.ext
          have hv := congrArg Fin.val hij
          simpa using hv⟩⟩
    exact hsmallTop.trans
      ((SimpleGraph.not_cliqueFree_iff_top_isContained
        (2 * (r + 2) + 1)).mp hnfree)
  obtain ⟨q, hqinj, hqadj, hq0, hqlast⟩ :=
    exists_compl_path_between_outside_sequence hp hmax hlong hfree w hw hout
  by_contra hnot
  have hwrap : Gᶜ.Adj (w 0) (w (Fin.last (r + 1))) := by
    rw [SimpleGraph.compl_adj]
    refine ⟨?_, hnot⟩
    intro heq
    have hind := hw heq
    have hval := congrArg Fin.val hind
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  apply hcycle
  apply cycleGraph_isContained_of_sequence q hqinj hqadj
  intro i j hi hj
  have hi0 : i = 0 := Fin.ext hi
  have hjlast : j = Fin.last (2 * r + 2) := Fin.ext (by
    simp only [Fin.val_last]
    omega)
  subst i
  subst j
  rw [hq0, hqlast]
  exact hwrap

/-- Every sufficiently large finite set outside an endpoint-unextendable
path is a clique in the path color. -/
theorem endpointPath_outside_finset_isClique
    {V : Type*} {G : SimpleGraph V} {n r : ℕ}
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p)
    (hlong : 5 * (r + 2) ≤ n + 2)
    (hcycle : ¬ SimpleGraph.cycleGraph (2 * r + 3) ⊑ Gᶜ)
    {U : Finset V} (hout : ∀ x ∈ U, x ∉ Set.range p)
    (hUcard : r + 2 ≤ U.card) :
    G.IsClique (U : Set V) := by
  classical
  intro a ha b hb hab
  change a ∈ U at ha
  change b ∈ U at hb
  obtain ⟨w, hwinj, hwU, hw0, hwlast⟩ :=
    exists_injective_sequence_with_endpoints ha hb hab hUcard
  rw [← hw0, ← hwlast]
  exact endpointPath_outside_endpoints_adj hp hmax hlong hcycle w hwinj
    (fun i ↦ hout (w i) (hwU i))

end Erdos570
