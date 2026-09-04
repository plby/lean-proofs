/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.RegularPair

open Finset Fintype SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- A local spelling of the standard typical-vertex estimate.  This is the
single-pair counting input used in Zhao's Proposition 4.5 and in every greedy
regular-pair embedding argument. -/
theorem card_lowDegreeVertices_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {rho : ℝ} {C D S T : Finset V}
    (hunif : G.IsUniform rho C D)
    (hSC : S ⊆ C) (hTD : T ⊆ D)
    (_hS : rho * #C ≤ #S) (hT : rho * #D ≤ #T) :
    (({x ∈ S | (#({y ∈ T | G.Adj x y}) : ℝ) <
        (G.edgeDensity C D - rho) * #T} : Finset V).card : ℝ) ≤ rho * #C := by
  classical
  let bad : Finset V := {x ∈ S | (#({y ∈ T | G.Adj x y}) : ℝ) <
    (G.edgeDensity C D - rho) * #T}
  change (#bad : ℝ) ≤ rho * #C
  by_contra! hbad
  have hbadLarge : (#C : ℝ) * rho ≤ #bad := by
    rw [mul_comm]
    exact hbad.le
  have hbadSub : bad ⊆ C := (filter_subset _ _).trans hSC
  have hTLarge : (#D : ℝ) * rho ≤ #T := by simpa [mul_comm] using hT
  have hunifBad : |(G.edgeDensity bad T : ℝ) - G.edgeDensity C D| < rho :=
    hunif hbadSub hTD hbadLarge hTLarge
  have hbadNe : bad.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hbad
    have hrho : 0 < rho := hunif.pos
    have hC0 : 0 ≤ (#C : ℝ) := by positivity
    norm_num at hbad
    nlinarith [mul_nonneg hrho.le hC0]
  have hboundPos : 0 < (G.edgeDensity C D - rho) * (#T : ℝ) := by
    obtain ⟨x, hxbad⟩ := hbadNe
    have hx := (mem_filter.1 hxbad).2
    exact (Nat.cast_nonneg _).trans_lt hx
  have hTpos : 0 < (#T : ℝ) := by
    by_contra h
    have : (#T : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [this, mul_zero] at hboundPos
    exact lt_irrefl 0 hboundPos
  have hthreshold : 0 ≤ (G.edgeDensity C D : ℝ) - rho :=
    nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hboundPos.le) hTpos
  have hinteredges :
      (#(Rel.interedges G.Adj bad T) : ℝ) ≤
        (#bad : ℝ) * #T * (G.edgeDensity C D - rho) := by
    refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq
      (Rel.interedges_eq_biUnion _)).trans card_biUnion_le).trans ?_
    simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc,
      mul_comm (#T : ℝ)]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le
  have hdensity : (G.edgeDensity bad T : ℝ) ≤ G.edgeDensity C D - rho := by
    rw [edgeDensity_def]
    push_cast
    refine div_le_of_le_mul₀ (by positivity) hthreshold ?_
    rw [mul_comm]
    exact hinteredges
  rw [abs_sub_lt_iff] at hunifBad
  linarith

/-- Vertices of `C` whose degree into `D` is below the regular-pair
threshold. -/
def atypicalVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (rho : ℝ) (C D : Finset V) : Finset V :=
  {x ∈ C | (#({y ∈ D | G.Adj x y}) : ℝ) <
    (G.edgeDensity C D - rho) * #D}

/-- The cleaned side of a regular pair, obtained by deleting its atypical
vertices. -/
def cleanedSide (G : SimpleGraph V) [DecidableRel G.Adj]
    (rho : ℝ) (C D : Finset V) : Finset V :=
  C \ atypicalVertices G rho C D

theorem card_atypicalVertices_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {rho : ℝ} {C D : Finset V}
    (hunif : G.IsUniform rho C D) (hrho : rho ≤ 1) :
    (#(atypicalVertices G rho C D) : ℝ) ≤ rho * #C := by
  have hC : rho * (#C : ℝ) ≤ #C := by
    nlinarith [hunif.pos.le, (Nat.cast_nonneg (#C) : (0 : ℝ) ≤ #C)]
  have hD : rho * (#D : ℝ) ≤ #D := by
    nlinarith [hunif.pos.le, (Nat.cast_nonneg (#D) : (0 : ℝ) ≤ #D)]
  simpa [atypicalVertices] using
    card_lowDegreeVertices_le G hunif (Finset.Subset.rfl) (Finset.Subset.rfl)
      hC hD

/-- Removing `bad` vertices costs at most `#bad` neighbors.  This elementary
finite-set estimate is the bookkeeping step used after the atypical-vertex
bound. -/
theorem card_neighbors_cleaned_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X bad : Finset V) (v : V) (k : ℕ)
    (hdeg : k + #bad ≤ #(X.filter (G.Adj v))) :
    k ≤ #((X \ bad).filter (G.Adj v)) := by
  have hsub : X.filter (G.Adj v) ⊆
      (X \ bad).filter (G.Adj v) ∪ bad := by
    intro w hw
    by_cases hbad : w ∈ bad
    · exact mem_union_right _ hbad
    · apply mem_union_left
      rw [mem_filter, mem_sdiff]
      exact ⟨⟨(mem_filter.mp hw).1, hbad⟩, (mem_filter.mp hw).2⟩
  have hc : #(X.filter (G.Adj v)) ≤
      #((X \ bad).filter (G.Adj v)) + #bad :=
    (card_le_card hsub).trans (card_union_le _ _)
  omega

/-- The inductive core of a root-preserving greedy tree embedding.  Non-root
vertices are sent to the candidate set indexed by their color.  The root may
lie outside those candidate sets. -/
private theorem exists_rooted_colored_copy_aux
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card A = n + 1) (hT : T.IsTree)
    (root : A) (color : A → Fin 2)
    (hcolor : ∀ ⦃a b⦄, T.Adj a b → color a ≠ color b)
    (candidate : Fin 2 → Finset B) (rootImage : B)
    (hroot : ∀ j, j ≠ color root →
      Fintype.card A ≤ #{w ∈ candidate j | G.Adj rootImage w})
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ candidate i,
      Fintype.card A ≤ #{w ∈ candidate j | G.Adj v w}) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root → f a ∈ candidate (color a) := by
  classical
  induction n generalizing A with
  | zero =>
      have hsub : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let F : A → B := fun _ ↦ rootImage
      have hF_inj : Function.Injective F := fun a b _ ↦ hsub.elim a b
      let f : T.Copy G :=
        ⟨⟨F, fun {a b} hab ↦ False.elim (T.ne_of_adj hab (hsub.elim a b))⟩, hF_inj⟩
      refine ⟨f, rfl, ?_⟩
      intro a ha
      exact False.elim (ha (hsub.elim a root))
  | succ n ih =>
      have hcard_large : 1 < Fintype.card A := by omega
      have hnontrivial : Nontrivial A :=
        Fintype.one_lt_card_iff_nontrivial.mp hcard_large
      let : Nontrivial A := hnontrivial
      obtain ⟨x₀, x₁, hxne, hx₀deg, hx₁deg⟩ :=
        hT.exists_ne_and_degree_eq_one
      obtain ⟨x, hxroot, hxdeg⟩ : ∃ x : A, x ≠ root ∧ T.degree x = 1 := by
        by_cases h : x₀ = root
        · exact ⟨x₁, fun h' ↦ hxne (h.trans h'.symm), hx₁deg⟩
        · exact ⟨x₀, h, hx₀deg⟩
      obtain ⟨parent, hxparent, hparent_unique⟩ :=
        degree_eq_one_iff_existsUnique_adj.mp hxdeg
      let s : Set A := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let root' : s := ⟨root, by simpa [s] using hxroot.symm⟩
      let color' : s → Fin 2 := fun a ↦ color a
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : A ↦ a = x)
        change Fintype.card {a : A // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree := by
        exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
          hT.isAcyclic.induce s⟩
      have hcolor' : ∀ ⦃a b : s⦄, T'.Adj a b → color' a ≠ color' b := by
        intro a b hab
        exact hcolor (by simpa [T', color'] using hab)
      have hroot' : ∀ j, j ≠ color' root' →
          Fintype.card s ≤ #{w ∈ candidate j | G.Adj rootImage w} := by
        intro j hj
        apply (show Fintype.card s ≤ Fintype.card A by omega).trans
        exact hroot j (by simpa [root', color'] using hj)
      have hcross' : ∀ i j, i ≠ j → ∀ v ∈ candidate i,
          Fintype.card s ≤ #{w ∈ candidate j | G.Adj v w} := by
        intro i j hij v hv
        exact (show Fintype.card s ≤ Fintype.card A by omega).trans
          (hcross i j hij v hv)
      obtain ⟨f, hfroot, hfmem⟩ :=
        ih T' hcard' hT' root' color' hcolor' hroot' hcross'
      let parent' : s := ⟨parent, by simpa [s] using hxparent.ne'⟩
      let choices : Finset B :=
        (candidate (color x)).filter (G.Adj (f parent'))
      have hcolor_parent : color parent ≠ color x := hcolor hxparent.symm
      have hchoices : Fintype.card A ≤ #choices := by
        by_cases hp : parent = root
        · subst parent
          have hfp : f parent' = rootImage := by
            simpa [parent', root'] using hfroot
          change Fintype.card A ≤
            #((candidate (color x)).filter (G.Adj (f parent')))
          rw [hfp]
          exact hroot (color x) hcolor_parent.symm
        · have hpmem : f parent' ∈ candidate (color parent) := by
            have := hfmem parent' (by
              intro h
              apply hp
              exact Subtype.ext_iff.mp h)
            simpa [parent', color'] using this
          exact hcross (color parent) (color x) hcolor_parent (f parent') hpmem
      let used : Finset B := univ.image f
      have hused : #used = Fintype.card s := by
        exact Finset.card_image_iff.mpr fun _ _ _ _ h ↦ f.injective h
      have hused_lt : #used < #choices := by omega
      obtain ⟨w, hwchoices, hwunused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hused_lt
      have hwmem : w ∈ candidate (color x) := (mem_filter.mp hwchoices).1
      have hwadj : G.Adj (f parent') w := (mem_filter.mp hwchoices).2
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        apply hwunused
        exact mem_image.mpr ⟨a, mem_univ a, hwa.symm⟩
      let F : A → B := fun a ↦ if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      have hF_adj : ∀ ⦃a b⦄, T.Adj a b → G.Adj (F a) (F b) := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          have hbp : b = parent := hparent_unique b hab
          subst b
          simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj.symm
        · by_cases hb : b = x
          · subst b
            have hap : a = parent := hparent_unique a hab.symm
            subst a
            simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj
          · let a' : s := ⟨a, by simpa [s] using ha⟩
            let b' : s := ⟨b, by simpa [s] using hb⟩
            have hab' : T'.Adj a' b' := by simpa [T', a', b'] using hab
            have hmap := f.toHom.map_rel hab'
            simpa [F, ha, hb, a', b'] using hmap
      have hF_inj : Function.Injective F := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          by_cases hb : b = x
          · exact hb.symm
          · exfalso
            apply hw_not_range ⟨b, by simpa [s] using hb⟩
            simpa [F, hb] using hab
        · by_cases hb : b = x
          · subst b
            exfalso
            apply hw_not_range ⟨a, by simpa [s] using ha⟩
            simpa [F, ha] using hab.symm
          · have hsub : (⟨a, by simpa [s] using ha⟩ : s) =
                ⟨b, by simpa [s] using hb⟩ := by
              apply f.injective
              simpa [F, ha, hb] using hab
            exact Subtype.ext_iff.mp hsub
      let f' : T.Copy G := ⟨⟨F, by
        intro a b hab
        exact hF_adj hab⟩, hF_inj⟩
      refine ⟨f', ?_, ?_⟩
      · change F root = rootImage
        simp only [F, dif_neg hxroot.symm]
        simpa [root'] using hfroot
      · intro a haroot
        by_cases ha : a = x
        · subst a
          simpa [f', F] using hwmem
        · have hsub_ne : (⟨a, by simpa [s] using ha⟩ : s) ≠ root' := by
            intro h
            apply haroot
            exact Subtype.ext_iff.mp h
          have := hfmem ⟨a, by simpa [s] using ha⟩ hsub_ne
          simpa [f', F, ha, color'] using this

/-- A root-preserving greedy embedding theorem for any proper two-coloring of
a finite tree.  The cardinal assumptions are deliberately expressed as
candidate counts, so the regularity consequences can be applied directly. -/
theorem exists_rooted_colored_copy
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (root : A) (color : A → Fin 2)
    (hcolor : ∀ ⦃a b⦄, T.Adj a b → color a ≠ color b)
    (candidate : Fin 2 → Finset B) (rootImage : B)
    (hroot : ∀ j, j ≠ color root →
      Fintype.card A ≤ #{w ∈ candidate j | G.Adj rootImage w})
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ candidate i,
      Fintype.card A ≤ #{w ∈ candidate j | G.Adj v w}) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root → f a ∈ candidate (color a) := by
  apply exists_rooted_colored_copy_aux T G (Fintype.card A - 1)
  · have hpos : 0 < Fintype.card A :=
      Fintype.card_pos_iff.mpr hT.connected.nonempty
    omega
  · exact hT
  · exact hcolor
  · exact hroot
  · exact hcross

/-- The canonical rooted two-coloring of a tree colors its root by `0`. -/
@[simp] theorem coloringTwoOfVert_root
    {A : Type*} [Fintype A] (T : SimpleGraph A) (hT : T.IsTree) (root : A) :
    hT.coloringTwoOfVert root root = 0 := by
  change (⟨T.dist root root % 2, _⟩ : Fin 2) = 0
  apply Fin.eq_of_val_eq
  simp

/-- A root-preserving greedy embedding using Mathlib's canonical bipartition of
the tree.  This is the form used after deleting the atypical vertices of a
regular pair: `candidate 0` and `candidate 1` are the two cleaned clusters,
and `hcross` is the residual minimum-degree estimate. -/
theorem exists_rooted_tree_copy
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (root : A)
    (candidate : Fin 2 → Finset B) (rootImage : B)
    (hroot : Fintype.card A ≤
      #{w ∈ candidate 1 | G.Adj rootImage w})
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ candidate i,
      Fintype.card A ≤ #{w ∈ candidate j | G.Adj v w}) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root → f a ∈ candidate (hT.coloringTwoOfVert root a) := by
  apply exists_rooted_colored_copy T G hT root (hT.coloringTwoOfVert root)
  · intro a b hab
    exact (hT.coloringTwoOfVert root).valid hab
  · intro j hj
    have hj0 : j ≠ 0 := by simpa using hj
    have hj1 : j = 1 := by
      apply Fin.eq_of_val_eq
      have hjval : j.val ≠ 0 := by
        intro h
        apply hj0
        apply Fin.eq_of_val_eq
        simpa using h
      omega
    simpa [hj1] using hroot
  · exact hcross

/-- A regular-pair version of the greedy tree embedding theorem.  Both sides
are first cleaned by deleting the vertices below the usual
`density - rho` threshold.  The two capacity inequalities ensure that a
typical vertex still has `card A` available neighbors after the atypical
vertices on the other side have been deleted. -/
theorem exists_rooted_tree_copy_of_uniform
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (root : A) (rootImage : B)
    {rho : ℝ} {X Y : Finset B}
    (hunif : G.IsUniform rho X Y) (hrho : rho ≤ 1)
    (hcapX : (Fintype.card A : ℝ) + rho * #X ≤
      (G.edgeDensity X Y - rho) * #X)
    (hcapY : (Fintype.card A : ℝ) + rho * #Y ≤
      (G.edgeDensity X Y - rho) * #Y)
    (hroot : (Fintype.card A : ℝ) + rho * #Y ≤
      (#(Y.filter (G.Adj rootImage)) : ℝ)) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root →
        f a ∈ if hT.coloringTwoOfVert root a = 0 then
          cleanedSide G rho X Y else cleanedSide G rho Y X := by
  classical
  let badX := atypicalVertices G rho X Y
  let badY := atypicalVertices G rho Y X
  let goodX := X \ badX
  let goodY := Y \ badY
  have hbadX : (#badX : ℝ) ≤ rho * #X := by
    simpa [badX] using card_atypicalVertices_le G hunif hrho
  have hbadY : (#badY : ℝ) ≤ rho * #Y := by
    simpa [badY] using card_atypicalVertices_le G hunif.symm hrho
  have hrootReal : (Fintype.card A : ℝ) + #badY ≤
      (#(Y.filter (G.Adj rootImage)) : ℝ) := by
    linarith
  have hrootNat : Fintype.card A + #badY ≤
      #(Y.filter (G.Adj rootImage)) := by
    exact_mod_cast hrootReal
  have hrootGood : Fintype.card A ≤
      #(goodY.filter (G.Adj rootImage)) := by
    simpa [goodY] using
      card_neighbors_cleaned_ge G Y badY rootImage (Fintype.card A) hrootNat
  have hXY : ∀ v ∈ goodX,
      Fintype.card A ≤ #(goodY.filter (G.Adj v)) := by
    intro v hv
    have hv' : v ∈ X \ badX := by simpa [goodX] using hv
    have hvX : v ∈ X := (mem_sdiff.mp hv').1
    have hvnot : v ∉ badX := (mem_sdiff.mp hv').2
    have hvdeg : (G.edgeDensity X Y - rho) * (#Y : ℝ) ≤
        (#(Y.filter (G.Adj v)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      apply hvnot
      simpa [badX, atypicalVertices, hvX, hlt]
    have hvReal : (Fintype.card A : ℝ) + #badY ≤
        (#(Y.filter (G.Adj v)) : ℝ) := by
      calc
        (Fintype.card A : ℝ) + #badY ≤
            (Fintype.card A : ℝ) + rho * #Y := by gcongr
        _ ≤ (G.edgeDensity X Y - rho) * #Y := hcapY
        _ ≤ (#(Y.filter (G.Adj v)) : ℝ) := hvdeg
    have hvNat : Fintype.card A + #badY ≤
        #(Y.filter (G.Adj v)) := by
      exact_mod_cast hvReal
    simpa [goodY] using
      card_neighbors_cleaned_ge G Y badY v (Fintype.card A) hvNat
  have hYX : ∀ v ∈ goodY,
      Fintype.card A ≤ #(goodX.filter (G.Adj v)) := by
    intro v hv
    have hv' : v ∈ Y \ badY := by simpa [goodY] using hv
    have hvY : v ∈ Y := (mem_sdiff.mp hv').1
    have hvnot : v ∉ badY := (mem_sdiff.mp hv').2
    have hvdeg : (G.edgeDensity X Y - rho) * (#X : ℝ) ≤
        (#(X.filter (G.Adj v)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      apply hvnot
      have hlt' : (#(X.filter (G.Adj v)) : ℝ) <
          (G.edgeDensity Y X - rho) * #X := by
        simpa [G.edgeDensity_comm X Y] using hlt
      simpa [badY, atypicalVertices, hvY, hlt']
    have hvReal : (Fintype.card A : ℝ) + #badX ≤
        (#(X.filter (G.Adj v)) : ℝ) := by
      calc
        (Fintype.card A : ℝ) + #badX ≤
            (Fintype.card A : ℝ) + rho * #X := by gcongr
        _ ≤ (G.edgeDensity X Y - rho) * #X := hcapX
        _ ≤ (#(X.filter (G.Adj v)) : ℝ) := hvdeg
    have hvNat : Fintype.card A + #badX ≤
        #(X.filter (G.Adj v)) := by
      exact_mod_cast hvReal
    simpa [goodX] using
      card_neighbors_cleaned_ge G X badX v (Fintype.card A) hvNat
  let candidate : Fin 2 → Finset B := fun i ↦ if i = 0 then goodX else goodY
  have fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
    by_cases hi : i = 0
    · exact Or.inl hi
    · right
      apply Fin.eq_of_val_eq
      have hiVal : i.val ≠ 0 := by
        intro h
        apply hi
        apply Fin.eq_of_val_eq
        simpa using h
      omega
  obtain ⟨f, hfroot, hfmem⟩ :=
    exists_rooted_tree_copy T G hT root candidate rootImage (by
      simpa [candidate] using hrootGood) (by
      intro i j hij v hv
      rcases fin_two_cases i with rfl | rfl <;>
        rcases fin_two_cases j with rfl | rfl
      · exact False.elim (hij rfl)
      · simpa [candidate] using hXY v (by simpa [candidate] using hv)
      · simpa [candidate] using hYX v (by simpa [candidate] using hv)
      · exact False.elim (hij rfl))
  refine ⟨f, hfroot, ?_⟩
  intro a ha
  have hm := hfmem a ha
  by_cases hc : hT.coloringTwoOfVert root a = 0
  · simpa [candidate, hc, goodX, badX, cleanedSide] using hm
  · simpa [candidate, hc, goodY, badY, cleanedSide] using hm

/-! ### Ordered rooted forests -/

/-- An ordered rooted forest is represented as an ordered finite family of
finite rooted trees.  Using `Fin m` as the component index makes the order
part of the data, as in Zhao's definition of an ordered small-tree forest. -/
structure OrderedRootedForest (m : ℕ) where
  size : Fin m → ℕ
  tree : (i : Fin m) → SimpleGraph (Fin (size i))
  isTree : ∀ i, (tree i).IsTree
  root : (i : Fin m) → Fin (size i)

namespace OrderedRootedForest

variable {m : ℕ}

/-- The total number of vertices in an ordered rooted forest. -/
def order (F : OrderedRootedForest m) : ℕ := ∑ i, F.size i

/-- Delete the first component of a nonempty ordered forest. -/
def tail {m : ℕ} (F : OrderedRootedForest (m + 1)) :
    OrderedRootedForest m where
  size i := F.size i.succ
  tree i := F.tree i.succ
  isTree i := F.isTree i.succ
  root i := F.root i.succ

@[simp] theorem order_tail_add_head {m : ℕ}
    (F : OrderedRootedForest (m + 1)) :
    F.size 0 + F.tail.order = F.order := by
  simp [order, tail, Fin.sum_univ_succ]

/-- A simultaneous embedding of all components.  The additional global
injectivity condition says that copies of distinct components are disjoint. -/
structure Embedding (F : OrderedRootedForest m) {B : Type*}
    (G : SimpleGraph B) where
  copy : ∀ i, (F.tree i).Copy G
  injective : Function.Injective fun z : Σ i, Fin (F.size i) ↦ copy z.1 z.2

theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases hi : i = 0
  · exact Or.inl hi
  · right
    apply Fin.eq_of_val_eq
    have hiVal : i.val ≠ 0 := by
      intro h
      apply hi
      apply Fin.eq_of_val_eq
      simpa using h
    omega

/-- Assemble independently embedded rooted trees into one forest embedding.
The candidate blocks assigned to different components are disjoint, and all
root images lie outside every candidate block.  These are exactly the
separation invariants maintained by the allocation steps in Zhao 5.4/5.8. -/
theorem embedding_of_component_copies
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B)
    (rootImage : Fin m → B)
    (candidate : Fin m → Fin 2 → Finset B)
    (f : ∀ i, (F.tree i).Copy G)
    (hfroot : ∀ i, f i (F.root i) = rootImage i)
    (hfmem : ∀ i a, a ≠ F.root i →
      f i a ∈ candidate i ((F.isTree i).coloringTwoOfVert (F.root i) a))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i k j, rootImage i ∉ candidate k j)
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint (candidate i 0 ∪ candidate i 1)
        (candidate k 0 ∪ candidate k 1)) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈ candidate i
          ((F.isTree i).coloringTwoOfVert (F.root i) a) := by
  classical
  have hinjective : Function.Injective
      (fun z : Σ i, Fin (F.size i) ↦ f z.1 z.2) := by
    rintro ⟨i, a⟩ ⟨k, b⟩ hxy
    dsimp only at hxy
    by_cases hik : i = k
    · subst k
      have hval : a = b := (f i).injective hxy
      subst b
      rfl
    · by_cases hxroot : a = F.root i
      · by_cases hyroot : b = F.root k
        · have himage : rootImage i = rootImage k := by
            simpa [hxroot, hyroot, hfroot] using hxy
          exact False.elim (hik (hrootInjective himage))
        · have hymem := hfmem k b hyroot
          have hout := hrootOutside i k
            ((F.isTree k).coloringTwoOfVert (F.root k) b)
          apply False.elim
          apply hout
          rw [← hfroot i, ← hxroot, hxy]
          exact hymem
      · by_cases hyroot : b = F.root k
        · have hxmem := hfmem i a hxroot
          have hout := hrootOutside k i
            ((F.isTree i).coloringTwoOfVert (F.root i) a)
          apply False.elim
          apply hout
          rw [← hfroot k, ← hyroot, ← hxy]
          exact hxmem
        · have hxmem := hfmem i a hxroot
          have hymem := hfmem k b hyroot
          have hxUnion : f i a ∈ candidate i 0 ∪ candidate i 1 := by
            rcases fin_two_eq_zero_or_one
                ((F.isTree i).coloringTwoOfVert (F.root i) a) with hc | hc
            · rw [hc] at hxmem
              exact mem_union_left _ hxmem
            · rw [hc] at hxmem
              exact mem_union_right _ hxmem
          have hyUnion : f k b ∈ candidate k 0 ∪ candidate k 1 := by
            rcases fin_two_eq_zero_or_one
                ((F.isTree k).coloringTwoOfVert (F.root k) b) with hc | hc
            · rw [hc] at hymem
              exact mem_union_left _ hymem
            · rw [hc] at hymem
              exact mem_union_right _ hymem
          have hd := Finset.disjoint_left.mp (hdisjoint i k hik) hxUnion
          exact False.elim (hd (hxy ▸ hyUnion))
  let E : F.Embedding G := ⟨f, hinjective⟩
  exact ⟨E, hfroot, hfmem⟩

/-- Embed an ordered rooted forest after an allocator has assigned a disjoint
pair of candidate blocks to each component.  All numerical hypotheses are
explicit minimum-degree/capacity inequalities. -/
theorem exists_embedding_of_disjoint_candidates
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B)
    (candidate : Fin m → Fin 2 → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i k j, rootImage i ∉ candidate k j)
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint (candidate i 0 ∪ candidate i 1)
        (candidate k 0 ∪ candidate k 1))
    (hrootDegree : ∀ i, F.size i ≤
      #{w ∈ candidate i 1 | G.Adj (rootImage i) w})
    (hcross : ∀ i c d, c ≠ d → ∀ v ∈ candidate i c,
      F.size i ≤ #{w ∈ candidate i d | G.Adj v w}) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈ candidate i
          ((F.isTree i).coloringTwoOfVert (F.root i) a) := by
  classical
  have hex : ∀ i, ∃ f : (F.tree i).Copy G,
      f (F.root i) = rootImage i ∧
      ∀ a, a ≠ F.root i →
        f a ∈ candidate i
          ((F.isTree i).coloringTwoOfVert (F.root i) a) := by
    intro i
    apply exists_rooted_tree_copy (F.tree i) G (F.isTree i)
      (F.root i) (candidate i) (rootImage i)
    · simpa using hrootDegree i
    · intro c d hcd v hv
      simpa using hcross i c d hcd v hv
  let f : ∀ i, (F.tree i).Copy G := fun i ↦ (hex i).choose
  have hfroot : ∀ i, f i (F.root i) = rootImage i := fun i ↦ (hex i).choose_spec.1
  have hfmem : ∀ i a, a ≠ F.root i →
      f i a ∈ candidate i
        ((F.isTree i).coloringTwoOfVert (F.root i) a) :=
    fun i ↦ (hex i).choose_spec.2
  exact embedding_of_component_copies F G rootImage candidate f hfroot hfmem
    hrootInjective hrootOutside hdisjoint

/-- Ordered-forest embedding into one shared candidate pair.  The total
forest order is used as a reserve: after each component is embedded, deleting
its image leaves enough degree for the tail of the ordered forest. -/
theorem exists_embedding_in_shared_candidates
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B) (candidate : Fin 2 → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i c, rootImage i ∉ candidate c)
    (hrootDegree : ∀ i, F.order ≤
      #{w ∈ candidate 1 | G.Adj (rootImage i) w})
    (hcross : ∀ c d, c ≠ d → ∀ v ∈ candidate c,
      F.order ≤ #{w ∈ candidate d | G.Adj v w}) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈ candidate
          ((F.isTree i).coloringTwoOfVert (F.root i) a) := by
  classical
  induction m generalizing candidate with
  | zero =>
      let copies : ∀ i : Fin 0, (F.tree i).Copy G := fun i ↦ Fin.elim0 i
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩
        exact Fin.elim0 i
      let E : F.Embedding G := ⟨copies, hinjective⟩
      refine ⟨E, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      let Ftail : OrderedRootedForest m := F.tail
      let rootImageTail : Fin m → B := fun i ↦ rootImage i.succ
      have hhead_le : F.size 0 ≤ F.order := by
        rw [← F.order_tail_add_head]
        omega
      obtain ⟨fhead, hfheadRoot, hfheadMem⟩ :=
        exists_rooted_tree_copy (F.tree 0) G (F.isTree 0) (F.root 0)
          candidate (rootImage 0) (by
            simpa using hhead_le.trans (hrootDegree 0)) (by
            intro c d hcd v hv
            simpa using hhead_le.trans (hcross c d hcd v hv))
      let used : Finset B := univ.image fhead
      have husedCard : #used = F.size 0 := by
        rw [show #used = Fintype.card (Fin (F.size 0)) by
          exact card_image_iff.mpr fun _ _ _ _ h ↦ fhead.injective h]
        simp
      have htail_add_used : Ftail.order + #used = F.order := by
        rw [husedCard]
        simpa [Ftail, add_comm] using F.order_tail_add_head
      let candidateTail : Fin 2 → Finset B := fun c ↦ candidate c \ used
      have htailRootInjective : Function.Injective rootImageTail := by
        intro i k h
        exact Fin.succ_inj.mp (hrootInjective h)
      have htailRootOutside : ∀ i c, rootImageTail i ∉ candidateTail c := by
        intro i c h
        exact hrootOutside i.succ c (mem_sdiff.mp h).1
      have htailRootDegree : ∀ i, Ftail.order ≤
          #{w ∈ candidateTail 1 | G.Adj (rootImageTail i) w} := by
        intro i
        apply card_neighbors_cleaned_ge G (candidate 1) used (rootImageTail i)
          Ftail.order
        rw [htail_add_used]
        exact hrootDegree i.succ
      have htailCross : ∀ c d, c ≠ d → ∀ v ∈ candidateTail c,
          Ftail.order ≤ #{w ∈ candidateTail d | G.Adj v w} := by
        intro c d hcd v hv
        apply card_neighbors_cleaned_ge G (candidate d) used v Ftail.order
        rw [htail_add_used]
        exact hcross c d hcd v (mem_sdiff.mp hv).1
      obtain ⟨Etail, hEtailRoot, hEtailMem⟩ :=
        ih Ftail rootImageTail candidateTail htailRootInjective
          htailRootOutside htailRootDegree htailCross
      have hheadTailDisjoint : ∀ a i b, fhead a ≠ Etail.copy i b := by
        intro a i b hab
        by_cases hbroot : b = Ftail.root i
        · by_cases haroot : a = F.root 0
          · have htailRoot : Etail.copy i b = rootImage i.succ := by
              rw [hbroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            have himage : rootImage 0 = rootImage i.succ := by
              rw [← hfheadRoot, ← haroot, ← htailRoot]
              exact hab
            have hindex : (0 : Fin (m + 1)) = i.succ := hrootInjective himage
            have hval := congrArg Fin.val hindex
            simp at hval
          · have hamem := hfheadMem a haroot
            apply hrootOutside i.succ
              ((F.isTree 0).coloringTwoOfVert (F.root 0) a)
            have htailRoot : Etail.copy i b = rootImage i.succ := by
              rw [hbroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            rw [← htailRoot, ← hab]
            exact hamem
        · have hbmem := hEtailMem i b hbroot
          have hbunused : Etail.copy i b ∉ used :=
            (mem_sdiff.mp hbmem).2
          apply hbunused
          exact mem_image.mpr ⟨a, mem_univ a, hab⟩
      let copies : ∀ i, (F.tree i).Copy G :=
        Fin.cases fhead (fun i ↦ Etail.copy i)
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩ ⟨k, b⟩ hab
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change fhead a = fhead b at hab
            have : a = b := fhead.injective hab
            subst b
            rfl
          · change fhead a = Etail.copy k b at hab
            exact False.elim (hheadTailDisjoint a k b hab)
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change Etail.copy i a = fhead b at hab
            exact False.elim (hheadTailDisjoint b i a hab.symm)
          · have htail :
                (⟨i, a⟩ : Σ i, Fin (Ftail.size i)) = ⟨k, b⟩ := by
                apply Etail.injective
                change Etail.copy i a = Etail.copy k b at hab
                exact hab
            cases htail
            rfl
      let E : F.Embedding G := ⟨copies, hinjective⟩
      refine ⟨E, ?_, ?_⟩
      · intro i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · change fhead (F.root 0) = rootImage 0
          exact hfheadRoot
        · change Etail.copy i (F.root i.succ) = rootImage i.succ
          have hi := hEtailRoot i
          change Etail.copy i (F.root i.succ) = rootImage i.succ at hi
          exact hi
      · intro i a ha
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · change fhead a ∈ candidate
            ((F.isTree 0).coloringTwoOfVert (F.root 0) a)
          exact hfheadMem a ha
        · have ha' : a ≠ Ftail.root i := by
            change a ≠ F.root i.succ
            exact ha
          have hm := hEtailMem i a ha'
          change Etail.copy i a ∈ candidate
            ((F.isTree i.succ).coloringTwoOfVert (F.root i.succ) a)
          have hm' := (mem_sdiff.mp hm).1
          change Etail.copy i a ∈ candidate
            ((F.isTree i.succ).coloringTwoOfVert (F.root i.succ) a) at hm'
          exact hm'

/-- A Zhao-5.4-style ordered rooted forest embedding into one regular pair,
with the analytic/numerical assumptions stated explicitly.  The roots have
prescribed distinct images outside the pair.  The total forest order, rather
than the size of one component, is reserved at every greedy step. -/
theorem exists_embedding_in_uniform_pair
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B) {rho : ℝ} {X Y : Finset B}
    (hrootInjective : Function.Injective rootImage)
    (hunif : G.IsUniform rho X Y) (hrho : rho ≤ 1)
    (hcapX : (F.order : ℝ) + rho * #X ≤
      (G.edgeDensity X Y - rho) * #X)
    (hcapY : (F.order : ℝ) + rho * #Y ≤
      (G.edgeDensity X Y - rho) * #Y)
    (hrootDegree : ∀ i, (F.order : ℝ) + rho * #Y ≤
      (#(Y.filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i,
      rootImage i ∉ cleanedSide G rho X Y ∧
      rootImage i ∉ cleanedSide G rho Y X) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈
          if (F.isTree i).coloringTwoOfVert (F.root i) a = 0 then
            cleanedSide G rho X Y
          else cleanedSide G rho Y X := by
  classical
  let badX := atypicalVertices G rho X Y
  let badY := atypicalVertices G rho Y X
  let goodX := X \ badX
  let goodY := Y \ badY
  have hbadX : (#badX : ℝ) ≤ rho * #X := by
    simpa [badX] using card_atypicalVertices_le G hunif hrho
  have hbadY : (#badY : ℝ) ≤ rho * #Y := by
    simpa [badY] using card_atypicalVertices_le G hunif.symm hrho
  have hrootGood : ∀ i, F.order ≤
      #(goodY.filter (G.Adj (rootImage i))) := by
    intro i
    have hiReal : (F.order : ℝ) + #badY ≤
        (#(Y.filter (G.Adj (rootImage i))) : ℝ) := by
      linarith [hrootDegree i]
    have hiNat : F.order + #badY ≤
        #(Y.filter (G.Adj (rootImage i))) := by
      exact_mod_cast hiReal
    simpa [goodY] using
      card_neighbors_cleaned_ge G Y badY (rootImage i) F.order hiNat
  have hXY : ∀ v ∈ goodX,
      F.order ≤ #(goodY.filter (G.Adj v)) := by
    intro v hv
    have hv' : v ∈ X \ badX := by simpa [goodX] using hv
    have hvX : v ∈ X := (mem_sdiff.mp hv').1
    have hvnot : v ∉ badX := (mem_sdiff.mp hv').2
    have hvdeg : (G.edgeDensity X Y - rho) * (#Y : ℝ) ≤
        (#(Y.filter (G.Adj v)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      apply hvnot
      simpa [badX, atypicalVertices, hvX, hlt]
    have hvReal : (F.order : ℝ) + #badY ≤
        (#(Y.filter (G.Adj v)) : ℝ) := by
      calc
        (F.order : ℝ) + #badY ≤
            (F.order : ℝ) + rho * #Y := by gcongr
        _ ≤ (G.edgeDensity X Y - rho) * #Y := hcapY
        _ ≤ (#(Y.filter (G.Adj v)) : ℝ) := hvdeg
    have hvNat : F.order + #badY ≤ #(Y.filter (G.Adj v)) := by
      exact_mod_cast hvReal
    simpa [goodY] using
      card_neighbors_cleaned_ge G Y badY v F.order hvNat
  have hYX : ∀ v ∈ goodY,
      F.order ≤ #(goodX.filter (G.Adj v)) := by
    intro v hv
    have hv' : v ∈ Y \ badY := by simpa [goodY] using hv
    have hvY : v ∈ Y := (mem_sdiff.mp hv').1
    have hvnot : v ∉ badY := (mem_sdiff.mp hv').2
    have hvdeg : (G.edgeDensity X Y - rho) * (#X : ℝ) ≤
        (#(X.filter (G.Adj v)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      apply hvnot
      have hlt' : (#(X.filter (G.Adj v)) : ℝ) <
          (G.edgeDensity Y X - rho) * #X := by
        simpa [G.edgeDensity_comm X Y] using hlt
      simpa [badY, atypicalVertices, hvY, hlt']
    have hvReal : (F.order : ℝ) + #badX ≤
        (#(X.filter (G.Adj v)) : ℝ) := by
      calc
        (F.order : ℝ) + #badX ≤
            (F.order : ℝ) + rho * #X := by gcongr
        _ ≤ (G.edgeDensity X Y - rho) * #X := hcapX
        _ ≤ (#(X.filter (G.Adj v)) : ℝ) := hvdeg
    have hvNat : F.order + #badX ≤ #(X.filter (G.Adj v)) := by
      exact_mod_cast hvReal
    simpa [goodX] using
      card_neighbors_cleaned_ge G X badX v F.order hvNat
  let candidate : Fin 2 → Finset B := fun c ↦ if c = 0 then goodX else goodY
  obtain ⟨E, hEr, hEm⟩ := exists_embedding_in_shared_candidates
    F G rootImage candidate hrootInjective (by
      intro i c
      by_cases hc : c = 0
      · simpa [candidate, hc, goodX, badX, cleanedSide] using (hrootOutside i).1
      · simpa [candidate, hc, goodY, badY, cleanedSide] using (hrootOutside i).2) (by
      intro i
      simpa [candidate] using hrootGood i) (by
      intro c d hcd v hv
      rcases fin_two_eq_zero_or_one c with rfl | rfl <;>
        rcases fin_two_eq_zero_or_one d with rfl | rfl
      · exact False.elim (hcd rfl)
      · simpa [candidate] using hXY v (by simpa [candidate] using hv)
      · simpa [candidate] using hYX v (by simpa [candidate] using hv)
      · exact False.elim (hcd rfl))
  refine ⟨E, hEr, ?_⟩
  intro i a ha
  have hm := hEm i a ha
  by_cases hc : (F.isTree i).coloringTwoOfVert (F.root i) a = 0
  · simpa [candidate, hc, goodX, badX, cleanedSide] using hm
  · simpa [candidate, hc, goodY, badY, cleanedSide] using hm

/-- The regular-pair allocation form of the ordered-forest embedding lemma.
Each component is assigned a (possibly sliced) uniform pair.  Distinct
assignments have disjoint cleaned sides, as happens for different edges of a
cluster matching or for disjoint slices of one regular pair. -/
theorem exists_embedding_over_disjoint_uniform_pairs
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B) {rho : ℝ}
    (X Y : Fin m → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈
          if (F.isTree i).coloringTwoOfVert (F.root i) a = 0 then
            cleanedSide G rho (X i) (Y i)
          else cleanedSide G rho (Y i) (X i) := by
  classical
  let candidate : Fin m → Fin 2 → Finset B := fun i c ↦
    if c = 0 then cleanedSide G rho (X i) (Y i)
    else cleanedSide G rho (Y i) (X i)
  have hex : ∀ i, ∃ f : (F.tree i).Copy G,
      f (F.root i) = rootImage i ∧
      ∀ a, a ≠ F.root i →
        f a ∈ candidate i
          ((F.isTree i).coloringTwoOfVert (F.root i) a) := by
    intro i
    simpa [candidate] using
      exists_rooted_tree_copy_of_uniform (F.tree i) G (F.isTree i)
        (F.root i) (rootImage i) (hunif i) hrho (by simpa using hcapX i)
        (by simpa using hcapY i) (by simpa using hrootDegree i)
  let f : ∀ i, (F.tree i).Copy G := fun i ↦ (hex i).choose
  have hfroot : ∀ i, f i (F.root i) = rootImage i := fun i ↦ (hex i).choose_spec.1
  have hfmem : ∀ i a, a ≠ F.root i →
      f i a ∈ candidate i
        ((F.isTree i).coloringTwoOfVert (F.root i) a) :=
    fun i ↦ (hex i).choose_spec.2
  obtain ⟨E, hEr, hEm⟩ := embedding_of_component_copies
    F G rootImage candidate f hfroot hfmem hrootInjective (by
      intro i k c
      by_cases hc : c = 0
      · simpa [candidate, hc] using (hrootOutside i k).1
      · simpa [candidate, hc] using (hrootOutside i k).2) (by
      intro i k hik
      simpa [candidate] using hdisjoint i k hik)
  exact ⟨E, hEr, by simpa [candidate] using hEm⟩

end OrderedRootedForest

end Erdos547b.RegularPair

#print axioms Erdos547b.RegularPair.card_atypicalVertices_le
#print axioms Erdos547b.RegularPair.exists_rooted_tree_copy_of_uniform
#print axioms Erdos547b.RegularPair.OrderedRootedForest.exists_embedding_in_shared_candidates
#print axioms Erdos547b.RegularPair.OrderedRootedForest.exists_embedding_in_uniform_pair
#print axioms Erdos547b.RegularPair.OrderedRootedForest.exists_embedding_over_disjoint_uniform_pairs
