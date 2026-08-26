/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Partite

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoFact72

open Finset Fintype SimpleGraph

/-- Cardinality of a fiber of an arbitrary two-part assignment.  Unlike a
graph coloring, the assignment used in Fact 7.2 may put adjacent vertices in
part zero. -/
def partCount {α : Type*} [Fintype α] (side : α → Fin 2) (i : Fin 2) : ℕ :=
  #(univ.filter fun x ↦ side x = i)

private theorem partCount_induce_compl_singleton_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (side : α → Fin 2) (x : α) (i : Fin 2) :
    partCount (fun y : ({x}ᶜ : Set α) ↦ side y) i ≤ partCount side i := by
  classical
  unfold partCount
  rw [← card_image_of_injective _ Subtype.val_injective]
  apply card_le_card
  intro a ha
  rcases mem_image.mp ha with ⟨y, hy, rfl⟩
  simpa only [mem_filter, mem_univ, true_and] using hy

/-- Inductive core of the rooted semibipartite greedy lemma. -/
private theorem exists_rooted_semibipartite_copy_aux
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card α = n + 1) (hT : T.IsTree)
    (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (A : Fin 2 → Finset β) (hA : Set.PairwiseDisjoint Set.univ A)
    (hdeg : ∀ i j, ¬(i = 1 ∧ j = 1) → ∀ v ∈ A i,
      partCount side j ≤ #((G.neighborFinset v) ∩ A j))
    (root : α) (rootImage : β) (hrootImage : rootImage ∈ A (side root)) :
    ∃ f : T.Copy G, f root = rootImage ∧ ∀ x, f x ∈ A (side x) := by
  classical
  induction n generalizing α with
  | zero =>
      have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let F : α → β := fun _ ↦ rootImage
      have hF_inj : Function.Injective F := fun u v _ ↦ hsub.elim u v
      let f : T.Copy G :=
        ⟨⟨F, fun {u v} huv ↦ False.elim (T.ne_of_adj huv (hsub.elim u v))⟩, hF_inj⟩
      refine ⟨f, rfl, ?_⟩
      intro x
      simpa [f, F, hsub.elim x root] using hrootImage
  | succ n ih =>
      have hlarge : 1 < Fintype.card α := by omega
      letI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hlarge
      obtain ⟨x₀, x₁, hxne, hx₀deg, hx₁deg⟩ := hT.exists_ne_and_degree_eq_one
      obtain ⟨x, hxroot, hxdeg⟩ : ∃ x : α, x ≠ root ∧ T.degree x = 1 := by
        by_cases h : x₀ = root
        · exact ⟨x₁, fun h' ↦ hxne (h.trans h'.symm), hx₁deg⟩
        · exact ⟨x₀, h, hx₀deg⟩
      obtain ⟨parent, hxparent, hparent_unique⟩ :=
        degree_eq_one_iff_existsUnique_adj.mp hxdeg
      let s : Set α := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let side' : s → Fin 2 := fun a ↦ side a
      let root' : s := ⟨root, by simpa [s] using hxroot.symm⟩
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : α ↦ a = x)
        change Fintype.card {a : α // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
          hT.isAcyclic.induce s⟩
      have hindep' : ∀ ⦃u v : s⦄, T'.Adj u v → side' u = 1 → side' v ≠ 1 := by
        intro u v huv hu
        exact hindep (by simpa [T', side'] using huv) (by simpa [side'] using hu)
      have hdeg' : ∀ i j, ¬(i = 1 ∧ j = 1) → ∀ v ∈ A i,
          partCount side' j ≤ #((G.neighborFinset v) ∩ A j) := by
        intro i j hij v hv
        exact (partCount_induce_compl_singleton_le side x j).trans (hdeg i j hij v hv)
      have hrootImage' : rootImage ∈ A (side' root') := by
        simpa [root', side'] using hrootImage
      obtain ⟨f, hfroot, hfmem⟩ :=
        ih T' hcard' hT' side' hindep' hdeg' root' hrootImage'
      let parent' : s := ⟨parent, by simpa [s] using hxparent.ne'⟩
      have hparentmem : f parent' ∈ A (side parent) := by
        simpa [parent', side'] using hfmem parent'
      have hnot11 : ¬(side parent = 1 ∧ side x = 1) := by
        intro h
        exact hindep hxparent.symm h.1 h.2
      let used : Finset β :=
        (univ.filter fun a : s ↦ side' a = side x).image f
      have husedcard : #used = partCount side' (side x) := by
        dsimp only [used, partCount]
        exact card_image_iff.mpr fun _ _ _ _ h ↦ f.injective h
      have hpartcount : partCount side (side x) = partCount side' (side x) + 1 := by
        unfold partCount
        rw [show (univ.filter fun a : α ↦ side a = side x) =
            insert x ((univ.filter fun a : α ↦ side a = side x).erase x) by
          rw [insert_erase (by simp)]]
        rw [card_insert_of_notMem]
        · congr 1
          apply card_bij (fun a ha ↦ ⟨a, by
            have := (mem_erase.mp ha).1
            simpa [s] using this⟩)
          · intro a ha
            simp only [mem_erase, mem_filter, mem_univ, true_and] at ha
            simpa [side', s, ha.2]
          · intro a₁ ha₁ a₂ ha₂ h
            exact Subtype.ext_iff.mp h
          · intro a ha
            refine ⟨a.1, ?_, rfl⟩
            simp only [mem_erase, mem_filter, mem_univ, true_and]
            exact ⟨a.2, by simpa [side', s] using ha⟩
        · simp
      let choices : Finset β := (G.neighborFinset (f parent')) ∩ A (side x)
      have hchoices : partCount side (side x) ≤ #choices := by
        exact hdeg (side parent) (side x) hnot11 (f parent') hparentmem
      have husedlt : #used < #choices := by omega
      obtain ⟨w, hwchoices, hwunused⟩ :=
        exists_mem_notMem_of_card_lt_card husedlt
      have hwadj : G.Adj (f parent') w :=
        (G.mem_neighborFinset _ _).mp (mem_inter.mp hwchoices).1
      have hwpart : w ∈ A (side x) := (mem_inter.mp hwchoices).2
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        by_cases hc : side a = side x
        · apply hwunused
          exact mem_image.mpr ⟨a, by simpa [side'] using hc, hwa.symm⟩
        · have hdisj := hA (Set.mem_univ (side x)) (Set.mem_univ (side a))
              (fun h ↦ hc h.symm)
          have hfa : f a ∈ A (side a) := by simpa [side'] using hfmem a
          rw [← hwa] at hfa
          exact Finset.disjoint_left.mp hdisj hwpart hfa
      let F : α → β := fun a ↦ if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      have hF_adj : ∀ ⦃u v⦄, T.Adj u v → G.Adj (F u) (F v) := by
        intro u v huv
        by_cases hu : u = x
        · subst u
          have hvp : v = parent := hparent_unique v huv
          subst v
          simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj.symm
        · by_cases hv : v = x
          · subst v
            have hup : u = parent := hparent_unique u huv.symm
            subst u
            simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj
          · let u' : s := ⟨u, by simpa [s] using hu⟩
            let v' : s := ⟨v, by simpa [s] using hv⟩
            have huv' : T'.Adj u' v' := by simpa [T', u', v'] using huv
            have hmap := f.toHom.map_rel huv'
            simpa [F, hu, hv, u', v'] using hmap
      have hF_inj : Function.Injective F := by
        intro u v huv
        by_cases hu : u = x
        · subst u
          by_cases hv : v = x
          · exact hv.symm
          · exfalso
            apply hw_not_range ⟨v, by simpa [s] using hv⟩
            simpa [F, hv] using huv
        · by_cases hv : v = x
          · subst v
            exfalso
            apply hw_not_range ⟨u, by simpa [s] using hu⟩
            simpa [F, hu] using huv.symm
          · have hsub : (⟨u, by simpa [s] using hu⟩ : s) =
                ⟨v, by simpa [s] using hv⟩ := by
              apply f.injective
              simpa [F, hu, hv] using huv
            exact Subtype.ext_iff.mp hsub
      let f' : T.Copy G := ⟨⟨F, fun {_ _} h ↦ hF_adj h⟩, hF_inj⟩
      refine ⟨f', ?_, ?_⟩
      · change F root = rootImage
        simp only [F, dif_neg hxroot.symm]
        simpa [root'] using hfroot
      · intro a
        by_cases ha : a = x
        · subst a
          simpa [f', F] using hwpart
        · have := hfmem ⟨a, by simpa [s] using ha⟩
          simpa [f', F, ha, side'] using this

/-- Root-preserving greedy embedding for a target whose second part is
independent.  Edges inside the first target part are allowed. -/
theorem exists_rooted_semibipartite_copy
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (A : Fin 2 → Finset β) (hA : Set.PairwiseDisjoint Set.univ A)
    (hdeg : ∀ i j, ¬(i = 1 ∧ j = 1) → ∀ v ∈ A i,
      partCount side j ≤ #((G.neighborFinset v) ∩ A j))
    (root : α) (rootImage : β) (hrootImage : rootImage ∈ A (side root)) :
    ∃ f : T.Copy G, f root = rootImage ∧ ∀ x, f x ∈ A (side x) := by
  apply exists_rooted_semibipartite_copy_aux T G (Fintype.card α - 1)
    (by
      have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hT.connected.nonempty
      omega)
    hT side hindep A hA hdeg root rootImage hrootImage

private theorem card_restrict_le {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (x : α) :
    #(univ.filter fun a : ({x}ᶜ : Set α) ↦ (a : α) ∈ S) ≤ #S := by
  rw [← card_image_of_injective _ Subtype.val_injective]
  apply card_le_card
  intro a ha
  rcases mem_image.mp ha with ⟨y, hy, rfl⟩
  simpa using hy

/-- Induction which first removes the deferred leaves in the second target
part and then invokes the semibipartite core embedding. -/
private theorem fact72_part3_aux
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card α = n + 1) (hT : T.IsTree)
    (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset α) (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (parts : Fin 2 → Finset β) (hparts : Set.PairwiseDisjoint Set.univ parts)
    (hAA : ∀ a ∈ parts 0,
      partCount side 0 ≤ #((G.neighborFinset a) ∩ parts 0))
    (hBA : ∀ b ∈ parts 1,
      partCount side 0 ≤ #((G.neighborFinset b) ∩ parts 0))
    (hAB : ∀ a ∈ parts 0,
      #active ≤ #((G.neighborFinset a) ∩ parts 1))
    (hglobal : ∀ a ∈ parts 0, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootCore : side root = 0 ∨ root ∈ active)
    (rootImage : β) (hrootImage : rootImage ∈ parts (side root)) :
    ∃ f : T.Copy G, f root = rootImage ∧
      (∀ x, side x = 0 → f x ∈ parts 0) ∧
      (∀ x ∈ active, f x ∈ parts 1) := by
  classical
  induction n generalizing α with
  | zero =>
      have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let F : α → β := fun _ ↦ rootImage
      have hF_inj : Function.Injective F := fun u v _ ↦ hsub.elim u v
      let f : T.Copy G :=
        ⟨⟨F, fun {u v} huv ↦ False.elim (T.ne_of_adj huv (hsub.elim u v))⟩, hF_inj⟩
      refine ⟨f, rfl, ?_, ?_⟩
      · intro x hx
        have hsx : side x = side root := congrArg side (hsub.elim x root)
        have hr : side root = 0 := hsx.symm.trans hx
        change rootImage ∈ parts 0
        simpa [hr] using hrootImage
      · intro x hx
        have hsx : side x = side root := congrArg side (hsub.elim x root)
        have hx1 : side x = 1 := hactive x hx
        have hr : side root = 1 := hsx.symm.trans hx1
        change rootImage ∈ parts 1
        simpa [hr] using hrootImage
  | succ n ih =>
      let deferred : Finset α := (univ.filter fun x ↦ side x = 1) \ active
      by_cases hD : deferred.Nonempty
      · obtain ⟨x, hxD⟩ := hD
        have hxside : side x = 1 := (mem_filter.mp (mem_sdiff.mp hxD).1).2
        have hxactive : x ∉ active := (mem_sdiff.mp hxD).2
        have hxdeg : T.degree x = 1 := hdeferred x hxside hxactive
        have hxroot : x ≠ root := by
          intro h
          subst x
          rcases hrootCore with hr | hr
          · exact Fin.zero_ne_one (hr.symm.trans hxside)
          · exact hxactive hr
        obtain ⟨parent, hxparent, hparent_unique⟩ :=
          degree_eq_one_iff_existsUnique_adj.mp hxdeg
        have hparentside : side parent = 0 := by
          have hpne : side parent ≠ 1 := hindep hxparent hxside
          have hz : side parent = 0 ∨ side parent = 1 := by
            generalize side parent = i
            fin_cases i <;> simp
          exact hz.resolve_right hpne
        let s : Set α := {x}ᶜ
        let T' : SimpleGraph s := T.induce s
        let side' : s → Fin 2 := fun a ↦ side a
        let active' : Finset s := univ.filter fun a ↦ (a : α) ∈ active
        let root' : s := ⟨root, by simpa [s] using hxroot.symm⟩
        have hcard' : Fintype.card s = n + 1 := by
          have hc := Fintype.card_subtype_compl (fun a : α ↦ a = x)
          change Fintype.card {a : α // ¬a = x} = n + 1
          rw [hc, hcard]
          simp
        have hT' : T'.IsTree :=
          ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
            hT.isAcyclic.induce s⟩
        have hindep' : ∀ ⦃u v : s⦄, T'.Adj u v → side' u = 1 → side' v ≠ 1 := by
          intro u v huv hu
          exact hindep (by simpa [T', side'] using huv) (by simpa [side'] using hu)
        have hactive' : ∀ y ∈ active', side' y = 1 := by
          intro y hy
          have hy' : (y : α) ∈ active := by simpa [active'] using hy
          simpa [side'] using hactive y hy'
        have hdeferred' : ∀ y, side' y = 1 → y ∉ active' → T'.degree y = 1 := by
          intro y hyside hyactive
          have hyside' : side (y : α) = 1 := by simpa [side'] using hyside
          have hyactive' : (y : α) ∉ active := by simpa [active'] using hyactive
          have hydeg : T.degree (y : α) = 1 := hdeferred y hyside' hyactive'
          rw [T.degree_induce_of_neighborSet_subset]
          · exact hydeg
          · intro z hyz
            show z ≠ x
            intro hzx
            subst z
            exact hindep hyz hyside' hxside
        have hAA' : ∀ a ∈ parts 0,
            partCount side' 0 ≤ #((G.neighborFinset a) ∩ parts 0) := by
          intro a ha
          exact (partCount_induce_compl_singleton_le side x 0).trans (hAA a ha)
        have hBA' : ∀ b ∈ parts 1,
            partCount side' 0 ≤ #((G.neighborFinset b) ∩ parts 0) := by
          intro b hb
          exact (partCount_induce_compl_singleton_le side x 0).trans (hBA b hb)
        have hAB' : ∀ a ∈ parts 0,
            #active' ≤ #((G.neighborFinset a) ∩ parts 1) := by
          intro a ha
          exact (card_restrict_le active x).trans (hAB a ha)
        have hglobal' : ∀ a ∈ parts 0, Fintype.card s - 1 ≤ G.degree a := by
          intro a ha
          have := hglobal a ha
          omega
        have hrootCore' : side' root' = 0 ∨ root' ∈ active' := by
          rcases hrootCore with hr | hr
          · exact Or.inl (by simpa [side', root'] using hr)
          · exact Or.inr (by simp [active', root', hr])
        have hrootImage' : rootImage ∈ parts (side' root') := by
          simpa [side', root'] using hrootImage
        obtain ⟨f, hfroot, hfzero, hfact⟩ :=
          ih T' hcard' hT' side' hindep' active' hactive' hdeferred'
            hAA' hBA' hAB' hglobal' root' hrootCore' hrootImage'
        let parent' : s := ⟨parent, by simpa [s] using hxparent.ne'⟩
        have hparentPart : f parent' ∈ parts 0 := by
          apply hfzero parent'
          simpa [side', parent'] using hparentside
        let used : Finset β := univ.image f
        have husedcard : #used = Fintype.card s :=
          card_image_iff.mpr fun _ _ _ _ h ↦ f.injective h
        have hparentUsed : f parent' ∈ used := mem_image.mpr ⟨parent', mem_univ _, rfl⟩
        have hnotSubset : ¬G.neighborFinset (f parent') ⊆ used := by
          intro hsubset
          have hproper : G.neighborFinset (f parent') ⊂ used := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
            intro heq
            have : f parent' ∈ G.neighborFinset (f parent') := heq ▸ hparentUsed
            simpa using this
          have hlt : G.degree (f parent') < #used := by
            exact card_lt_card hproper
          have hglob := hglobal (f parent') hparentPart
          omega
        obtain ⟨w, hwneighbor, hwunused⟩ := not_subset.mp hnotSubset
        have hwadj : G.Adj (f parent') w := (G.mem_neighborFinset _ _).mp hwneighbor
        have hw_not_range : ∀ a : s, w ≠ f a := by
          intro a hwa
          apply hwunused
          exact mem_image.mpr ⟨a, mem_univ _, hwa.symm⟩
        let F : α → β := fun a ↦ if h : a = x then w else f ⟨a, by simpa [s] using h⟩
        have hF_adj : ∀ ⦃u v⦄, T.Adj u v → G.Adj (F u) (F v) := by
          intro u v huv
          by_cases hu : u = x
          · subst u
            have hvp : v = parent := hparent_unique v huv
            subst v
            simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj.symm
          · by_cases hv : v = x
            · subst v
              have hup : u = parent := hparent_unique u huv.symm
              subst u
              simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj
            · let u' : s := ⟨u, by simpa [s] using hu⟩
              let v' : s := ⟨v, by simpa [s] using hv⟩
              have huv' : T'.Adj u' v' := by simpa [T', u', v'] using huv
              have hmap := f.toHom.map_rel huv'
              simpa [F, hu, hv, u', v'] using hmap
        have hF_inj : Function.Injective F := by
          intro u v huv
          by_cases hu : u = x
          · subst u
            by_cases hv : v = x
            · exact hv.symm
            · exfalso
              apply hw_not_range ⟨v, by simpa [s] using hv⟩
              simpa [F, hv] using huv
          · by_cases hv : v = x
            · subst v
              exfalso
              apply hw_not_range ⟨u, by simpa [s] using hu⟩
              simpa [F, hu] using huv.symm
            · have hsub : (⟨u, by simpa [s] using hu⟩ : s) =
                  ⟨v, by simpa [s] using hv⟩ := by
                apply f.injective
                simpa [F, hu, hv] using huv
              exact Subtype.ext_iff.mp hsub
        let f' : T.Copy G := ⟨⟨F, fun {_ _} h ↦ hF_adj h⟩, hF_inj⟩
        refine ⟨f', ?_, ?_, ?_⟩
        · change F root = rootImage
          simp only [F, dif_neg hxroot.symm]
          simpa [root'] using hfroot
        · intro y hyside
          have hyx : y ≠ x := by
            intro h
            subst y
            exact Fin.zero_ne_one (hyside.symm.trans hxside)
          have := hfzero ⟨y, by simpa [s] using hyx⟩ (by simpa [side'] using hyside)
          simpa [f', F, hyx] using this
        · intro y hyactive
          have hyx : y ≠ x := fun h ↦ by subst y; exact hxactive hyactive
          have hyactive' : (⟨y, by simpa [s] using hyx⟩ : s) ∈ active' := by
            simp [active', hyactive]
          have := hfact ⟨y, by simpa [s] using hyx⟩ hyactive'
          simpa [f', F, hyx] using this
      · have hactive_eq : active = univ.filter fun x ↦ side x = 1 := by
          apply Finset.Subset.antisymm
          · intro x hx
            exact mem_filter.mpr ⟨mem_univ _, hactive x hx⟩
          · intro x hx
            by_contra hxact
            apply hD
            exact ⟨x, mem_sdiff.mpr ⟨hx, hxact⟩⟩
        have hcount1 : partCount side 1 = #active := by
          simp [partCount, hactive_eq]
        have hdegCore : ∀ i j, ¬(i = 1 ∧ j = 1) → ∀ v ∈ parts i,
            partCount side j ≤ #((G.neighborFinset v) ∩ parts j) := by
          intro i j hij v hv
          fin_cases i <;> fin_cases j
          · exact hAA v hv
          · simpa [hcount1] using hAB v hv
          · exact hBA v hv
          · exact False.elim (hij ⟨rfl, rfl⟩)
        obtain ⟨f, hfroot, hfmem⟩ :=
          exists_rooted_semibipartite_copy T G hT side hindep parts hparts
            hdegCore root rootImage hrootImage
        refine ⟨f, hfroot, ?_, ?_⟩
        · intro x hx
          simpa [hx] using hfmem x
        · intro x hx
          have hx1 := hactive x hx
          simpa [hx1] using hfmem x

/-- Zhao's Fact 7.2(3), with either of its two prescribed-root conclusions.
The set `active` is the source's `Ũ₂`; all second-part vertices outside it
are required to be leaves. -/
theorem fact72_part3
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset α) (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (parts : Fin 2 → Finset β) (hparts : Set.PairwiseDisjoint Set.univ parts)
    (hAA : ∀ a ∈ parts 0,
      partCount side 0 ≤ #((G.neighborFinset a) ∩ parts 0))
    (hBA : ∀ b ∈ parts 1,
      partCount side 0 ≤ #((G.neighborFinset b) ∩ parts 0))
    (hAB : ∀ a ∈ parts 0,
      #active ≤ #((G.neighborFinset a) ∩ parts 1))
    (hglobal : ∀ a ∈ parts 0, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootCore : side root = 0 ∨ root ∈ active)
    (rootImage : β) (hrootImage : rootImage ∈ parts (side root)) :
    ∃ f : T.Copy G, f root = rootImage := by
  obtain ⟨f, hf, -, -⟩ := fact72_part3_aux T G (Fintype.card α - 1)
    (by
      have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hT.connected.nonempty
      omega)
    hT side hindep active hactive hdeferred parts hparts hAA hBA hAB hglobal
    root hrootCore rootImage hrootImage
  exact ⟨f, hf⟩

/-- In a nontrivial tree, if the second side is independent, then its
nonleaves are fewer than the vertices on the first side.  This is the count
used implicitly in Zhao's proof of Fact 7.2(2). -/
theorem card_nonleaves_second_lt_first
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset α) (hactive : ∀ x ∈ active, side x = 1)
    (hnonleaf : ∀ x ∈ active, T.degree x ≠ 1) :
    #active < partCount side 0 := by
  classical
  let U0 : Finset α := univ.filter fun x ↦ side x = 0
  let U1 : Finset α := univ.filter fun x ↦ side x = 1
  have h01 : Disjoint U0 U1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have h0 : side x = 0 := (mem_filter.mp hx0).2
    have h1 : side x = 1 := (mem_filter.mp hx1).2
    exact Fin.zero_ne_one (h0.symm.trans h1)
  have hcover : U0 ∪ U1 = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true, U0, U1, mem_filter, true_and]
    generalize side x = i
    fin_cases i <;> simp
  have hcards : #U0 + #U1 = Fintype.card α := by
    rw [← card_union_of_disjoint h01, hcover, card_univ]
  have hactiveSub : active ⊆ U1 := by
    intro x hx
    simp [U1, hactive x hx]
  let H : SimpleGraph α := T.between (U0 : Set α) (U1 : Set α)
  have hdegree (x : α) (hx : x ∈ U1) : H.degree x = T.degree x := by
    rw [← H.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext y
    simp only [H, mem_neighborFinset, between_adj]
    constructor
    · exact fun h ↦ h.1
    · intro hxy
      have hx1 : side x = 1 := (mem_filter.mp hx).2
      have hyne : side y ≠ 1 := hindep hxy hx1
      have hy0 : side y = 0 := by
        have hz : side y = 0 ∨ side y = 1 := by
          generalize side y = i
          fin_cases i <;> simp
        exact hz.resolve_right hyne
      exact ⟨hxy, Or.inr ⟨by simp [U1, hx1], by simp [U0, hy0]⟩⟩
  have hsumH : (∑ x ∈ U1, H.degree x) = #H.edgeFinset :=
    isBipartiteWith_sum_degrees_eq_card_edges' (by
      simpa [H] using T.between_isBipartiteWith (Finset.disjoint_coe.mpr h01))
  have hsumT : (∑ x ∈ U1, T.degree x) = #H.edgeFinset := by
    rw [← hsumH]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hdegree x hx).symm
  have hedgeMono : #H.edgeFinset ≤ #T.edgeFinset := by
    apply card_le_card
    exact edgeFinset_mono between_le
  have hpoint (x : α) (hx : x ∈ U1) :
      1 + (if x ∈ active then 1 else 0) ≤ T.degree x := by
    have hpos : 0 < T.degree x := hT.preconnected.degree_pos_of_nontrivial x
    by_cases hxa : x ∈ active
    · rw [if_pos hxa]
      have hne := hnonleaf x hxa
      omega
    · rw [if_neg hxa]
      omega
  have hlower : #U1 + #active ≤ ∑ x ∈ U1, T.degree x := by
    have hfilter : U1.filter (fun x ↦ x ∈ active) = active := by
      ext x
      simp only [mem_filter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hactiveSub h, h⟩
    have hindicator : (∑ x ∈ U1, if x ∈ active then 1 else 0) = #active := by
      rw [Finset.sum_boole, hfilter]
      simp
    calc
      #U1 + #active = ∑ x ∈ U1, (1 + if x ∈ active then 1 else 0) := by
        rw [sum_add_distrib]
        rw [← Finset.card_eq_sum_ones U1, hindicator]
      _ ≤ _ := sum_le_sum fun x hx ↦ hpoint x hx
  have hedge := hT.card_edgeFinset
  have hU0 : #U0 = partCount side 0 := rfl
  rw [hsumT] at hlower
  omega

/-- Zhao's Fact 7.2(2).  We retain the harmless nontriviality assumption
implicit in the paper's positive-size-tree setting and make `A.Nonempty`
explicit so that a root image can be chosen. -/
theorem fact72_part2
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nontrivial α]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (parts : Fin 2 → Finset β) (hparts : Set.PairwiseDisjoint Set.univ parts)
    (hAne : (parts 0).Nonempty)
    (hAA : ∀ a ∈ parts 0,
      partCount side 0 ≤ #((G.neighborFinset a) ∩ parts 0))
    (hBA : ∀ b ∈ parts 1,
      partCount side 0 ≤ #((G.neighborFinset b) ∩ parts 0))
    (hAB : ∀ a ∈ parts 0,
      partCount side 0 ≤ #((G.neighborFinset a) ∩ parts 1))
    (hglobal : ∀ a ∈ parts 0, Fintype.card α - 1 ≤ G.degree a) :
    T ⊑ G := by
  classical
  let active : Finset α :=
    univ.filter fun x ↦ side x = 1 ∧ T.degree x ≠ 1
  have hactiveSide : ∀ x ∈ active, side x = 1 := by
    intro x hx
    exact (mem_filter.mp hx).2.1
  have hactiveNonleaf : ∀ x ∈ active, T.degree x ≠ 1 := by
    intro x hx
    exact (mem_filter.mp hx).2.2
  have hactiveCard : #active ≤ partCount side 0 :=
    (card_nonleaves_second_lt_first T hT side hindep active
      hactiveSide hactiveNonleaf).le
  have hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1 := by
    intro x hxside hxactive
    by_contra hxdeg
    apply hxactive
    simp [active, hxside, hxdeg]
  have hzeroNonempty : ∃ x, side x = 0 := by
    let u : α := Classical.choice (inferInstance : Nonempty α)
    obtain ⟨v, huv⟩ := hT.connected.preconnected.exists_adj_of_nontrivial u
    by_cases hu : side u = 0
    · exact ⟨u, hu⟩
    · have hu1 : side u = 1 := by
        have hz : side u = 0 ∨ side u = 1 := by
          generalize side u = i
          fin_cases i <;> simp
        exact hz.resolve_left hu
      have hvne : side v ≠ 1 := hindep huv hu1
      have hv0 : side v = 0 := by
        have hz : side v = 0 ∨ side v = 1 := by
          generalize side v = i
          fin_cases i <;> simp
        exact hz.resolve_right hvne
      exact ⟨v, hv0⟩
  obtain ⟨root, hrootSide⟩ := hzeroNonempty
  obtain ⟨rootImage, hrootImage0⟩ := hAne
  have hrootImage : rootImage ∈ parts (side root) := by
    simpa [hrootSide] using hrootImage0
  have hABactive : ∀ a ∈ parts 0,
      #active ≤ #((G.neighborFinset a) ∩ parts 1) := by
    intro a ha
    exact hactiveCard.trans (hAB a ha)
  obtain ⟨f, hf⟩ := fact72_part3 T G hT side hindep active hactiveSide
    hdeferred parts hparts hAA hBA hABactive hglobal root (Or.inl hrootSide)
    rootImage hrootImage
  exact ⟨f⟩

end Erdos547b.ZhaoFact72

#print axioms Erdos547b.ZhaoFact72.exists_rooted_semibipartite_copy
#print axioms Erdos547b.ZhaoFact72.fact72_part3
#print axioms Erdos547b.ZhaoFact72.card_nonleaves_second_lt_first
#print axioms Erdos547b.ZhaoFact72.fact72_part2
