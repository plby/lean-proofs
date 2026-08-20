import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: FiniteConnectedIntersectionGrouping]
lemma FiniteConnectedIntersectionGrouping
    {X : Type*} [TopologicalSpace X]
    {ι : Type*}
    (s : Finset ι) (piece : ι → Set X) (K : Set X)
    (hpiece_nonempty : ∀ i, i ∈ s → (piece i).Nonempty)
    (hpiece_connected : ∀ i, i ∈ s → IsConnected (piece i))
    (hpiece_subset : ∀ i, i ∈ s → piece i ⊆ K) :
    ∃ groupedPieces : Finset (Set X),
      ∃ groupOf : ι → Set X,
        (∀ i, i ∈ s →
          groupOf i =
            ⋃ j ∈
              ({j : ι | j ∈ s ∧
                Relation.ReflTransGen
                  (fun u v : ι => u ∈ s ∧ v ∈ s ∧
                    (piece u ∩ piece v).Nonempty) i j} : Set ι),
              piece j) ∧
        (∀ i, i ∈ s → groupOf i ∈ groupedPieces) ∧
        (∀ G, G ∈ groupedPieces → ∃ i, i ∈ s ∧ groupOf i = G) ∧
        (∀ G ∈ groupedPieces, G.Nonempty ∧ IsConnected G ∧ G ⊆ K) ∧
        (∀ i, i ∈ s → piece i ⊆ groupOf i) := by
-- BODY
  classical
  let adj : ι → ι → Prop := fun u v =>
    u ∈ s ∧ v ∈ s ∧ (piece u ∩ piece v).Nonempty
  let reachableFrom : ι → Set ι := fun i =>
    {j : ι | j ∈ s ∧ Relation.ReflTransGen adj i j}
  let groupOf : ι → Set X := fun i =>
    ⋃ j ∈ reachableFrom i, piece j
  let groupedPieces : Finset (Set X) := s.image groupOf
  have hgroup_nonempty :
      ∀ i, i ∈ s → (groupOf i).Nonempty := by
    intro i hi
    rcases hpiece_nonempty i hi with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨i, ⟨hi, Relation.ReflTransGen.refl⟩, hx⟩
  have hgroup_subset :
      ∀ i, i ∈ s → groupOf i ⊆ K := by
    intro i _hi x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
    exact hpiece_subset j hj.1 hxj
  have hgroup_connected :
      ∀ i, i ∈ s → IsConnected (groupOf i) := by
    intro i hi
    have hreachable_nonempty : (reachableFrom i).Nonempty :=
      ⟨i, hi, Relation.ReflTransGen.refl⟩
    have hpieces_connected :
        ∀ j, j ∈ reachableFrom i → IsConnected (piece j) := by
      intro j hj
      exact hpiece_connected j hj.1
    have hadj_symm : Symmetric adj := by
      intro u v huv
      exact ⟨huv.2.1, huv.1, by simpa [Set.inter_comm] using huv.2.2⟩
    have hreachable_symm :
        ∀ {u v : ι}, Relation.ReflTransGen adj u v →
          Relation.ReflTransGen adj v u := by
      intro u v huv
      induction huv with
      | refl =>
          exact Relation.ReflTransGen.refl
      | tail _ hpq ih =>
          exact (Relation.ReflTransGen.single (hadj_symm hpq)).trans ih
    have hrestrict_path :
        ∀ {u v : ι}, u ∈ reachableFrom i →
          Relation.ReflTransGen adj u v →
            Relation.ReflTransGen
              (fun p q : ι => (piece p ∩ piece q).Nonempty ∧
                p ∈ reachableFrom i) u v := by
      intro u v hu huv
      induction huv with
      | refl =>
          exact Relation.ReflTransGen.refl
      | tail huv hpq ih =>
          exact Relation.ReflTransGen.tail ih
            ⟨hpq.2.2, ⟨hpq.1, hu.2.trans huv⟩⟩
    have hreachable_preconnected :
        ∀ j, j ∈ reachableFrom i → ∀ k, k ∈ reachableFrom i →
          Relation.ReflTransGen
            (fun p q : ι => (piece p ∩ piece q).Nonempty ∧
              p ∈ reachableFrom i) j k := by
      intro j hj k hk
      have hji_base : Relation.ReflTransGen adj j i :=
        hreachable_symm hj.2
      have hji :=
        hrestrict_path (u := j) (v := i) hj hji_base
      have hi_reachable : i ∈ reachableFrom i :=
        ⟨hi, Relation.ReflTransGen.refl⟩
      have hik :=
        hrestrict_path (u := i) (v := k) hi_reachable hk.2
      exact hji.trans hik
    exact IsConnected.biUnion_of_reflTransGen hreachable_nonempty
      hpieces_connected hreachable_preconnected
  refine ⟨groupedPieces, groupOf, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _hi
    rfl
  · intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro G hG
    rcases Finset.mem_image.mp hG with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · intro G hG
    rcases Finset.mem_image.mp hG with ⟨i, hi, rfl⟩
    exact ⟨hgroup_nonempty i hi, hgroup_connected i hi, hgroup_subset i hi⟩
  · intro i hi x hx
    exact Set.mem_iUnion₂.mpr ⟨i, ⟨hi, Relation.ReflTransGen.refl⟩, hx⟩
