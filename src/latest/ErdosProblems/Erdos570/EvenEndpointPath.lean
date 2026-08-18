/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EndpointPath
import ErdosProblems.Erdos570.EvenLeafCycle

/-!
# The endpoint-path obstruction for even cycles

For an even cycle, an endpoint-unextendable path together with `h` outside
vertices directly gives a complementary `C_(2h)`: choose distinct path
vertices which are common complementary neighbors of each cyclically
consecutive pair of outside vertices and alternate around the cycle.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

def cyclicSucc {h : ℕ} (hh : 0 < h) (i : Fin h) : Fin h :=
  ⟨(i.val + 1) % h, Nat.mod_lt _ hh⟩

def evenEndpointSequence
    {V : Type*} {n h : ℕ} (p : Fin (n + 2) → V)
    (w : Fin h → V) (f : Fin h → Fin (n + 1))
    (z : Fin (2 * h)) : V :=
  if z.val % 2 = 0 then
    w ⟨z.val / 2, by omega⟩
  else
    p (f ⟨z.val / 2, by omega⟩).castSucc

theorem evenEndpointSequence_injective
    {V : Type*} {n h : ℕ} {p : Fin (n + 2) → V}
    {w : Fin h → V} {f : Fin h → Fin (n + 1)}
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hf : Function.Injective f)
    (hout : ∀ i, w i ∉ Set.range p) :
    Function.Injective (evenEndpointSequence p w f) := by
  intro a b hab
  simp only [evenEndpointSequence] at hab
  split at hab <;> rename_i ha
  · split at hab <;> rename_i hb
    · have hq := congrArg Fin.val (hw hab)
      apply Fin.ext
      simp only [Fin.val_mk] at hq
      omega
    · exact (hout _ ⟨_, hab.symm⟩).elim
  · split at hab <;> rename_i hb
    · exact (hout _ ⟨_, hab⟩).elim
    · have hpidx := hp hab
      have hbase :
          f ⟨a.val / 2, by omega⟩ = f ⟨b.val / 2, by omega⟩ := by
        apply Fin.ext
        have hval := congrArg Fin.val hpidx
        simpa using hval
      have hfidx := hf hbase
      have hq := congrArg Fin.val hfidx
      apply Fin.ext
      simp only [Fin.val_mk] at hq
      omega

theorem cycleGraph_even_isContained_of_endpoint_common
    {V : Type*} {G : SimpleGraph V} {n h : ℕ} (hh : 2 ≤ h)
    {p : Fin (n + 2) → V} {w : Fin h → V}
    {f : Fin h → Fin (n + 1)}
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hf : Function.Injective f)
    (hout : ∀ i, w i ∉ Set.range p)
    (hcommon : ∀ i, f i ∈ endpointPathCommonComplIndices G p
      (w i) (w (cyclicSucc (by omega) i))) :
    SimpleGraph.cycleGraph (2 * h) ⊑ Gᶜ := by
  let q := evenEndpointSequence p w f
  have hqinj : Function.Injective q :=
    evenEndpointSequence_injective hp hw hf hout
  apply cycleGraph_isContained_of_sequence q hqinj
  · intro a b hab
    simp only [q, evenEndpointSequence]
    split <;> rename_i ha
    · split <;> rename_i hb
      · omega
      · let i : Fin h := ⟨a.val / 2, by omega⟩
        have hia : (⟨a.val / 2, by omega⟩ : Fin h) = i := rfl
        have hib : (⟨b.val / 2, by omega⟩ : Fin h) = i := by
          apply Fin.ext
          simp only [i, Fin.val_mk]
          omega
        rw [hia, hib]
        exact (mem_endpointPathCommonComplIndices.mp (hcommon i)).1
    · split <;> rename_i hb
      · let i : Fin h := ⟨a.val / 2, by omega⟩
        have hia : (⟨a.val / 2, by omega⟩ : Fin h) = i := rfl
        have hnext : (⟨b.val / 2, by omega⟩ : Fin h) =
            cyclicSucc (by omega) i := by
          apply Fin.ext
          change b.val / 2 = (a.val / 2 + 1) % h
          have hnotlast : a.val / 2 + 1 < h := by omega
          rw [Nat.mod_eq_of_lt hnotlast]
          omega
        rw [hia, hnext]
        exact (mem_endpointPathCommonComplIndices.mp (hcommon i)).2.symm
      · omega
  · intro a b ha hb
    let a0 : Fin (2 * h) := ⟨0, by omega⟩
    let blast : Fin (2 * h) := ⟨2 * h - 1, by omega⟩
    have ha0 : a = a0 := Fin.ext ha
    have hblast : b = blast := Fin.ext (by simp [blast]; omega)
    rw [ha0, hblast]
    simp only [q, evenEndpointSequence, a0, blast, Nat.zero_mod, if_pos]
    have hodd : (2 * h - 1) % 2 ≠ 0 := by omega
    rw [if_neg hodd]
    let ilast : Fin h := ⟨h - 1, by omega⟩
    let izero : Fin h := ⟨0, by omega⟩
    have hidxlast : (⟨(2 * h - 1) / 2, by omega⟩ : Fin h) = ilast := by
      ext
      simp [ilast]
      omega
    have hidxzero : (⟨0 / 2, by omega⟩ : Fin h) = izero := by
      ext
      simp [izero]
    have hnext : cyclicSucc (by omega) ilast = izero := by
      ext
      change (h - 1 + 1) % h = 0
      have hsub : h - 1 + 1 = h := by omega
      rw [hsub, Nat.mod_self]
    rw [hidxlast, hidxzero, ← hnext]
    exact (mem_endpointPathCommonComplIndices.mp (hcommon ilast)).2

/-- A long endpoint-unextendable path cannot leave `h` outside vertices
when the complementary graph is `C_(2h)`-free. -/
theorem endpointPath_outside_card_lt_of_evenCycle_free
    {V : Type*} {G : SimpleGraph V} {n h : ℕ} (hh : 2 ≤ h)
    {p : Fin (n + 2) → V} (hp : IsEndpointPath G p)
    (hmax : EndpointUnextendable G p)
    (hlong : 5 * h + 1 ≤ n + 2)
    (hcycle : ¬ SimpleGraph.cycleGraph (2 * h) ⊑ Gᶜ)
    {U : Finset V} (hout : ∀ x ∈ U, x ∉ Set.range p) :
    U.card < h := by
  classical
  by_contra hnot
  have hhU : h ≤ U.card := Nat.le_of_not_gt hnot
  let A : Fin h → Finset V := fun _ ↦ U
  obtain ⟨w, hwinj, hwU⟩ := exists_injective_mem_of_card_ge A (by
    intro i
    simpa [A] using hhU)
  have hwout : ∀ i, w i ∉ Set.range p := by
    intro i
    exact hout (w i) (by simpa [A] using hwU i)
  have hfree : Gᶜ.CliqueFree (2 * h + 1) := by
    by_contra hnfree
    apply hcycle
    have hsmallTop : SimpleGraph.cycleGraph (2 * h) ⊑
        SimpleGraph.completeGraph (Fin (2 * h + 1)) := by
      rw [SimpleGraph.isContained_top_iff]
      exact ⟨
        ⟨fun i ↦ ⟨i.val, by omega⟩, by
          intro i j hij
          apply Fin.ext
          have hv := congrArg Fin.val hij
          simpa using hv⟩⟩
    exact hsmallTop.trans
      ((SimpleGraph.not_cliqueFree_iff_top_isContained (2 * h + 1)).mp hnfree)
  let I : Fin h → Finset (Fin (n + 1)) := fun i ↦
    endpointPathCommonComplIndices G p (w i)
      (w (cyclicSucc (by omega) i))
  have hIcard : ∀ i, h ≤ (I i).card := by
    intro i
    have hc := card_endpointPathCommonComplIndices_ge hp hmax
      (hwout i) (hwout (cyclicSucc (by omega) i)) hfree
    change h ≤ (endpointPathCommonComplIndices G p (w i)
      (w (cyclicSucc (by omega) i))).card
    apply (show h ≤ n + 1 - 4 * h by omega).trans hc
  obtain ⟨f, hfinj, hfmem⟩ := exists_injective_mem_of_card_ge I hIcard
  apply hcycle
  exact cycleGraph_even_isContained_of_endpoint_common hh hp.injective
    hwinj hfinj hwout (by
      intro i
      simpa [I] using hfmem i)

end Erdos570
