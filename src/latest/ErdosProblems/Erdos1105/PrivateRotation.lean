import ErdosProblems.Erdos1105.PrivateNeighbors
import ErdosProblems.Erdos1105.PrivatePaths
import ErdosProblems.Erdos1105.RotationCounting

namespace Erdos1105

open SimpleGraph

/-- The final rotation contradiction in the component-size argument.
The two initial private palettes are trapped on overlapping subpaths. -/
theorem private_path_rotation_impossible {V C : Type*} [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : p.length = n + 2) (hnil : ¬p.Nil)
    (hlast : PrivateAt c p.penultimate
      (c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩))
    (hH : ∀ f : (cycleGraph (n + 3)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hno₀ : ¬R.Adj x p.penultimate) (hno₁ : ¬R.Adj p.snd y)
    (hwithin₀ : ∀ w (hw : R.Adj x w),
      PrivateAt c x (c ⟨s(x, w), hw.ne⟩) → w ∈ p.dropLast.support)
    (hwithin₁ : ∀ w (hw : R.Adj p.snd w),
      PrivateAt c p.snd (c ⟨s(p.snd, w), hw.ne⟩) → w ∈ p.tail.support)
    (hnew : n + 2 ≤ (privateColors c x).card + (privateColors c p.snd).card) : False := by
  classical
  let v : Fin (n + 3) ↪ V :=
    ⟨fun i ↦ p.getVert i.val, fun i j hij ↦ Fin.ext (hp.getVert_injOn
      (by change i.val ≤ p.length; have := i.isLt; omega)
      (by change j.val ≤ p.length; have := j.isLt; omega) hij)⟩
  have hv₀ : v 0 = x := by
    change p.getVert 0 = x
    exact p.getVert_zero
  have hv₁ : v 1 = p.snd := by
    change p.getVert (1 : Fin (n + 3)).val = p.snd
    rw [Fin.val_one]
  have hvlast : v (Fin.last (n + 2)) = y := by
    change p.getVert (n + 2) = y
    rw [← hlen, Walk.getVert_length]
  have hvpenult : v ⟨n + 1, by omega⟩ = p.penultimate := by
    change p.getVert (n + 1) = p.getVert (p.length - 1)
    congr 1
    omega
  have hw₀ : ∀ w (hw : R.Adj (v 0) w),
      PrivateAt c (v 0) (c ⟨s(v 0, w), hw.ne⟩) → w ∈ p.dropLast.support := by
    simpa only [hv₀] using hwithin₀
  have hw₁ : ∀ w (hw : R.Adj (v 1) w),
      PrivateAt c (v 1) (c ⟨s(v 1, w), hw.ne⟩) → w ∈ p.tail.support := by
    simpa only [hv₁] using hwithin₁
  have hcount₀ := private_colors_le_neighbor_indices c R hpalette v 0
    (fun i : Fin (n + 3) ↦ i.val < n + 2) (by
      intro w hw hpriv
      obtain ⟨i, hwi, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hw₀ w hw hpriv)
      have hi' : i < p.length := by rw [Walk.length_dropLast] at hi; omega
      refine ⟨⟨i, by omega⟩, ?_, ?_⟩
      · change i < n + 2
        omega
      change p.getVert i = w
      rw [← Walk.getVert_dropLast hi']
      exact hwi)
  have hcount₁ := private_colors_le_neighbor_indices c R hpalette v 1
    (fun i : Fin (n + 3) ↦ 1 ≤ i.val) (by
      intro w hw hpriv
      obtain ⟨i, hwi, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hw₁ w hw hpriv)
      have hi' : i + 1 < n + 3 := by rw [Walk.length_tail] at hi; omega
      refine ⟨⟨i + 1, hi'⟩, ?_, ?_⟩
      · change 1 ≤ i + 1
        omega
      change p.getVert (i + 1) = w
      rw [← Walk.getVert_tail]
      exact hwi)
  let G := R.comap v
  have hGno₀ : ¬G.Adj 0 ⟨n + 1, by omega⟩ := by
    simpa only [G, comap_adj, hv₀, hvpenult] using hno₀
  have hGno₁ : ¬G.Adj 1 (Fin.last (n + 2)) := by
    simpa only [G, comap_adj, hv₁, hvlast] using hno₁
  have hGcount : n + 2 ≤
      (Finset.univ.filter (fun i : Fin (n + 3) ↦ G.Adj 0 i ∧ i.val < n + 2)).card +
      (Finset.univ.filter (fun i : Fin (n + 3) ↦ G.Adj 1 i ∧ 1 ≤ i.val)).card := by
    have h := Nat.add_le_add hcount₀ hcount₁
    have hnew' : n + 2 ≤ (privateColors c (v 0)).card + (privateColors c (v 1)).card := by
      simpa only [hv₀, hv₁] using hnew
    exact hnew'.trans h
  obtain ⟨q, hq, hqend, hq₀, hq₁⟩ := exists_rotating_chords G hGno₀ hGno₁ hGcount
  have hpath (i j : Fin (n + 3)) (hij : j.val = i.val + 1) : R.Adj (v i) (v j) := by
    change R.Adj (p.getVert i.val) (p.getVert j.val)
    rw [hij]
    apply p.adj_getVert_succ
    have := j.isLt
    omega
  have hclosing : extendColor c s(v (Fin.last (n + 2)), v 0) = extendColor c s(v 0, v 1) := by
    rw [hvlast, hv₀, hv₁]
    apply private_path_closing_eq_first c R hR howned p hp (by omega) hnil hlast
    rw [hlen]
    exact hH
  obtain ⟨f, hf⟩ := rainbow_cycle_of_rotating_chords c R hR v hpath q hq hqend hq₀ hq₁ hclosing
  exact hH f hf

end Erdos1105
