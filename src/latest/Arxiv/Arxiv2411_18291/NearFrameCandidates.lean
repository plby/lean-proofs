import Arxiv.Arxiv2411_18291.IndexedNearFrame
import Arxiv.Arxiv2411_18291.AsymptoticFrameCount
import Arxiv.Arxiv2411_18291.GoodEdgeFrameCounts

/-!
# Many exchange embeddings with monochromatic near cliques

Fix only the base map and the colours of its edges. Good-edge clique counts
and the frame-count theorem supply a polynomially dense family of full
exchange embeddings whose near cliques have the prescribed colours. The
near frame itself is not fixed.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

def nearFrameDensityConstant (b : ℝ) (q r : ℕ) : ℝ :=
  (3 / 4 : ℝ) * (b ^ (q.choose r - 1) / (4 * (q - r).factorial)) ^ q.choose r

theorem nearFrameDensityConstant_pos {b : ℝ} (hb : 0 < b) (q r : ℕ) :
    0 < nearFrameDensityConstant b q r := by unfold nearFrameDensityConstant; positivity

variable {J W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q r} {A : Finset (Block W q)}

theorem eventually_near_frame_candidates (hA : IsExchangeFamily S A) (hr : 0 < r)
    (hqr : r < q) {b α τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (hgap : α * ((q.choose r - 1 : ℕ) : ℝ) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) r, ∀ D : Finset (Block (Fin n) q),
      b * (n : ℝ) ^ (-α) ≤ density K →
      (∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q r r| ≤
          (n : ℝ) ^ (-τ) * cliqueMainTerm n (density K) q r r) →
      ∀ σ : J → Equiv.Perm (Fin n), ∀ φ : S.base.val ↪ Fin n,
      ∀ colour : Fin (q.choose r) → J,
      (∀ i, hA.nearRootImage hr φ i ∈ mapGraph (σ (colour i)).toEmbedding G) →
      ∃ T : Finset (EmbeddingExtension φ),
        (nearFrameDensityConstant b q r *
          (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ) * q.choose r))) *
            (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
        ∀ f ∈ T, ∀ i, mapBlock f.val (hA.nearPattern hr i) ∈
          mapGraph (σ (colour i)).toEmbedding D := by
  classical
  let c : ℝ := b ^ (q.choose r - 1) / (2 * (q - r).factorial)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hk : 0 < q.choose r := Nat.choose_pos hqr.le
  let idx (i : ℕ) : Fin (q.choose r) := if hi : i < q.choose r then ⟨i, hi⟩ else ⟨0, hk⟩
  have hidx (i : Fin (q.choose r)) : idx i = i := by
    dsimp only [idx]
    rw [dif_pos i.isLt]
  have hcoeff : (3 / 4 : ℝ) * (c / 2) ^ q.choose r = nearFrameDensityConstant b q r := by
    dsimp only [c, nearFrameDensityConstant]
    congr 1
    congr 1
    ring
  filter_upwards [eventually_good_edge_rooted_count_lower q r hb hτ,
    eventually_frameCandidateExtensions_density S.base.val (hA.nearPattern hr) hqr
      (hA.nearPattern_private_pairwise hr) (hA.nearPattern_private_card hr) hc hgap]
        with n hnear hframe
  intro K G D hd hcount σ φ colour hcolour
  let e (i : ℕ) := hA.nearRootImage hr φ (idx i)
  let C (i : ℕ) := (mapGraph (σ (colour (idx i))).toEmbedding D).filter
    (fun Q => (e i).val ⊆ Q.val)
  have heB (i : ℕ) : (e i).val ⊆ usedVertices φ := hA.nearRootImage_subset hr φ (idx i)
  have hC (i : ℕ) : ∀ Q ∈ C i, (e i).val ⊆ Q.val := fun _ hQ => (mem_filter.mp hQ).2
  have hφ (i : Fin (q.choose r)) (x : S.base.val)
      (hx : x.val ∈ (hA.nearPattern hr i).val) : φ x ∈ (e i).val := by
    simpa only [e, hidx] using hA.nearRootImage_contains hr φ i x hx
  have hsize (i : ℕ) (_hi : i < q.choose r) :
      c * (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ))) * (n : ℝ) ^ (q - r) ≤ (C i).card :=
    hnear K G D hd hcount (σ (colour (idx i))) (e i) (hcolour (idx i))
  have hbnd := hframe φ e C hφ heB hC hsize
  rw [hcoeff, S.base.property] at hbnd
  refine ⟨frameCandidateExtensions φ (hA.nearPattern hr) (fun i => C i), hbnd, ?_⟩
  intro f hf i
  have hfi : mapBlock f.val (hA.nearPattern hr i) ∈ C i :=
    ((mem_frameCandidateExtensions φ (hA.nearPattern hr) (fun j => C j) f).mp hf) i
  have hmem : mapBlock f.val (hA.nearPattern hr i) ∈
      mapGraph (σ (colour (idx i))).toEmbedding D := (mem_filter.mp hfi).1
  simpa only [hidx] using hmem

end Arxiv2411_18291
