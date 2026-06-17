import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph Finset

variable {V : Type*} (G : SimpleGraph V) (n : ℕ)

/-- **De Bruijn–Erdős colouring theorem** (1951). A graph `G` is `n`-colourable iff every finite
induced subgraph is `n`-colourable. The forward direction is restriction; the backward direction is
a compactness argument, here via Rado's selection lemma (`Finset.rado_selection`). -/
theorem SimpleGraph.colorable_iff_forall_finite_induce :
    G.Colorable n ↔ ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n := by
  classical
  constructor
  · -- (→) restrict a global colouring to each finite induced subgraph
    rintro ⟨C⟩ s
    exact ⟨Coloring.mk (fun v => C ↑v) (fun {a b} hab => C.valid (induce_adj.mp hab))⟩
  · -- (←) stitch the finite colourings into a global one by compactness
    intro h
    -- a chosen colouring of each finite induced subgraph
    let col : (s : Finset V) → (G.induce (↑s : Set V)).Coloring (Fin n) := fun s => (h s).some
    -- the local data fed to Rado's lemma
    let g : Finset V → V → Fin n := fun s x =>
      if hx : x ∈ s then col s ⟨x, Finset.mem_coe.2 hx⟩
      else col {x} ⟨x, Finset.mem_coe.2 (Finset.mem_singleton_self x)⟩
    obtain ⟨χ, hχ⟩ := Finset.rado_selection g
    refine ⟨Coloring.mk χ (fun {u v} huv => ?_)⟩
    obtain ⟨t, hst, hagree⟩ := hχ {u, v}
    have hu : u ∈ t := hst (by simp)
    have hv : v ∈ t := hst (by simp)
    have eu : χ u = col t ⟨u, Finset.mem_coe.2 hu⟩ := (hagree u (by simp)).trans (dif_pos hu)
    have ev : χ v = col t ⟨v, Finset.mem_coe.2 hv⟩ := (hagree v (by simp)).trans (dif_pos hv)
    rw [eu, ev]
    exact (col t).valid (induce_adj.mpr huv)

#print axioms SimpleGraph.colorable_iff_forall_finite_induce
