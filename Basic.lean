import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
  --notations about ⋃₀ and ⋂₀

variable (U : Type)
variable (A B C: Set U)
variable (F G : Set (Set U) )

example : A ⊆ B → A ∩ C ⊆ B ∩ C := by
  intro h1 x h2
  rw [Set.mem_inter_iff]
  rw [Set.mem_inter_iff] at h2
  have h3 : x ∈ A := h2.left
  have h4 : x ∈ B := h1 h3
  apply And.intro h4 h2.right

example : A ⊆ B → A ∪ C ⊆ B ∪ C := by
  intro h1 x h2
  rw [Set.mem_union]
  rw [Set.mem_union] at h2
  cases' h2 with h2A h2C
  have h3 : x ∈ B := h1 h2A
  exact Or.inl h3
  exact Or.inr h2C

example : A ∈ F → ⋂₀ F ⊆ A := by
  intro h1 x h2
  rw [Set.mem_sInter] at h2
  have h2A : A ∈ F → x ∈ A := h2 A
  exact h2A h1

--Exercise P.32 22
example : ⋂₀ ( F ∪ G) = ⋂₀ F ∩ ⋂₀G := by
  --begin
  --A = B ↔ ( A → B ) ∧ ( B → A )
  ext x
  apply Iff.intro
  --A → ( C ∧ D )
  intro h1
  rw [Set.mem_inter_iff]
  apply And.intro
  --C
  rw [Set.mem_sInter] at h1
  intro t
  have h2 := h1 t
  intro h3
  apply h2
  rw [Set.mem_union]
  exact Or.inl h3
  --D
  rw [Set.mem_sInter] at h1
  intro t
  have h2 := h1 t
  intro h3
  apply h2
  rw [Set.mem_union]
  exact Or.inr h3
  --B → A
  intro h1
  rw [Set.mem_sInter]
  intro t
  intro h2
  cases' h2 with h2F h2G
  --case h2F
  rw [Set.mem_inter_iff] at h1
  have h3 := h1.left
  rw [Set.mem_sInter] at h3
  apply h3
  exact h2F
  --case h2G
  rw [Set.mem_inter_iff] at h1
  have h3 := h1.right
  rw [Set.mem_sInter] at h3
  apply h3
  exact h2G
  --end
