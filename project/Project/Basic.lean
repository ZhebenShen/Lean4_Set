import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice
  --notations about ⋃₀ and ⋂₀
import Mathlib.Data.Set.Function
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

example (A B C : Set U) : A ⊆ B → A ∩ C ⊆ B ∩ C := by
  intro h1 x h2
  rw [Set.mem_inter_iff]
  rw [Set.mem_inter_iff] at h2
  have h3 : x ∈ A := h2.left
  have h4 : x ∈ B := h1 h3
  apply And.intro h4 h2.right

example (A B C : Set U) : A ⊆ B → A ∪ C ⊆ B ∪ C := by
    intro h1 x h2
    rw [Set.mem_union]
    rw [Set.mem_union] at h2
    cases' h2 with h2A h2C
    have h3 : x ∈ B := h1 h2A
    · exact Or.inl h3
    · exact Or.inr h2C

example (A : Set U) (F : Set (Set U)): A ∈ F → ⋂₀ F ⊆ A := by
    intro h1 x h2
    rw [Set.mem_sInter] at h2
    have h2A : A ∈ F → x ∈ A := h2 A
    exact h2A h1

--Exercise P.32 22
example (F G : Set (Set U)) : ⋂₀ ( F ∪ G) = ⋂₀F ∩ ⋂₀G := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_inter_iff]
    apply And.intro
    · rw [Set.mem_sInter] at h1
      intro t
      have h2 := h1 t
      intro h3
      apply h2
      rw [Set.mem_union]
      exact Or.inl h3
    · rw [Set.mem_sInter] at h1
      intro t
      have h2 := h1 t
      intro h3
      apply h2
      rw [Set.mem_union]
      exact Or.inr h3
  · intro h1
    rw [Set.mem_sInter]
    intro t
    intro h2
    cases' h2 with h2F h2G
    · rw [Set.mem_inter_iff] at h1
      have h3 := h1.left
      rw [Set.mem_sInter] at h3
      apply h3
      exact h2F
    · rw [Set.mem_inter_iff] at h1
      have h3 := h1.right
      rw [Set.mem_sInter] at h3
      apply h3
      exact h2G

--Exercise P.26 4
example (F G : Set (Set U)) : F ⊆ G → ⋃₀F ⊆ ⋃₀G := by
  intro h1 x h2
  rw [Set.mem_sUnion]
  rw [Set.mem_sUnion] at h2
  obtain ⟨S,hS⟩ := h2
  have h2 := h1 hS.left
  have h3 := And.intro h2 hS.right
  exact Exists.intro S h3

--Exercise P.32 21
example (F G : Set (Set U)) : ⋃₀ ( F ∪ G ) = ⋃₀F ∪ ⋃₀G := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_sUnion] at h1
    obtain ⟨S,hS⟩ := h1
    rw [Set.mem_union] at hS
    rw [Set.mem_union]
    rcases hS with ⟨h1, h2⟩
    cases' h1 with h1F h2G
    · apply Or.inl
      rw [Set.mem_sUnion]
      apply Exists.intro S
      exact And.intro h1F h2
    · apply Or.inr
      rw [Set.mem_sUnion]
      apply Exists.intro S
      exact And.intro h2G h2
  · intro h1
    rw [Set.mem_sUnion]
    rw [Set.mem_union] at h1
    cases' h1 with h1F h1G
    · rw [Set.mem_sUnion] at h1F
      obtain ⟨S,h2⟩ := h1F
      apply Exists.intro S
      rw [Set.mem_union]
      have h3 : S ∈ F ∨ S ∈ G := Or.inl h2.left
      exact And.intro h3 h2.right
    · rw [Set.mem_sUnion] at h1G
      obtain ⟨S,h2⟩ := h1G
      apply Exists.intro S
      rw [Set.mem_union]
      have h3 : S ∈ F ∨ S ∈ G := Or.inr h2.left
      exact And.intro h3 h2.right

--Exercise P.26 7a
example (A B : Set U) : 𝒫 A ∩ 𝒫 B = 𝒫 ( A ∩ B ) := by
  ext S
  apply Iff.intro
  · intro h1
    rw [Set.mem_powerset_iff]
    intro x h2
    rw [Set.mem_inter_iff]
    rw [Set.mem_inter_iff] at h1
    rw [Set.mem_powerset_iff] at h1
    rw [Set.mem_powerset_iff] at h1
    have h3 := h1.left h2
    have h4 := h1.right h2
    exact And.intro h3 h4
  · intro h1
    rw [Set.mem_inter_iff]
    rw [Set.mem_powerset_iff]
    rw [Set.mem_powerset_iff]
    rw [Set.mem_powerset_iff] at h1
    apply And.intro
    · intro x h2
      have h3 := h1 h2
      rw [Set.mem_inter_iff] at h3
      exact h3.left
    · intro x h2
      have h3 := h1 h2
      rw [Set.mem_inter_iff] at h3
      exact h3.right

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  apply Iff.intro
  ·
    intro h1
    rw [Set.mem_sUnion]
    rw [Set.mem_union] at h1
    cases' h1 with h1A h1B
    · apply Exists.intro A
      apply And.intro
      · have h2 : A = A ∨ A = B := by
          apply Or.inl rfl
        exact h2
      · exact h1A
    apply Exists.intro B
    apply And.intro
    · have h2 : B = A ∨ B = B := by
        apply Or.inr rfl
      exact h2
    · exact h1B
  ·
    intro h1
    rw [Set.mem_sUnion] at h1
    obtain ⟨C,h2⟩ := h1
    cases' h2 with h3 h2C
    rw [Set.mem_union]
    cases' h3 with h3A h3B
    · rw [←h3A]
      exact Or.inl h2C
    · rw [Set.mem_singleton_iff] at h3B
      rw [←h3B]
      exact Or.inr h2C

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_union]
    rw [Set.mem_sUnion] at h1
    obtain ⟨S, h2⟩ := h1
    rw [Set.mem_sUnion, Set.mem_sUnion]
    cases' h2 with h3 h2S
    rw [Set.mem_union] at h3
    cases' h3 with h3F h3G
    · apply Or.inl
      apply Exists.intro S
      apply And.intro h3F h2S
    · apply Or.inr
      apply Exists.intro S
      apply And.intro h3G h2S
  · intro h1
    rw [Set.mem_sUnion]
    rw [Set.mem_union] at h1
    cases' h1 with h1F h1G
    · rw [Set.mem_sUnion] at h1F
      obtain ⟨S, h2⟩ := h1F
      apply Exists.intro S
      have h3 : S ∈ F ∪ G := Or.inl h2.left
      apply And.intro h3 h2.right
    · rw [Set.mem_sUnion] at h1G
      obtain ⟨S, h2⟩ := h1G
      apply Exists.intro S --Use S
      have h3 : S ∈ F ∪ G := Or.inr h2.left
      apply And.intro h3 h2.right

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro
  · intro h1 S h2 x h3
    apply h1
    rw [Set.mem_sUnion]
    use S
  · intro h1 x h2
    rw [Set.mem_sUnion] at h2
    obtain ⟨S, h3⟩ := h2
    have h4 := h1 S
    have h5 := h4 h3.left
    exact h5 h3.right

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_inter_iff] at h1
    rw [Set.mem_sUnion] at h1
    have h2 := h1.right
    obtain ⟨S, h3⟩ := h2
    use (A ∩ S)
    rw [Set.mem_setOf]
    apply And.intro
    · use S
      apply And.intro
      · exact h3.left
      · rfl
    · rw [Set.mem_inter_iff]
      exact And.intro h1.left h3.right
  · intro h1
    rw [Set.mem_sUnion] at h1
    rw [Set.mem_inter_iff]
    rw [Set.mem_sUnion]
    obtain ⟨S, h2⟩ := h1
    cases' h2 with h2 h3
    rw [Set.mem_setOf] at h2
    obtain ⟨u, h4⟩ := h2
    rw [h4.right] at h3
    rw [Set.mem_inter_iff] at h3
    apply And.intro
    · exact h3.left
    · use u
      exact And.intro h4.left h3.right

theorem compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_compl_iff, Set.mem_union] at h1
    rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_compl_iff]
    push_neg at h1
    exact h1
  · intro h1
    rw [Set.mem_compl_iff, Set.mem_union]
    rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_compl_iff] at h1
    push_neg
    exact h1

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_compl_iff, Set.mem_inter_iff] at h1
    rw [Set.mem_union, Set.mem_compl_iff, Set.mem_compl_iff]
    rw [not_and_or] at h1
    exact h1
  · intro h1
    rw [Set.mem_compl_iff, Set.mem_inter_iff]
    rw [Set.mem_union, Set.mem_compl_iff, Set.mem_compl_iff] at h1
    rw [not_and_or]
    exact h1

--Exercise P.38 2a
example (A B C: Set U) : A ×ˢ ( B ∪ C ) = ( A ×ˢ B ) ∪ ( A ×ˢ C ) := by
  ext x
  apply Iff.intro
  · intro h1
    rw [Set.mem_union, Set.mem_prod, Set.mem_prod]
    rw [Set.mem_prod, Set.mem_union] at h1
    cases' h1 with h1A h2
    cases' h2 with h2B h2C
    · apply Or.inl
      exact And.intro h1A h2B
    · apply Or.inr
      exact And.intro h1A h2C
  · intro h1
    rw [Set.mem_prod, Set.mem_union]
    rw [Set.mem_union, Set.mem_prod, Set.mem_prod] at h1
    apply And.intro
    · cases' h1 with h1B h1C
      · exact h1B.left
      · exact h1C.left
    · cases' h1 with h1B h1C
      · apply Or.inl
        exact h1B.right
      · apply Or.inr
        exact h1C.right

def Dom {A B : Type} (R : Set (A × B)) : Set A :=
  {a : A | ∃ (b : B), (a, b) ∈ R}

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
  {b : B | ∃ (a : A), (a, b) ∈ R}

def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
  {(b, a) : B × A | (a, b) ∈ R}

def comp {A B C : Type} (S : Set (B × C)) (R : Set (A × B)) : Set (A × C) :=
  {(a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S}

theorem Theorem_3E_1 {A B : Type} (R : Set (A × B)) : Dom (inv R) = Ran R := by rfl

theorem Theorem_3E_2 {A B : Type} (R : Set (A × B)) : Ran (inv R) = Dom R := by rfl

theorem Theorem_3E_3 {A B : Type} (R : Set (A × B)) : inv (inv R) = R := by rfl

theorem inv_def {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
  (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

--Exercise P.53 21
example {A B C D : Type}
  (R : Set (A × B)) (S : Set (B × C)) (T : Set (C × D)) :
    comp T (comp S R) = comp (comp T S) R := by
      apply Set.ext
      intro (a, d)
      apply Iff.intro
      · intro h1
        cases' h1 with c hc
        cases' hc with h2 h3
        cases' h2 with b hb
        exists b
        apply And.intro hb.left
        exists c
        apply And.intro hb.right h3
      · intro h2
        cases' h2 with b hb
        cases' hb with h3 h4
        cases' h4 with c hc
        exists c
        apply And.intro (Exists.intro b (And.intro h3 hc.left)) hc.right

--P.47 Theorem_3I
theorem Theorem_3I {A B C : Type}
  (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by
      apply Set.ext
      intro (u, v)
      apply Iff.intro
      · intro h1
        rw [inv_def] at h1
        unfold comp at h1
        rw [Set.mem_setOf] at h1
        rcases h1 with ⟨b, hR, hS⟩
        unfold comp
        rw [← inv_def] at hR hS
        rw [Set.mem_setOf]
        use b
      · intro h1
        rw [inv_def]
        unfold comp
        rw [Set.mem_setOf]
        unfold comp at h1
        rcases h1 with ⟨b, hS, hR⟩
        rw [inv_def] at hS hR
        use b
