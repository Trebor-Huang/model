{-# OPTIONS --type-in-type #-}

⊥ : Set
⊥ = (X : Set) → X

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ

syntax Σ A (λ a → P) = Σ[ a ∈ A ] P
infixr 1 Σ

𝕍 : Set
𝕍 = (X : Set) → ((A : Set) → (A → X) → X) → X

comp : (A : Set) → (A → 𝕍) → 𝕍
comp A f = λ X F → F A λ a → f a X F

syntax comp A (λ a → V) = [ a ∈ A ∣ V ]
infix 10 comp

infix 2 _≡_ _∈_
_≡_ : {A : Set} → A → A → Set
x ≡ y = (P : _ → Set) → P x → P y

exist : (A : Set) (P : A → Set) → Set
exist A P = (X : Set) → ((a : A) → P a → X) → X

syntax exist A (λ a → P) = ∃[ a ∈ A ] P
infixr 1 exist

_×_ : Set → Set → Set
A × B = (X : Set) → (A → B → X) → X

_,,_ : {A B : Set} → A → B → A × B
a ,, b = λ X f → f a b

fst : {A B : Set} → A × B → A
fst p = p _ (λ a b → a)

snd : {A B : Set} → A × B → B
snd p = p _ (λ a b → b)

infixr 2 _×_
infixr 1 _,_ _,,_

_∈_ : 𝕍 → 𝕍 → Set
x ∈ y = snd (y (𝕍 × Set) λ A f → [ a ∈ A ∣ fst (f a) ] ,, ∃[ a ∈ A ]
  ((X : Set) → (F : (A : Set) → (A → X) → X) → fst (f a) X F ≡ x X F))

Δ : Set
Δ = Σ[ x ∈ 𝕍 ] (x ∈ x → ⊥)

R : 𝕍
R = [ p ∈ Δ ∣ proj₁ p ]

R∉R : R ∈ R → ⊥
R∉R p = p ⊥ λ (x , q) eq → q {!   !}
