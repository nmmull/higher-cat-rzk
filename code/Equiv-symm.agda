{-# OPTIONS --without-K #-}

module Equiv-symm where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

infix 40 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

id : {A : Set} → A → A
id x = x

infix 30 _∼_
_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = ∀ (x : A) → f x ≡ g x

is-equiv : {A B : Set} (f : A → B) → Set
is-equiv {A} {B} f =
  (Σ[ r ∈ (B → A) ] (r ∘ f ∼ id))
  × (Σ[ s ∈ (B → A) ] (f ∘ s ∼ id))

_≃_ : (A B : Set) → Set
A ≃ B = Σ[ f ∈ (A → B) ] (is-equiv f)

qinv : {A B : Set} (f : A → B) → Set
qinv {A} {B} f = Σ[ r ∈ (B → A) ] (r ∘ f ∼ id × f ∘ r ∼ id)

idʳ-∼ : {A B : Set} → (f : A → B) → f ∘ id ∼ f
idʳ-∼ f x = refl

idˡ-∼ : {A B : Set} → (f : A → B) → id ∘ f ∼ f
idˡ-∼ f x = refl

foo :
  {A B C : Set} →
  {g₁ g₂ : A → B} →
  (f : B → C) →
  g₁ ∼ g₂ →
  f ∘ g₁ ∼ f ∘ g₂
foo f g₁∼g₂ x = cong (λ z → f z) (g₁∼g₂ x)

is-equiv→qinv : {A B : Set} {f : A → B} → is-equiv f → qinv f
is-equiv→qinv {_} {_} {f} ((r , rf∼id) , (s , fs∼id)) =
  (r , (rf∼id , fr∼id)) where
  fr∼id : f ∘ r ∼ id
  fr∼id a =
    begin
      f (r a)
    ≡⟨ cong (λ z → f (r z)) (sym (fs∼id a))  ⟩
      f (r (f (s a)))
    ≡⟨ cong (λ z → f z) (rf∼id (s a)) ⟩
      f (s a)
    ≡⟨ fs∼id a ⟩
      a
    ∎

sym-≃-helper : {A B : Set} → (g : A → B) → qinv g → B ≃ A
sym-≃-helper g (g⁻¹ , g⁻¹g∼id , gg⁻¹∼id) =
  g⁻¹ , (g , gg⁻¹∼id) , (g , g⁻¹g∼id)

sym-≃ : {A B : Set} → A ≃ B → B ≃ A
sym-≃ {A} {B} (g , g-is-equiv) = sym-≃-helper g (is-equiv→qinv g-is-equiv)
