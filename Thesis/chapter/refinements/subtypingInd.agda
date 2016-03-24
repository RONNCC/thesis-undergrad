module SubtypingInd where

open import Coinduction using (∞; ♯_; ♭)


data Session : Set where
  One : Session
  _⊗_ : Session -> Session -> Session
  _⊸_ : Session -> Session -> Session
  _⊓_ : Session -> Session -> Session
  _⊔_ : Session -> Session -> Session


data _≤_ : Session -> Session -> Set where
  ≤-One : One ≤ One
  ≤-⊗   : {a b a' b' : Session} -> (a ≤ a') -> (b ≤ b') -> (a ⊗ b) ≤ (a' ⊗ b')
  ≤-⊸   : {a b a' b' : Session} -> (a' ≤ a) -> (b ≤ b') -> (a ⊸ b) ≤ (a' ⊸ b')

  ≤-⊓R  : {a b₁ b₂ : Session} -> (a ≤ b₁) -> (a ≤ b₂) -> a ≤ (b₁ ⊓ b₂)
  ≤-⊓L₁ : {a₁ a₂ b : Session} -> (a₁ ≤ b) -> (a₁ ⊓ a₂) ≤ b
  ≤-⊓L₂ : {a₁ a₂ b : Session} -> (a₂ ≤ b) -> (a₁ ⊓ a₂) ≤ b

  ≤-⊔R₁ : {a b₁ b₂ : Session} -> (a ≤ b₁) -> a ≤ (b₁ ⊔ b₂)
  ≤-⊔R₂ : {a b₁ b₂ : Session} -> (a ≤ b₂) -> a ≤ (b₁ ⊔ b₂)
  ≤-⊔L  : {a₁ a₂ b : Session} -> (a₁ ≤ b) -> (a₂ ≤ b) -> (a₁ ⊔ a₂) ≤ b

  ≤-⊔⊓  : {a₁ a₂ b₁ b₂ c : Session} -> c ≤ (a₁ ⊔ b₁) -> c ≤ (a₁ ⊔ b₂)
        -> c ≤ (a₂ ⊔ b₁) -> c ≤ (a₂ ⊔ b₂) -> c ≤ ((a₁ ⊓ a₂) ⊔ (b₁ ⊓ b₂))
  ≤-⊓⊔  : {a₁ a₂ b₁ b₂ c : Session} -> (a₁ ⊓ b₁) ≤ c -> (a₁ ⊓ b₂) ≤ c
        -> (a₂ ⊓ b₁) ≤ c -> (a₂ ⊓ b₂) ≤ c -> ((a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)) ≤ c


≤-refl : (a : Session) -> a ≤ a
≤-refl One = ≤-One
≤-refl (a ⊗ b) = ≤-⊗ (≤-refl a) (≤-refl b)
≤-refl (a ⊸ b) = ≤-⊸ (≤-refl a) (≤-refl b)
≤-refl (a₁ ⊓ a₂) = ≤-⊓R (≤-⊓L₁ (≤-refl a₁)) (≤-⊓L₂ (≤-refl a₂))
≤-refl (a₁ ⊔ a₂) = ≤-⊔L (≤-⊔R₁ (≤-refl a₁)) (≤-⊔R₂ (≤-refl a₂))

≤-trans : {a b c : Session} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans (≤-⊓L₁ a₁≤b) b≤c = ≤-⊓L₁ (≤-trans a₁≤b b≤c)
≤-trans (≤-⊓L₂ a₂≤b) b≤c = ≤-⊓L₂ (≤-trans a₂≤b b≤c)
≤-trans (≤-⊔L a₁≤b a₂≤b) b≤c = ≤-⊔L (≤-trans a₁≤b b≤c) (≤-trans a₂≤b b≤c)
≤-trans (≤-⊓⊔ x₁ x₂ x₃ x₄) b≤c =
  ≤-⊓⊔ (≤-trans x₁ b≤c) (≤-trans x₂ b≤c) (≤-trans x₃ b≤c) (≤-trans x₄ b≤c)
≤-trans a≤b (≤-⊓R b≤c₁ b≤c₂) = ≤-⊓R (≤-trans a≤b b≤c₁) (≤-trans a≤b b≤c₂)
≤-trans a≤b (≤-⊔R₁ b≤c₁) = ≤-⊔R₁ (≤-trans a≤b b≤c₁)
≤-trans a≤b (≤-⊔R₂ b≤c₂) = ≤-⊔R₂ (≤-trans a≤b b≤c₂)
≤-trans a≤b (≤-⊔⊓ x₁ x₂ x₃ x₄) =
  ≤-⊔⊓ (≤-trans a≤b x₁) (≤-trans a≤b x₂) (≤-trans a≤b x₃) (≤-trans a≤b x₄)
≤-trans ≤-One b≤c = b≤c
≤-trans (≤-⊗ a₁≤b₁ a₂≤b₂) (≤-⊗ b₁≤c₁ b₂≤c₂) =
  ≤-⊗ (≤-trans a₁≤b₁ b₁≤c₁) (≤-trans a₂≤b₂ b₂≤c₂)
≤-trans (≤-⊸ b₁≤a₁ a₂≤b₂) (≤-⊸ c₁≤b₁ b₂≤c₂) =
  ≤-⊸ (≤-trans c₁≤b₁ b₁≤a₁) (≤-trans a₂≤b₂ b₂≤c₂)
≤-trans (≤-⊓R a≤b₁ a≤b₂) (≤-⊓L₁ b₁≤c) = ≤-trans a≤b₁ b₁≤c
≤-trans (≤-⊓R a≤b₁ a≤b₂) (≤-⊓L₂ b₂≤c) = ≤-trans a≤b₂ b₂≤c
≤-trans (≤-⊓R a≤b₁ a≤b₂) (≤-⊓⊔ x₁ x₂ x₃ x₄) = {!   !}
≤-trans (≤-⊔R₁ a≤b₁) (≤-⊔L b₁≤c b₂≤c) = ≤-trans a≤b₁ b₁≤c
≤-trans (≤-⊔R₂ a≤b₂) (≤-⊔L b₁≤c b₂≤c) = ≤-trans a≤b₂ b₂≤c
≤-trans (≤-⊔⊓ x₁ x₂ x₃ x₄) b≤c = {!   !}

{-
-}
