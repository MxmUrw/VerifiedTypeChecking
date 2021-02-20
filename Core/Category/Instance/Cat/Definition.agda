

module Verification.Core.Category.Instance.Cat.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type.Definition
open import Verification.Core.Category.Iso

------------------
-- The category of categories


id-Cat : ∀{X : Category 𝑖} -> Functor X X
⟨ id-Cat ⟩ = id-𝒰
IFunctor.map (of id-Cat) f = f
IFunctor.functoriality-id (of id-Cat) = refl
IFunctor.functoriality-◆ (of id-Cat) = refl
IFunctor.functoriality-≣ (of id-Cat) = id


comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘} -> (F : Functor X Y) -> (G : Functor Y Z) -> Functor X Z
⟨ comp-Cat F G ⟩ = comp-𝒰 ⟨ F ⟩ ⟨ G ⟩
IFunctor.map (of comp-Cat F G) f = map (map f)
IFunctor.functoriality-id (of comp-Cat F G) = {!!}
IFunctor.functoriality-◆ (of comp-Cat F G) = {!!}
IFunctor.functoriality-≣ (of comp-Cat F G) = {!!}

-- instance IFunctor:comp-Cat = #openstruct comp-Cat


-- IFunctor:comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘}
--                     -> (F : Functor X Y) -> (G : Functor Y Z) -> IFunctor X Z (comp-Cat ⟨ F ⟩ ⟨ G ⟩)
-- IFunctor.map (IFunctor:comp-Cat F G) f = map (map f)
--   -- ≡[ i ]⟨ map (functoriality-id) ⟩
-- IFunctor.functoriality-id (IFunctor:comp-Cat F G) {a = a} =  map (map id)   ≣⟨ functoriality-≣ functoriality-id ⟩
--                                                              map id         ≣⟨ functoriality-id ⟩
--                                                              id ∎
--  -- a [ i ]⟨ map (functoriality-◆ f g i) ⟩
--  -- (map f) (map g) ⟩
-- IFunctor.functoriality-◆ (IFunctor:comp-Cat F G) {f = f} {g} = map (map (f ◆ g)) ≣⟨ functoriality-≣ functoriality-◆ ⟩
--                                                                map (map f ◆ map g) ≣⟨ functoriality-◆ ⟩
--                                                                map (map f) ◆ map (map g) ∎
-- IFunctor.functoriality-≣ (IFunctor:comp-Cat F G) {f = f} {g} x = functoriality-≣ (functoriality-≣ x)

-- Functor:comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘}
--                     -> (F : Functor X Y) -> (G : Functor Y Z) -> Functor X Z
-- Functor:comp-Cat F G = functor _ {{IFunctor:comp-Cat F G}}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record ≣-Functor (F G : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field
      object-path : ⟨ F ⟩ ≡ ⟨ G ⟩
      arrow-path  : ∀{a b} -> ∀(f : Hom a b) -> transport (λ i -> Hom (object-path i a) (object-path i b)) (map f) ≣ map f



Category:Category : (𝑖 : 𝔏 ^ 3) -> Category _
⟨ Category:Category 𝑖 ⟩ = Category 𝑖
ICategory.Hom (of Category:Category 𝑖) = Functor
ICategory._≣_ (of Category:Category 𝑖) = ≣-Functor
ICategory.IEquiv:≣ (of Category:Category 𝑖) = {!!}
ICategory.id (of Category:Category 𝑖) = id-Cat
ICategory._◆_ (of Category:Category 𝑖) = comp-Cat
ICategory.unit-l-◆ (of Category:Category 𝑖) = {!!}
ICategory.unit-r-◆ (of Category:Category 𝑖) = {!!}
ICategory.unit-2-◆ (of Category:Category 𝑖) = {!!}
ICategory.assoc-l-◆ (of Category:Category 𝑖) = {!!}
ICategory.assoc-r-◆ (of Category:Category 𝑖) = {!!}
ICategory._◈_ (of Category:Category 𝑖) = {!!}

instance ICategory:Category = #openstruct Category:Category

-- instance
--   ICategory:Category : ICategory (Category 𝑖) _
--   ICategory.Hom ICategory:Category = Functor
--   ICategory._≣_ ICategory:Category F G = ∑ λ (p : ⟨ F ⟩ ≡ ⟨ G ⟩) -> ∀{a b} -> ∀(f : Hom a b) -> PathP (λ i -> Hom (p i a) (p i b)) (map f) (map f)
--   ICategory.IEquiv:≣ ICategory:Category = {!!}
--   ICategory.id ICategory:Category = Functor:id-Cat
--   ICategory._◆_ ICategory:Category = Functor:comp-Cat
--   ICategory._◈_ ICategory:Category = {!!}
--   ICategory.unit-l-◆ ICategory:Category = {!!}
--   ICategory.unit-r-◆ ICategory:Category = {!!}
--   ICategory.unit-2-◆ ICategory:Category = {!!}
--   ICategory.assoc-l-◆ ICategory:Category = {!!}
--   ICategory.assoc-r-◆ ICategory:Category = {!!}


{-

LiftCategory : Category 𝑖 -> (J : ULevel ^ 3) -> 𝒰 (J ⌄ ₀ ⊔ 𝑖 ⌄ ₀)
LiftCategory X J = Lift {j = J ⌄ ₀} ⟨ X ⟩

instance
  ICategory:LiftCategory : ∀{C : Category 𝑖} -> ICategory (LiftCategory C 𝑗) _
  ICategory.Hom (ICategory:LiftCategory {𝑗 = J} {C = C}) (lift a) (lift b) = Lift {j = J ⌄ ₁} (Hom a b)
  ICategory._≣_ (ICategory:LiftCategory {𝑗 = J} {C = C}) (lift f) (lift g) = Lift {j = J ⌄ ₂} (f ≣ g)
  ICategory.IEquiv:≣ (ICategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  ICategory.id (ICategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  ICategory._◆_ (ICategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  ICategory._◈_ (ICategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  ICategory.unit-l-◆ (ICategory:LiftCategory {C}) = {!!}
  ICategory.unit-r-◆ (ICategory:LiftCategory {C}) = {!!}
  ICategory.unit-2-◆ (ICategory:LiftCategory {C}) = {!!}
  ICategory.assoc-l-◆ (ICategory:LiftCategory {C}) = {!!}
  ICategory.assoc-r-◆ (ICategory:LiftCategory {C}) = {!!}


Category:LiftCategory : ∀(C : Category 𝑖) {𝑗 : ULevel ^ 3} -> Category (𝑖 ⌄ ₀ ⊔ 𝑗 ⌄ ₀ , 𝑖 ⌄ ₁ ⊔ 𝑗 ⌄ ₁ , 𝑖 ⌄ ₂ ⊔ 𝑗 ⌄ ₂)
Category:LiftCategory C {j} = category (LiftCategory C j) {{ICategory:LiftCategory {𝑗 = j} {C = C}}}


instance
  ILiftHom:Functor : ∀{C : Category 𝑖} {D : Category 𝑗} -> ILiftHom (Category:LiftCategory C {zipL 𝑖 𝑗}) (Category:LiftCategory D {zipL 𝑖 𝑗}) (Functor C D)
  ⟨ ⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F ⟩ (lift x) = lift (⟨ F ⟩ x)
  IFunctor.map (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) (lift f) = lift (map f)
  IFunctor.functoriality-id (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  IFunctor.functoriality-◆ (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  ⟨ IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G ⟩ x = lower (⟨ G ⟩ (lift x))
  IFunctor.map (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) f = lower (map (lift f))
  IFunctor.functoriality-id (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  IFunctor.functoriality-◆ (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  IIso-𝒰./⟲ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}
  IIso-𝒰./⟳ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}


-}
