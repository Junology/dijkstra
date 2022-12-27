/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!

# Monad homomorphism

A ***monad transformation*** is a natural transformation between monads which preserves `pure` and `bind`.
More precisely, for monads `m : Type u → Type v` and `n : Type u → Type w`, the type `MonadHom m n` consists of morphisms `app : {α : Type u} → m α → n α` satisfying the following:

```lean
MonadHom.app_pure : {α : Type u} : ∀ (a : α), app (pure a) = pure a
MonadHom.app_bind : {α β : Type u} : ∀ (x : m α) (f : α → m β) : app (x >>= f) = app x >>= app ∘ f
```

-/

universe u v v₁ v₂ v₃ w 

/-- For monads `m : Type u → Type v` and `n : Type u → Type w`, a monad homomorphism from `m` to `n` is a family of maps `app : {α : Type u} → m α → n α` which respects `pure` and `bind`. -/
structure MonadHom (m : Type u → Type v) [Monad m] (n : Type u → Type w) [Monad n] where
  app {α : Type u} : m α → n α
  app_pure {α : Type u} (a : α) : app (pure a) = pure a
  app_bind {α β : Type u} (x : m α) (f : α → m β) : app (x >>= f) = app x >>= app ∘ f

namespace MonadHom

/-- Composition of two monad homomorphisms. @warning Be careful about the order of the arguments; here we follow the convention of `Mathlib.CategoryTheory`. -/
def comp {m₁ : Type u → Type v₁} [Monad m₁] {m₂ : Type u → Type v₂} [Monad m₂] {m₃ : Type u → Type v₃} [Monad m₃] (F : MonadHom m₁ m₂) (G : MonadHom m₂ m₃) : MonadHom m₁ m₃ where
  app := G.app ∘ F.app
  app_pure a := G.app_pure a ▸ F.app_pure a ▸ rfl
  app_bind x f := G.app_bind (F.app x) (F.app ∘ f) ▸ F.app_bind x f ▸ rfl

/-- Two monad homomorphisms `F` and `G` equal to each other provided `F.app = G.app` by virtue of the `proofIrrel` -/
theorem eq {m : Type u → Type v} [instm : Monad m] {n :Type u → Type w} [instn : Monad n] : {F G : @MonadHom m instm n instn} → @MonadHom.app m instm n instn F = @MonadHom.app m instm n instn G → F = G
| mk _ _ _, mk _ _ _, rfl => rfl

/-- Functional extensionality for monad homomorphisms. -/
theorem ext {m : Type u → Type v} [Monad m] {n : Type u → Type w} [Monad n] {F G : MonadHom m n} (h : ∀ {α : Type u} (x : m α), F.app x = G.app x) : F = G := by
  apply MonadHom.eq (m:=m)
  funext _ x
  exact h x

end MonadHom
