/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Control.Lawful
import Dijkstra.Control.Monad.Hom

/-!

# Monad transformer

-/

universe u v w

class MonadTransformer (t : (Type u → Type v) → (Type u → Type w)) where
  instMonad (m : Type u → Type v) [Monad m] : Monad (t m)
  instMonadLift (m : Type u → Type v) [Monad m] : MonadLift m (t m)
  liftHom {m : Type u → Type v} [Monad m] {n : Type u → Type v} [Monad n] : MonadHom m n → MonadHom (t m) (t n)
  monadLift_pure {m : Type u → Type v} [Monad m] [LawfulMonad m] : ∀ {α : Type u} (a : α), (instMonadLift m).monadLift (pure a) = pure (f:=t m) a
  monadLift_bind {m : Type u → Type v} [Monad m] [LawfulMonad m] : ∀ {α β : Type u} (x : m α) (f : α → m β), (instMonadLift m).monadLift (x >>= f) = (instMonadLift m).monadLift x >>= (instMonadLift m).monadLift ∘ f
  lift_natural {m : Type u → Type v} [Monad m] [LawfulMonad m] {n : Type u → Type v} [Monad n] [LawfulMonad m] (F : MonadHom m n) : ∀ {α : Type u} (x : m α), monadLift (F.app x) = F.app (monadLift x)

attribute [instance 1] MonadTransformer.instMonad MonadTransformer.instMonadLift

instance (ρ : Type _) : MonadTransformer (ReaderT ρ) where
  instMonad _ := inferInstance
  instMonadLift _ := inferInstance
  liftHom F := {
    app := λ x => F.app ∘ x
    app_pure := by
      intro _ a; funext r
      conv => lhs; change F.app (pure a); rw [F.app_pure]
    app_bind := by
      intro _ _ x f; funext r; dsimp
      conv => lhs; dsimp [bind, ReaderT.bind]; rw [F.app_bind]
  }
  monadLift_pure := by intros; rfl
  monadLift_bind := by intros; rfl
  lift_natural F := by
    intro _ x
    dsimp [MonadHom.comp, monadLift,MonadLift.monadLift]


instance (ε : Type u) : MonadTransformer (ExceptT ε) where
  instMonad _ := inferInstance
  instMonadLift _ := inferInstance
  liftHom F := {
    app := F.app
    app_pure := by
      intro _ a
      dsimp [pure, ExceptT.pure, ExceptT.mk]
      rw [F.app_pure]
    app_bind := by
      intro _ _ x f
      dsimp [bind, ExceptT.bind, ExceptT.mk]
      rw [F.app_bind]
      apply bind_congr
      intro a
      cases a
      case error e => dsimp [ExceptT.bindCont]; rw [F.app_pure]
      case ok a => dsimp [ExceptT.bindCont]
  }
  monadLift_pure a := by
    conv => lhs; dsimp [MonadLift.monadLift, ExceptT.lift]
    conv => rhs; dsimp [pure, ExceptT.pure]
    apply congrArg
    rw [map_pure]
  monadLift_bind x f := by
    dsimp [MonadLift.monadLift, ExceptT.lift]
    conv => rhs; dsimp [bind, ExceptT.bind]; congr; dsimp [ExceptT.mk, ExceptT.bindCont]
    apply congrArg
    conv => lhs; rw [map_eq_pure_bind, bind_assoc]; rhs; ext; rw [←map_eq_pure_bind]
    conv => rhs; rw [map_bind]; rhs; ext a; change Except.ok <$> f a; 
  lift_natural F _ x := rfl

