/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra

universe u

@[reducible]
def WPExcept (ε : Type u) := ExceptT ε WPPure

instance (ε : Type u) : Monad (WPExcept ε) :=
  inferInstanceAs (Monad (ExceptT ε WPPure))

protected
def WPExcept.rel (ε : Type u) : MonadRel (WPExcept ε) (WPExcept ε) where
  rel {α} x y := ∀ (p : Except ε α → Prop), y.predT p → x.predT p
  pure a p := by dsimp; exact id
  bind {α} {β} {x} {y} f g hxy hfg p := by
    dsimp [bind] at *
    dsimp [ExceptT.bind, ExceptT.mk]
    apply mrel_bind (m:=WPPure) hxy
    intro a
    cases a
    case a.error e =>
      dsimp [ExceptT.bindCont]
      exact mrel_pure (m:=WPPure) _
    case a.ok a =>
      dsimp [ExceptT.bindCont]
      exact hfg a

instance (ε : Type u) : SpecMonad (WPExcept ε) where
  rel := WPExcept.rel ε
  trans := by
    dsimp [WPExcept.rel]
    intro α x y z hxy hyz p hp
    exact hxy p (hyz p hp)

example (ε : Type u) (α : Type _) : WPPure α → WPExcept ε α := monadLift
