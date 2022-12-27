/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Init
import Dijkstra.Control.Lawful
import Dijkstra.Control.Monad.Hom
import Dijkstra.Control.Monad.Rel
import Dijkstra.Control.Monad.Dijkstra
import Dijkstra.Control.Monad.Spec
import Dijkstra.Control.Monad.Transformer

universe u

@[reducible]
def WPExcept (ε : Type u) := ExceptT ε WPPure

instance (ε : Type u) : Monad (WPExcept ε) :=
  inferInstanceAs (Monad (ExceptT ε WPPure))

instance (ε : Type u) : SpecMonad (WPExcept ε) where
  rel {α} x y := ∀ (p : Except ε α → Prop), y.predT p → x.predT p
  rel_pure a p := by dsimp; exact id
  rel_bind {α} {β} {x} {y} f g hxy hfg p := by
    dsimp [bind] at *
    dsimp [ExceptT.bind, ExceptT.mk]
    apply SpecMonad.toMonadRel.rel_bind (m:=WPPure) (n:=WPPure) hxy
    intro a
    cases a
    case a.error e =>
      dsimp [ExceptT.bindCont]
      exact SpecMonad.toMonadRel.rel_pure (m:=WPPure) (n:=WPPure) _
    case a.ok a =>
      dsimp [ExceptT.bindCont]
      exact hfg a

example (ε : Type u) (α : Type _) : WPPure α → WPExcept ε α := monadLift
