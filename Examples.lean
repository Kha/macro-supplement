import Lean  -- necessary only for the last tactic example

section «2»
namespace Typing
axiom Ctxt : Type
axiom Term : Type
axiom Typ  : Type
axiom Typing : Ctxt → Term → Typ → Type
-- typing
notation Γ "⊢" e ":" τ => Typing Γ e τ
-- end
#check fun a b c => a ⊢ b : c
--macro Γ:term "⊢" e:term ":" τ:term : term => `(Typing $Γ $e $τ)
--
--syntax term "⊢" term ":" term : term
--macro_rules
--  | `($Γ ⊢ $e : $τ) => `(Typing $Γ $e $τ)
end Typing

-- already built into Lean
/-
-- exists
notation "∃" b "," P => Exists (fun b => P)
-- end
-/
#check ∃ x, x = x
#check ∃ (x : Nat), x = x


-- defthunk
macro "defthunk" id:ident ":=" e:term : command =>
  `(def $id := Thunk.mk (fun _ => $e))
defthunk big := mkArray 100000 true
-- end
#check big


namespace Union
abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α
macro:100 x:term " ∈ " s:term:99 : term => `(mem $x $s)

-- union
syntax "{" term "|" term "}" : term
macro_rules
  | `({$x ∈ $s | $p}) => `(setOf (fun $x => $x ∈ $s ∧ $p))
  | `({$b      | $p}) => `(setOf (fun $b => $p))

notation "⋃" b "," p => Union {b | p}
-- end

#check ⋃ x,              x = x
#check ⋃ (x : Set Unit), x = x
#check ⋃ x ∈ univ,       x = x


-- le
macro_rules
  | `({$x ≤ $e | $p}) => `(setOf (fun $x => $x ≤ $e ∧ $p))
-- end

#check {x ≤ 1 | x = x}
end Union


-- final example: see ./Bigop.lean
end «2»


section «3»
-- see also ./Expander.lean

-- hygiene_example
def x := 1
def e := fun (y : Nat) => x
notation "const" e => fun (x : Nat) => e
def y := const x
-- end
#check y


-- hygiene_example2
macro "m" n:ident : command => `(
  def f := 1
  macro "mm" : command => `(def $n:ident := f    def f := $n:ident))
-- end
m f
mm
mm
end «3»


section «6»
-- myTac
macro "myTac" : tactic => `(intro h; exact h)
theorem triv (p : Prop) : p → p := by myTac
-- end

open Lean.Elab.Tactic
-- myTac2
def myTac2 : TacticM Unit :=
  do let stx ← `(tactic|intro h; exact h); evalTactic stx
-- end
end «6»
