import Init.Lean  -- necessary only for the last tactic example
-- The new, macro-based frontend is not the default yet, so we activate it explicitly for the remaining file
new_frontend

section «2»
namespace Typing
axiom Ctxt : Type
axiom Term : Type
axiom Typ  : Type
axiom Typing : Ctxt → Term → Typ → Type
-- NOTE: example in the paper is minimally simplified by eliding the otherwise irrelevant token precedence
/-
-- typing
notation Γ "⊢" e ":" τ => Typing Γ e τ
-- end
-/
notation Γ "⊢":50 e ":" τ => Typing Γ e τ
#check fun a b c => a ⊢ b : c
--macro Γ:term "⊢":50 e:term ":" τ:term : term => `(Typing $Γ $e $τ)
--
--syntax term "⊢":50 term ":" term : term
--macro_rules
--| `($Γ ⊢ $e : $τ) => `(Typing $Γ $e $τ)
end Typing

-- exists
notation "∃" b "," P => Exists (fun b => P)
-- end
#check ∃ x, x = x
#check ∃ (x : Nat), x = x


-- defthunk
macro "defthunk" id:ident ":=" e:term : command =>
`(def $id:ident := Thunk.mk (fun _ => $e))
defthunk big := mkArray 100000 true
-- end
#check big


namespace Union
abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α
macro x:term " ∈ ":100 s:term:99 : term => `(mem $x $s)

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
section
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
end
end «3»


section «6»
-- myTac
macro "myTac" : tactic => `(intro h; exact h)
theorem triv (p : Prop) : p → p := begin myTac end
-- end

open Lean.Elab.Tactic
-- myTac2
def myTac2 : TacticM Unit :=
do stx ← `(tactic|intro h; exact h); evalTactic stx
-- end
end «6»
