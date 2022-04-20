import Lean

namespace Lean
namespace Expander

open Lean.Syntax

-- Result of name resolution. As in the paper, we will ignore the second component here.
abbrev NameRes := Name × List String
-- We model the global context more precisely as a mapping from symbols to qualified symbols,
-- e.g. (`a ↦ [`ns1.a, `ns2.a])
abbrev GlobalContext := Name → List NameRes

-- the simplified transformer monad
structure TransformerContext where
  gctx : GlobalContext
  currMacroScope : MacroScope

abbrev TransformerM := ReaderT TransformerContext Id
abbrev Transformer := Syntax → TransformerM Syntax

-- support syntax quotations in transformers
instance : MonadQuotation TransformerM where
  getCurrMacroScope   := do let ctx ← read; pure ctx.currMacroScope
  -- dummy impls, unused
  withFreshMacroScope := fun x => x
  getRef              := pure Syntax.missing
  withRef             := fun _ x => x
  -- The actual implementation also adds the current module name to macro scopes for global uniqueness,
  -- which we can ignore in this single-file example.
  getMainModule       := pure `Expander

-- the expander extension of the transformer monad
structure ExpanderContext extends TransformerContext where
  lctx : NameSet
  macros : Name → Option Transformer

abbrev ExpanderM := ReaderT ExpanderContext <| StateT MacroScope <| ExceptT String <| Id

instance MonadQuotation : MonadQuotation ExpanderM where
  getCurrMacroScope   := do let ctx ← read; pure ctx.currMacroScope
  withFreshMacroScope := fun x => do
    let fresh ← modifyGet (fun n => (n, n + 1))
    withReader (fun ctx => { ctx with currMacroScope := fresh }) x
  getMainModule       := pure `Expander
  -- dummy impls, unused
  getRef              := pure Syntax.missing
  withRef             := fun _ x => x

-- implicitly coerce transformer monad into expander monad
instance : Coe (TransformerM α) (ExpanderM α) where
  coe t := fun ctx => t ctx.toTransformerContext

-- simplified: ignore the module name parameter
def addMacroScope (n : Name) (scp : MacroScope) : Name :=
  Lean.addMacroScope `Expander n scp

def getGlobalContext : TransformerM GlobalContext := do
  return (← read).gctx

def getLocalContext : ExpanderM NameSet := do
  return (← read).lctx

def resolve (gctx : GlobalContext) (n : Name) : List NameRes :=
  gctx n

-- slightly more meaningful name
def getIdentVal : Syntax → Name := Syntax.getId

def getPreresolved : Syntax → List NameRes
  | Syntax.ident (preresolved := preresolved) .. => preresolved
  | _                                            => []

def mkOverloadedIds (cs : List NameRes) : Syntax :=
  Syntax.node choiceKind (cs.toArray.map (mkIdent ∘ Prod.fst))

def withLocal (l : Name) : ExpanderM Syntax → ExpanderM Syntax :=
  withReader (fun ctx => { ctx with lctx := ctx.lctx.insert l })

def getTransformerFor (k : SyntaxNodeKind) : ExpanderM (Syntax → ExpanderM Syntax) := do
  match (← read).macros k with
  | some t => return fun stx => t stx
  | none   => throw ("unknown macro " ++ toString k)

-- slightly simplified from the actual implementation
partial def getAntiquotationIds (stx : Syntax) : ExpanderM (Array Syntax) := do
  let mut ids := #[]
  for stx in stx.topDown do
    if (isAntiquot stx || isTokenAntiquot stx) && !isEscapedAntiquot stx then
      let anti := getAntiquotTerm stx
      if anti.isIdent then ids := ids.push anti
      else throw "complex antiquotation not allowed here"
  return ids

-- Get all pattern vars (as `Syntax.ident`s) in `stx`
partial def getPatternVars (stx : Syntax) : ExpanderM (Array Syntax) :=
  if stx.isQuot then
    getAntiquotationIds stx
  else match stx with
    | `(_)            => #[]
    | `($id:ident)    => #[id]
    | `($id:ident@$e) => do (← getPatternVars e).push id
    | _               => throw "unsupported pattern in syntax match"

-- expand
partial def expand : Syntax → ExpanderM Syntax
  | `($id:ident) => do
    let val : Name := getIdentVal id
    let gctx ← getGlobalContext
    let lctx ← getLocalContext
    if lctx.contains val then
      pure (mkIdent val)
    else match resolve gctx val ++ getPreresolved id with
      | []        => throw ("unknown identifier " ++ toString val)
      | [(id, _)] => pure (mkIdent id)
      | ids       => pure (mkOverloadedIds ids)
  | `(fun ($id : $ty) => $e) => do
    let val := getIdentVal id
    let ty ← expand ty
    let e ← withLocal val (expand e)
    `(fun ($(mkIdent val) : $ty) => $e)
-- end
  -- more core forms
  | `(fun $id:ident => $e) => do
    let e ← withLocal (getIdentVal id) (expand e)
    `(fun $id:ident => $e)
  | `($num:numLit) => `($num:numLit)
  | `($str:strLit) => `($str:strLit)
  | `($n:quotedName) => `($n:quotedName)
  | `($fn $args*) => do
    let fn ← expand fn
    let args ← args.mapM expand
    `($fn $args*)
  | `(def $id := $e) => do
    let e ← expand e
    `(def $id := $e)
  -- syntax: keep as-is
  | `(syntax $[(name := $n)]? $[(priority := $prio)]? $[$args:stx]* : $kind) => `(syntax $[(name := $n)]? $[(priority := $prio)]? $[$args:stx]* : $kind)
  -- macro_rules: expand rhs (but not lhs) to exercise syntax quotation macro
  | `(macro_rules | $lhs => $rhs) => do
    let vars ← getPatternVars lhs
    let rhs ← vars.foldr (fun var ex => withLocal var.getId ex) (expand rhs)
    `(macro_rules | $lhs => $rhs)
  -- we will ignore double-backtick quotations generated by `notation` for this example
  | `(``($e)) => `(`($e))
  | stx => do
    -- expansion consists of multiple commands => yield and get called back per command
    if stx.isOfKind nullKind then pure stx else do
    let t ← getTransformerFor stx.getKind
    let stx ← withFreshMacroScope (t stx)
    expand stx

open Lean.Elab.Term.Quotation
-- quoteSyntax
partial def quoteSyntax : Syntax → TransformerM Syntax
  | Syntax.ident info rawVal val preresolved => do
    let gctx ← getGlobalContext
    let preresolved := resolve gctx val ++ preresolved
    `(Syntax.ident SourceInfo.none $(quote rawVal)
        (addMacroScope $(quote val) msc) $(quote preresolved))
  | stx@(Syntax.node k args) =>
    if isAntiquot stx then pure (getAntiquotTerm stx)
    else do
      let args ← args.mapM quoteSyntax
      `(Syntax.node $(quote k) $(quote args))
  | Syntax.atom info val => `(Syntax.atom SourceInfo.none $(quote val))
  | Syntax.missing => pure Syntax.missing

def expandStxQuot (stx : Syntax) : TransformerM Syntax := do
  let stx ← quoteSyntax (stx.getArg 1)
  `(do msc ← getCurrMacroScope; pure $stx)
-- end

-- two more, simple macros
def expandDo : Transformer
  | `(do $id:ident ← $val:term; $body:term) => `(Bind.bind $val (fun $id:ident => $body))
  | _                                  => pure Syntax.missing

def expandParen : Transformer
  | `(($e)) => pure e
  | _       => pure Syntax.missing

-- custom Syntax pretty printer for our core forms that uses the paper's notation for hygienic identifiers
def ppIdent (n : Name) : Format :=
  let v := extractMacroScopes n
  format <| v.scopes.foldl Name.mkNum v.name

-- flip to make output more readable
def hideMacroRulesRhs := false

open Std.Format
partial def pp : Syntax → Format
  | `($id:ident) => match getPreresolved id with
    | [] => ppIdent id.getId
    | ps => ppIdent id.getId ++ bracket "{" (joinSep (ps.map (format ∘ Prod.fst)) ", ") "}"
  | `(fun ($id : $ty) => $e) => paren f!"fun {paren (pp id ++ " : " ++ pp ty)} => {pp e}"
  | `(fun $id => $e) => paren f!"fun {pp id} => {pp e}"
  | `($num:numLit) => format (num.isNatLit?.getD 0)
  | `($str:strLit) => repr (str.isStrLit?.getD "")
  | `($fn $args*) => paren <| pp fn ++ " " ++ joinSep (args.toList.map pp) line
  | `(def $id:ident := $e) => f!"def {ppIdent id.getId} := {pp e}"
  | `(syntax $[(name := $n)]? $[(priority := $prio)]? $[$args:stx]* : $kind) => "syntax ..."  -- irrelevant for this example
  | `(macro_rules | $lhs => $rhs) => f!"macro_rules |{lhs.reprint.getD ""} => {if hideMacroRulesRhs then f!"..." else pp rhs}"
  | stx => f!"<not a core form: {stx}>"

-- integrate example expander into frontend, between parser and elaborator. Not pretty.
section Elaboration
open Lean.Elab
open Lean.Elab.Frontend

-- run expander: adapt global context and set of macro from Environment
def expanderToFrontend (ref : Syntax) (e : ExpanderM Syntax) : FrontendM Syntax := runCommandElabM <| withRef ref do
  let st ← get
  let scope := st.scopes.head!
  match e {
    gctx := fun n => (match st.env.find? n with
      | some _ => [(n, [])]
      | none   => [] : List NameRes),
    lctx := {},
    currMacroScope := st.nextMacroScope,
    macros := fun k =>
      -- our hardcoded example macros
      if k == `Lean.Parser.Term.quot then some expandStxQuot
      else if k == `Lean.Parser.Term.do then some expandDo
      else if k == `Lean.Parser.Term.paren then some expandParen
      -- `notation`, `macro`, and macros generated at runtime
      else
        match macroAttribute.getValues st.env k with
        | t::_ => some (fun stx ctx =>
          match t stx {
            mainModule := `Expander
            currMacroScope := ctx.currMacroScope
            ref := ref
            methods := Macro.mkMethods {
              expandMacro?     := fun stx => do
                match (← expandMacroImpl? st.env stx) with
                | some (_, stx') => some stx'
                | none           => none
              hasDecl          := fun declName => return st.env.contains declName
              getCurrNamespace := return scope.currNamespace
              resolveNamespace? := fun n => return ResolveName.resolveNamespace? st.env scope.currNamespace scope.openDecls n
              resolveGlobalName := fun n => return ResolveName.resolveGlobalName st.env scope.currNamespace scope.openDecls n
            }
          } {
            macroScope := 0
          } with
          | EStateM.Result.ok stx s => stx
          | _ => Syntax.missing)
        | _           => none
  } (st.nextMacroScope + 1) with
  | Except.ok (stx, nextMacroScope) => do
    modify (fun st => {st with nextMacroScope := nextMacroScope})
    pure stx
  | Except.error e => do
    logError e
    pure Syntax.missing

partial def processCommand (cmd : Syntax) : FrontendM Unit := do
  let cmd' ← expanderToFrontend cmd <| expand cmd
  if cmd'.isOfKind nullKind then
    -- expander returned multiple commands => process in turn
    cmd'.getArgs.forM processCommand
  else do
    runCommandElabM <| logInfo (pp cmd')
    elabCommandAtFrontend cmd'

partial def processCommands : FrontendM Unit := do
  let cmdState    ← getCommandState
  let parserState ← getParserState
  let inputCtx    ← getInputContext
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, ps, messages) ← pure (Parser.parseCommand inputCtx pmctx parserState cmdState.messages)
  setParserState ps
  setMessages messages
  if Parser.isEOI cmd then do
    pure ()
  else do
    processCommand cmd
    processCommands

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (_, st) ← processCommands { inputCtx := inputCtx } |>.run { commandState := Command.mkState env {} opts, parserState := {}, cmdPos := 0 }
  pure (st.commandState.env, st.commandState.messages)

def run (input : String) : CoreM Unit := do
  let env  ← getEnv
  let opts ← getOptions
  let (env, messages) ← liftM $ process input env opts
  messages.forM fun msg => do
    IO.println (← msg.toString)

end Elaboration

-- examples
-- see also `hideMacroRulesRhs` above

#eval run "
def x := 1
def e := fun (y : Nat) => x
notation \"const\" e => fun (x : Nat) => e
def y := const x
"

#eval run "
macro \"m\" n:ident : command => `(
  def f := 1
  macro \"mm\" : command => `(
    def $n:ident := f
    def f := $n:ident))
m f
mm
mm
"

end Expander
end Lean
