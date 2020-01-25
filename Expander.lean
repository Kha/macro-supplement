import Init.Lean
namespace Lean
namespace Expander

-- Result of name resolution. As in the paper, we will ignore the second component here.
abbrev NameRes := Name × List String
-- We model the global context more precisely as a mapping from symbols to qualified symbols,
-- e.g. (`a ↦ [`a.a, `a.b])
abbrev GlobalContext := Name → List NameRes

-- the simplified transformer monad
structure TransformerM.Context :=
(gctx : GlobalContext)
(currMacroScope : MacroScope)

abbrev TransformerM := ReaderT TransformerM.Context Id
abbrev Transformer := Syntax → TransformerM Syntax

-- support syntax quotations in transformers
instance : MonadQuotation TransformerM := {
  getCurrMacroScope   := do ctx ← read; pure ctx.currMacroScope,
  withFreshMacroScope := fun _ x => x,  -- dummy impl, unused
  -- The actual implementation also adds the current module name to macro scopes for global uniqueness,
  -- which we can ignore in this single-file example.
  getMainModule       := pure `Expander
}

-- the expander extension of the transformer monad
structure ExpanderM.Context extends TransformerM.Context :=
(lctx : NameSet)
(macros : Name → Option Transformer)

abbrev ExpanderM := ReaderT ExpanderM.Context $ StateT MacroScope $ ExceptT String $ Id

instance MonadQuotation : MonadQuotation ExpanderM := {
  getCurrMacroScope   := do ctx ← read; pure ctx.currMacroScope,
  withFreshMacroScope := fun α x => do
    fresh ← modifyGet (fun n => (n, n + 1));
    adaptReader (fun (ctx : ExpanderM.Context) => {ctx with currMacroScope := fresh}) x,
  getMainModule       := pure `Expander
}

-- implicitly coerce transformer monad into expander monad
instance {α : Type} : HasCoe (TransformerM α) (ExpanderM α) := {
  coe := fun t ctx => pure $ t {..ctx}
}

-- simplified: ignore the module name parameter
def addMacroScope (n : Name) (scp : MacroScope) : Name :=
Lean.addMacroScope `Expander n scp

def getGlobalContext : TransformerM GlobalContext := do
ctx ← read;
pure ctx.gctx

def getLocalContext : ExpanderM NameSet := do
ctx ← read;
pure ctx.lctx

def resolve (gctx : GlobalContext) (n : Name) : List NameRes :=
gctx n

-- slightly more meaningful name
def getIdentVal : Syntax → Name := Syntax.getId

def getPreresolved : Syntax → List NameRes
| Syntax.ident _ _ _ preresolved => preresolved
| _                              => []

def mkOverloadedIds (cs : List NameRes) : Syntax :=
Syntax.node choiceKind (cs.toArray.map (mkTermId ∘ Prod.fst))

def withLocal (l : Name) : ExpanderM Syntax → ExpanderM Syntax :=
adaptReader (fun (ctx : ExpanderM.Context) => {ctx with lctx := ctx.lctx.insert l})

def getTransformerFor (k : SyntaxNodeKind) : ExpanderM (Syntax → ExpanderM Syntax) := do
ctx ← read;
match ctx.macros k with
| some t => pure (fun stx => t stx)
| none   => throw ("unknown macro " ++ toString k)

-- expand
partial def expand : Syntax → ExpanderM Syntax
| stx ⇒ match_syntax stx with
  | `($id:ident) => do
    let val := getIdentVal id;
    gctx ← getGlobalContext;
    lctx ← getLocalContext;
    if lctx.contains val then
      pure (mkTermId val)
    else match resolve gctx val ++ getPreresolved id with
      | []        ⇒ throw ("unknown identifier " ++ toString val)
      | [(id, _)] ⇒ pure (mkTermId id)
      | ids       ⇒ pure (mkOverloadedIds ids)
  | `(fun ($id:ident : $ty) ⇒ $e) ⇒ do
    let val := getIdentVal id;
    ty ← expand ty;
    e ← withLocal val (expand e);
    `(fun ($(mkTermId val) : $ty) ⇒ $e)
-- end
  -- more core forms
  | `(fun $id:ident ⇒ $e) ⇒ do
    e ← withLocal (getIdentVal id) (expand e);
    `(fun $id:ident ⇒ $e)
  | `($num:num) => `($num:num)
  | `($str:str) => `($str:str)
  | `($n:quotedName) => `($n:quotedName)
  | `($fn $args*) => do
    fn ← expand fn;
    args ← args.mapM expand;
    `($fn $args*)
  | `(def $id := $e) => do
    e ← expand e;
    `(def $id := $e)
  -- syntax: keep as-is
  | `(syntax [$cat] $args* : $kind) => `(syntax [$cat] $args* : $kind)
  -- macro_rules: expand rhs (but not lhs) to exercise syntax quotation macro
  | `(macro_rules | $lhs => $rhs) => do
    let vars := Lean.Elab.Term.Quotation.getPatternVars lhs;
    rhs ← vars.foldr (fun var ex => withLocal (var.getIdAt 0) ex) (expand rhs);
    `(macro_rules | $lhs => $rhs)
  | _ => do
    -- expansion consists of multiple commands => yield and get called back per command
    if stx.isOfKind nullKind then pure stx else do
    t ← getTransformerFor stx.getKind;
    stx ← withFreshMacroScope (t stx);
    expand stx

open Lean.Elab.Term.Quotation
-- quoteSyntax
partial def quoteSyntax : Syntax → TransformerM Syntax
| Syntax.ident info rawVal val preresolved ⇒ do
  gctx ← getGlobalContext;
  let preresolved := resolve gctx val ++ preresolved;
  `(Syntax.ident none $(quote rawVal) (addMacroScope $(quote val) msc) $(quote preresolved))
| stx@(Syntax.node k args) ⇒
  if isAntiquot stx then pure (getAntiquotTerm stx)
  else do
    args ← args.mapM quoteSyntax;
    `(Syntax.node $(quote k) $(quote args))
| Syntax.atom info val ⇒ `(Syntax.atom none $(quote val))
| Syntax.missing ⇒ pure Syntax.missing

def expandStxQuot (stx : Syntax) : TransformerM Syntax := do
stx ← quoteSyntax (stx.getArg 1);
`(do msc ← getCurrMacroScope; pure $stx)
-- end

-- two more, simple macros
def expandDo (stx : Syntax) : TransformerM Syntax :=
match_syntax stx with
| `(do $id:ident ← $val; $body:term) => `(HasBind.bind $val (fun $id:ident => $body))
| _                                  => pure Syntax.missing

def expandParen (stx : Syntax) : TransformerM Syntax :=
match_syntax stx with
| `(($e)) => pure e
| _       => pure Syntax.missing

-- custom Syntax pretty printer for our core forms that uses the paper's notation for hygienic identifiers
open Lean.Format
def ppIdent (n : Name) : Format :=
let v := extractMacroScopes n;
fmt $ v.scopes.foldl mkNameNum v.name

-- flip to make output more readable
def hideMacroRulesRhs := false

partial def pp : Syntax → Format
| stx => match_syntax stx with
  | `($id:ident) => match getPreresolved id with
    | [] => ppIdent id.getId
    | ps => ppIdent id.getId ++ bracket "{" (joinSep (ps.map (fmt ∘ Prod.fst)) ", ") "}"
  | `(fun ($id : $ty) => $e) => paren $ "fun " ++ paren (pp id ++ " : " ++ pp ty) ++ " ⇒ " ++ pp e
  | `(fun $id => $e) => paren $ "fun " ++ pp id ++ " ⇒ " ++ pp e
  | `($num:numLit) => fmt (num.isNatLit?.getD 0)
  | `($str:strLit) => repr (str.isStrLit?.getD "")
  | `($fn $args*) => paren $ pp fn ++ " " ++ joinSep (args.toList.map pp) line
  | `(def $id:ident := $e) => "def " ++ ppIdent id.getId ++ " := " ++ pp e
  | `(syntax [$cat] $args* : $kind) => "syntax ..."  -- irrelevant for this example
  | `(macro_rules | $lhs => $rhs) => "macro_rules |" ++ lhs.reprint.getD "" ++ " => " ++ (if hideMacroRulesRhs then "..." else pp rhs)
  | _ => "<not a core form: " ++ toString stx ++ ">"

-- integrate example expander into frontend, between parser and elaborator. Not pretty.
section Elaboration
open Lean.Elab
open Lean.Elab.Frontend

def runCommandElabM' (x : Command.CommandElabM Syntax) : FrontendM Syntax :=
fun ctx => do
  cmdPos ← liftIOCore! $ ctx.cmdPosRef.get;
  let cmdCtx : Command.Context := { cmdPos := cmdPos, stateRef := ctx.commandStateRef, fileName := ctx.inputCtx.fileName, fileMap := ctx.inputCtx.fileMap };
  EIO.catchExceptions (x cmdCtx) (fun _ => pure Syntax.missing)

-- run expander: adapt global context and set of macro from Environment
def expanderToFrontend (ref : Syntax) (e : ExpanderM Syntax) : FrontendM Syntax := runCommandElabM' $ do
st ← get;
match e {
  gctx := fun n => (match st.env.find? n with
    | some _ => [(n, [])]
    | none   => [] : List NameRes),
  lctx := {},
  currMacroScope := st.nextMacroScope,
  macros := fun k =>
    -- our hardcoded example macros
    if k == `Lean.Parser.Term.stxQuot then some expandStxQuot
    else if k == `Lean.Parser.Term.do then some expandDo
    else if k == `Lean.Parser.Term.paren then some expandParen
    -- `notation`, `macro`, and macros generated at runtime
    else
      let table := (macroAttribute.ext.getState st.env).table;
      match table.find? k with
      | some (t::_) => some (fun stx ctx => match t stx {mainModule := `Expander, ..ctx} with Except.ok stx => stx | _ => Syntax.missing)
      | _           => none
} (st.nextMacroScope + 1) with
| Except.ok (stx, nextMacroScope) => do
  modify (fun st => {st with nextMacroScope := nextMacroScope});
  pure stx
| Except.error e => do
  logError ref e;
  pure Syntax.missing

partial def processCommand : Syntax → FrontendM Unit
| cmd => do
  cmd' ← expanderToFrontend cmd (expand cmd);
  if cmd'.isOfKind nullKind then
    -- expander returned multiple commands => process in turn
    cmd'.getArgs.forM processCommand
  else do
    runCommandElabM $ logInfo cmd (pp cmd');
    elabCommandAtFrontend cmd'

partial def processCommands : Unit → FrontendM Unit
| () => do
  cmdState    ← getCommandState;
  parserState ← getParserState;
  inputCtx    ← getInputContext;
  (cmd, ps, messages) ← pure (Parser.parseCommand cmdState.env inputCtx parserState cmdState.messages);
  setParserState ps;
  setMessages messages;
  if Parser.isEOI cmd then do
    pure ()
  else do
    processCommand cmd;
    processCommands ()

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
let fileName   := fileName.getD "<input>";
let inputCtx   := Parser.mkInputContext input fileName;
parserStateRef ← IO.mkRef { Parser.ModuleParserState . };
cmdStateRef    ← IO.mkRef $ Command.mkState env {} opts;
ps ← parserStateRef.get;
cmdPosRef ← IO.mkRef ps.pos;
EIO.adaptExcept (fun (ex : Empty) => Empty.rec _ ex) $
  processCommands () { commandStateRef := cmdStateRef, parserStateRef := parserStateRef, cmdPosRef := cmdPosRef, inputCtx := inputCtx };
cmdState ← cmdStateRef.get;
pure (cmdState.env, cmdState.messages)

def run (input : String) : MetaIO Unit := do
env  ← MetaIO.getEnv;
opts ← MetaIO.getOptions;
(env, messages) ← liftM $ process input env opts;
messages.forM $ fun msg => IO.println msg;
pure ()

end Elaboration

-- examples
-- see also `hideMacroRulesRhs` above

#eval run "
def x := 1
def e := fun (y : Nat) ⇒ x
notation \"const\" e ⇒ fun (x : Nat) ⇒ e
def y := const x
"

#eval run "
macro \"m\" n:ident : command => `(
  def f := 1
  macro \"mm\" : command => `(
    def $n:ident := f
    def f := $n:ident
  )
)
m f
mm
mm
"

end Expander
end Lean
